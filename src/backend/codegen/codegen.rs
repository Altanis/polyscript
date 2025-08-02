use inkwell::basic_block::BasicBlock;
// backend/codegen/codegen.rs
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue};
use inkwell::{AddressSpace, FloatPredicate, IntPredicate};
use std::collections::HashMap;

use crate::frontend::semantics::analyzer::{AllocationKind, NameInterner, PrimitiveKind, SemanticAnalyzer, Type, TypeSymbolId, TypeSymbolKind, ValueSymbolId};
use crate::frontend::syntax::ast::{AstNode, AstNodeKind, BoxedAstNode};
use crate::utils::kind::Operation;

pub type StringLiteralId = usize;

pub struct CodeGen<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    
    analyzer: &'a SemanticAnalyzer,

    variables: HashMap<ValueSymbolId, PointerValue<'ctx>>,
    functions: HashMap<ValueSymbolId, FunctionValue<'ctx>>,

    string_interner: NameInterner,
    string_literals: HashMap<StringLiteralId, PointerValue<'ctx>>,
    
    continue_blocks: Vec<BasicBlock<'ctx>>,
    break_blocks: Vec<BasicBlock<'ctx>>,

    current_function: Option<FunctionValue<'ctx>>,
    
    type_map: HashMap<TypeSymbolId, BasicTypeEnum<'ctx>>,
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    pub fn get_malloc(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("malloc") {
            return func;
        }

        let usize_type = self.context.i64_type();
        let ret_type = self.context.ptr_type(AddressSpace::default());
        let malloc_type = ret_type.fn_type(&[usize_type.into()], false);
        self.module.add_function("malloc", malloc_type, None)
    }

    pub fn get_free(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("free") {
            return func;
        }

        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let free_type = self.context.void_type().fn_type(&[ptr_type.into()], false);
        self.module.add_function("free", free_type, None)
    }

    pub fn build_malloc(&self, size: IntValue<'ctx>) -> PointerValue<'ctx> {
        let malloc_fn = self.get_malloc();

        self.builder
            .build_call(malloc_fn, &[size.into()], "")
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value()
    }

    pub fn build_free(&self, ptr: PointerValue<'ctx>) {
        let free_fn = self.get_free();

        self.builder
            .build_call(free_fn, &[ptr.into()], "")
            .unwrap();
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    /// Maps a semantic type from the analyzer to a concrete LLVM type.
    fn map_semantic_type(&mut self, ty: &Type) -> Option<BasicTypeEnum<'ctx>> {
        match ty {
            Type::Base { symbol, .. } => {
                if let Some(&llvm_ty) = self.type_map.get(symbol) {
                    return Some(llvm_ty);
                }

                let type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
                let llvm_ty = match &type_symbol.kind {
                    TypeSymbolKind::Primitive(p) => match p {
                        PrimitiveKind::Int => self.context.i64_type().as_basic_type_enum(),
                        PrimitiveKind::Float => self.context.f64_type().as_basic_type_enum(),
                        PrimitiveKind::Bool => self.context.bool_type().as_basic_type_enum(),
                        PrimitiveKind::Char => self.context.i8_type().as_basic_type_enum(),
                        PrimitiveKind::String => self.context.ptr_type(AddressSpace::default()).as_basic_type_enum(),
                        PrimitiveKind::Void | PrimitiveKind::Never => return None,
                    },
                    TypeSymbolKind::Struct((scope_id, _)) => {
                        let struct_name = self.analyzer.symbol_table.get_type_name(type_symbol.name_id);
                        if let Some(existing) = self.module.get_struct_type(struct_name) {
                            return Some(existing.as_basic_type_enum());
                        }

                        let llvm_struct = self.context.opaque_struct_type(struct_name);
                        self.type_map.insert(*symbol, llvm_struct.as_basic_type_enum());
    
                        let scope = self.analyzer.symbol_table.get_scope(*scope_id).unwrap();
                        let mut field_symbols: Vec<_> = scope.values.values()
                            .map(|&id| self.analyzer.symbol_table.get_value_symbol(id).unwrap())
                            .collect();
                        field_symbols.sort_by_key(|s| s.span.unwrap().start);
    
                        let field_types: Vec<_> = field_symbols.iter()
                            .map(|field_symbol| self.map_semantic_type(field_symbol.type_id.as_ref().unwrap()).unwrap())
                            .collect();
                        
                        llvm_struct.set_body(&field_types, false);
                        llvm_struct.as_basic_type_enum()
                    },
                    _ => unimplemented!("map_semantic_type for complex type: {}", self.analyzer.symbol_table.display_type_symbol(type_symbol)),
                };

                self.type_map.insert(*symbol, llvm_ty);
                Some(llvm_ty)
            },
            Type::Reference(_) | Type::MutableReference(_) 
                => Some(self.context.ptr_type(AddressSpace::default()).as_basic_type_enum())
        }
    }

    fn is_primitive(&self, ty: &Type) -> bool {
        match ty {
            Type::Base { symbol, .. } => {
                let type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
                matches!(type_symbol.kind, TypeSymbolKind::Primitive(_))
            },
            _ => false
        }
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    fn compile_integer_literal(&mut self, value: i64) -> BasicValueEnum<'ctx> {
        self.context.i64_type()
            .const_int(value as u64, true)
            .as_basic_value_enum()
    }

    fn compile_float_literal(&mut self, value: f64) -> BasicValueEnum<'ctx> {
        self.context.f64_type()
            .const_float(value)
            .as_basic_value_enum()
    }

    fn compile_bool_literal(&mut self, value: bool) -> BasicValueEnum<'ctx> {
        self.context.bool_type()
            .const_int(value as u64, false)
            .as_basic_value_enum()
    }

    fn compile_string_literal(&mut self, value: &String) -> BasicValueEnum<'ctx> {
        let key = self.string_interner.intern(value);
        if let Some(ptr) = self.string_literals.get(&key) {
            return ptr.as_basic_value_enum();
        }

        let string_const = self.context.const_string(value.as_bytes(), true);

        let global = self.module.add_global(string_const.get_type(), None, "");
        global.set_initializer(&string_const);
        global.set_constant(true);
        global.set_linkage(Linkage::Private);

        let ptr_type = string_const.get_type();
        let zero = self.context.i32_type().const_int(0, false);

        let ptr = unsafe {
            self.builder.build_gep(
                ptr_type, 
                global.as_pointer_value(), 
                &[zero, zero], 
                ""
            ).unwrap()
        };

        self.string_literals.insert(key, ptr);
        ptr.as_basic_value_enum()
    }

    fn compile_char_literal(&mut self, value: char) -> BasicValueEnum<'ctx> {
        self.context.i8_type()
            .const_int(value as u8 as u64, false)
            .as_basic_value_enum()
    }

    fn compile_identifier(&mut self, value_id: ValueSymbolId, ty: &Type) -> BasicValueEnum<'ctx> {
        if let Some(&ptr) = self.variables.get(&value_id) {
            let ty = self.map_semantic_type(ty).unwrap();
            return self.builder.build_load(ty, ptr, "").unwrap();
        }

        if let Some(func) = self.functions.get(&value_id) {
            return func.as_global_value().as_basic_value_enum();
        }

        panic!("unresolved identiifer during codegen");
    }

    fn compile_variable_declaration(&mut self, initializer: &BoxedAstNode, value_id: ValueSymbolId) -> Option<BasicValueEnum<'ctx>> {
        let symbol = self.analyzer.symbol_table.get_value_symbol(value_id).unwrap();
        let ty = symbol.type_id.as_ref().unwrap();

        let ptr = match symbol.allocation_kind {
            AllocationKind::Stack => {
                let ty = self.map_semantic_type(ty).unwrap();
                self.builder.build_alloca(ty, "").unwrap()
            },
            AllocationKind::Heap if matches!(initializer.kind, AstNodeKind::HeapExpression(_)) => {
                let ty = self.map_semantic_type(ty).unwrap();
                self.builder.build_alloca(ty, "").unwrap()
            },
            AllocationKind::Heap => {
                let llvm_ty = self.map_semantic_type(ty).unwrap();
                let size = llvm_ty.size_of().unwrap();
                self.build_malloc(size)
            },
            _ => unreachable!(),
        };

        self.variables.insert(value_id, ptr);

        let init_val = self.compile_node(initializer).unwrap();
        self.builder.build_store(ptr, init_val).unwrap();

        None
    }

    fn compile_place_expression(&mut self, node: &AstNode) -> Option<PointerValue<'ctx>> {
        match &node.kind {
            AstNodeKind::Identifier(_) => {
                let var_id = node.value_id.unwrap();
                self.variables.get(&var_id).copied()
            },
            AstNodeKind::UnaryOperation { operator: Operation::Dereference, operand } => {
                let ptr_to_ptr = self.compile_node(operand).unwrap().into_pointer_value();
                let inner_ptr_type = self.map_semantic_type(node.type_id.as_ref().unwrap()).unwrap();
                Some(self.builder.build_load(inner_ptr_type, ptr_to_ptr, "").unwrap().into_pointer_value())
            },
            _ => panic!("Expression is not a valid place expression for codegen: {:?}", node.kind),
        }
    }

    fn compile_unary_operation(&mut self, operator: Operation, operand_node: &BoxedAstNode) -> Option<BasicValueEnum<'ctx>> {
        if operator == Operation::ImmutableAddressOf || operator == Operation::MutableAddressOf {
            let ptr = self.compile_place_expression(operand_node).unwrap();
            return Some(ptr.as_basic_value_enum());
        }

        if operator == Operation::Dereference {
            let operand = self.compile_node(operand_node).unwrap();
            let ptr = operand.into_pointer_value();
            let operand_type = operand_node.type_id.as_ref().unwrap();

            let pointee_type_id = match operand_type {
                Type::Reference(inner) | Type::MutableReference(inner) => inner,
                _ => panic!("CodeGen: cannot dereference non-pointer type"),
            };

            let pointee_type = self.map_semantic_type(pointee_type_id).unwrap();
            return Some(self.builder.build_load(pointee_type, ptr, "").unwrap());
        }
    
        let operand_type = operand_node.type_id.as_ref().unwrap();
        if !self.is_primitive(operand_type) {
            unimplemented!("codegen for overloaded unary operator `{:?}` on type `{}`", operator, self.analyzer.symbol_table.display_type(operand_type));
        }
        
        let operand = self.compile_node(operand_node).unwrap();
        let is_float = operand.is_float_value();
    
        match operator {
            Operation::Neg => {
                if is_float {
                    Some(self.builder.build_float_neg(operand.into_float_value(), "").unwrap().into())
                } else {
                    Some(self.builder.build_int_neg(operand.into_int_value(), "").unwrap().into())
                }
            },
            Operation::Not | Operation::BitwiseNegate => {
                Some(self.builder.build_not(operand.into_int_value(), "").unwrap().into())
            },
            _ => unreachable!("Operator `{:?}` was not handled", operator),
        }
    }

    fn compile_core_binary_op(&mut self, operator: Operation, left: BasicValueEnum<'ctx>, right: BasicValueEnum<'ctx>, is_float: bool) -> BasicValueEnum<'ctx> {
        if is_float {
            let l = left.into_float_value();
            let r = right.into_float_value();
            match operator {
                Operation::Plus => self.builder.build_float_add(l, r, "").unwrap().into(),
                Operation::Minus => self.builder.build_float_sub(l, r, "").unwrap().into(),
                Operation::Mul => self.builder.build_float_mul(l, r, "").unwrap().into(),
                Operation::Div => self.builder.build_float_div(l, r, "").unwrap().into(),
                Operation::Mod => self.builder.build_float_rem(l, r, "").unwrap().into(),
                Operation::Equivalence => self.builder.build_float_compare(FloatPredicate::OEQ, l, r, "").unwrap().into(),
                Operation::NotEqual => self.builder.build_float_compare(FloatPredicate::ONE, l, r, "").unwrap().into(),
                Operation::GreaterThan => self.builder.build_float_compare(FloatPredicate::OGT, l, r, "").unwrap().into(),
                Operation::Geq => self.builder.build_float_compare(FloatPredicate::OGE, l, r, "").unwrap().into(),
                Operation::LessThan => self.builder.build_float_compare(FloatPredicate::OLT, l, r, "").unwrap().into(),
                Operation::Leq => self.builder.build_float_compare(FloatPredicate::OLE, l, r, "").unwrap().into(),
                _ => unreachable!("codegen for non-primitive float binary op: {:?}", operator)
            }
        } else {
            let l = left.into_int_value();
            let r = right.into_int_value();
            match operator {
                Operation::Plus => self.builder.build_int_add(l, r, "").unwrap().into(),
                Operation::Minus => self.builder.build_int_sub(l, r, "").unwrap().into(),
                Operation::Mul => self.builder.build_int_mul(l, r, "").unwrap().into(),
                Operation::Div => self.builder.build_int_signed_div(l, r, "").unwrap().into(),
                Operation::Mod => self.builder.build_int_signed_rem(l, r, "").unwrap().into(),
                Operation::BitwiseAnd => self.builder.build_and(l, r, "").unwrap().into(),
                Operation::BitwiseOr => self.builder.build_or(l, r, "").unwrap().into(),
                Operation::BitwiseXor => self.builder.build_xor(l, r, "").unwrap().into(),
                Operation::LeftBitShift => self.builder.build_left_shift(l, r, "").unwrap().into(),
                Operation::RightBitShift => self.builder.build_right_shift(l, r, true, "").unwrap().into(),
                Operation::Equivalence => self.builder.build_int_compare(IntPredicate::EQ, l, r, "").unwrap().into(),
                Operation::NotEqual => self.builder.build_int_compare(IntPredicate::NE, l, r, "").unwrap().into(),
                Operation::GreaterThan => self.builder.build_int_compare(IntPredicate::SGT, l, r, "").unwrap().into(),
                Operation::Geq => self.builder.build_int_compare(IntPredicate::SGE, l, r, "").unwrap().into(),
                Operation::LessThan => self.builder.build_int_compare(IntPredicate::SLT, l, r, "").unwrap().into(),
                Operation::Leq => self.builder.build_int_compare(IntPredicate::SLE, l, r, "").unwrap().into(),
                _ => unreachable!("codegen for non-primitive int/bool binary op: {:?}", operator)
            }
        }
    }

    fn compile_binary_operation(&mut self, operator: Operation, left_node: &BoxedAstNode, right_node: &BoxedAstNode) -> Option<BasicValueEnum<'ctx>> {
        if operator == Operation::Assign {
            let target_ptr = self.compile_place_expression(left_node).unwrap();
            let value_to_store = self.compile_node(right_node).unwrap();
            self.builder.build_store(target_ptr, value_to_store).unwrap();
            return None;
        }

        let left_type = left_node.type_id.as_ref().unwrap();
        if !self.is_primitive(left_type) {
            unimplemented!("codegen for overloaded binary operator `{:?}` on type `{}`", operator, self.analyzer.symbol_table.display_type(left_type));
        }

        if operator.is_assignment() {
            let target_ptr = self.compile_place_expression(left_node).unwrap();
            
            let base_op = match operator {
                Operation::PlusEq => Operation::Plus,
                Operation::MinusEq => Operation::Minus,
                Operation::MulEq => Operation::Mul,
                Operation::DivEq => Operation::Div,
                Operation::ModEq => Operation::Mod,
                Operation::BitwiseAndEq => Operation::BitwiseAnd,
                Operation::BitwiseOrEq => Operation::BitwiseOr,
                Operation::BitwiseXorEq => Operation::BitwiseXor,
                Operation::LeftBitShiftEq => Operation::LeftBitShift,
                Operation::RightBitShiftEq => Operation::RightBitShift,
                _ => unreachable!("unhandled compound assignment op {:?}", operator),
            };
            
            let loaded_left = self.builder.build_load(self.map_semantic_type(left_type).unwrap(), target_ptr, "").unwrap();
            let right = self.compile_node(right_node).unwrap();
            let is_float = loaded_left.is_float_value();
            
            let value_to_store = self.compile_core_binary_op(base_op, loaded_left, right, is_float);
            
            self.builder.build_store(target_ptr, value_to_store).unwrap();
            return None;
        }

        let left = self.compile_node(left_node).unwrap();
        let right = self.compile_node(right_node).unwrap();
        let is_float = left.is_float_value();

        Some(self.compile_core_binary_op(operator, left, right, is_float))
    }

    fn compile_conditional_operation(&mut self, operator: Operation, left: &BoxedAstNode, right: &BoxedAstNode) -> Option<BasicValueEnum<'ctx>> {
        let function = self.current_function.unwrap();
    
        match operator {
            Operation::And => {
                let left_val = self.compile_node(left).unwrap().into_int_value();
                let then_block = self.context.append_basic_block(function, "");
                let else_block = self.context.append_basic_block(function, "");
                let merge_block = self.context.append_basic_block(function, "");
    
                self.builder.build_conditional_branch(left_val, then_block, else_block).unwrap();
    
                self.builder.position_at_end(then_block);
                let right_val = self.compile_node(right).unwrap().into_int_value();
                self.builder.build_unconditional_branch(merge_block).unwrap();
                let then_block_end = self.builder.get_insert_block().unwrap();
    
                self.builder.position_at_end(else_block);
                self.builder.build_unconditional_branch(merge_block).unwrap();
                let else_block_end = self.builder.get_insert_block().unwrap();
                
                self.builder.position_at_end(merge_block);
                let phi = self.builder.build_phi(self.context.bool_type(), "").unwrap();
                phi.add_incoming(&[
                    (&right_val, then_block_end),
                    (&left_val, else_block_end),
                ]);
                
                Some(phi.as_basic_value())
            },
            Operation::Or => {
                let left_val = self.compile_node(left).unwrap().into_int_value();
                let then_block = self.context.append_basic_block(function, "");
                let else_block = self.context.append_basic_block(function, "");
                let merge_block = self.context.append_basic_block(function, "");
    
                self.builder.build_conditional_branch(left_val, else_block, then_block).unwrap();
    
                self.builder.position_at_end(then_block);
                let right_val = self.compile_node(right).unwrap().into_int_value();
                self.builder.build_unconditional_branch(merge_block).unwrap();
                let then_block_end = self.builder.get_insert_block().unwrap();
    
                self.builder.position_at_end(else_block);
                self.builder.build_unconditional_branch(merge_block).unwrap();
                let else_block_end = self.builder.get_insert_block().unwrap();
                
                self.builder.position_at_end(merge_block);
                let phi = self.builder.build_phi(self.context.bool_type(), "").unwrap();
                phi.add_incoming(&[
                    (&right_val, then_block_end),
                    (&left_val, else_block_end),
                ]);
                
                Some(phi.as_basic_value())
            },
            _ => {
                let left_type = left.type_id.as_ref().unwrap();
                if !self.is_primitive(left_type) {
                    unimplemented!("codegen for overloaded conditional operator `{:?}` on type `{}`", operator, self.analyzer.symbol_table.display_type(left_type));
                }

                let left_val = self.compile_node(left).unwrap();
                let right_val = self.compile_node(right).unwrap();
                let is_float = left_val.is_float_value();

                Some(self.compile_core_binary_op(operator, left_val, right_val, is_float))
            }
        }
    }

    fn compile_heap_expression(&mut self, inner_expr: &BoxedAstNode) -> Option<BasicValueEnum<'ctx>> {
        let inner_type = inner_expr.type_id.as_ref().unwrap();
        let llvm_inner_type = self.map_semantic_type(inner_type).unwrap();

        let size = llvm_inner_type.size_of().unwrap();
        let raw_ptr = self.build_malloc(size);

        let inner_value = self.compile_node(inner_expr).unwrap();
        self.builder.build_store(raw_ptr, inner_value).unwrap();

        Some(raw_ptr.as_basic_value_enum())
    }

    fn compile_block(&mut self, stmts: &[AstNode]) -> Option<BasicValueEnum<'ctx>> {
        let mut last_val = None;

        for stmt in stmts {
            last_val = self.compile_node(stmt);
        }

        last_val
    }

    fn compile_if_statement(
        &mut self,
        condition: &BoxedAstNode,
        then_branch: &BoxedAstNode,
        else_if_branches: &[(BoxedAstNode, BoxedAstNode)],
        else_branch: &Option<BoxedAstNode>,
        return_type: Option<&Type>,
    ) -> Option<BasicValueEnum<'ctx>> {
        let function = self.current_function.unwrap();
        
        let merge_block = self.context.append_basic_block(function, "");
        
        let mut incoming_phis = Vec::new();

        let cond_val = self.compile_node(condition).unwrap().into_int_value();
        let then_block = self.context.append_basic_block(function, "");
        
        let mut last_else_block = self.context.append_basic_block(function, "");
        self.builder.build_conditional_branch(cond_val, then_block, last_else_block).unwrap();

        self.builder.position_at_end(then_block);
        let then_val = self.compile_node(then_branch);
        if self.builder.get_insert_block().unwrap().get_terminator().is_none() {
            self.builder.build_unconditional_branch(merge_block).unwrap();
        }
        if let Some(val) = then_val {
            incoming_phis.push((val, self.builder.get_insert_block().unwrap()));
        }

        for (else_if_cond, elseif_branch) in else_if_branches.iter() {
            self.builder.position_at_end(last_else_block);
            
            let elseif_then_block = self.context.append_basic_block(function, "");
            let next_else_block = self.context.append_basic_block(function, "");

            let elseif_cond_val = self.compile_node(else_if_cond).unwrap().into_int_value();
            self.builder.build_conditional_branch(elseif_cond_val, elseif_then_block, next_else_block).unwrap();
            
            self.builder.position_at_end(elseif_then_block);
            let elseif_val = self.compile_node(elseif_branch);
            if self.builder.get_insert_block().unwrap().get_terminator().is_none() {
                self.builder.build_unconditional_branch(merge_block).unwrap();
            }
            if let Some(val) = elseif_val {
                incoming_phis.push((val, self.builder.get_insert_block().unwrap()));
            }
            
            last_else_block = next_else_block;
        }

        self.builder.position_at_end(last_else_block);
        if let Some(else_node) = else_branch {
            let else_val = self.compile_node(else_node);
            if let Some(val) = else_val {
                incoming_phis.push((val, self.builder.get_insert_block().unwrap()));
            }
        }
        if self.builder.get_insert_block().unwrap().get_terminator().is_none() {
            self.builder.build_unconditional_branch(merge_block).unwrap();
        }

        self.builder.position_at_end(merge_block);

        if let Some(ty) = return_type
            && !matches!(self.analyzer.symbol_table.get_type_symbol(ty.get_base_symbol()).unwrap().kind, TypeSymbolKind::Primitive(PrimitiveKind::Void | PrimitiveKind::Never))
            && !incoming_phis.is_empty()
        {
            let llvm_type = self.map_semantic_type(ty).unwrap();
            let phi = self.builder.build_phi(llvm_type, "").unwrap();

            for (val, block) in incoming_phis {
                phi.add_incoming(&[(&val, block)]);
            }

            return Some(phi.as_basic_value());
        }
        
        None
    }

    fn compile_while_loop(&mut self, condition: &BoxedAstNode, body: &BoxedAstNode) -> Option<BasicValueEnum<'ctx>> {
        let function = self.current_function.unwrap();

        let cond_block = self.context.append_basic_block(function, "while.cond");
        let body_block = self.context.append_basic_block(function, "while.body");
        let after_block = self.context.append_basic_block(function, "while.after");

        self.continue_blocks.push(cond_block);
        self.break_blocks.push(after_block);

        self.builder.build_unconditional_branch(cond_block).unwrap();

        self.builder.position_at_end(cond_block);
        let cond_val = self.compile_node(condition).unwrap().into_int_value();
        self.builder.build_conditional_branch(cond_val, body_block, after_block).unwrap();

        self.builder.position_at_end(body_block);
        self.compile_node(body);
        if self.builder.get_insert_block().unwrap().get_terminator().is_none() {
            self.builder.build_unconditional_branch(cond_block).unwrap();
        }

        self.builder.position_at_end(after_block);
        
        self.continue_blocks.pop();
        self.break_blocks.pop();

        None
    }

    fn compile_for_loop(
        &mut self,
        initializer: &Option<BoxedAstNode>,
        condition: &Option<BoxedAstNode>,
        increment: &Option<BoxedAstNode>,
        body: &BoxedAstNode,
    ) -> Option<BasicValueEnum<'ctx>> {
        let function = self.current_function.unwrap();

        if let Some(init) = initializer {
            self.compile_node(init);
        }

        let cond_block = self.context.append_basic_block(function, "for.cond");
        let body_block = self.context.append_basic_block(function, "for.body");
        let inc_block = self.context.append_basic_block(function, "for.inc");
        let after_block = self.context.append_basic_block(function, "for.after");

        self.continue_blocks.push(inc_block);
        self.break_blocks.push(after_block);

        self.builder.build_unconditional_branch(cond_block).unwrap();

        self.builder.position_at_end(cond_block);
        let cond_val = if let Some(cond) = condition {
            self.compile_node(cond).unwrap().into_int_value()
        } else {
            self.context.bool_type().const_int(1, false)
        };
        self.builder.build_conditional_branch(cond_val, body_block, after_block).unwrap();

        self.builder.position_at_end(body_block);
        self.compile_node(body);
        if self.builder.get_insert_block().unwrap().get_terminator().is_none() {
            self.builder.build_unconditional_branch(inc_block).unwrap();
        }

        self.builder.position_at_end(inc_block);
        if let Some(inc) = increment {
            self.compile_node(inc);
        }
        if self.builder.get_insert_block().unwrap().get_terminator().is_none() {
            self.builder.build_unconditional_branch(cond_block).unwrap();
        }

        self.builder.position_at_end(after_block);
        
        self.continue_blocks.pop();
        self.break_blocks.pop();
        
        None
    }

    fn compile_type_cast(&mut self, expr: &BoxedAstNode, target_type: &Type) -> Option<BasicValueEnum<'ctx>> {
        let source_val = self.compile_node(expr).unwrap();
        let source_type = expr.type_id.as_ref().unwrap();

        let llvm_target_type = self.map_semantic_type(target_type).unwrap();

        let source_prim = if let Type::Base { symbol, .. } = source_type {
            if let TypeSymbolKind::Primitive(p) = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap().kind { Some(p) } else { None }
        } else { None };

        let target_prim = if let Type::Base { symbol, .. } = target_type {
            if let TypeSymbolKind::Primitive(p) = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap().kind { Some(p) } else { None }
        } else { None };

        match (source_prim, target_prim) {
            (Some(PrimitiveKind::Int), Some(PrimitiveKind::Float)) => {
                Some(self.builder.build_signed_int_to_float(source_val.into_int_value(), llvm_target_type.into_float_type(), "").unwrap().into())
            },
            (Some(PrimitiveKind::Float), Some(PrimitiveKind::Int)) => {
                Some(self.builder.build_float_to_signed_int(source_val.into_float_value(), llvm_target_type.into_int_type(), "").unwrap().into())
            },
            (Some(PrimitiveKind::Int), Some(PrimitiveKind::Int)) |
            (Some(PrimitiveKind::Char), Some(PrimitiveKind::Int)) |
            (Some(PrimitiveKind::Int), Some(PrimitiveKind::Char)) => {
                Some(self.builder.build_int_cast_sign_flag(source_val.into_int_value(), llvm_target_type.into_int_type(), true, "").unwrap().into())
            },
            (Some(PrimitiveKind::Float), Some(PrimitiveKind::Float)) => {
                Some(self.builder.build_float_cast(source_val.into_float_value(), llvm_target_type.into_float_type(), "").unwrap().into())
            },
            _ => panic!("cannot cast {:?} to {:?}", source_prim, target_prim)
        }
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    pub fn new(context: &'ctx Context, builder: &'a Builder<'ctx>, module: &'a Module<'ctx>, analyzer: &'a SemanticAnalyzer) -> Self {
        CodeGen {
            context,
            builder,
            module,
            analyzer,
            variables: HashMap::new(),
            functions: HashMap::new(),
            string_interner: NameInterner::new(),
            string_literals: HashMap::new(),
            continue_blocks: vec![],
            break_blocks: vec![],
            current_function: None,
            type_map: HashMap::new(),
        }
    }

    pub fn compile_program(&mut self, program: &AstNode) {
        let fn_type = self.context.i32_type().fn_type(&[], false);
        let main_fn = self.module.add_function("main", fn_type, None);
        self.current_function = Some(main_fn);
        let entry = self.context.append_basic_block(main_fn, "entry");
        self.builder.position_at_end(entry);

        let AstNodeKind::Program(stmts) = &program.kind else { unreachable!(); };
        for stmt in stmts.iter() {
            self.compile_node(stmt);
        }

        if self.builder.get_insert_block().and_then(|b| b.get_terminator()).is_none() {
            self.builder.build_return(Some(&self.context.i32_type().const_int(0, false))).unwrap();
        }
    }

    fn compile_node(&mut self, stmt: &AstNode) -> Option<BasicValueEnum<'ctx>> {
        match &stmt.kind {
            AstNodeKind::IntegerLiteral(value) => Some(self.compile_integer_literal(*value)),
            AstNodeKind::FloatLiteral(value) => Some(self.compile_float_literal(*value)),
            AstNodeKind::BooleanLiteral(value) => Some(self.compile_bool_literal(*value)),
            AstNodeKind::StringLiteral(value) => Some(self.compile_string_literal(value)),
            AstNodeKind::CharLiteral(value) => Some(self.compile_char_literal(*value)),
            AstNodeKind::Identifier(_) => Some(self.compile_identifier(stmt.value_id.unwrap(), stmt.type_id.as_ref().unwrap())),
            AstNodeKind::VariableDeclaration { initializer, .. }
                => self.compile_variable_declaration(initializer, stmt.value_id.unwrap()),
            AstNodeKind::UnaryOperation { operator, operand }
                => self.compile_unary_operation(*operator, operand),
            AstNodeKind::BinaryOperation { operator, left, right }
                => self.compile_binary_operation(*operator, left, right),
            AstNodeKind::ConditionalOperation { operator, left, right }
                => self.compile_conditional_operation(*operator, left, right),
            AstNodeKind::HeapExpression(expr) => self.compile_heap_expression(expr),
            AstNodeKind::Block(stmts) => self.compile_block(stmts),
            AstNodeKind::ExpressionStatement(expr) => {
                self.compile_node(expr);
                None
            },
            AstNodeKind::Return(opt_expr) => {
                if let Some(expr) = opt_expr {
                    let value = self.compile_node(expr).unwrap();
                    self.builder.build_return(Some(&value)).unwrap();
                } else {
                    self.builder.build_return(None).unwrap();
                }

                None
            },
            AstNodeKind::IfStatement {
                condition,
                then_branch,
                else_if_branches,
                else_branch,
            } => self.compile_if_statement(condition, then_branch, else_if_branches, else_branch, stmt.type_id.as_ref()),
            AstNodeKind::WhileLoop { condition, body } => self.compile_while_loop(condition, body),
            AstNodeKind::ForLoop { initializer, condition, increment, body }
                => self.compile_for_loop(initializer, condition, increment, body),
            AstNodeKind::Break => {
                let break_block = self.break_blocks.last().unwrap();
                self.builder.build_unconditional_branch(*break_block).unwrap();
                None
            },
            AstNodeKind::Continue => {
                let continue_block = self.continue_blocks.last().unwrap();
                self.builder.build_unconditional_branch(*continue_block).unwrap();
                None
            },
            AstNodeKind::TypeCast { expr, .. }
                => self.compile_type_cast(expr, stmt.type_id.as_ref().unwrap()),
            _ => unimplemented!()
        }
    }
}