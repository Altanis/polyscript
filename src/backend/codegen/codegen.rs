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

        match symbol.allocation_kind {
            AllocationKind::Stack => {
                let ty = self.map_semantic_type(ty).unwrap();
                let alloca = self.builder.build_alloca(ty, "").unwrap();
                self.variables.insert(value_id, alloca);

                let init_val = self.compile_node(initializer).unwrap();
                self.builder.build_store(alloca, init_val).unwrap();
            },
            AllocationKind::Heap => {
                let llvm_ty = self.map_semantic_type(ty).unwrap();
                let size = llvm_ty.size_of().unwrap();

                let ptr = self.build_malloc(size);

                self.variables.insert(value_id, ptr);

                let init_val = self.compile_node(initializer).unwrap();
                self.builder.build_store(ptr, init_val).unwrap();
            },
            _ => unreachable!()
        }

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
            current_function: None,
            type_map: HashMap::new(),
        }
    }

    pub fn compile_program(&mut self, program: &AstNode) {
        let AstNodeKind::Program(stmts) = &program.kind else { unreachable!(); };
        for stmt in stmts.iter() {
            self.compile_node(stmt);
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
            _ => unimplemented!()
        }
    }
}