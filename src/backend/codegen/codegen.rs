use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicType, BasicTypeEnum, FunctionType};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue};
use inkwell::{AddressSpace, FloatPredicate, IntPredicate};
use std::collections::HashMap;

use crate::frontend::semantics::analyzer::{
    AllocationKind, NameInterner, PrimitiveKind, SemanticAnalyzer, TraitImpl, Type, TypeSymbolId,
    TypeSymbolKind, ValueSymbolId, ValueSymbolKind,
};
use crate::frontend::syntax::ast::{AstNode, AstNodeKind, BoxedAstNode};
use crate::utils::kind::Operation;

pub type StringLiteralId = usize;

pub struct CodeGen<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    
    fn_ast_map: HashMap<ValueSymbolId, &'a AstNode>,
    monomorphization_cache: HashMap<(ValueSymbolId, Vec<Type>), FunctionValue<'ctx>>,
    current_substitution_map: Option<HashMap<TypeSymbolId, Type>>,

    analyzer: &'a SemanticAnalyzer,

    variables: HashMap<ValueSymbolId, PointerValue<'ctx>>,
    functions: HashMap<ValueSymbolId, FunctionValue<'ctx>>,
    constants: HashMap<ValueSymbolId, BasicValueEnum<'ctx>>,

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
    fn resolve_type(&self, ty: &Type) -> Type {
        let mut current_ty = ty.clone();
        loop {
            let Type::Base { symbol, args } = &current_ty else { break };
            let type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();

            if let TypeSymbolKind::TypeAlias((_, Some(aliased_type))) = &type_symbol.kind {
                let substitutions = type_symbol
                    .generic_parameters
                    .iter()
                    .zip(args.iter())
                    .map(|(param_id, concrete_type)| (*param_id, concrete_type.clone()))
                    .collect();

                current_ty = Self::apply_codegen_substitution(aliased_type, &substitutions);
            } else {
                break;
            }
        }
        current_ty
    }

    fn is_impl_applicable(&self, instance_type: &Type, imp: &TraitImpl) -> bool {
        let instance_args = if let Type::Base { args, .. } = instance_type {
            args
        } else {
            return imp.type_specialization.is_empty();
        };

        let impl_target_arg_ids = &imp.type_specialization;
        if instance_args.len() != impl_target_arg_ids.len() {
            return false;
        }

        for (instance_arg, &impl_target_arg_id) in instance_args.iter().zip(impl_target_arg_ids) {
            let target_symbol = self.analyzer.symbol_table.get_type_symbol(impl_target_arg_id).unwrap();

            if !imp.impl_generic_params.contains(&target_symbol.id) {
                let resolved_instance_arg = self.resolve_type(instance_arg);
                let resolved_impl_arg = self.resolve_type(&Type::new_base(impl_target_arg_id));

                if resolved_instance_arg != resolved_impl_arg {
                    return false;
                }
            }
        }

        true
    }

    fn resolve_associated_type(&self, concrete_type: &Type, trait_type: &Type, member_name: &str) -> Option<Type> {
        let trait_id = trait_type.get_base_symbol();
        let type_id = concrete_type.get_base_symbol();

        let impls_for_trait = self.analyzer.trait_registry.register.get(&trait_id)?;
        let impls_for_type = impls_for_trait.get(&type_id)?;

        for imp in impls_for_type {
            if !self.is_impl_applicable(concrete_type, imp) {
                continue;
            }

            let assoc_type_symbol = self.analyzer.symbol_table.find_type_symbol_in_scope(member_name, imp.impl_scope_id).unwrap();
            let TypeSymbolKind::TypeAlias((_, Some(aliased_type_template))) = &assoc_type_symbol.kind else { unreachable!() };
            let instance_args = if let Type::Base { args, .. } = concrete_type { args } else { &vec![] };

            let mut substitutions: HashMap<_, _> = imp.impl_generic_params.iter()
                .zip(instance_args.iter())
                .map(|(param_id, concrete_type)| (*param_id, concrete_type.clone()))
                .collect();

            if let Type::Base { args, .. } = trait_type {
                let trait_symbol = self.analyzer.symbol_table.get_type_symbol(trait_id).unwrap();
                let trait_generic_substitutions: HashMap<_, _> = trait_symbol.generic_parameters.iter()
                    .zip(args.iter())
                    .map(|(param_id, concrete_type)| (*param_id, concrete_type.clone()))
                    .collect();

                substitutions.extend(trait_generic_substitutions);
            }

            return Some(Self::apply_codegen_substitution(
                aliased_type_template,
                &substitutions,
            ));
        }

        None
    }

    /// Maps a semantic type from the analyzer to a concrete LLVM type.
    fn map_semantic_type(&mut self, ty: &Type) -> Option<BasicTypeEnum<'ctx>> {
        let substitution = if let Type::Base { symbol, .. } = ty {
            if let Some(sub_map) = &self.current_substitution_map {
                sub_map.get(symbol).cloned() 
            } else {
                None
            }
        } else {
            None
        };

        if let Some(concrete_type) = substitution {
            return self.map_semantic_type(&concrete_type);
        }

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
                    TypeSymbolKind::Enum(_) => self.context.i64_type().as_basic_type_enum(),
                    TypeSymbolKind::Generic(_) => self.context.ptr_type(AddressSpace::default()).as_basic_type_enum(),
                    TypeSymbolKind::FunctionSignature { .. }
                        => self.context.ptr_type(AddressSpace::default()).as_basic_type_enum(),
                    TypeSymbolKind::TypeAlias((_, Some(aliased_type))) => return self.map_semantic_type(aliased_type),
                    TypeSymbolKind::OpaqueTypeProjection { ty: opaque_ty, tr: opaque_tr, member } => {
                        let mut concrete_base = opaque_ty.clone();
                        if let Some(substitutions) = &self.current_substitution_map {
                            concrete_base = Self::apply_codegen_substitution(&concrete_base, substitutions);
                        }
                        
                        let base_symbol_of_projection = self.analyzer.symbol_table.get_type_symbol(concrete_base.get_base_symbol()).unwrap();
                        
                        if let TypeSymbolKind::Generic(_) = base_symbol_of_projection.kind {
                            self.context.ptr_type(AddressSpace::default()).as_basic_type_enum()
                        } else {
                            let concrete_trait = if let Some(substitutions) = &self.current_substitution_map {
                                Self::apply_codegen_substitution(opaque_tr, substitutions)
                            } else {
                                opaque_tr.clone()
                            };

                            let resolved = self.resolve_associated_type(&concrete_base, &concrete_trait, member).unwrap();
                            return self.map_semantic_type(&resolved);
                        }
                    }
                    _ => unimplemented!("map_semantic_type for complex type: {}", self.analyzer.symbol_table.display_type_symbol(type_symbol)),
                };

                self.type_map.insert(*symbol, llvm_ty);
                Some(llvm_ty)
            },
            Type::Reference(_) | Type::MutableReference(_) 
                => Some(self.context.ptr_type(AddressSpace::default()).as_basic_type_enum())
        }
    }

    fn map_semantic_fn_type(&mut self, ty: &Type) -> FunctionType<'ctx> {
        let Type::Base { symbol, .. } = ty else { unreachable!(); };
        let type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
        let TypeSymbolKind::FunctionSignature { params, return_type, .. } = &type_symbol.kind else { unreachable!(); };

        let llvm_params: Vec<_> = params
            .iter()
            .filter_map(|p| self.map_semantic_type(p).map(|t| t.into()))
            .collect();

        let llvm_return = self.map_semantic_type(return_type);

        if let Some(ret_type) = llvm_return {
            ret_type.fn_type(&llvm_params, false)
        } else {
            self.context.void_type().fn_type(&llvm_params, false)
        }
    }

    /// Applies the current substitution context to a semantic function type
    /// to get the specialized signature.
    fn apply_codegen_substitution(ty: &Type, substitutions: &HashMap<TypeSymbolId, Type>) -> Type {
        match ty {
            Type::Base { symbol: base_symbol_id, args } => {
                if let Some(substituted_type) = substitutions.get(base_symbol_id) {
                    return substituted_type.clone();
                }

                let substituted_args = args
                    .iter()
                    .map(|arg| Self::apply_codegen_substitution(arg, substitutions))
                    .collect();

                Type::Base {
                    symbol: *base_symbol_id,
                    args: substituted_args,
                }
            },
            Type::Reference(inner) => {
                Type::Reference(Box::new(Self::apply_codegen_substitution(inner, substitutions)))
            },
            Type::MutableReference(inner) => {
                Type::MutableReference(Box::new(Self::apply_codegen_substitution(inner, substitutions)))
            }
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

    fn box_if_needed(&mut self, value: BasicValueEnum<'ctx>, from_type: &Type, to_type: &Type) -> BasicValueEnum<'ctx> {
        let to_symbol = self.analyzer.symbol_table.get_type_symbol(to_type.get_base_symbol()).unwrap();

        if let TypeSymbolKind::Generic(_) = to_symbol.kind {
            let from_symbol = self.analyzer.symbol_table.get_type_symbol(from_type.get_base_symbol()).unwrap();
            if !matches!(from_symbol.kind, TypeSymbolKind::Generic(_)) {
                let llvm_type = value.get_type();
                if !llvm_type.is_pointer_type() {
                    let size = llvm_type.size_of().unwrap();
                    let ptr = self.build_malloc(size);
                    self.builder.build_store(ptr, value).unwrap();
                    return ptr.as_basic_value_enum();
                }
            }
        }

        value
    }

    fn trait_name_to_fn_name(&self, trait_name: &str) -> String {
        trait_name
            .chars()
            .enumerate()
            .map(|(i, c)| {
                if i != 0 && c.is_uppercase() {
                    format!("_{}", c.to_lowercase())
                } else {
                    c.to_lowercase().to_string()
                }
            })
            .collect::<String>()
    }

    fn find_trait_fn(&mut self, instance_type: &Type, trait_name: &str, fn_name: &str, rhs_type: Option<&Type>) -> Option<FunctionValue<'ctx>> {
        let trait_id = *self.analyzer.trait_registry.default_traits.get(trait_name)?;
        let type_id = instance_type.get_base_symbol();

        let impls_for_trait = self.analyzer.trait_registry.register.get(&trait_id)?;
        let impls_for_type = impls_for_trait.get(&type_id)?;

        let applicable_impl = impls_for_type.iter().find(|imp| {
            match rhs_type {
                Some(the_rhs_type) => {
                    if let Some(&impl_rhs_symbol_id) = imp.trait_generic_specialization.first() {
                        return impl_rhs_symbol_id == the_rhs_type.get_base_symbol();
                    }

                    false
                },
                None => {
                    return imp.trait_generic_specialization.is_empty();
                }
            }
        })?;

        let fn_symbol = self
            .analyzer
            .symbol_table
            .find_value_symbol_in_scope(fn_name, applicable_impl.impl_scope_id)?;
            
        self.functions.get(&fn_symbol.id).copied()
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
            AstNodeKind::SelfExpr => {
                let var_id = node.value_id.unwrap();
                self.variables.get(&var_id).copied()
            },
            AstNodeKind::UnaryOperation { operator: Operation::Dereference, operand } => {
                let ptr_to_ptr = self.compile_node(operand).unwrap().into_pointer_value();
                let inner_ptr_type = self.map_semantic_type(node.type_id.as_ref().unwrap()).unwrap();
                Some(self.builder.build_load(inner_ptr_type, ptr_to_ptr, "").unwrap().into_pointer_value())
            },
            AstNodeKind::FieldAccess { left, right } => {
                let struct_ptr = self.compile_place_expression(left)?;
    
                let member_symbol = self.analyzer.symbol_table.get_value_symbol(right.value_id.unwrap()).unwrap();
                let member_scope = self.analyzer.symbol_table.get_scope(member_symbol.scope_id).unwrap();
    
                let mut sorted_field_symbols: Vec<_> = member_scope.values.values()
                    .map(|&id| self.analyzer.symbol_table.get_value_symbol(id).unwrap())
                    .collect();
                sorted_field_symbols.sort_by_key(|s| s.span.unwrap().start);
                let field_index = sorted_field_symbols
                    .iter()
                    .position(|s| s.id == member_symbol.id)
                    .unwrap() as u32;
    
                let left_type = left.type_id.as_ref().unwrap();
                let base_type = if let Type::Reference(inner) | Type::MutableReference(inner) = left_type {
                    &**inner
                } else {
                    left_type
                };
                
                let struct_llvm_type = self.map_semantic_type(base_type).unwrap().into_struct_type();
                let field_ptr = self.builder.build_struct_gep(struct_llvm_type, struct_ptr, field_index, "").unwrap();
                Some(field_ptr)
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
        if !self.is_primitive(operand_type) && let Some((trait_name, _)) = operator.to_trait_data() {
            let fn_name = self.trait_name_to_fn_name(&trait_name);
            let callee = self.find_trait_fn(operand_type, &trait_name, &fn_name, None).unwrap();
            
            let operand = self.compile_node(operand_node).unwrap();
            let call = self.builder.build_call(callee, &[operand.into()], "").unwrap();
            
            return call.try_as_basic_value().left();
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
        let right_type = right_node.type_id.as_ref().unwrap();
        
        if !self.is_primitive(left_type) && let Some((trait_name, _)) = operator.to_trait_data() {
            let fn_name = self.trait_name_to_fn_name(&trait_name);
            let callee = self.find_trait_fn(left_type, &trait_name, &fn_name, Some(right_type)).unwrap();

            let left = self.compile_node(left_node).unwrap();
            let right = self.compile_node(right_node).unwrap();

            let call = self.builder.build_call(callee, &[left.into(), right.into()], "").unwrap();
            return call.try_as_basic_value().left();
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

        let cond_block = self.context.append_basic_block(function, "");
        let body_block = self.context.append_basic_block(function, "");
        let after_block = self.context.append_basic_block(function, "");

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

        let cond_block = self.context.append_basic_block(function, "");
        let body_block = self.context.append_basic_block(function, "");
        let inc_block = self.context.append_basic_block(function, "");
        let after_block = self.context.append_basic_block(function, "");

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

        #[derive(Debug)]
        enum CastableKind {
            Int,
            Float,
            Char,
            Enum,
        }

        let get_kind = |ty: &Type| {
            if let Type::Base { symbol, .. } = ty {
                let sym = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
                return match sym.kind {
                    TypeSymbolKind::Primitive(PrimitiveKind::Int) => Some(CastableKind::Int),
                    TypeSymbolKind::Primitive(PrimitiveKind::Float) => Some(CastableKind::Float),
                    TypeSymbolKind::Primitive(PrimitiveKind::Char) => Some(CastableKind::Char),
                    TypeSymbolKind::Enum(_) => Some(CastableKind::Enum),
                    _ => None,
                };
            }
            None
        };

        let source_kind = get_kind(source_type);
        let target_kind = get_kind(target_type);

        match (source_kind, target_kind) {
            (Some(CastableKind::Int), Some(CastableKind::Float)) => Some(self.builder.build_signed_int_to_float(
                source_val.into_int_value(), 
                llvm_target_type.into_float_type(), 
                ""
            ).unwrap().into()),
            (Some(CastableKind::Float), Some(CastableKind::Int)) => Some(self.builder.build_float_to_signed_int(
                source_val.into_float_value(), 
                llvm_target_type.into_int_type(), 
                ""
            ).unwrap().into()),
            (Some(CastableKind::Int), Some(CastableKind::Int)) |
            (Some(CastableKind::Char), Some(CastableKind::Int)) |
            (Some(CastableKind::Int), Some(CastableKind::Char)) |
            (Some(CastableKind::Enum), Some(CastableKind::Int)) => Some(self.builder.build_int_cast_sign_flag(
                source_val.into_int_value(),
                llvm_target_type.into_int_type(), 
                true, ""
            ).unwrap().into()),
            (Some(CastableKind::Float), Some(CastableKind::Float)) => Some(self.builder.build_float_cast(
                source_val.into_float_value(),
                llvm_target_type.into_float_type(), ""
            ).unwrap().into()),
            (s, t) => panic!("codegen cannot handle cast from {:?} to {:?}", s, t)
        }
    }

    fn compile_struct_declaration(&mut self, struct_node: &AstNode) {
        let struct_type = struct_node.type_id.as_ref().unwrap();
        self.map_semantic_type(struct_type);
    }

    fn compile_enum_declaration(&mut self, enum_node: &AstNode) {
        let AstNodeKind::EnumDeclaration { name, variants } = &enum_node.kind else { unreachable!(); };

        let enum_type_symbol = self.analyzer.symbol_table.find_type_symbol_from_scope(enum_node.scope_id.unwrap(), name).unwrap();
        let enum_llvm_type = self.map_semantic_type(&Type::new_base(enum_type_symbol.id)).unwrap().into_int_type();

        let TypeSymbolKind::Enum((scope_id, _)) = enum_type_symbol.kind else { unreachable!(); };

        let mut current_discriminant: i64 = 0;

        for (variant_name, (_variant_node, initializer_opt)) in variants.iter() {
            if let Some(initializer) = initializer_opt && let AstNodeKind::IntegerLiteral(val) = initializer.kind {
                current_discriminant = val;
            }

            let variant_symbol = self.analyzer.symbol_table.find_value_symbol_in_scope(variant_name, scope_id).unwrap();
            let const_val = enum_llvm_type.const_int(current_discriminant as u64, false);

            self.constants.insert(variant_symbol.id, const_val.into());
            current_discriminant += 1;
        }
    }

    fn compile_function_declaration(&mut self, node: &AstNode) {
        let value_id = node.value_id.unwrap();
        let fn_symbol = self.analyzer.symbol_table.get_value_symbol(value_id).unwrap();
        let fn_type = fn_symbol.type_id.as_ref().unwrap();

        let llvm_fn_type = self.map_semantic_fn_type(fn_type);
        let fn_name = self.analyzer.symbol_table.get_value_name(fn_symbol.name_id);
        let function = self.module.add_function(fn_name, llvm_fn_type, None);

        self.functions.insert(value_id, function);
    }

    fn compile_function_body(&mut self, node: &AstNode) {
        let AstNodeKind::Function { parameters, body, .. } = &node.kind else { unreachable!(); };
        let function = self.functions[&node.value_id.unwrap()];

        let old_fn = self.current_function.take();
        let old_vars = self.variables.clone();
        self.variables.clear();
        self.current_function = Some(function);

        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        for (i, param_node) in parameters.iter().enumerate() {
            let param_value = function.get_nth_param(i as u32).unwrap();
            let param_symbol = self.analyzer.symbol_table.get_value_symbol(param_node.value_id.unwrap()).unwrap();
            let param_name = self.analyzer.symbol_table.get_value_name(param_symbol.name_id);
            param_value.set_name(param_name);

            let alloca = self.builder.build_alloca(param_value.get_type(), param_name).unwrap();
            self.builder.build_store(alloca, param_value).unwrap();
            self.variables.insert(param_node.value_id.unwrap(), alloca);
        }

        let body_val = self.compile_node(body.as_ref().unwrap());

        if self.builder.get_insert_block().and_then(|b| b.get_terminator()).is_none() {
            if function.get_type().get_return_type().is_some() {
                self.builder.build_return(Some(&body_val.unwrap())).unwrap();
            } else {
                self.builder.build_return(None).unwrap();
            }
        }
        
        self.current_function = old_fn;
        self.variables = old_vars;
    }

    fn compile_struct_literal(&mut self, struct_type: &Type, fields: &indexmap::IndexMap<String, AstNode>) -> Option<BasicValueEnum<'ctx>> {
        let llvm_struct_type = self.map_semantic_type(struct_type).unwrap().into_struct_type();
        let mut aggregate = llvm_struct_type.get_undef();

        let Type::Base { symbol, .. } = struct_type else { unreachable!() };
        let struct_type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
        let TypeSymbolKind::Struct((scope_id, _)) = struct_type_symbol.kind else { unreachable!() };

        let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
        let mut sorted_field_symbols: Vec<_> = scope.values.values()
            .map(|&id| self.analyzer.symbol_table.get_value_symbol(id).unwrap())
            .collect();
        sorted_field_symbols.sort_by_key(|s| s.span.unwrap().start);

        let field_name_to_index: HashMap<String, u32> = sorted_field_symbols
            .iter()
            .enumerate()
            .map(|(i, s)| {
                let name = self.analyzer.symbol_table.get_value_name(s.name_id);
                (name.to_string(), i as u32)
            })
            .collect();

        for (field_name, field_expr) in fields.iter() {
            let field_val = self.compile_node(field_expr).unwrap();
            let field_index = *field_name_to_index.get(field_name).unwrap();

            aggregate = self.builder
                .build_insert_value(aggregate, field_val, field_index, "")
                .unwrap()
                .into_struct_value();
        }
        
        Some(aggregate.into())
    }

    fn compile_field_access(&mut self, left: &BoxedAstNode, right: &BoxedAstNode) -> Option<BasicValueEnum<'ctx>> {
        if let AstNodeKind::PathQualifier { .. } = &left.kind {
            let member_symbol = self.analyzer.symbol_table.get_value_symbol(right.value_id.unwrap()).unwrap();
            return match member_symbol.kind {
                ValueSymbolKind::Function(_) => Some(self.functions.get(&member_symbol.id).unwrap().as_global_value().as_basic_value_enum()),
                ValueSymbolKind::Variable => Some(*self.constants.get(&member_symbol.id).unwrap()),
                _ => unreachable!()
            };
        }
    
        let is_static_access = if let AstNodeKind::Identifier(name) = &left.kind {
            self.analyzer.symbol_table.find_type_symbol_from_scope(left.scope_id.unwrap(), name).is_some()
        } else {
            false
        };
    
        let member_symbol = self.analyzer.symbol_table.get_value_symbol(right.value_id.unwrap()).unwrap();
    
        if is_static_access {
            return match member_symbol.kind {
                ValueSymbolKind::EnumVariant | ValueSymbolKind::Variable => Some(*self.constants.get(&member_symbol.id).unwrap()),
                ValueSymbolKind::Function(_) => Some(self.functions.get(&member_symbol.id).unwrap().as_global_value().as_basic_value_enum()),
                _ => unreachable!(),
            };
        }
        
        match member_symbol.kind {
            ValueSymbolKind::Function(_) => Some(self.functions.get(&member_symbol.id).unwrap().as_global_value().as_basic_value_enum()),
            ValueSymbolKind::StructField => {
                let struct_ptr = self.compile_place_expression(left).unwrap();
    
                let member_scope = self.analyzer.symbol_table.get_scope(member_symbol.scope_id).unwrap();
                let mut sorted_field_symbols: Vec<_> = member_scope.values.values()
                    .map(|&id| self.analyzer.symbol_table.get_value_symbol(id).unwrap())
                    .collect();
                sorted_field_symbols.sort_by_key(|s| s.span.unwrap().start);
                
                let field_index = sorted_field_symbols
                    .iter()
                    .position(|s| s.id == member_symbol.id)
                    .unwrap() as u32;
    
                let base_type = match left.type_id.as_ref().unwrap() {
                    Type::Reference(inner) | Type::MutableReference(inner) => &**inner,
                    _ => left.type_id.as_ref().unwrap(),
                };
                let struct_llvm_type = self.map_semantic_type(base_type).unwrap().into_struct_type();
                
                let field_ptr = self.builder.build_struct_gep(struct_llvm_type, struct_ptr, field_index, "").unwrap();
                let field_type = self.map_semantic_type(member_symbol.type_id.as_ref().unwrap()).unwrap();
                
                Some(self.builder.build_load(field_type, field_ptr, "").unwrap())
            }
            _ => unreachable!(),
        }
    }

    fn compile_function_body_into(&mut self, node: &AstNode, function: FunctionValue<'ctx>) {
        let AstNodeKind::Function { parameters, body, .. } = &node.kind else { unreachable!(); };

        let old_fn = self.current_function.take();
        let old_vars = self.variables.clone();
        self.variables.clear();
        self.current_function = Some(function);

        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        for (i, param_node) in parameters.iter().enumerate() {
            let param_value = function.get_nth_param(i as u32).unwrap();
            let param_symbol = self.analyzer.symbol_table.get_value_symbol(param_node.value_id.unwrap()).unwrap();
            let param_name = self.analyzer.symbol_table.get_value_name(param_symbol.name_id);
            param_value.set_name(param_name);

            let alloca = self.builder.build_alloca(param_value.get_type(), param_name).unwrap();
            self.builder.build_store(alloca, param_value).unwrap();

            self.variables.insert(param_node.value_id.unwrap(), alloca);
        }

        let body_val = self.compile_node(body.as_ref().unwrap());

        if self.builder.get_insert_block().and_then(|b| b.get_terminator()).is_none() {
            if function.get_type().get_return_type().is_some() {
                self.builder.build_return(Some(&body_val.unwrap())).unwrap();
            } else {
                self.builder.build_return(None).unwrap();
            }
        }
        
        self.current_function = old_fn;
        self.variables = old_vars;
    }

    fn compile_monomorphized_function_with_subs(
        &mut self,
        generic_fn_id: ValueSymbolId,
        substitutions: &HashMap<TypeSymbolId, Type>,
    ) -> FunctionValue<'ctx> {
        let generic_fn_symbol = self.analyzer.symbol_table.get_value_symbol(generic_fn_id).unwrap();
        
        let mut sorted_subs: Vec<_> = substitutions.iter().collect();
        sorted_subs.sort_by_key(|(k, _)| **k);
        let concrete_types_for_cache = sorted_subs.iter().map(|(_, t)| (*t).clone()).collect::<Vec<_>>();
        let cache_key = (generic_fn_id, concrete_types_for_cache);

        if let Some(cached_fn) = self.monomorphization_cache.get(&cache_key) {
            return *cached_fn;
        }

        let generic_fn_node = self.fn_ast_map[&generic_fn_id];

        let base_name = self.analyzer.symbol_table.get_value_name(generic_fn_symbol.name_id);
        let type_names = sorted_subs
            .iter()
            .map(|(_, t)| self.analyzer.symbol_table.display_type(t))
            .collect::<Vec<_>>()
            .join(",");
        let mangled_name = format!("{}<{}>", base_name, type_names);

        if let Some(existing_fn) = self.module.get_function(&mangled_name) {
            self.monomorphization_cache.insert(cache_key, existing_fn);
            return existing_fn;
        }

        let specialized_fn_type = Self::apply_codegen_substitution(generic_fn_symbol.type_id.as_ref().unwrap(), substitutions);
        let llvm_fn_type = self.map_semantic_fn_type(&specialized_fn_type);

        let function = self.module.add_function(&mangled_name, llvm_fn_type, None);
        
        self.monomorphization_cache.insert(cache_key.clone(), function);

        let old_sub_map = self.current_substitution_map.take();
        self.current_substitution_map = Some(substitutions.clone());

        self.compile_function_body_into(generic_fn_node, function);

        self.current_substitution_map = old_sub_map;

        function
    }

    fn compile_function_call(
        &mut self,
        function_node: &BoxedAstNode,
        arguments: &[AstNode],
        generic_arguments: &Option<Vec<Type>>,
        return_type: Option<&Type>,
    ) -> Option<BasicValueEnum<'ctx>> {
        let old_sub_map = self.current_substitution_map.clone();
        let mut call_substitutions = old_sub_map.clone().unwrap_or_default();
        let callee_id: ValueSymbolId;

        if let AstNodeKind::FieldAccess { left, right } = &function_node.kind {
            callee_id = right.value_id.unwrap();

            let instance_type = self.resolve_type(left.type_id.as_ref().unwrap());
            if let Type::Base { symbol: type_id, args } = &instance_type {
                let type_symbol = self.analyzer.symbol_table.get_type_symbol(*type_id).unwrap();
                if !type_symbol.generic_parameters.is_empty() {
                    let impl_subs: HashMap<_, _> = type_symbol
                        .generic_parameters
                        .iter()
                        .zip(args.iter())
                        .map(|(p, c)| (*p, c.clone()))
                        .collect();
                    call_substitutions.extend(impl_subs);
                }
            }
        } else {
            callee_id = function_node.value_id.unwrap();
        }

        let callee_symbol = self.analyzer.symbol_table.get_value_symbol(callee_id).unwrap();
        let fn_type_symbol = self
            .analyzer
            .symbol_table
            .get_type_symbol(callee_symbol.type_id.as_ref().unwrap().get_base_symbol())
            .unwrap();

        if !fn_type_symbol.generic_parameters.is_empty() {
            let callsite_generics = generic_arguments.as_ref().unwrap();
            let method_subs: HashMap<_, _> = fn_type_symbol
                .generic_parameters
                .iter()
                .zip(callsite_generics.iter())
                .map(|(p, c)| (*p, c.clone()))
                .collect();
            call_substitutions.extend(method_subs);
        }

        let callee = if call_substitutions.is_empty() || self.current_substitution_map.as_ref() == Some(&call_substitutions) {
            *self.functions.get(&callee_id).unwrap()
        } else {
            self.compile_monomorphized_function_with_subs(callee_id, &call_substitutions)
        };

        self.current_substitution_map = Some(call_substitutions);

        let mut compiled_args: Vec<BasicValueEnum<'ctx>> = Vec::new();
        if let AstNodeKind::FieldAccess { left, .. } = &function_node.kind {
            let is_static_call = if let AstNodeKind::Identifier(name) = &left.kind {
                self.analyzer
                    .symbol_table
                    .find_type_symbol_from_scope(left.scope_id.unwrap(), name)
                    .is_some()
            } else {
                matches!(left.kind, AstNodeKind::PathQualifier { .. })
            };
            if !is_static_call {
                let instance_value = self.compile_node(left).unwrap();
                compiled_args.push(instance_value);
            }
        }
        for arg_node in arguments {
            let arg_value = self.compile_node(arg_node).unwrap();
            compiled_args.push(arg_value);
        }

        self.current_substitution_map = old_sub_map;

        let call = self
            .builder
            .build_call(
                callee,
                &compiled_args.iter().map(|v| (*v).into()).collect::<Vec<_>>(),
                "",
            )
            .unwrap();

        if return_type.is_some() && callee.get_type().get_return_type().is_some() {
            return call.try_as_basic_value().left();
        }

        None
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    pub fn new(context: &'ctx Context, builder: &'a Builder<'ctx>, module: &'a Module<'ctx>, analyzer: &'a SemanticAnalyzer, program: &'a AstNode) -> Self {
        let mut fn_ast_map = HashMap::new();
        let mut queue = vec![program];

        while let Some(node) = queue.pop() {
            if let AstNodeKind::Function { .. } = &node.kind && let Some(id) = node.value_id {
                fn_ast_map.insert(id, node);
            }

            queue.extend(node.children());
        }

        CodeGen {
            context,
            builder,
            module,
            fn_ast_map,
            monomorphization_cache: HashMap::new(),
            current_substitution_map: None,
            analyzer,
            variables: HashMap::new(),
            functions: HashMap::new(),
            constants: HashMap::new(),
            string_interner: NameInterner::new(),
            string_literals: HashMap::new(),
            continue_blocks: vec![],
            break_blocks: vec![],
            current_function: None,
            type_map: HashMap::new(),
        }
    }

    pub fn compile_program(&mut self, program: &AstNode) {
        let AstNodeKind::Program(stmts) = &program.kind else { unreachable!(); };

        self.compile_declarations_pass(stmts);
        self.compile_executable_code_pass(stmts);
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    fn compile_declarations_pass(&mut self, stmts: &[AstNode]) {
        for stmt in stmts.iter() {
            match &stmt.kind {
                AstNodeKind::Function { .. } => {
                    let fn_symbol = self.analyzer.symbol_table.get_value_symbol(stmt.value_id.unwrap()).unwrap();
                    let fn_type_symbol = self.analyzer.symbol_table.get_type_symbol(fn_symbol.type_id.as_ref().unwrap().get_base_symbol()).unwrap();
                    if fn_type_symbol.generic_parameters.is_empty() {
                        self.compile_function_declaration(stmt);
                    }
                },
                AstNodeKind::StructDeclaration { .. } => self.compile_struct_declaration(stmt),
                AstNodeKind::EnumDeclaration { .. } => self.compile_enum_declaration(stmt),
                AstNodeKind::ImplDeclaration { associated_constants, associated_functions, .. } => {
                    for const_node in associated_constants {
                        let init_val = self.compile_node(const_node).unwrap();
                        self.constants.insert(const_node.value_id.unwrap(), init_val);
                    }

                    for func_node in associated_functions {
                        self.compile_function_declaration(func_node);
                    }
                },
                AstNodeKind::VariableDeclaration { mutable: false, .. } => {
                    let init_val = self.compile_node(stmt).unwrap();
                    self.constants.insert(stmt.value_id.unwrap(), init_val);
                },
                _ => {}
            }
        }
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    fn compile_executable_code_pass(&mut self, stmts: &[AstNode]) {
        for stmt in stmts.iter() {
            if let AstNodeKind::Function { body, .. } = &stmt.kind && body.is_some() {
                self.compile_function_body(stmt);
            }

            if let AstNodeKind::ImplDeclaration { associated_functions, .. } = &stmt.kind {
                for func_node in associated_functions {
                    self.compile_function_body(func_node);
                }
            }
        }

        let main_fn_type = self.context.i32_type().fn_type(&[], false);
        let main_fn = self.module.add_function("main", main_fn_type, None);
        self.current_function = Some(main_fn);
        let entry = self.context.append_basic_block(main_fn, "entry");
        self.builder.position_at_end(entry);

        for stmt in stmts.iter() {
            match &stmt.kind {
                AstNodeKind::Function {..} | AstNodeKind::StructDeclaration {..} |
                AstNodeKind::EnumDeclaration {..} | AstNodeKind::ImplDeclaration {..} |
                AstNodeKind::VariableDeclaration { mutable: false, .. } => {},
                _ => {
                    self.compile_node(stmt);
                }
            }
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
            AstNodeKind::SelfExpr => Some(self.compile_identifier(stmt.value_id.unwrap(), stmt.type_id.as_ref().unwrap())),
            AstNodeKind::VariableDeclaration { initializer, mutable: false, .. } => {
                let init_val = self.compile_node(initializer).unwrap();
                self.constants.insert(stmt.value_id.unwrap(), init_val);
                Some(init_val)
            },
            AstNodeKind::VariableDeclaration { initializer, mutable: true, .. }
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
            AstNodeKind::StructLiteral { fields, .. }
                => self.compile_struct_literal(stmt.type_id.as_ref().unwrap(), fields),
            AstNodeKind::AssociatedConstant { initializer, .. } => {
                let init_val = self.compile_node(initializer).unwrap();
                self.constants.insert(stmt.value_id.unwrap(), init_val);
                Some(init_val)
            },
            AstNodeKind::FieldAccess { left, right } => self.compile_field_access(left, right),
            AstNodeKind::FunctionCall { function, arguments, generic_arguments }
                => self.compile_function_call(function, arguments, generic_arguments, stmt.type_id.as_ref()),
            AstNodeKind::Function { .. } | AstNodeKind::TraitDeclaration { .. } => None,
            kind => unimplemented!("cannot compile node of kind {:?}", kind)
        }
    }
}