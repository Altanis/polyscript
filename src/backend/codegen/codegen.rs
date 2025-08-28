use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicType, BasicTypeEnum, FunctionType, StructType};
use inkwell::values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue};
use inkwell::{AddressSpace, FloatPredicate, IntPredicate};
use std::collections::HashMap;

use crate::frontend::semantics::analyzer::{AllocationKind, NameInterner, PrimitiveKind, ScopeId, ScopeKind, SemanticAnalyzer, Type, TypeSymbolId, TypeSymbolKind, ValueSymbolId, ValueSymbolKind};
use crate::mir::ir_node::{BoxedMIRNode, CaptureStrategy, MIRNode, MIRNodeKind};
use crate::utils::kind::Operation;

pub type StringLiteralId = usize;

#[derive(Debug, Clone, Copy)]
pub struct RcRepr<'ctx> {
    /// { ref_count: i64, drop_fn: void (*)(i8*), data: T }
    pub rc_struct_type: StructType<'ctx>,
    pub llvm_data_type: BasicTypeEnum<'ctx>,
    pub clone_data_fn: FunctionValue<'ctx>,
    pub drop_data_fn: FunctionValue<'ctx>,
}

fn get_base_variable(node: &MIRNode) -> Option<usize> {
    match &node.kind {
        MIRNodeKind::Identifier(_) => node.value_id,
        MIRNodeKind::FieldAccess { left, .. } => get_base_variable(left),
        MIRNodeKind::UnaryOperation { operator: Operation::Dereference, .. } => None,
        _ => None,
    }
}

pub struct CodeGen<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    
    analyzer: &'a SemanticAnalyzer,

    variables: HashMap<ValueSymbolId, PointerValue<'ctx>>,
    functions: HashMap<ValueSymbolId, FunctionValue<'ctx>>,
    constants: HashMap<ValueSymbolId, BasicValueEnum<'ctx>>,

    string_interner: NameInterner,
    string_literals: HashMap<StringLiteralId, PointerValue<'ctx>>,
    
    continue_blocks: Vec<BasicBlock<'ctx>>,
    break_blocks: Vec<BasicBlock<'ctx>>,

    current_function: Option<FunctionValue<'ctx>>,
    rvo_return_ptr: Option<PointerValue<'ctx>>,
    
    type_map: HashMap<TypeSymbolId, BasicTypeEnum<'ctx>>,

    rc_map: HashMap<Type, RcRepr<'ctx>>
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
    fn compile_scope_drop(&mut self, scope_id: ScopeId) {
        let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
        for &value_id in scope.values.values() {
            let symbol = self.analyzer.symbol_table.get_value_symbol(value_id).unwrap();

            if symbol.allocation_kind == AllocationKind::Heap
                && let Some(ptr_to_rc_ptr) = self.variables.get(&value_id)
            {
                let rc_ptr_type = self.context.ptr_type(AddressSpace::default());
                let rc_ptr = self.builder.build_load(rc_ptr_type, *ptr_to_rc_ptr, "").unwrap();

                let decref_fn = self.get_decref();
                self.builder.build_call(decref_fn, &[rc_ptr.into()], "").unwrap();
            }
        }
    }

    fn mangle_name(&self, ty: &Type) -> String {
        self.analyzer.symbol_table.display_type(ty).replace(|c: char| !c.is_alphanumeric(), "_")
    }

    fn get_rc_header_type(&self) -> StructType<'ctx> {
        if let Some(ty) = self.module.get_struct_type("RcHeader") {
            return ty;
        }

        let ref_count_type = self.context.i64_type();
        let drop_fn_ptr_type = self.context.ptr_type(AddressSpace::default());

        let header_type = self.context.opaque_struct_type("RcHeader");
        header_type.set_body(&[ref_count_type.into(), drop_fn_ptr_type.into()], false);
        header_type
    }
    
    fn get_incref(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("incref") {
            return func;
        }
    
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let fn_type = self.context.void_type().fn_type(&[ptr_type.into()], false);
        let function = self.module.add_function("incref", fn_type, Some(Linkage::Internal));
    
        let entry = self.context.append_basic_block(function, "entry");
        let old_block = self.builder.get_insert_block();
        self.builder.position_at_end(entry);
    
        let rc_ptr_generic = function.get_first_param().unwrap().into_pointer_value();
    
        let is_null = self.builder.build_is_null(rc_ptr_generic, "is_null").unwrap();
        let not_null_block = self.context.append_basic_block(function, "not_null");
        let end_block = self.context.append_basic_block(function, "end");
        self.builder.build_conditional_branch(is_null, end_block, not_null_block).unwrap();
    
        self.builder.position_at_end(not_null_block);
        
        let rc_header_type = self.get_rc_header_type();

        let ref_count_ptr = self.builder.build_struct_gep(rc_header_type, rc_ptr_generic, 0, "ref_count_ptr").unwrap();
        
        let old_count = self.builder.build_load(self.context.i64_type(), ref_count_ptr, "old_count").unwrap().into_int_value();
        let new_count = self.builder.build_int_add(old_count, self.context.i64_type().const_int(1, false), "new_count").unwrap();
        self.builder.build_store(ref_count_ptr, new_count).unwrap();
    
        self.builder.build_unconditional_branch(end_block).unwrap();
        self.builder.position_at_end(end_block);
        self.builder.build_return(None).unwrap();
    
        if let Some(bb) = old_block { self.builder.position_at_end(bb); }
        function
    }

    fn get_decref(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("decref") {
            return func;
        }
    
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let fn_type = self.context.void_type().fn_type(&[ptr_type.into()], false);
        let function = self.module.add_function("decref", fn_type, Some(Linkage::Internal));
    
        let entry = self.context.append_basic_block(function, "entry");
        let old_block = self.builder.get_insert_block();
        self.builder.position_at_end(entry);
    
        let rc_ptr_generic = function.get_first_param().unwrap().into_pointer_value();
    
        let is_null = self.builder.build_is_null(rc_ptr_generic, "is_null").unwrap();
        let not_null_block = self.context.append_basic_block(function, "not_null");
        let end_block = self.context.append_basic_block(function, "end");
        self.builder.build_conditional_branch(is_null, end_block, not_null_block).unwrap();
        
        self.builder.position_at_end(not_null_block);
    
        let rc_header_type = self.get_rc_header_type();

        let ref_count_ptr = self.builder.build_struct_gep(rc_header_type, rc_ptr_generic, 0, "ref_count_ptr").unwrap();
        let old_count = self.builder.build_load(self.context.i64_type(), ref_count_ptr, "old_count").unwrap().into_int_value();
        let new_count = self.builder.build_int_sub(old_count, self.context.i64_type().const_int(1, false), "new_count").unwrap();
        self.builder.build_store(ref_count_ptr, new_count).unwrap();
        
        let is_zero = self.builder.build_int_compare(IntPredicate::EQ, new_count, self.context.i64_type().const_int(0, false), "is_zero").unwrap();
        
        let drop_block = self.context.append_basic_block(function, "drop");
        self.builder.build_conditional_branch(is_zero, drop_block, end_block).unwrap();
        
        self.builder.position_at_end(drop_block);
    
        let drop_fn_ptr_ptr = self.builder.build_struct_gep(rc_header_type, rc_ptr_generic, 1, "drop_fn_ptr_ptr").unwrap();
        let drop_fn_ptr = self.builder.build_load(self.context.ptr_type(AddressSpace::default()), drop_fn_ptr_ptr, "drop_fn_ptr").unwrap().into_pointer_value();
        
        let header_size = rc_header_type.size_of().unwrap();
        let data_ptr = unsafe {
            self.builder.build_gep(self.context.i8_type(), rc_ptr_generic, &[header_size], "data_ptr").unwrap()
        };
        
        let drop_fn_type = self.context.void_type().fn_type(&[ptr_type.into()], false);
        self.builder.build_indirect_call(drop_fn_type, drop_fn_ptr, &[data_ptr.into()], "").unwrap();
        
        self.build_free(rc_ptr_generic);
    
        self.builder.build_unconditional_branch(end_block).unwrap();
        self.builder.position_at_end(end_block);
        self.builder.build_return(None).unwrap();
        
        if let Some(bb) = old_block { self.builder.position_at_end(bb); }
        function
    }

    fn wrap_in_rc(&mut self, ty: &Type) -> RcRepr<'ctx> {
        if let Some(repr) = self.rc_map.get(ty) {
            return *repr;
        }

        let type_name_mangled = self.mangle_name(ty);
        let llvm_data_type = self.map_semantic_type(ty).unwrap();

        let rc_header_type = self.get_rc_header_type();
        let rc_struct_type = self.context.opaque_struct_type(&format!("Rc_{}", type_name_mangled));
        rc_struct_type.set_body(&[rc_header_type.into(), llvm_data_type], false);

        let drop_data_fn = self.build_drop_data_fn(ty, &type_name_mangled, llvm_data_type);
        let clone_data_fn = self.build_clone_data_fn(ty, &type_name_mangled, llvm_data_type);

        let repr = RcRepr { rc_struct_type, llvm_data_type, clone_data_fn, drop_data_fn };
        self.rc_map.insert(ty.clone(), repr);
        repr
    }

    fn build_drop_data_fn(&mut self, ty: &Type, name: &String, llvm_data_type: BasicTypeEnum<'ctx>) -> FunctionValue<'ctx> {
        let fn_type = self.context.void_type().fn_type(&[self.context.ptr_type(AddressSpace::default()).into()], false);
        let function = self.module.add_function(&format!("drop_data_{}", name), fn_type, Some(Linkage::Internal));

        let old_block = self.builder.get_insert_block();
        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        let data_ptr_generic = function.get_first_param().unwrap().into_pointer_value();
        data_ptr_generic.set_name("data_ptr_generic");

        if let Type::Base { symbol, .. } = ty {
            let type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
            if let TypeSymbolKind::Struct((scope_id, _)) = type_symbol.kind {
                let llvm_struct_type = llvm_data_type.into_struct_type();
                
                let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
                let mut field_symbols: Vec<_> = scope.values.values()
                    .map(|&id| self.analyzer.symbol_table.get_value_symbol(id).unwrap())
                    .collect();
                field_symbols.sort_by_key(|s| s.span.unwrap().start);

                for (i, field_symbol) in field_symbols.iter().enumerate() {
                    let field_semantic_type = field_symbol.type_id.as_ref().unwrap();

                    if field_semantic_type.is_heap_ref() {
                        let field_ptr_ptr = self.builder.build_struct_gep(
                            llvm_struct_type,
                            data_ptr_generic,
                            i as u32,
                            &format!("field{idx}_ptr_ptr", idx = i),
                        ).unwrap();
                        let field_ptr = self.builder.build_load(self.context.ptr_type(AddressSpace::default()), field_ptr_ptr, "").unwrap();

                        let decref = self.get_decref();
                        self.builder.build_call(decref, &[field_ptr.into()], &format!("decref_{i}")).unwrap();
                    }
                }
            }
        }

        self.builder.build_return(None).unwrap();
        if let Some(block) = old_block { self.builder.position_at_end(block); }
        function
    }

    fn build_clone_data_fn(&mut self, ty: &Type, name: &String, llvm_data_type: BasicTypeEnum<'ctx>) -> FunctionValue<'ctx> {
        let fn_type = llvm_data_type.fn_type(&[self.context.ptr_type(AddressSpace::default()).into()], false);
        let function = self.module.add_function(&format!("clone_data_{}", name), fn_type, Some(Linkage::Internal));

        let old_block = self.builder.get_insert_block();
        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        let original_data_ptr = function.get_first_param().unwrap().into_pointer_value();
        original_data_ptr.set_name("original_data_ptr");

        let original_data = self.builder.build_load(llvm_data_type, original_data_ptr, "original_data").unwrap();

        if let Type::Base { symbol, .. } = ty {
            let type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
            if let TypeSymbolKind::Struct((scope_id, _)) = type_symbol.kind {
                let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
                let mut field_symbols: Vec<_> = scope.values.values()
                    .map(|&id| self.analyzer.symbol_table.get_value_symbol(id).unwrap())
                    .collect();
                field_symbols.sort_by_key(|s| s.span.unwrap().start);

                for (i, field_symbol) in field_symbols.iter().enumerate() {
                    let field_semantic_type = field_symbol.type_id.as_ref().unwrap();
                    if field_semantic_type.is_heap_ref() {
                        let field_val = self.builder.build_extract_value(
                            original_data.into_struct_value(),
                            i as u32,
                            &format!("field_{i}_val")
                        ).unwrap();

                        let incref = self.get_incref();
                        self.builder.build_call(incref, &[field_val.into()], "").unwrap();
                    }
                }
            }
        }

        self.builder.build_return(Some(&original_data)).unwrap();
        if let Some(block) = old_block { self.builder.position_at_end(block); }
        function
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    /// Determines if a type should be returned through return-value optimizations.
    fn is_rvo_candidate(&self, ty: &Type) -> bool {
        match ty {
            Type::Base { symbol, .. } => {
                if let Some(type_symbol) = self.analyzer.symbol_table.get_type_symbol(*symbol) {
                    matches!(type_symbol.kind, TypeSymbolKind::Struct(_))
                } else { false }
            },
            _ => false
        }
    }

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
                        PrimitiveKind::StaticString => self.context.ptr_type(AddressSpace::default()).as_basic_type_enum(),
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
                    TypeSymbolKind::FunctionSignature { .. } => {
                        // Represent functions as fat pointer `{fn_ptr, env_λ_ptr}`.
                        let fn_ptr_type = self.context.ptr_type(AddressSpace::default());
                        let env_ptr_type = self.context.ptr_type(AddressSpace::default());
                        self.context
                            .struct_type(&[fn_ptr_type.into(), env_ptr_type.into()], false)
                            .as_basic_type_enum()
                    },
                    TypeSymbolKind::TypeAlias((_, Some(aliased_type))) => return self.map_semantic_type(aliased_type),
                    _ => unimplemented!("cannot map semantic type to LLVM type: {} {:#?}", self.analyzer.symbol_table.display_type_symbol(type_symbol), type_symbol.span),
                };

                self.type_map.insert(*symbol, llvm_ty);
                Some(llvm_ty)
            },
            Type::Reference { .. } | Type::MutableReference { .. } 
                => Some(self.context.ptr_type(AddressSpace::default()).as_basic_type_enum())
        }
    }

    fn map_semantic_fn_type(&mut self, ty: &Type, is_closure: bool) -> FunctionType<'ctx> {
        let Type::Base { symbol, .. } = ty else { unreachable!(); };
        let type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
        let TypeSymbolKind::FunctionSignature { params, return_type, .. } = &type_symbol.kind else { unreachable!(); };

        let mut llvm_params: Vec<_> = params
            .iter()
            .map(|p| self.map_semantic_type(p).unwrap().into())
            .collect();

        let mut param_offset = 0;
        if is_closure {
            let env_ptr_type = self.context.ptr_type(AddressSpace::default());
            llvm_params.insert(0, env_ptr_type.into());
            param_offset = 1;
        }

        let use_rvo = self.is_rvo_candidate(return_type);
        if use_rvo {
            let return_type_ptr = self.context.ptr_type(AddressSpace::default());
            llvm_params.insert(param_offset, return_type_ptr.into());
        }

        let llvm_return = self.map_semantic_type(return_type);

        if let Some(llvm_return) = llvm_return && !use_rvo {
            llvm_return.fn_type(&llvm_params, false)
        } else {
            self.context.void_type().fn_type(&llvm_params, false)
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
                None => imp.trait_generic_specialization.is_empty(),
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

        let ptr = unsafe { global.as_pointer_value().const_gep(ptr_type, &[zero, zero]) };

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
            let llvm_ty = self.map_semantic_type(ty).unwrap();
            let load = self.builder.build_load(llvm_ty, ptr, "").unwrap();

            if ty.is_heap_ref() {
                let incref = self.get_incref();
                self.builder.build_call(incref, &[load.into()], &format!("increfr_{ptr}")).unwrap();
            }

            return load;
        }

        if let Some(func) = self.functions.get(&value_id).cloned() {
            let closure_struct_type = self.map_semantic_type(ty).unwrap().into_struct_type();
            let closure_ptr = self.builder.build_alloca(closure_struct_type, "fn_ptr_wrapper").unwrap();

            let fn_ptr_field = self.builder.build_struct_gep(closure_struct_type, closure_ptr, 0, "").unwrap();
            self.builder.build_store(fn_ptr_field, func.as_global_value().as_pointer_value()).unwrap();

            let env_ptr_field = self.builder.build_struct_gep(closure_struct_type, closure_ptr, 1, "").unwrap();
            let env_ptr_type = self.context.ptr_type(AddressSpace::default());
            self.builder.build_store(env_ptr_field, env_ptr_type.const_null()).unwrap();

            return self.builder.build_load(closure_struct_type, closure_ptr, "").unwrap();
        }

        if let Some(konst) = self.constants.get(&value_id) {
            return *konst;
        }

        panic!("unresolved identifier during codegen {}", 
            self.analyzer.symbol_table.display_value_symbol(self.analyzer.symbol_table.get_value_symbol(value_id).as_ref().unwrap())
        );
    }

    fn compile_variable_declaration(&mut self, initializer: &BoxedMIRNode, value_id: ValueSymbolId) -> Option<BasicValueEnum<'ctx>> {
        let symbol = self.analyzer.symbol_table.get_value_symbol(value_id).unwrap();
        let ty = symbol.type_id.as_ref().unwrap();

        let llvm_ty_for_alloca = if symbol.allocation_kind == AllocationKind::Heap {
            self.context.ptr_type(AddressSpace::default()).as_basic_type_enum()
        } else {
            self.map_semantic_type(ty).unwrap()
        };

        let ptr = self.builder.build_alloca(llvm_ty_for_alloca, "").unwrap();
        self.variables.insert(value_id, ptr);

        let init_val = self.compile_node(initializer).unwrap();
        self.builder.build_store(ptr, init_val).unwrap();

        None
    }

    fn compile_place_expression(&mut self, node: &MIRNode) -> Option<PointerValue<'ctx>> {
        match &node.kind {
            MIRNodeKind::Identifier(_) => {
                let var_id = node.value_id.unwrap();
                self.variables.get(&var_id).copied()
            },
            MIRNodeKind::SelfExpr => {
                let var_id = node.value_id.unwrap();
                self.variables.get(&var_id).copied()
            },
            MIRNodeKind::UnaryOperation { operator: Operation::Dereference, operand } => {
                let operand_type = operand.type_id.as_ref().unwrap();
                let is_heap = operand_type.is_heap_ref();
                let ptr = self.compile_node(operand).unwrap().into_pointer_value();

                if is_heap {
                    let inner_type = match operand_type {
                        Type::Reference { inner, .. } | Type::MutableReference { inner, .. } => inner,
                        _ => unreachable!(),
                    };
                    let rc_repr = self.wrap_in_rc(inner_type);
                    Some(self.builder.build_struct_gep(rc_repr.rc_struct_type, ptr, 1, "data_ptr").unwrap())
                } else {
                    Some(ptr)
                }
            },
            MIRNodeKind::FieldAccess { left, .. } => {
                let struct_ptr = self.compile_place_expression(left)?;
    
                let member_symbol = self.analyzer.symbol_table.get_value_symbol(node.value_id.unwrap()).unwrap();
                if !matches!(member_symbol.kind, ValueSymbolKind::StructField) {
                    return None;
                }
                
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
                let base_type = if let Type::Reference { inner, .. } | Type::MutableReference { inner, .. } = left_type {
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

    fn compile_unary_operation(&mut self, operator: Operation, operand_node: &BoxedMIRNode) -> Option<BasicValueEnum<'ctx>> {
        if operator == Operation::ImmutableAddressOf || operator == Operation::MutableAddressOf {
            let ptr = self.compile_place_expression(operand_node).unwrap();
            return Some(ptr.as_basic_value_enum());
        }

        if operator == Operation::Dereference {
            let operand = self.compile_node(operand_node).unwrap();
            let ptr = operand.into_pointer_value();
            let operand_type = operand_node.type_id.as_ref().unwrap();

            let (inner_type, is_heap) = match operand_type {
                Type::Reference { inner, is_heap } => (&**inner, *is_heap),
                Type::MutableReference { inner, is_heap } => (&**inner, *is_heap),
                _ => panic!("CodeGen: cannot dereference non-pointer type"),
            };

            if is_heap {
                let rc_repr = self.wrap_in_rc(inner_type);
                let data_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, ptr, 1, "data_ptr").unwrap();
                
                let cloned_val = self.builder.build_call(rc_repr.clone_data_fn, &[data_ptr.into()], "cloned_val").unwrap();
                return cloned_val.try_as_basic_value().left();
            } else {
                let pointee_type = self.map_semantic_type(inner_type).unwrap();
                return Some(self.builder.build_load(pointee_type, ptr, "").unwrap());
            }
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

    fn compile_binary_operation(&mut self, operator: Operation, left_node: &BoxedMIRNode, right_node: &BoxedMIRNode) -> Option<BasicValueEnum<'ctx>> {
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

    fn compile_conditional_operation(&mut self, operator: Operation, left: &BoxedMIRNode, right: &BoxedMIRNode) -> Option<BasicValueEnum<'ctx>> {
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

     fn compile_heap_expression(&mut self, inner_expr: &BoxedMIRNode) -> Option<BasicValueEnum<'ctx>> {
        let rc_repr = self.wrap_in_rc(inner_expr.type_id.as_ref().unwrap());

        let size = rc_repr.rc_struct_type.size_of().unwrap();
        let raw_ptr = self.build_malloc(size);
        
        let header_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, raw_ptr, 0, "header_ptr").unwrap();
        let ref_count_ptr = self.builder.build_struct_gep(self.get_rc_header_type(), header_ptr, 0, "").unwrap();
        self.builder.build_store(ref_count_ptr, self.context.i64_type().const_int(1, false)).unwrap();
        
        let drop_fn_ptr_ptr = self.builder.build_struct_gep(self.get_rc_header_type(), header_ptr, 1, "").unwrap();
        self.builder.build_store(drop_fn_ptr_ptr, rc_repr.drop_data_fn.as_global_value().as_pointer_value()).unwrap();

        let data_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, raw_ptr, 1, "data_ptr").unwrap();
        let inner_value = self.compile_node(inner_expr).unwrap();
        self.builder.build_store(data_ptr, inner_value).unwrap();
        
        Some(raw_ptr.as_basic_value_enum())
     }
 
    fn compile_block(&mut self, stmts: &[MIRNode], scope_id: ScopeId) -> Option<BasicValueEnum<'ctx>> {
        let mut last_val = None;
        let last_stmt_is_expr = stmts.last().is_some_and(|s| !matches!(s.kind, MIRNodeKind::ExpressionStatement(_)));

        for stmt in stmts {
            last_val = self.compile_node(stmt);
        }

        if self.builder.get_insert_block().and_then(|b| b.get_terminator()).is_none() {
            if last_stmt_is_expr
                && let Some(last_expr) = stmts.last()
                && let Some(base_var_id) = get_base_variable(last_expr)
            {
                let symbol = self.analyzer.symbol_table.get_value_symbol(base_var_id).unwrap();
                if symbol.allocation_kind == AllocationKind::Heap {
                    let val = last_val.unwrap();
                    let incref = self.get_incref();
                    self.builder.build_call(incref, &[val.into()], "").unwrap();
                }
            }
            
            self.compile_scope_drop(scope_id);
        }
        
        last_val
    }

    fn compile_if_statement(
        &mut self,
        condition: &BoxedMIRNode,
        then_branch: &BoxedMIRNode,
        else_if_branches: &[(BoxedMIRNode, BoxedMIRNode)],
        else_branch: &Option<BoxedMIRNode>,
        return_type: Option<&Type>,
    ) -> Option<BasicValueEnum<'ctx>> {
        let function = self.current_function.unwrap();
        
        let merge_block = self.context.append_basic_block(function, "");
        
        let mut incoming_phis = vec![];

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

    fn compile_while_loop(&mut self, condition: &BoxedMIRNode, body: &BoxedMIRNode) -> Option<BasicValueEnum<'ctx>> {
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
        initializer: &Option<BoxedMIRNode>,
        condition: &Option<BoxedMIRNode>,
        increment: &Option<BoxedMIRNode>,
        body: &BoxedMIRNode,
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

    fn compile_type_cast(&mut self, expr: &BoxedMIRNode, target_type: &Type) -> Option<BasicValueEnum<'ctx>> {
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

    fn compile_struct_declaration(&mut self, struct_node: &MIRNode) {
        let struct_type = struct_node.type_id.as_ref().unwrap();
        self.map_semantic_type(struct_type);
    }

    fn compile_enum_declaration(&mut self, enum_node: &MIRNode) {
        let MIRNodeKind::EnumDeclaration { name, variants } = &enum_node.kind else { unreachable!(); };

        let enum_type_symbol = self.analyzer.symbol_table.find_type_symbol_from_scope(enum_node.scope_id, name).unwrap();
        let enum_llvm_type = self.map_semantic_type(&Type::new_base(enum_type_symbol.id)).unwrap().into_int_type();

        let TypeSymbolKind::Enum((scope_id, _)) = enum_type_symbol.kind else { unreachable!(); };

        let mut current_discriminant: i64 = 0;

        for (variant_name, (_variant_node, initializer_opt)) in variants.iter() {
            if let Some(initializer) = initializer_opt && let MIRNodeKind::IntegerLiteral(val) = initializer.kind {
                current_discriminant = val;
            }

            let variant_symbol = self.analyzer.symbol_table.find_value_symbol_in_scope(variant_name, scope_id).unwrap();
            let const_val = enum_llvm_type.const_int(current_discriminant as u64, false);

            self.constants.insert(variant_symbol.id, const_val.into());
            current_discriminant += 1;
        }
    }

    fn compile_function_declaration(&mut self, node: &MIRNode) {
        let value_id = node.value_id.unwrap();
        
        let fn_symbol = self.analyzer.symbol_table.get_value_symbol(value_id).unwrap();
        let fn_type = fn_symbol.type_id.as_ref().unwrap();

        let is_closure = if let ValueSymbolKind::Function(_, captures) = &fn_symbol.kind { !captures.is_empty() } else { false };
        let llvm_fn_type = self.map_semantic_fn_type(fn_type, is_closure);

        let fn_name = self.analyzer.symbol_table.get_value_name(fn_symbol.name_id);
        let function = self.module.add_function(fn_name, llvm_fn_type, None);

        self.functions.insert(value_id, function);
    }

    fn compile_function_body(&mut self, node: &'a MIRNode) {
        let MIRNodeKind::Function { parameters, body, captures, .. } = &node.kind else { unreachable!(); };
        let fn_symbol_id = node.value_id.unwrap();

        let function = self.functions[&fn_symbol_id];

        let old_fn = self.current_function.take();
        let old_vars = self.variables.clone();
        let old_rvo_ptr = self.rvo_return_ptr.take();
        self.variables.clear();
        self.current_function = Some(function);

        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        let fn_symbol = self.analyzer.symbol_table.get_value_symbol(fn_symbol_id).unwrap();
        let fn_type = fn_symbol.type_id.as_ref().unwrap();
        let is_closure = !captures.is_empty();

        let Type::Base { symbol, .. } = fn_type else { unreachable!() };
        let type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
        let TypeSymbolKind::FunctionSignature { return_type, .. } = &type_symbol.kind else { unreachable!() };
        let use_rvo = self.is_rvo_candidate(return_type);

        let mut param_offset = 0;
        if is_closure {
            param_offset = 1;
            let env_raw_ptr = function.get_nth_param(0).unwrap().into_pointer_value();

            let capture_types: Vec<_> = captures.iter()
                .map(|c| {
                    let MIRNodeKind::EnvironmentCapture { strategy, .. } = &c.kind else { unreachable!(); };
                    let symbol = self.analyzer.symbol_table.get_value_symbol(c.value_id.unwrap()).unwrap();
                    let ty = symbol.type_id.as_ref().unwrap();

                    match strategy {
                        CaptureStrategy::Copy => self.map_semantic_type(ty).unwrap(),
                        CaptureStrategy::Reference | CaptureStrategy::MutableReference => self.context.ptr_type(AddressSpace::default()).into()
                    }
                })
                .collect();
            let env_struct_type = self.context.struct_type(&capture_types, false);

            for (i, capture) in captures.iter().enumerate() {
                let capture_id = capture.value_id.unwrap();
                let MIRNodeKind::EnvironmentCapture { strategy, .. } = &capture.kind else { unreachable!(); };
                let field_ptr = self.builder.build_struct_gep(env_struct_type, env_raw_ptr, i as u32, "").unwrap();

                let ptr_to_store_in_vars = match strategy {
                    CaptureStrategy::Copy => {
                        let loaded_val = self.builder.build_load(capture_types[i], field_ptr, "").unwrap();
                        let alloca = self.builder.build_alloca(capture_types[i], "").unwrap();
                        self.builder.build_store(alloca, loaded_val).unwrap();
                        alloca
                    },
                    CaptureStrategy::Reference | CaptureStrategy::MutableReference => {
                        self.builder.build_load(capture_types[i], field_ptr, "").unwrap().into_pointer_value()
                    }
                };

                self.variables.insert(capture_id, ptr_to_store_in_vars);
            }
        }
        
        if use_rvo {
            let return_val_ptr = function.get_nth_param(param_offset as u32).unwrap().into_pointer_value();
            self.rvo_return_ptr = Some(return_val_ptr);
            param_offset += 1;
        }

        for (i, param_node) in parameters.iter().enumerate() {
            let param_value = function.get_nth_param((i + param_offset) as u32).unwrap();
            let param_symbol = self.analyzer.symbol_table.get_value_symbol(param_node.value_id.unwrap()).unwrap();
            let param_name = self.analyzer.symbol_table.get_value_name(param_symbol.name_id);
            param_value.set_name(param_name);

            let alloca = self.builder.build_alloca(param_value.get_type(), param_name).unwrap();
            self.builder.build_store(alloca, param_value).unwrap();
            self.variables.insert(param_node.value_id.unwrap(), alloca);
        }

        let body_val = self.compile_node(body.as_ref().unwrap());

        if self.builder.get_insert_block().and_then(|b| b.get_terminator()).is_none() {
            if use_rvo {
                if let Some(val) = body_val {
                    let ret_ptr = self.rvo_return_ptr.unwrap();
                    self.builder.build_store(ret_ptr, val).unwrap();
                }
                self.builder.build_return(None).unwrap();
            } else if function.get_type().get_return_type().is_some() {
                self.builder.build_return(Some(&body_val.unwrap())).unwrap();
            } else {
                self.builder.build_return(None).unwrap();
            }
        }
        
        self.current_function = old_fn;
        self.variables = old_vars;
        self.rvo_return_ptr = old_rvo_ptr;
    }

    fn compile_struct_literal(&mut self, struct_type: &Type, fields: &indexmap::IndexMap<String, MIRNode>) -> Option<BasicValueEnum<'ctx>> {
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

    fn compile_function_call(&mut self, function: &BoxedMIRNode, arguments: &[MIRNode]) -> Option<BasicValueEnum<'ctx>> {
        let compiled_args: Vec<BasicValueEnum> = arguments.iter().map(|arg| self.compile_node(arg).unwrap()).collect();

        let callee_value = self.compile_node(function).unwrap();
        let closure_struct = callee_value.into_struct_value();

        let fn_ptr_val = self.builder.build_extract_value(closure_struct, 0, "fn_ptr").unwrap();
        let env_ptr_val = self.builder.build_extract_value(closure_struct, 1, "env_ptr").unwrap();

        let fn_ptr = fn_ptr_val.into_pointer_value();
        let env_ptr = env_ptr_val.into_pointer_value();

        let fn_symbol = self.analyzer.symbol_table.get_value_symbol(function.value_id.unwrap()).unwrap();
        let is_closure = if let ValueSymbolKind::Function(_, captures) = &fn_symbol.kind { !captures.is_empty() } else { false };
        let fn_type_ast = function.type_id.as_ref().unwrap();

        let Type::Base { symbol, .. } = fn_type_ast else { unreachable!() };
        let type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
        let TypeSymbolKind::FunctionSignature { return_type, .. } = &type_symbol.kind else { unreachable!() };
        let use_rvo = self.is_rvo_candidate(return_type);

        let mut return_ptr = None;
        if use_rvo {
            let return_llvm_type = self.map_semantic_type(return_type).unwrap();
            let ptr = self.builder.build_alloca(return_llvm_type, "rvo_ret_val").unwrap();
            return_ptr = Some(ptr);
        }

        let mut final_args: Vec<_> = Vec::new();
        
        if is_closure { final_args.push(env_ptr.into()); }
        if let Some(ptr) = return_ptr { final_args.push(ptr.into()); }
        final_args.extend(compiled_args.iter().map(|v| BasicMetadataValueEnum::from(*v)));

        let fn_type = self.map_semantic_fn_type(function.type_id.as_ref().unwrap(), is_closure);
        let call = self.builder.build_indirect_call(fn_type, fn_ptr, &final_args, "").unwrap();

        if use_rvo {
            let loaded_val = self.builder.build_load(self.map_semantic_type(return_type).unwrap(), return_ptr.unwrap(), "").unwrap();
            Some(loaded_val)
        } else {
            call.try_as_basic_value().left()
        }
    }

    fn compile_field_access(&mut self, stmt: &MIRNode) -> Option<BasicValueEnum<'ctx>> {
        let symbol = self
            .analyzer
            .symbol_table
            .get_value_symbol(stmt.value_id.unwrap())
            .unwrap();

        if let ValueSymbolKind::Function(_, _) = symbol.kind {
            let func_val = *self.functions.get(&symbol.id).unwrap();
            let closure_struct_type = self.map_semantic_type(stmt.type_id.as_ref().unwrap()).unwrap().into_struct_type();
            let closure_ptr = self.builder.build_alloca(closure_struct_type, "").unwrap();
            
            let fn_ptr_field = self.builder.build_struct_gep(closure_struct_type, closure_ptr, 0, "").unwrap();
            self.builder.build_store(fn_ptr_field, func_val.as_global_value().as_pointer_value()).unwrap();

            let env_ptr_field = self.builder.build_struct_gep(closure_struct_type, closure_ptr, 1, "").unwrap();
            let env_ptr_type = self.context.ptr_type(AddressSpace::default());
            self.builder.build_store(env_ptr_field, env_ptr_type.const_null()).unwrap();
            
            return Some(self.builder.build_load(closure_struct_type, closure_ptr, "").unwrap());
        }

        let field_ptr = self.compile_place_expression(stmt).unwrap();
        let field_type = stmt.type_id.as_ref().unwrap();
        let llvm_field_type = self.map_semantic_type(field_type).unwrap();
        Some(self.builder.build_load(llvm_field_type, field_ptr, "").unwrap())
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
            constants: HashMap::new(),
            string_interner: NameInterner::new(),
            string_literals: HashMap::new(),
            continue_blocks: vec![],
            break_blocks: vec![],
            current_function: None,
            rvo_return_ptr: None,
            type_map: HashMap::new(),
            rc_map: HashMap::new()
        }
    }

    pub fn compile_program(&mut self, program: &'a MIRNode) {
        let MIRNodeKind::Program(stmts) = &program.kind else { unreachable!(); };
    
        let functions = self.compile_declarations_pass(stmts);
        for func in functions {
            self.compile_function_body(func);
        }
    
        let main_fn_type = self.context.i32_type().fn_type(&[], false);
        let main_fn = self.module.add_function("main", main_fn_type, None);
        self.current_function = Some(main_fn);
        let entry = self.context.append_basic_block(main_fn, "entry");
        self.builder.position_at_end(entry);
    
        for stmt in stmts.iter() {
            match &stmt.kind {
                MIRNodeKind::Function {..} | MIRNodeKind::StructDeclaration {..} |
                MIRNodeKind::EnumDeclaration {..} | MIRNodeKind::VariableDeclaration { mutable: false, .. } => {},
                _ => {
                    self.compile_node(stmt);
                }
            }
        }
    
        if self.builder.get_insert_block().and_then(|b| b.get_terminator()).is_none() {
            self.builder.build_return(Some(&self.context.i32_type().const_int(0, false))).unwrap();
        }
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    fn compile_declarations_pass(&mut self, stmts: &'a [MIRNode]) -> Vec<&'a MIRNode> {
        let mut functions = vec![];

        for stmt in stmts.iter() {
            self.compile_declaration_node(stmt, &mut functions);
        }

        functions
    }

    fn compile_declaration_node(&mut self, stmt: &'a MIRNode, functions: &mut Vec<&'a MIRNode>) {
        for child in stmt.children() {
            self.compile_declaration_node(child, functions);
        }

        match &stmt.kind {
            MIRNodeKind::Function { .. } => {
                self.compile_function_declaration(stmt);
                functions.push(stmt);
            },
            MIRNodeKind::StructDeclaration { .. } => self.compile_struct_declaration(stmt),
            MIRNodeKind::EnumDeclaration { .. } => self.compile_enum_declaration(stmt),
            MIRNodeKind::VariableDeclaration { mutable: false, .. } => {
                let init_val = self.compile_node(stmt).unwrap();
                self.constants.insert(stmt.value_id.unwrap(), init_val);
            },
            _ => {}
        }
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    fn compile_node(&mut self, stmt: &MIRNode) -> Option<BasicValueEnum<'ctx>> {
        match &stmt.kind {
            MIRNodeKind::IntegerLiteral(value) => Some(self.compile_integer_literal(*value)),
            MIRNodeKind::FloatLiteral(value) => Some(self.compile_float_literal(*value)),
            MIRNodeKind::BooleanLiteral(value) => Some(self.compile_bool_literal(*value)),
            MIRNodeKind::StringLiteral(value) => Some(self.compile_string_literal(value)),
            MIRNodeKind::CharLiteral(value) => Some(self.compile_char_literal(*value)),
            MIRNodeKind::Identifier(_) => Some(self.compile_identifier(stmt.value_id.unwrap(), stmt.type_id.as_ref().unwrap())),
            MIRNodeKind::SelfExpr => Some(self.compile_identifier(stmt.value_id.unwrap(), stmt.type_id.as_ref().unwrap())),
            MIRNodeKind::VariableDeclaration { initializer, mutable: false, .. } => {
                let init_val = self.compile_node(initializer).unwrap();
                self.constants.insert(stmt.value_id.unwrap(), init_val);
                Some(init_val)
            },
            MIRNodeKind::VariableDeclaration { initializer, mutable: true, .. }
                => self.compile_variable_declaration(initializer, stmt.value_id.unwrap()),
            MIRNodeKind::UnaryOperation { operator, operand }
                => self.compile_unary_operation(*operator, operand),
            MIRNodeKind::BinaryOperation { operator, left, right }
                => self.compile_binary_operation(*operator, left, right),
            MIRNodeKind::ConditionalOperation { operator, left, right }
                => self.compile_conditional_operation(*operator, left, right),
            MIRNodeKind::HeapExpression(expr) => self.compile_heap_expression(expr),
            MIRNodeKind::Block(stmts) => self.compile_block(stmts, stmt.scope_id),
            MIRNodeKind::ExpressionStatement(expr) => {
                self.compile_node(expr);
                None
            },
            MIRNodeKind::Return(opt_expr) => {
                if let Some(expr) = opt_expr {
                    let value = self.compile_node(expr).unwrap();
                    if let Some(base_var_id) = get_base_variable(expr) {
                        let symbol = self.analyzer.symbol_table.get_value_symbol(base_var_id).unwrap();
                        if symbol.allocation_kind == AllocationKind::Heap {
                            let incref = self.get_incref();
                            self.builder.build_call(incref, &[value.into()], "").unwrap();
                        }
                    }

                    let mut current_scope_id = Some(stmt.scope_id);
                    while let Some(scope_id) = current_scope_id {
                        let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
                        self.compile_scope_drop(scope_id);
                        if scope.kind == ScopeKind::Function {
                            break;
                        }
                        current_scope_id = scope.parent;
                    }

                    if let Some(ret_ptr) = self.rvo_return_ptr {
                        self.builder.build_store(ret_ptr, value).unwrap();
                        self.builder.build_return(None).unwrap();
                    } else {
                        self.builder.build_return(Some(&value)).unwrap();
                    }
                } else {
                    let mut current_scope_id = Some(stmt.scope_id);
                    while let Some(scope_id) = current_scope_id {
                        let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
                        self.compile_scope_drop(scope_id);
                        if scope.kind == ScopeKind::Function {
                            break;
                        }
                        current_scope_id = scope.parent;
                    }
                    self.builder.build_return(None).unwrap();
                }

                None
            },
            MIRNodeKind::IfStatement {
                condition,
                then_branch,
                else_if_branches,
                else_branch,
            } => self.compile_if_statement(condition, then_branch, else_if_branches, else_branch, stmt.type_id.as_ref()),
            MIRNodeKind::WhileLoop { condition, body } => self.compile_while_loop(condition, body),
            MIRNodeKind::ForLoop { initializer, condition, increment, body }
                => self.compile_for_loop(initializer, condition, increment, body),
            MIRNodeKind::Break => {
                let break_block = *self.break_blocks.last().unwrap();

                let mut current_scope_id = Some(stmt.scope_id);
                while let Some(scope_id) = current_scope_id {
                    let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
                    self.compile_scope_drop(scope_id);

                    if scope.kind == ScopeKind::ForLoop || scope.kind == ScopeKind::WhileLoop {
                        break;
                    }

                    current_scope_id = scope.parent;
                }

                self.builder.build_unconditional_branch(break_block).unwrap();
                None
            },
            MIRNodeKind::Continue => {
                let continue_block = *self.continue_blocks.last().unwrap();

                let mut current_scope_id = Some(stmt.scope_id);
                while let Some(scope_id) = current_scope_id {
                    let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
                    self.compile_scope_drop(scope_id);

                    if scope.kind == ScopeKind::ForLoop || scope.kind == ScopeKind::WhileLoop {
                        break;
                    }

                    current_scope_id = scope.parent;
                }

                self.builder.build_unconditional_branch(continue_block).unwrap();
                None
            },
            MIRNodeKind::TypeCast { expr, .. }
                => self.compile_type_cast(expr, stmt.type_id.as_ref().unwrap()),
            MIRNodeKind::StructLiteral { fields, .. }
                => self.compile_struct_literal(stmt.type_id.as_ref().unwrap(), fields),
            MIRNodeKind::Function { .. } => {
                let value_id = stmt.value_id.unwrap();
                let function = self.functions.get(&value_id).unwrap();
                Some(function.as_global_value().as_pointer_value().into())
            },
            MIRNodeKind::FunctionCall { function, arguments } => self.compile_function_call(function, arguments),
            MIRNodeKind::FieldAccess { .. } => self.compile_field_access(stmt),
            kind => unimplemented!("cannot compile node of kind {:?}", kind)
        }
    }
}