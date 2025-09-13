use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::intrinsics::Intrinsic;
use inkwell::module::{Linkage, Module};
use inkwell::types::{BasicType, BasicTypeEnum, FunctionType, StructType};
use inkwell::values::{BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue, StructValue};
use inkwell::{AddressSpace, FloatPredicate, IntPredicate};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::Write;

use crate::frontend::semantics::analyzer::{NameInterner, PrimitiveKind, ScopeId, ScopeKind, SemanticAnalyzer, TraitImpl, Type, TypeSymbolId, TypeSymbolKind, ValueSymbol, ValueSymbolId, ValueSymbolKind};
use crate::mir::ir_node::{BoxedMIRNode, CaptureStrategy, MIRDirectiveKind, MIRNode, MIRNodeKind};
use crate::utils::kind::Operation;

pub type StringLiteralId = usize;

#[derive(Debug, Clone, Copy)]
pub struct RcRepr<'ctx> {
    pub rc_struct_type: StructType<'ctx>,
    pub llvm_data_type: BasicTypeEnum<'ctx>,
    pub clone_data_fn: FunctionValue<'ctx>,
    pub deallocate_data_fn: FunctionValue<'ctx>,
}

fn get_base_variable(node: &MIRNode) -> Option<usize> {
    match &node.kind {
        MIRNodeKind::Identifier(_) => node.value_id,
        MIRNodeKind::FieldAccess { left, .. } => get_base_variable(left),
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
    closure_info: HashMap<ValueSymbolId, Vec<(ValueSymbolId, CaptureStrategy)>>,

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
    fn get_c_malloc(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("malloc") {
            return func;
        }

        let usize_type = self.context.i64_type();
        let ret_type = self.context.ptr_type(AddressSpace::default());
        let malloc_type = ret_type.fn_type(&[usize_type.into()], false);
        self.module.add_function("malloc", malloc_type, None)
    }

    fn get_c_free(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("free") {
            return func;
        }

        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let free_type = self.context.void_type().fn_type(&[ptr_type.into()], false);
        self.module.add_function("free", free_type, None)
    }

    fn get_c_calloc(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("calloc") {
            return func;
        }

        let int_type = self.context.i64_type();
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let fn_type = ptr_type.fn_type(&[int_type.into(), int_type.into()], false);
        self.module.add_function("calloc", fn_type, None)
    }

    fn get_c_realloc(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("realloc") {
            return func;
        }

        let int_type = self.context.i64_type();
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let fn_type = ptr_type.fn_type(&[ptr_type.into(), int_type.into()], false);
        self.module.add_function("realloc", fn_type, None)
    }

    fn get_c_exit(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("exit") {
            return func;
        }

        let int_type = self.context.i32_type();
        let fn_type = self.context.void_type().fn_type(&[int_type.into()], false);
        self.module.add_function("exit", fn_type, None)
    }

    fn get_stdout(&self) -> PointerValue<'ctx> {
        let triple = self.module.get_triple();
        let target = triple.as_str().to_str().unwrap();

        let file_struct_type = self.module.get_struct_type("FILE").unwrap_or_else(|| self.context.opaque_struct_type("FILE"));
        let file_ptr_type = self.context.ptr_type(AddressSpace::default());

        if target.contains("windows") {
            let iob_func_name = "__acrt_iob_func";
            let iob_func = self.module.get_function(iob_func_name).unwrap_or_else(|| {
                let fn_type = file_ptr_type.fn_type(&[], false);
                self.module.add_function(iob_func_name, fn_type, Some(Linkage::External))
            });

            let iob_array_ptr = self.builder.build_call(iob_func, &[], "iob_array").unwrap()
                .try_as_basic_value().left().unwrap().into_pointer_value();
            
            unsafe {
                self.builder.build_gep(
                    file_struct_type,
                    iob_array_ptr,
                    &[self.context.i32_type().const_int(1, false)],
                    "stdout_ptr"
                ).unwrap()
            }
        } else if target.contains("darwin") {
            let stdout_global_name = "__stdoutp";
            let stdout_global = self.module.get_global(stdout_global_name)
                .unwrap_or_else(|| {
                    let global = self.module.add_global(file_ptr_type, None, stdout_global_name);
                    global.set_linkage(Linkage::External);
                    global
                });

            self.builder.build_load(file_ptr_type, stdout_global.as_pointer_value(), "stdout").unwrap().into_pointer_value()
        } else {
            let stdout_global_name = "stdout";
            let stdout_global = self.module.get_global(stdout_global_name)
                .unwrap_or_else(|| {
                    let global = self.module.add_global(file_ptr_type, None, stdout_global_name);
                    global.set_linkage(Linkage::External);
                    global
                });

            self.builder.build_load(file_ptr_type, stdout_global.as_pointer_value(), "stdout").unwrap().into_pointer_value()
        }
    }

    fn get_stderr(&self) -> PointerValue<'ctx> {
        let triple = self.module.get_triple();
        let target = triple.as_str().to_str().unwrap();

        let file_struct_type = self.module.get_struct_type("FILE").unwrap_or_else(|| self.context.opaque_struct_type("FILE"));
        let file_ptr_type = self.context.ptr_type(AddressSpace::default());

        if target.contains("windows") {
            let iob_func_name = "__acrt_iob_func";
            let iob_func = self.module.get_function(iob_func_name).unwrap_or_else(|| {
                let fn_type = file_ptr_type.fn_type(&[], false);
                self.module.add_function(iob_func_name, fn_type, Some(Linkage::External))
            });

            let iob_array_ptr = self.builder.build_call(iob_func, &[], "iob_array").unwrap()
                .try_as_basic_value().left().unwrap().into_pointer_value();

            unsafe {
                self.builder.build_gep(
                    file_struct_type,
                    iob_array_ptr,
                    &[self.context.i32_type().const_int(2, false)],
                    "stderr_ptr"
                ).unwrap()
            }
        } else if target.contains("darwin") {
            let stderr_global_name = "__stderrp";
            let stderr_global = self.module.get_global(stderr_global_name)
                .unwrap_or_else(|| {
                    let global = self.module.add_global(file_ptr_type, None, stderr_global_name);
                    global.set_linkage(Linkage::External);
                    global
                });

            self.builder.build_load(file_ptr_type, stderr_global.as_pointer_value(), "stderr").unwrap().into_pointer_value()
        } else {
            let stderr_global_name = "stderr";
            let stderr_global = self.module.get_global(stderr_global_name)
                .unwrap_or_else(|| {
                    let global = self.module.add_global(file_ptr_type, None, stderr_global_name);
                    global.set_linkage(Linkage::External);
                    global
                });
            
            self.builder.build_load(file_ptr_type, stderr_global.as_pointer_value(), "stderr").unwrap().into_pointer_value()
        }
    }

    fn get_c_fprintf(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("fprintf") {
            return func;
        }

        let i32_type = self.context.i32_type();
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let file_ptr_type = self.context.ptr_type(AddressSpace::default());

        let fn_type = i32_type.fn_type(&[file_ptr_type.into(), ptr_type.into()], true);
        self.module.add_function("fprintf", fn_type, None)
    }

    fn get_c_strlen(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("strlen") {
            return func;
        }

        let i64_type = self.context.i64_type();
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let fn_type = i64_type.fn_type(&[ptr_type.into()], false);
        self.module.add_function("strlen", fn_type, None)
    }

    fn get_c_pow(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("pow") {
            return func;
        }

        let f64_type = self.context.f64_type();
        let fn_type = f64_type.fn_type(&[f64_type.into(), f64_type.into()], false);
        self.module.add_function("pow", fn_type, Some(Linkage::External))
    }

    fn get_c_float_unary_fn(&self, name: &str) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function(name) {
            return func;
        }

        let f64_type = self.context.f64_type();
        let fn_type = f64_type.fn_type(&[f64_type.into()], false);
        self.module.add_function(name, fn_type, Some(Linkage::External))
    }

    fn get_c_atan2(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("atan2") {
            return func;
        }

        let f64_type = self.context.f64_type();
        let fn_type = f64_type.fn_type(&[f64_type.into(), f64_type.into()], false);
        self.module.add_function("atan2", fn_type, Some(Linkage::External))
    }

    fn get_c_srand(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("srand") {
            return func;
        }

        let i32_type = self.context.i32_type();
        let fn_type = self.context.void_type().fn_type(&[i32_type.into()], false);
        self.module.add_function("srand", fn_type, Some(Linkage::External))
    }

    fn get_c_rand(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("rand") {
            return func;
        }

        let i32_type = self.context.i32_type();
        let fn_type = i32_type.fn_type(&[], false);
        self.module.add_function("rand", fn_type, Some(Linkage::External))
    }

    fn get_c_time(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("time") {
            return func;
        }

        let i64_ptr_type = self.context.ptr_type(AddressSpace::default());
        let fn_type = self.context.i64_type().fn_type(&[i64_ptr_type.into()], false);
        self.module.add_function("time", fn_type, Some(Linkage::External))
    }

    fn get_c_getchar(&self) -> FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function("getchar") {
            return func;
        }

        let i32_type = self.context.i32_type();
        let fn_type = i32_type.fn_type(&[], false);
        self.module.add_function("getchar", fn_type, None)
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    fn is_heap_type(&self, ty: &Type) -> bool {
        !self.analyzer.is_copy_type(ty)
    }

    fn is_rvalue(&self, expr: &MIRNode) -> bool {
        matches!(
            expr.kind,
            MIRNodeKind::IntegerLiteral(_)
                | MIRNodeKind::FloatLiteral(_)
                | MIRNodeKind::BooleanLiteral(_)
                | MIRNodeKind::CharLiteral(_)
                | MIRNodeKind::StringLiteral(_)
                | MIRNodeKind::StructLiteral { .. }
                | MIRNodeKind::FunctionCall { .. }
                | MIRNodeKind::UnaryOperation { .. }
                | MIRNodeKind::BinaryOperation { .. }
                | MIRNodeKind::ConditionalOperation { .. }
                | MIRNodeKind::TypeCast { .. }
        )
    }
    
    fn build_rc_wrap(&mut self, value: BasicValueEnum<'ctx>, ty: &Type) -> PointerValue<'ctx> {
        let mangled_name = self.mangle_type_name(ty);
        let rc_repr = self.wrap_in_rc(ty);

        let size = rc_repr.rc_struct_type.size_of().unwrap();
        let raw_ptr = self.builder
            .build_call(self.get_c_malloc(), &[size.into()], &format!("heap_alloc.{mangled_name}"))
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value();
        
        let header_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, raw_ptr, 0, "rc.header_ptr").unwrap();
        let ref_count_ptr = self.builder.build_struct_gep(self.get_rc_header_type(), header_ptr, 0, "rc.ref_count_ptr").unwrap();
        self.builder.build_store(ref_count_ptr, self.context.i64_type().const_int(1, false)).unwrap();
        
        let deallocate_fn_ptr_ptr = self.builder.build_struct_gep(self.get_rc_header_type(), header_ptr, 1, "rc.deallocate_fn_ptr").unwrap();
        self.builder.build_store(deallocate_fn_ptr_ptr, rc_repr.deallocate_data_fn.as_global_value().as_pointer_value()).unwrap();

        let data_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, raw_ptr, 1, "rc.data_ptr").unwrap();
        self.builder.build_store(data_ptr, value).unwrap();
        
        raw_ptr
    }

    fn build_destructor_call(&mut self, ty: &Type, value: BasicValueEnum<'ctx>) {
        if self.is_heap_type(ty) {
            let decref_fn = self.get_decref();
            self.builder.build_call(decref_fn, &[value.into()], "decref_on_drop").unwrap();
            return;
        }

        let drop_trait_id = *self.analyzer.trait_registry.default_traits.get("Drop").unwrap();
        let type_id = ty.symbol;
    
        if let Some(impls_for_trait) = self.analyzer.trait_registry.register.get(&drop_trait_id)
            && let Some(impls_for_type) = impls_for_trait.get(&type_id)
        {
            let applicable_impl = impls_for_type.iter().find(|imp| {
                self.check_trait_impl_applicability_mir(ty, imp)
            });

            if let Some(imp) = applicable_impl {
                let drop_fn_symbol = self.analyzer.symbol_table
                    .find_value_symbol_in_scope("drop", imp.impl_scope_id)
                    .unwrap();
                
                let generic_drop_fn_type_id = drop_fn_symbol.type_id.as_ref().unwrap().symbol;
                
                let drop_fn_val = if !ty.args.is_empty() {
                    let mangled_name = self.mangle_monomorph_name(generic_drop_fn_type_id, &ty.args);
                    self.module.get_function(&mangled_name).unwrap()
                } else {
                    self.functions.get(&drop_fn_symbol.id).copied().unwrap()
                };
                
                let llvm_type = self.map_inner_semantic_type(ty).unwrap();
                let arg_ptr = self.builder.build_alloca(llvm_type, "drop_arg_ptr").unwrap();
                self.builder.build_store(arg_ptr, value).unwrap();
                self.builder.build_call(drop_fn_val, &[arg_ptr.into()], "").unwrap();
            }
        }

        let type_symbol = self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap();
        if let TypeSymbolKind::Struct((scope_id, _)) = type_symbol.kind {
            let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
            
            let mut field_symbols: Vec<_> = scope.values.values().map(|&id| self.analyzer.symbol_table.get_value_symbol(id).unwrap()).collect();
            field_symbols.sort_by_key(|s| s.span.unwrap().start);

            let struct_val = value.into_struct_value();

            for (i, field_symbol) in field_symbols.iter().enumerate() {
                let field_type = field_symbol.type_id.as_ref().unwrap();
                let field_name = self.analyzer.symbol_table.get_value_name(field_symbol.name_id);
                
                let field_val = self.builder.build_extract_value(
                    struct_val,
                    i as u32,
                    &format!("field_val_for_drop_{}", field_name)
                ).unwrap();
                
                self.build_destructor_call(field_type, field_val);
            }
        }
    }

    fn compile_scope_drop(&mut self, scope_id: ScopeId, moved_var_id: Option<ValueSymbolId>) {
        let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
        for &value_id in scope.values.values() {
            if moved_var_id == Some(value_id) {
                continue;
            }

            let symbol = self.analyzer.symbol_table.get_value_symbol(value_id).unwrap();
            let ty = symbol.type_id.as_ref().unwrap();

            if !self.is_heap_type(ty) {
                continue;
            }

            if let Some(ptr_to_rc_ptr) = self.variables.get(&value_id) {
                let name = self.analyzer.symbol_table.get_value_name(symbol.name_id);
                let rc_ptr_type = self.context.ptr_type(AddressSpace::default());
                let rc_ptr = self.builder.build_load(rc_ptr_type, *ptr_to_rc_ptr, &format!("{}_rc_ptr", name)).unwrap();

                let decref_fn = self.get_decref();
                self.builder.build_call(decref_fn, &[rc_ptr.into()], &format!("decref_{}", name)).unwrap();
            }
        }
    }

    fn mangle_monomorph_name<I>(&self, id: TypeSymbolId, concrete_types: I) -> String
    where
        I: IntoIterator,
        I::Item: Borrow<Type>
    {
        let mut out = String::new();
        write!(&mut out, "#{}", id).unwrap();

        let mut it = concrete_types.into_iter().peekable();
        if it.peek().is_some() {
            out.push('_');
        }
        
        for (i, ty) in it.enumerate() {
            if i > 0 {
                out.push('_');
            }

            let s = self.analyzer.symbol_table.display_type(ty.borrow());
            out.push_str(&s);
        }

        out
    }

    fn mangle_type_name(&self, ty: &Type) -> String {
        self.analyzer.symbol_table.display_type(ty).replace(|c: char| !c.is_alphanumeric(), "_")
    }

    fn get_rc_header_type(&self) -> StructType<'ctx> {
        if let Some(ty) = self.module.get_struct_type("RcHeader") {
            return ty;
        }

        let ref_count_type = self.context.i64_type();
        let deallocate_fn_ptr_type = self.context.ptr_type(AddressSpace::default());

        let header_type = self.context.opaque_struct_type("RcHeader");
        header_type.set_body(&[ref_count_type.into(), deallocate_fn_ptr_type.into()], false);
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
        rc_ptr_generic.set_name("rc_ptr");
    
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
        rc_ptr_generic.set_name("rc_ptr");
    
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
        
        let deallocate_block = self.context.append_basic_block(function, "deallocate");
        self.builder.build_conditional_branch(is_zero, deallocate_block, end_block).unwrap();
        
        self.builder.position_at_end(deallocate_block);
    
        let deallocate_fn_ptr_ptr = self.builder.build_struct_gep(rc_header_type, rc_ptr_generic, 1, "deallocate_fn_ptr_ptr").unwrap();
        let deallocate_fn_ptr = self.builder.build_load(self.context.ptr_type(AddressSpace::default()), deallocate_fn_ptr_ptr, "deallocate_fn_ptr").unwrap().into_pointer_value();
        
        let dealloc_fn_type = self.context.void_type().fn_type(&[ptr_type.into()], false);
        self.builder.build_indirect_call(dealloc_fn_type, deallocate_fn_ptr, &[rc_ptr_generic.into()], "deallocate_call").unwrap();
        
        self.builder.build_call(self.get_c_free(), &[rc_ptr_generic.into()], "free").unwrap();
    
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

        let type_name_mangled = self.mangle_type_name(ty);
        let llvm_data_type = self.map_inner_semantic_type(ty).unwrap();

        let rc_header_type = self.get_rc_header_type();
        let rc_struct_type = self.context.opaque_struct_type(&format!("Rc_{}", type_name_mangled));
        rc_struct_type.set_body(&[rc_header_type.into(), llvm_data_type], false);

        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let deallocate_fn_type = self.context.void_type().fn_type(&[ptr_type.into()], false);
        let deallocate_data_fn = self.module.add_function(&format!("deallocate_data_{}", type_name_mangled), deallocate_fn_type, Some(Linkage::Internal));

        let clone_fn_type = llvm_data_type.fn_type(&[ptr_type.into()], false);
        let clone_data_fn = self.module.add_function(&format!("clone_data_{}", type_name_mangled), clone_fn_type, Some(Linkage::Internal));
        
        let repr = RcRepr { rc_struct_type, llvm_data_type, clone_data_fn, deallocate_data_fn };
        self.rc_map.insert(ty.clone(), repr);

        self.build_deallocate_data_fn_body(ty, deallocate_data_fn);
        self.build_clone_data_fn_body(ty, clone_data_fn);

        repr
    }

    fn build_deallocate_data_fn_body(&mut self, ty: &Type, function: FunctionValue<'ctx>) {
        let old_block = self.builder.get_insert_block();
        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        let rc_ptr_generic = function.get_first_param().unwrap().into_pointer_value();
        rc_ptr_generic.set_name("rc_ptr_generic");

        let drop_trait_id = *self.analyzer.trait_registry.default_traits.get("Drop").unwrap();
        let type_id = ty.symbol;
        if let Some(impls_for_trait) = self.analyzer.trait_registry.register.get(&drop_trait_id)
            && let Some(impls_for_type) = impls_for_trait.get(&type_id)
            && let Some(imp) = impls_for_type.iter().find(|imp| self.check_trait_impl_applicability_mir(ty, imp))
            && let Some(drop_fn_symbol) = self.analyzer.symbol_table.find_value_symbol_in_scope("drop", imp.impl_scope_id)
            && let Some(drop_fn_val) = self.functions.get(&drop_fn_symbol.id).copied()
        {
            let rc_repr = self.wrap_in_rc(ty);
            let data_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, rc_ptr_generic, 1, "data_ptr").unwrap();
            self.builder.build_call(drop_fn_val, &[data_ptr.into()], "user_drop_call").unwrap();
        }

        let type_symbol = self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap();
        if let TypeSymbolKind::Struct((scope_id, _)) = type_symbol.kind {
            let rc_repr = self.wrap_in_rc(ty);

            let data_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, rc_ptr_generic, 1, "data_ptr").unwrap();
            let data_struct_val = self.builder.build_load(rc_repr.llvm_data_type, data_ptr, "struct_val").unwrap().into_struct_value();

            let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
            let mut field_symbols: Vec<_> = scope.values.values()
                .map(|&id| self.analyzer.symbol_table.get_value_symbol(id).unwrap())
                .collect();
            field_symbols.sort_by_key(|s| s.span.unwrap().start);

            for (i, field_symbol) in field_symbols.iter().enumerate() {
                let field_semantic_type = field_symbol.type_id.as_ref().unwrap();
                let field_name = self.analyzer.symbol_table.get_value_name(field_symbol.name_id);

                if self.is_heap_type(field_semantic_type) {
                    let field_val = self.builder.build_extract_value(
                        data_struct_val,
                        i as u32,
                        &format!("{}_rc_ptr", field_name)
                    ).unwrap();

                    let decref = self.get_decref();
                    self.builder.build_call(decref, &[field_val.into()], &format!("decref_{}", field_name)).unwrap();
                }
            }
        }

        self.builder.build_return(None).unwrap();
        if let Some(block) = old_block { self.builder.position_at_end(block); }
    }

    fn build_clone_data_fn_body(&mut self, ty: &Type, function: FunctionValue<'ctx>) {
        let old_block = self.builder.get_insert_block();
        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        let original_data_ptr = function.get_first_param().unwrap().into_pointer_value();
        original_data_ptr.set_name("original_data_ptr");
        
        let rc_repr = self.wrap_in_rc(ty);
        let original_data = self.builder.build_load(rc_repr.llvm_data_type, original_data_ptr, "original_data").unwrap();

        let type_symbol = self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap();
        if let TypeSymbolKind::Struct((scope_id, _)) = type_symbol.kind {
            let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
            let mut field_symbols: Vec<_> = scope.values.values()
                .map(|&id| self.analyzer.symbol_table.get_value_symbol(id).unwrap())
                .collect();
            field_symbols.sort_by_key(|s| s.span.unwrap().start);

            for (i, field_symbol) in field_symbols.iter().enumerate() {
                let field_semantic_type = field_symbol.type_id.as_ref().unwrap();
                if self.is_heap_type(field_semantic_type) {
                    let field_name = self.analyzer.symbol_table.get_value_name(field_symbol.name_id);
                    let field_val = self.builder.build_extract_value(
                        original_data.into_struct_value(),
                        i as u32,
                        &format!("{}_val", field_name)
                    ).unwrap();

                    let incref = self.get_incref();
                    self.builder.build_call(incref, &[field_val.into()], &format!("incref_{}", field_name)).unwrap();
                }
            }
        }

        self.builder.build_return(Some(&original_data)).unwrap();
        if let Some(block) = old_block { self.builder.position_at_end(block); }
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    fn is_rvo_candidate(&self, _: &Type) -> bool {
        false
    }

    fn check_trait_impl_applicability_mir(&self, instance_type: &Type, imp: &TraitImpl) -> bool {
        let instance_args = instance_type.args.clone();
        
        if instance_args.len() != imp.type_specialization.len() {
            return false;
        }
    
        for (instance_arg, &impl_target_arg_id) in instance_args.iter().zip(&imp.type_specialization) {
            if imp.impl_generic_params.contains(&impl_target_arg_id) {
                continue;
            }
    
            if instance_arg.symbol != impl_target_arg_id {
                return false;
            }
        }

        true
    }

    fn map_semantic_type(&mut self, ty: &Type) -> Option<BasicTypeEnum<'ctx>> {
        if self.is_heap_type(ty) {
            return Some(self.context.ptr_type(AddressSpace::default()).as_basic_type_enum());
        }

        self.map_inner_semantic_type(ty)
    }

    /// Maps a semantic type from the analyzer to a concrete LLVM type.
    fn map_inner_semantic_type(&mut self, ty: &Type) -> Option<BasicTypeEnum<'ctx>> {
        if let Some(&llvm_ty) = self.type_map.get(&ty.symbol) {
            return Some(llvm_ty);
        }

        let type_symbol = self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap();
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
                self.type_map.insert(ty.symbol, llvm_struct.as_basic_type_enum());

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

        self.type_map.insert(ty.symbol, llvm_ty);
        Some(llvm_ty)
    }

    fn map_semantic_fn_type(&mut self, ty: &Type, is_closure: bool) -> FunctionType<'ctx> {
        let type_symbol = self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap();
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
        let type_symbol = self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap();
        matches!(type_symbol.kind, TypeSymbolKind::Primitive(_))
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

    fn find_trait_fn_symbol(&mut self, instance_type: &Type, trait_name: &str, fn_name: &str, rhs_type: Option<&Type>) -> Option<&'a ValueSymbol> {
        let trait_id = *self.analyzer.trait_registry.default_traits.get(trait_name)?;
        let type_id = instance_type.symbol;

        let impls_for_trait = self.analyzer.trait_registry.register.get(&trait_id)?;
        let impls_for_type = impls_for_trait.get(&type_id)?;

        let applicable_impl = impls_for_type.iter().find(|imp| {
            match rhs_type {
                Some(the_rhs_type) => {
                    if let Some(&impl_rhs_symbol_id) = imp.trait_generic_specialization.first() {
                        return impl_rhs_symbol_id == the_rhs_type.symbol;
                    }
                    false
                },
                None => imp.trait_generic_specialization.is_empty(),
            }
        })?;

        self.analyzer.symbol_table.find_value_symbol_in_scope(fn_name, applicable_impl.impl_scope_id)
    }

    fn find_trait_fn(&mut self, instance_type: &Type, trait_name: &str, fn_name: &str, rhs_type: Option<&Type>) -> Option<FunctionValue<'ctx>> {
        let fn_symbol = self.find_trait_fn_symbol(instance_type, trait_name, fn_name, rhs_type)?;
        self.functions.get(&fn_symbol.id).copied()
    }

    fn build_overflow_check(&self, result_with_overflow: StructValue<'ctx>, op_name: &str) -> IntValue<'ctx> {
        let result = self.builder.build_extract_value(result_with_overflow, 0, "op_result").unwrap().into_int_value();
        let overflow_bit = self.builder.build_extract_value(result_with_overflow, 1, "overflow_bit").unwrap().into_int_value();

        let function = self.current_function.unwrap();
        let overflow_block = self.context.append_basic_block(function, &format!("{}_overflow", op_name));
        let continue_block = self.context.append_basic_block(function, &format!("{}_continue", op_name));

        self.builder.build_conditional_branch(overflow_bit, overflow_block, continue_block).unwrap();

        self.builder.position_at_end(overflow_block);
        let fprintf = self.get_c_fprintf();
        let stderr = self.get_stderr();
        let error_msg = self.builder
            .build_global_string_ptr(&format!("runtime error: integer {} overflow\n", op_name), &format!("{}_overflow_err_msg", op_name))
            .unwrap();
        self.builder.build_call(fprintf, &[stderr.into(), error_msg.as_pointer_value().into()], "").unwrap();
        let exit_func = self.get_c_exit();
        let exit_code = self.context.i32_type().const_int(1, false);
        self.builder.build_call(exit_func, &[exit_code.into()], "").unwrap();
        self.builder.build_unreachable().unwrap();

        self.builder.position_at_end(continue_block);
        result
    }

    fn build_runtime_error_check(&self, condition: IntValue<'ctx>, error_message: &str) {
        let function = self.current_function.unwrap();
        let error_block = self.context.append_basic_block(function, "runtime_error");
        let continue_block = self.context.append_basic_block(function, "continue");

        self.builder.build_conditional_branch(condition, error_block, continue_block).unwrap();

        self.builder.position_at_end(error_block);
        let fprintf = self.get_c_fprintf();
        let stderr = self.get_stderr();
        let msg_name = format!("{}_err_msg", error_message.chars().take(10).collect::<String>().replace(' ', "_"));
        let error_msg_ptr = self.builder.build_global_string_ptr(&format!("runtime error: {}\n", error_message), &msg_name).unwrap();
        self.builder.build_call(fprintf, &[stderr.into(), error_msg_ptr.as_pointer_value().into()], "").unwrap();
        let exit_func = self.get_c_exit();
        let exit_code = self.context.i32_type().const_int(1, false);
        self.builder.build_call(exit_func, &[exit_code.into()], "").unwrap();
        self.builder.build_unreachable().unwrap();

        self.builder.position_at_end(continue_block);
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

        let global = self.module.add_global(string_const.get_type(), None, &format!(".str.{}", key));
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
        let symbol = self.analyzer.symbol_table.get_value_symbol(value_id).unwrap();
        let name = self.analyzer.symbol_table.get_value_name(symbol.name_id);

        if let Some(&ptr) = self.variables.get(&value_id) {
            let llvm_ty = self.map_semantic_type(ty).unwrap();
            return self.builder.build_load(llvm_ty, ptr, name).unwrap();
        }

        if let ValueSymbolKind::Function(_, _) = &symbol.kind && let Some(func) = self.functions.get(&value_id).cloned() {
            let closure_struct_type = self.map_inner_semantic_type(ty).unwrap().into_struct_type();
            let closure_ptr = self.builder.build_alloca(closure_struct_type, &format!("{}_closure", name)).unwrap();

            let fn_ptr_field = self.builder.build_struct_gep(closure_struct_type, closure_ptr, 0, &format!("{}_fn_ptr.addr", name)).unwrap();
            self.builder.build_store(fn_ptr_field, func.as_global_value().as_pointer_value()).unwrap();

            let env_ptr_field = self.builder.build_struct_gep(closure_struct_type, closure_ptr, 1, &format!("{}_env_ptr.addr", name)).unwrap();
            
            if let Some(captures) = self.closure_info.get(&value_id).cloned() {
                let capture_types: Vec<_> = captures.iter().map(|(capture_id, strategy)| {
                    let capture_symbol = self.analyzer.symbol_table.get_value_symbol(*capture_id).unwrap();
                    let capture_type = capture_symbol.type_id.as_ref().unwrap();
                    match strategy {
                        CaptureStrategy::Copy => self.map_semantic_type(capture_type).unwrap(),
                        CaptureStrategy::Reference | CaptureStrategy::MutableReference => self.context.ptr_type(AddressSpace::default()).into()
                    }
                }).collect();
                let env_struct_type = self.context.struct_type(&capture_types, false);

                let env_ptr = self.builder.build_malloc(env_struct_type, "env_alloc").unwrap();
                
                for (i, (capture_id, strategy)) in captures.iter().enumerate() {
                    let capture_symbol = self.analyzer.symbol_table.get_value_symbol(*capture_id).unwrap();
                    let capture_name = self.analyzer.symbol_table.get_value_name(capture_symbol.name_id);
                    let field_ptr = self.builder.build_struct_gep(env_struct_type, env_ptr, i as u32, &format!("{}.addr", capture_name)).unwrap();
                    
                    match strategy {
                        CaptureStrategy::Copy => {
                            let value_to_store = self.compile_identifier(*capture_id, capture_symbol.type_id.as_ref().unwrap());
                            self.builder.build_store(field_ptr, value_to_store).unwrap();
                        },
                        CaptureStrategy::Reference | CaptureStrategy::MutableReference => {
                            let ptr_to_store = self.variables.get(capture_id).unwrap();
                            self.builder.build_store(field_ptr, *ptr_to_store).unwrap();
                        }
                    }
                }

                self.builder.build_store(env_ptr_field, env_ptr).unwrap();
            } else {
                let env_ptr_type = self.context.ptr_type(AddressSpace::default());
                self.builder.build_store(env_ptr_field, env_ptr_type.const_null()).unwrap();
            }

            return self.builder.build_load(closure_struct_type, closure_ptr, &format!("{}_closure.val", name)).unwrap();
        }

        if let Some(konst) = self.constants.get(&value_id) {
            return *konst;
        }

        panic!("unresolved identifier during codegen {}", self.analyzer.symbol_table.display_value_symbol(symbol));
    }

    fn compile_variable_declaration(&mut self, name: &str, initializer: &BoxedMIRNode, value_id: ValueSymbolId) -> Option<BasicValueEnum<'ctx>> {
        let symbol = self.analyzer.symbol_table.get_value_symbol(value_id).unwrap();
        let ty = symbol.type_id.as_ref().unwrap();
        let llvm_ty_for_alloca = self.map_semantic_type(ty).unwrap();

        let ptr = self.builder.build_alloca(llvm_ty_for_alloca, name).unwrap();
        self.variables.insert(value_id, ptr);

        let init_val = self.compile_node(initializer).unwrap();

        if self.is_heap_type(ty) && !self.is_rvalue(initializer) {
            let incref = self.get_incref();
            self.builder.build_call(incref, &[init_val.into()], &format!("incref_{}", name)).unwrap();
        }

        self.builder.build_store(ptr, init_val).unwrap();

        None
    }

    fn compile_place_expression(&mut self, node: &MIRNode) -> Option<PointerValue<'ctx>> {
        match &node.kind {
            MIRNodeKind::Identifier(_) | MIRNodeKind::SelfExpr => {
                let var_id = node.value_id.unwrap();
                self.variables.get(&var_id).copied()
            },
            MIRNodeKind::FieldAccess { left, .. } => {
                let mut struct_ptr = self.compile_place_expression(left)?;
    
                let base_type = left.type_id.as_ref().unwrap();

                if self.is_heap_type(base_type) {
                    let llvm_ptr_type = self.map_semantic_type(base_type).unwrap();
                    struct_ptr = self.builder.build_load(llvm_ptr_type, struct_ptr, "rc_ptr.load").unwrap().into_pointer_value();
                    
                    let rc_repr = self.wrap_in_rc(base_type);
                    struct_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, struct_ptr, 1, "rc.data_ptr").unwrap();
                }
                
                let member_symbol = self.analyzer.symbol_table.get_value_symbol(node.value_id.unwrap()).unwrap();
                let member_name = self.analyzer.symbol_table.get_value_name(member_symbol.name_id);
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
    
                let struct_llvm_type = self.map_inner_semantic_type(base_type).unwrap().into_struct_type();
                Some(self.builder.build_struct_gep(struct_llvm_type, struct_ptr, field_index, &format!("{}.addr", member_name)).unwrap())
            },
            _ => panic!("Expression is not a valid place expression for codegen: {:?}", node.kind),
        }
    }

    fn compile_core_unary_op(&mut self, operator: Operation, operand: BasicValueEnum<'ctx>, is_float: bool) -> BasicValueEnum<'ctx> {
        match operator {
            Operation::Neg => {
                if is_float {
                    self.builder.build_float_neg(operand.into_float_value(), "neg").unwrap().into()
                } else {
                    let op_int = operand.into_int_value();
                    let zero = op_int.get_type().const_zero();
                    
                    let sub_intrinsic = Intrinsic::find("llvm.ssub.with.overflow").unwrap();
                    let sub_fn = sub_intrinsic.get_declaration(self.module, &[op_int.get_type().into()]).unwrap();
                    let result_struct = self.builder.build_call(sub_fn, &[zero.into(), op_int.into()], "ssub_overflow_neg").unwrap()
                        .try_as_basic_value().left().unwrap().into_struct_value();
                        
                    self.build_overflow_check(result_struct, "negation").into()
                }
            },
            Operation::Not => {
                let int_val = operand.into_int_value();
                let zero = int_val.get_type().const_int(0, false);
                self.builder.build_int_compare(IntPredicate::EQ, int_val, zero, "logical_not").unwrap().into()
            },
            Operation::BitwiseNegate => {
                self.builder.build_not(operand.into_int_value(), "bitwise_not").unwrap().into()
            },
            _ => unreachable!("Operator `{:?}` was not handled", operator),
        }
    }

    fn compile_unary_operation(&mut self, operator: Operation, operand_node: &BoxedMIRNode, parent_node: &MIRNode) -> Option<BasicValueEnum<'ctx>> {
        let operand_type = operand_node.type_id.as_ref().unwrap();
        if !self.is_primitive(operand_type) && let Some((trait_name, _)) = operator.to_trait_data() {
            let fn_name = self.trait_name_to_fn_name(&trait_name);
            let callee_symbol = self.find_trait_fn_symbol(operand_type, &trait_name, &fn_name, None).unwrap();
            let callee = *self.functions.get(&callee_symbol.id).unwrap();

            let callee_type_id = callee_symbol.type_id.as_ref().unwrap().symbol;
            let callee_type_symbol = self.analyzer.symbol_table.get_type_symbol(callee_type_id).unwrap();

            let return_type = if let TypeSymbolKind::FunctionSignature { return_type, .. } = &callee_type_symbol.kind {
                return_type
            } else {
                unreachable!();
            };

            let use_rvo = self.is_rvo_candidate(return_type);
            let operand = self.compile_node(operand_node).unwrap();
            let mut args: Vec<BasicMetadataValueEnum> = vec![operand.into()];
            
            if use_rvo {
                let return_llvm_type = self.map_semantic_type(return_type).unwrap();
                let rvo_ptr = self.builder.build_alloca(return_llvm_type, "unary.op.rvo.ret.ptr").unwrap();
                args.insert(0, rvo_ptr.into());
                
                self.builder.build_call(callee, &args, "").unwrap();
                let loaded_val = self.builder.build_load(return_llvm_type, rvo_ptr, "unary.op.rvo.load").unwrap();
                return Some(loaded_val);
            } else {
                let call = self.builder.build_call(callee, &args, &format!("{}_call", fn_name)).unwrap();
                return call.try_as_basic_value().left();
            }
        }
    
        let operand = self.compile_node(operand_node).unwrap();
        let is_float = operand.is_float_value();
        
        let operand_data = if self.is_heap_type(operand_node.type_id.as_ref().unwrap()) {
            let rc_ptr = operand.into_pointer_value();
            let rc_repr = self.wrap_in_rc(operand_node.type_id.as_ref().unwrap());
            let data_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, rc_ptr, 1, "data_ptr").unwrap();
            self.builder.build_load(rc_repr.llvm_data_type, data_ptr, "data_val").unwrap()
        } else {
            operand
        };

        let result_data = self.compile_core_unary_op(operator, operand_data, is_float);
        
        let result_type = parent_node.type_id.as_ref().unwrap();
        if self.is_heap_type(result_type) {
            let result_ptr = self.build_rc_wrap(result_data, result_type);
            Some(result_ptr.as_basic_value_enum())
        } else {
            Some(result_data)
        }
    }
    
    fn compile_core_binary_op(&mut self, operator: Operation, left: BasicValueEnum<'ctx>, right: BasicValueEnum<'ctx>, is_float: bool) -> BasicValueEnum<'ctx> {
        if is_float {
            let l = left.into_float_value();
            let r = right.into_float_value();
            match operator {
                Operation::Plus => self.builder.build_float_add(l, r, "add").unwrap().into(),
                Operation::Minus => self.builder.build_float_sub(l, r, "sub").unwrap().into(),
                Operation::Mul => self.builder.build_float_mul(l, r, "mul").unwrap().into(),
                Operation::Exp => {
                    let pow_fn = self.get_c_pow();
                    let call = self.builder.build_call(pow_fn, &[l.into(), r.into()], "powf_call").unwrap();
                    call.try_as_basic_value().left().unwrap()
                },
                Operation::Div => self.builder.build_float_div(l, r, "div").unwrap().into(),
                Operation::Mod => self.builder.build_float_rem(l, r, "rem").unwrap().into(),
                Operation::Equivalence => self.builder.build_float_compare(FloatPredicate::OEQ, l, r, "eq").unwrap().into(),
                Operation::NotEqual => self.builder.build_float_compare(FloatPredicate::ONE, l, r, "ne").unwrap().into(),
                Operation::GreaterThan => self.builder.build_float_compare(FloatPredicate::OGT, l, r, "gt").unwrap().into(),
                Operation::Geq => self.builder.build_float_compare(FloatPredicate::OGE, l, r, "ge").unwrap().into(),
                Operation::LessThan => self.builder.build_float_compare(FloatPredicate::OLT, l, r, "lt").unwrap().into(),
                Operation::Leq => self.builder.build_float_compare(FloatPredicate::OLE, l, r, "le").unwrap().into(),
                _ => unreachable!("codegen for non-primitive float binary op: {:?}", operator)
            }
        } else {
            let l = left.into_int_value();
            let r = right.into_int_value();
            match operator {
                Operation::Plus => {
                    let add_intrinsic = inkwell::intrinsics::Intrinsic::find("llvm.sadd.with.overflow").unwrap();
                    let add_fn = add_intrinsic.get_declaration(self.module, &[l.get_type().into()]).unwrap();
                    let result_struct = self.builder.build_call(add_fn, &[l.into(), r.into()], "sadd_overflow").unwrap()
                        .try_as_basic_value().left().unwrap().into_struct_value();
                    self.build_overflow_check(result_struct, "addition").into()
                },
                Operation::Minus => {
                    let sub_intrinsic = inkwell::intrinsics::Intrinsic::find("llvm.ssub.with.overflow").unwrap();
                    let sub_fn = sub_intrinsic.get_declaration(self.module, &[l.get_type().into()]).unwrap();
                    let result_struct = self.builder.build_call(sub_fn, &[l.into(), r.into()], "ssub_overflow").unwrap()
                        .try_as_basic_value().left().unwrap().into_struct_value();
                    self.build_overflow_check(result_struct, "subtraction").into()
                },
                Operation::Mul => {
                    let mul_intrinsic = inkwell::intrinsics::Intrinsic::find("llvm.smul.with.overflow").unwrap();
                    let mul_fn = mul_intrinsic.get_declaration(self.module, &[l.get_type().into()]).unwrap();
                    let result_struct = self.builder.build_call(mul_fn, &[l.into(), r.into()], "smul_overflow").unwrap()
                        .try_as_basic_value().left().unwrap().into_struct_value();
                    self.build_overflow_check(result_struct, "multiplication").into()
                },
                Operation::Exp => {
                    let l_float = self.builder.build_signed_int_to_float(l, self.context.f64_type(), "l_as_float").unwrap();
                    let r_float = self.builder.build_signed_int_to_float(r, self.context.f64_type(), "r_as_float").unwrap();
                    
                    let pow_fn = self.get_c_pow();
                    let pow_float = self.builder.build_call(pow_fn, &[l_float.into(), r_float.into()], "powi_call").unwrap()
                        .try_as_basic_value().left().unwrap().into_float_value();

                    self.builder.build_float_to_signed_int(pow_float, self.context.i64_type(), "pow_as_int").unwrap().into()
                },
                Operation::Div | Operation::Mod => {
                    let function = self.current_function.unwrap();

                    let non_zero_block = self.context.append_basic_block(function, "div.non_zero");
                    let zero_block = self.context.append_basic_block(function, "div.zero");

                    let zero = r.get_type().const_int(0, false);
                    let is_zero = self.builder.build_int_compare(IntPredicate::EQ, r, zero, "is_divisor_zero").unwrap();

                    self.builder.build_conditional_branch(is_zero, zero_block, non_zero_block).unwrap();

                    self.builder.position_at_end(zero_block);
                    let fprintf = self.get_c_fprintf();
                    let stderr = self.get_stderr();
                    let error_msg = self.builder.build_global_string_ptr("runtime error: division by zero\n", "div_zero_err_msg").unwrap();
                    self.builder.build_call(fprintf, &[stderr.into(), error_msg.as_pointer_value().into()], "").unwrap();
                    let exit_func = self.get_c_exit();
                    let exit_code = self.context.i32_type().const_int(1, false);
                    self.builder.build_call(exit_func, &[exit_code.into()], "").unwrap();
                    self.builder.build_unreachable().unwrap();

                    self.builder.position_at_end(non_zero_block);

                    let min_int = l.get_type().const_int(i64::MIN as u64, true);
                    let neg_one = l.get_type().const_int(-1i64 as u64, true);
                    
                    let is_min_int = self.builder.build_int_compare(IntPredicate::EQ, l, min_int, "is_min_int").unwrap();
                    let is_neg_one = self.builder.build_int_compare(IntPredicate::EQ, r, neg_one, "is_neg_one").unwrap();
                    let is_overflow = self.builder.build_and(is_min_int, is_neg_one, "is_div_overflow").unwrap();
                    
                    self.build_runtime_error_check(is_overflow, "integer division overflow");

                    if operator == Operation::Div {
                        self.builder.build_int_signed_div(l, r, "div").unwrap().into()
                    } else {
                        self.builder.build_int_signed_rem(l, r, "rem").unwrap().into()
                    }
                },
                Operation::LeftBitShift | Operation::RightBitShift => {
                    let bitwidth = l.get_type().const_int(l.get_type().get_bit_width() as u64, false);
                    let zero = r.get_type().const_zero();

                    let is_negative = self.builder.build_int_compare(IntPredicate::SLT, r, zero, "is_shift_negative").unwrap();
                    let is_too_large = self.builder.build_int_compare(IntPredicate::SGE, r, bitwidth, "is_shift_too_large").unwrap();
                    let is_invalid_shift = self.builder.build_or(is_negative, is_too_large, "is_invalid_shift").unwrap();

                    self.build_runtime_error_check(is_invalid_shift, "invalid shift amount");
                    
                    if operator == Operation::LeftBitShift {
                        self.builder.build_left_shift(l, r, "shl").unwrap().into()
                    } else {
                        self.builder.build_right_shift(l, r, true, "shr").unwrap().into()
                    }
                },
                Operation::BitwiseAnd => self.builder.build_and(l, r, "and").unwrap().into(),
                Operation::BitwiseOr => self.builder.build_or(l, r, "or").unwrap().into(),
                Operation::BitwiseXor => self.builder.build_xor(l, r, "xor").unwrap().into(),
                Operation::Equivalence => self.builder.build_int_compare(IntPredicate::EQ, l, r, "eq").unwrap().into(),
                Operation::NotEqual => self.builder.build_int_compare(IntPredicate::NE, l, r, "ne").unwrap().into(),
                Operation::GreaterThan => self.builder.build_int_compare(IntPredicate::SGT, l, r, "gt").unwrap().into(),
                Operation::Geq => self.builder.build_int_compare(IntPredicate::SGE, l, r, "ge").unwrap().into(),
                Operation::LessThan => self.builder.build_int_compare(IntPredicate::SLT, l, r, "lt").unwrap().into(),
                Operation::Leq => self.builder.build_int_compare(IntPredicate::SLE, l, r, "le").unwrap().into(),
                _ => unreachable!("codegen for non-primitive int/bool binary op: {:?}", operator)
            }
        }
    }

    fn compile_binary_operation(&mut self, operator: Operation, left_node: &BoxedMIRNode, right_node: &BoxedMIRNode) -> Option<BasicValueEnum<'ctx>> {
        if operator == Operation::Assign {
            let target_ptr = self.compile_place_expression(left_node).unwrap();
            
            let left_type = left_node.type_id.as_ref().unwrap();
            if self.is_heap_type(left_type) {
                let old_val = self.builder.build_load(self.map_semantic_type(left_type).unwrap(), target_ptr, "assign.old_val").unwrap();
                let decref = self.get_decref();
                self.builder.build_call(decref, &[old_val.into()], "assign.decref").unwrap();
            }

            let value_to_store = self.compile_node(right_node).unwrap();
            
            let right_type = right_node.type_id.as_ref().unwrap();
            if self.is_heap_type(right_type) && !self.is_rvalue(right_node) {
                let incref = self.get_incref();
                self.builder.build_call(incref, &[value_to_store.into()], "assign.incref").unwrap();
            }

            self.builder.build_store(target_ptr, value_to_store).unwrap();
            return None;
        }

        let left_type = left_node.type_id.as_ref().unwrap();
        let right_type = right_node.type_id.as_ref().unwrap();
        
        if !self.is_primitive(left_type) && let Some((trait_name, _)) = operator.to_trait_data() {
            let fn_name = self.trait_name_to_fn_name(&trait_name);
            let callee_symbol = self.find_trait_fn_symbol(left_type, &trait_name, &fn_name, Some(right_type)).unwrap();
            let callee = *self.functions.get(&callee_symbol.id).unwrap();

            let callee_type_id = callee_symbol.type_id.as_ref().unwrap().symbol;
            let callee_type_symbol = self.analyzer.symbol_table.get_type_symbol(callee_type_id).unwrap();

            let return_type = if let TypeSymbolKind::FunctionSignature { return_type, .. } = &callee_type_symbol.kind {
                return_type
            } else {
                unreachable!();
            };

            let use_rvo = self.is_rvo_candidate(return_type);

            let left = self.compile_node(left_node).unwrap();
            let right = self.compile_node(right_node).unwrap();
            
            let mut args: Vec<BasicMetadataValueEnum> = vec![left.into(), right.into()];
            
            if use_rvo {
                let return_llvm_type = self.map_semantic_type(return_type).unwrap();
                let rvo_ptr = self.builder.build_alloca(return_llvm_type, "op.rvo.ret.ptr").unwrap();
                args.insert(0, rvo_ptr.into());
                
                self.builder.build_call(callee, &args, "").unwrap();
                let loaded_val = self.builder.build_load(return_llvm_type, rvo_ptr, "op.rvo.load").unwrap();
                return Some(loaded_val);
            } else {
                let call = self.builder.build_call(callee, &args, &format!("{}_call", fn_name)).unwrap();
                return call.try_as_basic_value().left();
            }
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
            
            let loaded_left = self.builder.build_load(self.map_semantic_type(left_type).unwrap(), target_ptr, "compound.load").unwrap();
            let right = self.compile_node(right_node).unwrap();
            let is_float = loaded_left.is_float_value();

            let left_data = if self.is_heap_type(left_type) {
                let rc_ptr = loaded_left.into_pointer_value();
                let rc_repr = self.wrap_in_rc(left_type);
                let data_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, rc_ptr, 1, "data_ptr").unwrap();
                self.builder.build_load(rc_repr.llvm_data_type, data_ptr, "data_val").unwrap()
            } else {
                loaded_left
            };

            let right_data = if self.is_heap_type(right_type) {
                let rc_ptr = right.into_pointer_value();
                let rc_repr = self.wrap_in_rc(right_type);
                let data_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, rc_ptr, 1, "data_ptr").unwrap();
                self.builder.build_load(rc_repr.llvm_data_type, data_ptr, "data_val").unwrap()
            } else {
                right
            };
            
            let value_to_store_data = self.compile_core_binary_op(base_op, left_data, right_data, is_float);
            
            if self.is_heap_type(left_type) {
                let old_val = self.builder.build_load(self.map_semantic_type(left_type).unwrap(), target_ptr, "compound.assign.old_val").unwrap();
                let decref = self.get_decref();
                self.builder.build_call(decref, &[old_val.into()], "compound.assign.decref").unwrap();
                
                let new_rc_ptr = self.build_rc_wrap(value_to_store_data, left_type);
                self.builder.build_store(target_ptr, new_rc_ptr.as_basic_value_enum()).unwrap();
            } else {
                self.builder.build_store(target_ptr, value_to_store_data).unwrap();
            }

            return None;
        }

        let left = self.compile_node(left_node).unwrap();
        let right = self.compile_node(right_node).unwrap();
        let is_float = left_node.type_id.as_ref().is_some_and(|t| self.analyzer.symbol_table.get_type_symbol(t.symbol).is_some_and(|s| matches!(s.kind, TypeSymbolKind::Primitive(PrimitiveKind::Float))));

        let left_data = if self.is_heap_type(left_type) {
            let rc_ptr = left.into_pointer_value();
            let rc_repr = self.wrap_in_rc(left_type);
            let data_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, rc_ptr, 1, "data_ptr").unwrap();
            self.builder.build_load(rc_repr.llvm_data_type, data_ptr, "data_val").unwrap()
        } else {
            left
        };

        let right_data = if self.is_heap_type(right_type) {
            let rc_ptr = right.into_pointer_value();
            let rc_repr = self.wrap_in_rc(right_type);
            let data_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, rc_ptr, 1, "data_ptr").unwrap();
            self.builder.build_load(rc_repr.llvm_data_type, data_ptr, "data_val").unwrap()
        } else {
            right
        };
        
        let result_data = self.compile_core_binary_op(operator, left_data, right_data, is_float);

        let result_type = if operator.is_conditional() {
            &Type::from_no_args(self.analyzer.get_primitive_type(PrimitiveKind::Bool))
        } else {
            left_type
        };

        if self.is_heap_type(result_type) {
            let result_ptr = self.build_rc_wrap(result_data, result_type);
            Some(result_ptr.as_basic_value_enum())
        } else {
            Some(result_data)
        }
    }

    fn compile_conditional_operation(&mut self, operator: Operation, left: &BoxedMIRNode, right: &BoxedMIRNode) -> Option<BasicValueEnum<'ctx>> {
        let function = self.current_function.unwrap();
    
        match operator {
            Operation::And => {
                let left_val = self.compile_node(left).unwrap().into_int_value();
                let then_block = self.context.append_basic_block(function, "and.rhs");
                let else_block = self.context.append_basic_block(function, "and.short_circuit");
                let merge_block = self.context.append_basic_block(function, "and.end");
    
                self.builder.build_conditional_branch(left_val, then_block, else_block).unwrap();
    
                self.builder.position_at_end(then_block);
                let right_val = self.compile_node(right).unwrap().into_int_value();
                self.builder.build_unconditional_branch(merge_block).unwrap();
                let then_block_end = self.builder.get_insert_block().unwrap();
    
                self.builder.position_at_end(else_block);
                self.builder.build_unconditional_branch(merge_block).unwrap();
                let else_block_end = self.builder.get_insert_block().unwrap();
                
                self.builder.position_at_end(merge_block);
                let phi = self.builder.build_phi(self.context.bool_type(), "and.result").unwrap();
                phi.add_incoming(&[
                    (&right_val, then_block_end),
                    (&left_val, else_block_end),
                ]);
                
                Some(phi.as_basic_value())
            },
            Operation::Or => {
                let left_val = self.compile_node(left).unwrap().into_int_value();
                let then_block = self.context.append_basic_block(function, "or.rhs");
                let else_block = self.context.append_basic_block(function, "or.short_circuit");
                let merge_block = self.context.append_basic_block(function, "or.end");
    
                self.builder.build_conditional_branch(left_val, else_block, then_block).unwrap();
    
                self.builder.position_at_end(then_block);
                let right_val = self.compile_node(right).unwrap().into_int_value();
                self.builder.build_unconditional_branch(merge_block).unwrap();
                let then_block_end = self.builder.get_insert_block().unwrap();
    
                self.builder.position_at_end(else_block);
                self.builder.build_unconditional_branch(merge_block).unwrap();
                let else_block_end = self.builder.get_insert_block().unwrap();
                
                self.builder.position_at_end(merge_block);
                let phi = self.builder.build_phi(self.context.bool_type(), "or.result").unwrap();
                phi.add_incoming(&[
                    (&right_val, then_block_end),
                    (&left_val, else_block_end),
                ]);
                
                Some(phi.as_basic_value())
            },
            _ => {
                let left_type = left.type_id.as_ref().unwrap();
                let right_type = right.type_id.as_ref().unwrap();

                if !self.is_primitive(left_type) && let Some((trait_name, _)) = operator.to_trait_data() {
                    let fn_name = self.trait_name_to_fn_name(&trait_name);
                    let callee_symbol = self.find_trait_fn_symbol(left_type, &trait_name, &fn_name, Some(right_type)).unwrap();
                    let callee = *self.functions.get(&callee_symbol.id).unwrap();

                    let callee_type_id = callee_symbol.type_id.as_ref().unwrap().symbol;
                    let callee_type_symbol = self.analyzer.symbol_table.get_type_symbol(callee_type_id).unwrap();

                    let return_type = if let TypeSymbolKind::FunctionSignature { return_type, .. } = &callee_type_symbol.kind {
                        return_type
                    } else {
                        unreachable!();
                    };

                    let use_rvo = self.is_rvo_candidate(return_type);
                    
                    let left_val = self.compile_node(left).unwrap();
                    let right_val = self.compile_node(right).unwrap();
                    let mut args: Vec<BasicMetadataValueEnum> = vec![left_val.into(), right_val.into()];

                    if use_rvo {
                        let return_llvm_type = self.map_semantic_type(return_type).unwrap();
                        let rvo_ptr = self.builder.build_alloca(return_llvm_type, "cond.op.rvo.ret.ptr").unwrap();
                        args.insert(0, rvo_ptr.into());
                        
                        self.builder.build_call(callee, &args, "").unwrap();
                        let loaded_val = self.builder.build_load(return_llvm_type, rvo_ptr, "cond.op.rvo.load").unwrap();
                        return Some(loaded_val);
                    } else {
                        let call = self.builder.build_call(callee, &args, &format!("{}_call", fn_name)).unwrap();
                        return call.try_as_basic_value().left();
                    }
                }

                let left_val = self.compile_node(left).unwrap();
                let right_val = self.compile_node(right).unwrap();
                let is_float = left_val.is_float_value();

                Some(self.compile_core_binary_op(operator, left_val, right_val, is_float))
            }
        }
    }
    
    fn compile_block(&mut self, stmts: &[MIRNode], scope_id: ScopeId) -> Option<BasicValueEnum<'ctx>> {
        let mut last_val = None;
        let last_stmt_is_expr = stmts.last().is_some_and(|s| !matches!(s.kind, MIRNodeKind::ExpressionStatement(_)));
        
        let moved_var_id = if last_stmt_is_expr {
            get_base_variable(stmts.last().unwrap())
        } else {
            None
        };

        for stmt in stmts {
            last_val = self.compile_node(stmt);
        }

        if self.builder.get_insert_block().and_then(|b| b.get_terminator()).is_none() {
            if last_stmt_is_expr
                && let Some(last_expr) = stmts.last()
                && let Some(base_var_id) = get_base_variable(last_expr)
            {
                let symbol = self.analyzer.symbol_table.get_value_symbol(base_var_id).unwrap();
                if self.is_heap_type(symbol.type_id.as_ref().unwrap()) {
                    let val = last_val.unwrap();
                    let incref = self.get_incref();
                    self.builder.build_call(incref, &[val.into()], "block_expr.incref").unwrap();
                }
            }
            
            self.compile_scope_drop(scope_id, moved_var_id);
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
        
        let merge_block = self.context.append_basic_block(function, "if.end");
        
        let mut incoming_phis = vec![];

        let cond_val = self.compile_node(condition).unwrap().into_int_value();
        let then_block = self.context.append_basic_block(function, "if.then");
        
        let mut next_cond_block = self.context.append_basic_block(function, "if.else");
        self.builder.build_conditional_branch(cond_val, then_block, next_cond_block).unwrap();

        self.builder.position_at_end(then_block);
        let then_val = self.compile_node(then_branch);
        if self.builder.get_insert_block().unwrap().get_terminator().is_none() {
            self.builder.build_unconditional_branch(merge_block).unwrap();
        }
        if let Some(val) = then_val {
            incoming_phis.push((val, self.builder.get_insert_block().unwrap()));
        }

        for (i, (else_if_cond, elseif_branch)) in else_if_branches.iter().enumerate() {
            self.builder.position_at_end(next_cond_block);
            
            let elseif_then_block = self.context.append_basic_block(function, &format!("elseif.then.{}", i));
            let next_else_block = self.context.append_basic_block(function, &format!("elseif.else.{}", i));

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
            
            next_cond_block = next_else_block;
        }

        self.builder.position_at_end(next_cond_block);
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

        if let Some(ty) = return_type {
            let type_symbol = self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap();
            if type_symbol.kind == TypeSymbolKind::Primitive(PrimitiveKind::Never) {
                if merge_block.get_terminator().is_none() {
                    self.builder.build_unreachable().unwrap();
                }

                return None;
            }

            if type_symbol.kind == TypeSymbolKind::Primitive(PrimitiveKind::Void) {
                return None;
            }

            if incoming_phis.len() > 1 {
                let llvm_type = self.map_semantic_type(ty).unwrap();
                let phi = self.builder.build_phi(llvm_type, "if.result").unwrap();
                
                for (val, block) in incoming_phis {
                    phi.add_incoming(&[(&val, block)]);
                }

                return Some(phi.as_basic_value());
            } else if let Some((val, _)) = incoming_phis.first() {
                return Some(*val);
            } else {
                if merge_block.get_terminator().is_none() {
                     self.builder.build_unreachable().unwrap();
                }

                return None;
            }
        }
        
        None
    }

    fn compile_while_loop(&mut self, condition: &BoxedMIRNode, body: &BoxedMIRNode) -> Option<BasicValueEnum<'ctx>> {
        let function = self.current_function.unwrap();

        let cond_block = self.context.append_basic_block(function, "while.cond");
        let body_block = self.context.append_basic_block(function, "while.body");
        let after_block = self.context.append_basic_block(function, "while.end");

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

        let cond_block = self.context.append_basic_block(function, "for.cond");
        let body_block = self.context.append_basic_block(function, "for.body");
        let inc_block = self.context.append_basic_block(function, "for.inc");
        let after_block = self.context.append_basic_block(function, "for.end");

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

    fn compile_type_cast_base(
        &mut self,
        expr: &BoxedMIRNode,
        target_type: &Type,
        source_val: BasicValueEnum<'ctx>,
    ) -> Option<BasicValueEnum<'ctx>> {
        let source_type = expr.type_id.as_ref().unwrap();
        let llvm_target_type = self.map_semantic_type(target_type).unwrap();

        #[derive(Debug, Clone, Copy)]
        enum CastableKind {
            Int,
            Float,
            Char,
            Enum,
        }

        let get_kind = |ty: &Type| {
            let sym = self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap();
            match sym.kind {
                TypeSymbolKind::Primitive(PrimitiveKind::Int) => Some(CastableKind::Int),
                TypeSymbolKind::Primitive(PrimitiveKind::Float) => Some(CastableKind::Float),
                TypeSymbolKind::Primitive(PrimitiveKind::Char) => Some(CastableKind::Char),
                TypeSymbolKind::Enum(_) => Some(CastableKind::Enum),
                _ => None,
            }
        };

        let source_kind = get_kind(source_type);
        let target_kind = get_kind(target_type);

        match (source_kind, target_kind) {
            (Some(CastableKind::Int), Some(CastableKind::Float)) => {
                return Some(self.builder.build_signed_int_to_float(
                    source_val.into_int_value(),
                    llvm_target_type.into_float_type(),
                    "sitofp",
                ).unwrap().into())
            }
            (Some(CastableKind::Float), Some(CastableKind::Int)) => {
                return Some(self.builder.build_float_to_signed_int(
                    source_val.into_float_value(),
                    llvm_target_type.into_int_type(),
                    "fptosi",
                ).unwrap().into())
            }
            (Some(CastableKind::Int), Some(CastableKind::Int))
            | (Some(CastableKind::Char), Some(CastableKind::Int))
            | (Some(CastableKind::Int), Some(CastableKind::Char))
            | (Some(CastableKind::Enum), Some(CastableKind::Int)) => {
                return Some(self.builder.build_int_cast_sign_flag(
                    source_val.into_int_value(),
                    llvm_target_type.into_int_type(),
                    true,
                    "intcast",
                ).unwrap().into())
            }
            (Some(CastableKind::Float), Some(CastableKind::Float)) => {
                return Some(self.builder.build_float_cast(
                    source_val.into_float_value(),
                    llvm_target_type.into_float_type(),
                    "fpcast",
                ).unwrap().into())
            },
            _ => {}
        }

        if let Some(CastableKind::Int) = source_kind {
            let int_val = source_val.into_int_value();
            let ptr_type = llvm_target_type.into_pointer_type();
            return Some(self.builder.build_int_to_ptr(int_val, ptr_type, "int_to_ptr").unwrap().into());
        }

        if let Some(CastableKind::Int) = target_kind {
            let ptr_val = source_val.into_pointer_value();
            let int_type = llvm_target_type.into_int_type();
            return Some(self.builder.build_ptr_to_int(ptr_val, int_type, "ptr_to_int").unwrap().into());
        }

        panic!("codegen cannot handle cast from {:?} to {:?}", source_kind, target_kind)
    }

    fn compile_type_cast(&mut self, expr: &BoxedMIRNode, target_type: &Type) -> Option<BasicValueEnum<'ctx>> {
        let source_val = self.compile_node(expr).unwrap();
        self.compile_type_cast_base(expr, target_type, source_val)
    }

    fn compile_struct_declaration(&mut self, struct_node: &MIRNode) {
        let struct_type = struct_node.type_id.as_ref().unwrap();
        self.map_semantic_type(struct_type);
    }

    fn compile_enum_declaration(&mut self, enum_node: &MIRNode) {
        let MIRNodeKind::EnumDeclaration { name, variants } = &enum_node.kind else { unreachable!(); };

        let enum_type_symbol = self.analyzer.symbol_table.find_type_symbol_from_scope(enum_node.scope_id, name).unwrap();
        let enum_llvm_type = self.map_inner_semantic_type(&Type::from_no_args(enum_type_symbol.id)).unwrap().into_int_type();

        let TypeSymbolKind::Enum((scope_id, _)) = enum_type_symbol.kind else { unreachable!(); };

        let mut current_discriminant: i64 = 0;

        for (variant_name, (_variant_node, initializer_opt)) in variants.iter() {
            if let Some(val) = initializer_opt {
                current_discriminant = *val;
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

        let type_symbol = self.analyzer.symbol_table.get_type_symbol(fn_type.symbol).unwrap();
        let TypeSymbolKind::FunctionSignature { return_type, .. } = &type_symbol.kind else { unreachable!() };
        let use_rvo = self.is_rvo_candidate(return_type);

        let mut param_offset = 0;
        if is_closure {
            let env_raw_ptr = function.get_nth_param(0).unwrap().into_pointer_value();
            env_raw_ptr.set_name("closure_env");
            param_offset = 1;

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
                let capture_symbol = self.analyzer.symbol_table.get_value_symbol(capture_id).unwrap();
                let capture_name = self.analyzer.symbol_table.get_value_name(capture_symbol.name_id);
                let MIRNodeKind::EnvironmentCapture { strategy, .. } = &capture.kind else { unreachable!(); };
                let field_ptr = self.builder.build_struct_gep(env_struct_type, env_raw_ptr, i as u32, &format!("{}.addr", capture_name)).unwrap();

                let ptr_to_store_in_vars = match strategy {
                    CaptureStrategy::Copy => {
                        let loaded_val = self.builder.build_load(capture_types[i], field_ptr, &format!("{}.val", capture_name)).unwrap();
                        let alloca = self.builder.build_alloca(capture_types[i], &format!("{}.local", capture_name)).unwrap();
                        self.builder.build_store(alloca, loaded_val).unwrap();
                        alloca
                    },
                    CaptureStrategy::Reference | CaptureStrategy::MutableReference => {
                        self.builder.build_load(capture_types[i], field_ptr, &format!("{}.ref", capture_name)).unwrap().into_pointer_value()
                    }
                };

                self.variables.insert(capture_id, ptr_to_store_in_vars);
            }
        }
        
        if use_rvo {
            let return_val_ptr = function.get_nth_param(param_offset as u32).unwrap().into_pointer_value();
            return_val_ptr.set_name("rvo.return_ptr");
            self.rvo_return_ptr = Some(return_val_ptr);
            param_offset += 1;
        }

        for (i, param_node) in parameters.iter().enumerate() {
            let param_value = function.get_nth_param((i + param_offset) as u32).unwrap();
            let param_symbol = self.analyzer.symbol_table.get_value_symbol(param_node.value_id.unwrap()).unwrap();
            let param_name = self.analyzer.symbol_table.get_value_name(param_symbol.name_id);
            param_value.set_name(param_name);

            let alloca = self.builder.build_alloca(param_value.get_type(), &format!("{}.addr", param_name)).unwrap();
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
        let llvm_struct_type = self.map_inner_semantic_type(struct_type).unwrap().into_struct_type();
        let mut aggregate = llvm_struct_type.get_undef();

        let struct_type_symbol = self.analyzer.symbol_table.get_type_symbol(struct_type.symbol).unwrap();
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

            let field_type = field_expr.type_id.as_ref().unwrap();
            if self.is_heap_type(field_type) && !self.is_rvalue(field_expr) {
                let incref = self.get_incref();
                self.builder.build_call(incref, &[field_val.into()], &format!("incref_{}", field_name)).unwrap();
            }

            aggregate = self.builder
                .build_insert_value(aggregate, field_val, field_index, &format!("insert.{}", field_name))
                .unwrap()
                .into_struct_value();
        }
        
        Some(aggregate.into())
    }

    fn compile_intrinsic_float_unary_op(&mut self, c_fn_name: &str, compiled_args: &[BasicValueEnum<'ctx>]) -> Option<BasicValueEnum<'ctx>> {
        let func = self.get_c_float_unary_fn(c_fn_name);
        let call = self.builder.build_call(func, &[compiled_args[0].into()], &format!("{}_call", c_fn_name)).unwrap();
        call.try_as_basic_value().left()
    }

    fn compile_function_call(&mut self, function: &BoxedMIRNode, arguments: &[MIRNode]) -> Option<BasicValueEnum<'ctx>> {
        if let Some(fn_symbol) = function.value_id.and_then(|id| self.analyzer.symbol_table.get_value_symbol(id)) {
            if fn_symbol.is_intrinsic {
                let fn_name = self.analyzer.symbol_table.get_value_name(fn_symbol.name_id);
                let compiled_args: Vec<_> = arguments.iter().map(|arg| self.compile_node(arg).unwrap()).collect();
                let int_type = self.context.i64_type();

                return match fn_name {
                    "calloc" => {
                        let func = self.get_c_calloc();
                        let nelem = compiled_args[0].into_int_value();
                        let elsize = compiled_args[1].into_int_value();
                        let call = self.builder.build_call(func, &[nelem.into(), elsize.into()], "calloc").unwrap();
                        let new_ptr = call.try_as_basic_value().left().unwrap().into_pointer_value();
                        Some(self.builder.build_ptr_to_int(new_ptr, int_type, "calloc_ptr_int").unwrap().into())
                    },
                    "realloc" => {
                        let func = self.get_c_realloc();
                        let ptr_as_int = compiled_args[0].into_int_value();
                        let ptr = self.builder.build_int_to_ptr(ptr_as_int, self.context.ptr_type(AddressSpace::default()), "realloc_ptr").unwrap();
                        let new_size = compiled_args[1].into_int_value();
                        let call = self.builder.build_call(func, &[ptr.into(), new_size.into()], "realloc").unwrap();
                        let new_ptr = call.try_as_basic_value().left().unwrap().into_pointer_value();
                        Some(self.builder.build_ptr_to_int(new_ptr, int_type, "realloc_new_ptr_int").unwrap().into())
                    },
                    "memcpy" => {
                        let dst_as_int = compiled_args[0].into_int_value();
                        let src_as_int = compiled_args[1].into_int_value();
                        let size = compiled_args[2].into_int_value();
                        let dst = self.builder.build_int_to_ptr(dst_as_int, self.context.ptr_type(AddressSpace::default()), "memcpy_dst").unwrap();
                        let src = self.builder.build_int_to_ptr(src_as_int, self.context.ptr_type(AddressSpace::default()), "memcpy_src").unwrap();
                        self.builder.build_memcpy(dst, 1, src, 1, size).unwrap();
                        None
                    },
                    "memmove" => {
                        let dst_as_int = compiled_args[0].into_int_value();
                        let src_as_int = compiled_args[1].into_int_value();
                        let size = compiled_args[2].into_int_value();
                        let dst = self.builder.build_int_to_ptr(dst_as_int, self.context.ptr_type(AddressSpace::default()), "memmove_dst").unwrap();
                        let src = self.builder.build_int_to_ptr(src_as_int, self.context.ptr_type(AddressSpace::default()), "memmove_src").unwrap();
                        self.builder.build_memmove(dst, 1, src, 1, size).unwrap();
                        None
                    },
                    "free" => {
                        let ptr_as_int = compiled_args[0].into_int_value();
                        let ptr = self.builder.build_int_to_ptr(ptr_as_int, self.context.ptr_type(AddressSpace::default()), "free_ptr").unwrap();
                        self.builder.build_call(self.get_c_free(), &[ptr.into()], "free").unwrap();
                        None
                    },
                    "incref" => {
                        let ptr_as_int = compiled_args[0].into_int_value();
                        let ptr = self.builder.build_int_to_ptr(ptr_as_int, self.context.ptr_type(AddressSpace::default()), "incref_ptr").unwrap();
                        let incref_fn = self.get_incref();
                        self.builder.build_call(incref_fn, &[ptr.into()], "incref_call").unwrap();
                        None
                    },
                    "decref" => {
                        let ptr_as_int = compiled_args[0].into_int_value();
                        let ptr = self.builder.build_int_to_ptr(ptr_as_int, self.context.ptr_type(AddressSpace::default()), "decref_ptr").unwrap();
                        let decref_fn = self.get_decref();
                        self.builder.build_call(decref_fn, &[ptr.into()], "decref_call").unwrap();
                        None
                    },
                    "print" => {
                        let fprintf = self.get_c_fprintf();
                        let stdout = self.get_stderr();
                        let format_str = self.builder.build_global_string_ptr("%s", "print_fmt").unwrap();
                        let str_val = compiled_args[0];
                        self.builder.build_call(fprintf, &[stdout.into(), format_str.as_pointer_value().into(), str_val.into()], "").unwrap();
                        None
                    },
                    "eprint" => {
                        let fprintf = self.get_c_fprintf();
                        let stderr = self.get_stderr();
                        let format_str = self.builder.build_global_string_ptr("%s", "eprint_fmt").unwrap();
                        let str_val = compiled_args[0];
                        self.builder.build_call(fprintf, &[stderr.into(), format_str.as_pointer_value().into(), str_val.into()], "").unwrap();
                        None
                    },
                    "print_char" => {
                        let fprintf = self.get_c_fprintf();
                        let stdout = self.get_stdout();
                        let format_str = self.builder.build_global_string_ptr("%c", "oprint_char_fmt").unwrap();
                        let char_val = compiled_args[0].into_int_value();
                        let promoted_char = self.builder.build_int_z_extend(char_val, self.context.i32_type(), "promoted_char").unwrap();
                        self.builder.build_call(fprintf, &[stdout.into(), format_str.as_pointer_value().into(), promoted_char.into()], "").unwrap();
                        None
                    },
                    "print_int" => {
                        let fprintf = self.get_c_fprintf();
                        let stdout = self.get_stdout();
                        let format_str = self.builder.build_global_string_ptr("%d\n", "oprint_int_fmt").unwrap();
                        let char_val = compiled_args[0].into_int_value();
                        let promoted_char = if char_val.get_type().get_bit_width() < 32 {
                            self.builder.build_int_z_extend(char_val, self.context.i32_type(), "int").unwrap()
                        } else if char_val.get_type().get_bit_width() > 32 {
                            self.builder.build_int_truncate(char_val, self.context.i32_type(), "int").unwrap()
                        } else {
                            char_val
                        };
                        self.builder.build_call(fprintf, &[stdout.into(), format_str.as_pointer_value().into(), promoted_char.into()], "").unwrap();
                        None
                    },
                    "eprint_char" => {
                        let fprintf = self.get_c_fprintf();
                        let stderr = self.get_stderr();
                        let format_str = self.builder.build_global_string_ptr("%c", "eprint_char_fmt").unwrap();
                        let char_val = compiled_args[0].into_int_value();
                        let promoted_char = self.builder.build_int_z_extend(char_val, self.context.i32_type(), "promoted_char").unwrap();
                        self.builder.build_call(fprintf, &[stderr.into(), format_str.as_pointer_value().into(), promoted_char.into()], "").unwrap();
                        None
                    },
                    "endproc" => {
                        let func = self.get_c_exit();
                        let code = self.builder.build_int_truncate(compiled_args[0].into_int_value(), self.context.i32_type(), "exit_code").unwrap();
                        self.builder.build_call(func, &[code.into()], "").unwrap();
                        self.builder.build_unreachable().unwrap();
                        None
                    },
                    "strlen" => {
                        let func = self.get_c_strlen();
                        let str_ptr = compiled_args[0].into_pointer_value();
                        let call = self.builder.build_call(func, &[str_ptr.into()], "strlen_call").unwrap();
                        call.try_as_basic_value().left()
                    },
                    "strget" => {
                        let str_ptr = compiled_args[0].into_pointer_value();
                        let index = compiled_args[1].into_int_value();
                        
                        let char_ptr = unsafe {
                            self.builder.build_gep(self.context.i8_type(), str_ptr, &[index], "char_ptr").unwrap()
                        };
                        let char_val = self.builder.build_load(self.context.i8_type(), char_ptr, "char_val").unwrap();

                        Some(char_val)
                    },
                    "getchar" => {
                        let func = self.get_c_getchar();
                        let call = self.builder.build_call(func, &[], "getchar_call").unwrap();
                        let i32_val = call.try_as_basic_value().left().unwrap().into_int_value();
                        let i8_type = self.context.i8_type();
                        let truncated_val = self.builder.build_int_truncate(i32_val, i8_type, "getchar_char").unwrap();
                        Some(truncated_val.into())
                    },
                    "ln_" => self.compile_intrinsic_float_unary_op("log", &compiled_args),
                    "log2_" => self.compile_intrinsic_float_unary_op("log2", &compiled_args),
                    "log10_" => self.compile_intrinsic_float_unary_op("log10", &compiled_args),
                    "sin_" => self.compile_intrinsic_float_unary_op("sin", &compiled_args),
                    "cos_" => self.compile_intrinsic_float_unary_op("cos", &compiled_args),
                    "tan_" => self.compile_intrinsic_float_unary_op("tan", &compiled_args),
                    "asin_" => self.compile_intrinsic_float_unary_op("asin", &compiled_args),
                    "acos_" => self.compile_intrinsic_float_unary_op("acos", &compiled_args),
                    "atan_" => self.compile_intrinsic_float_unary_op("atan", &compiled_args),
                    "sinh_" => self.compile_intrinsic_float_unary_op("sinh", &compiled_args),
                    "cosh_" => self.compile_intrinsic_float_unary_op("cosh", &compiled_args),
                    "tanh_" => self.compile_intrinsic_float_unary_op("tanh", &compiled_args),
                    "asinh_" => self.compile_intrinsic_float_unary_op("asinh", &compiled_args),
                    "acosh_" => self.compile_intrinsic_float_unary_op("acosh", &compiled_args),
                    "atanh_" => self.compile_intrinsic_float_unary_op("atanh", &compiled_args),
                    "atan2_" => {
                        let func = self.get_c_atan2();
                        let y = compiled_args[0];
                        let x = compiled_args[1];
                        let call = self.builder.build_call(func, &[y.into(), x.into()], "atan2_call").unwrap();
                        call.try_as_basic_value().left()
                    },
                    "random_" => {
                        let rand_fn = self.get_c_rand();
                        let rand_max_val = self.context.i32_type().const_int(2147483647, false); // RAND_MAX on most systems
                        let rand_val_i32 = self.builder.build_call(rand_fn, &[], "rand_call").unwrap()
                            .try_as_basic_value().left().unwrap().into_int_value();
                        
                        let rand_val_f64 = self.builder.build_signed_int_to_float(rand_val_i32, self.context.f64_type(), "rand_f64").unwrap();
                        let rand_max_f64 = self.builder.build_signed_int_to_float(rand_max_val, self.context.f64_type(), "rand_max_f64").unwrap();
    
                        let result = self.builder.build_float_div(rand_val_f64, rand_max_f64, "random_float").unwrap();
                        Some(result.into())
                    },
                    "drop" => {
                        let value_to_drop_node = &arguments[0];
                        let value_to_drop_type = value_to_drop_node.type_id.as_ref().unwrap();
                        let compiled_arg = compiled_args[0];
                        self.build_destructor_call(value_to_drop_type, compiled_arg);
                        None
                    },
                    "ref" => {
                        let arg_node = &arguments[0];
                        let arg_val = compiled_args[0];
                        let arg_type = arg_node.type_id.as_ref().unwrap();

                        let llvm_type = self.map_semantic_type(arg_type).unwrap();
                        let ptr = self.builder.build_alloca(llvm_type, "ref_arg_ptr").unwrap();
                        self.builder.build_store(ptr, arg_val).unwrap();

                        Some(self.builder.build_ptr_to_int(ptr, self.context.i64_type(), "ref_addr").unwrap().into())
                    },
                    "deref" => {
                        let arg_node = &arguments[0];
                        if let MIRNodeKind::TypeCast { expr: ptr_expr, .. } = &arg_node.kind {
                            let ptr_as_int = self.compile_node(ptr_expr).unwrap().into_int_value();

                            let llvm_type_to_load = self.map_semantic_type(arg_node.type_id.as_ref().unwrap()).unwrap();
                            let llvm_ptr_type = self.context.ptr_type(AddressSpace::default());
                            
                            let ptr = self.builder.build_int_to_ptr(ptr_as_int, llvm_ptr_type, "deref_ptr").unwrap();

                            Some(self.builder.build_load(llvm_type_to_load, ptr, "deref_load").unwrap())
                        } else { unreachable!(); }
                    },
                    _ => unreachable!()
                };
            }
            
            let fn_name = self.analyzer.symbol_table.get_value_name(fn_symbol.name_id);
            let impl_scope = self.analyzer.symbol_table.get_scope(fn_symbol.scope_id).unwrap();

            let drop_trait_id = *self.analyzer.trait_registry.default_traits.get("Drop").unwrap();
            let TypeSymbolKind::Trait(drop_scope_id) = self.analyzer.symbol_table.get_type_symbol(drop_trait_id).unwrap().kind else { unreachable!(); };

            if (impl_scope.trait_id.is_some() || (impl_scope.id == drop_scope_id))
                && let Some(argument) = arguments.first()
                && let Some(ty_id) = argument.type_id.as_ref()
            {
                let is_drop = if let Some(trait_id) = impl_scope.trait_id { trait_id == drop_trait_id } else { impl_scope.id == drop_scope_id };

                let rc_ptr = if self.is_heap_type(ty_id) {
                    let rc_ptr_ptr = self.compile_node(argument).unwrap().into_pointer_value();
                    Some(self.builder.build_load(self.context.ptr_type(AddressSpace::default()), rc_ptr_ptr, "rc_ptr").unwrap())
                } else {
                    None
                };

                if fn_name == "drop" && is_drop {
                    if let Some(rc_ptr) = rc_ptr {
                        let decref_fn = self.get_decref();
                        self.builder.build_call(decref_fn, &[rc_ptr.into()], "heap.drop.decref").unwrap();
                    }

                    return None;
                }
            }
        }

        let callee_type = function.type_id.as_ref().unwrap();
        let type_symbol = self.analyzer.symbol_table.get_type_symbol(callee_type.symbol).unwrap();
        let TypeSymbolKind::FunctionSignature { return_type, instance, .. } = &type_symbol.kind else { unreachable!() };
        
        let mut final_args: Vec<BasicMetadataValueEnum<'ctx>> = Vec::new();
        let mut explicit_args = arguments;

        let callee_value = self.compile_node(function).unwrap();
        let closure_struct = if self.is_heap_type(callee_type) && callee_value.is_pointer_value() {
            let rc_ptr = callee_value.into_pointer_value();
            let rc_repr = self.wrap_in_rc(callee_type);
            let data_ptr = self.builder.build_struct_gep(rc_repr.rc_struct_type, rc_ptr, 1, "rc.data_ptr").unwrap();
            self.builder.build_load(rc_repr.llvm_data_type, data_ptr, "fn.closure_struct").unwrap()
        } else {
            callee_value
        }.into_struct_value();
        let fn_ptr_val = self.builder.build_extract_value(closure_struct, 0, "fn_ptr").unwrap();
        let env_ptr_val = self.builder.build_extract_value(closure_struct, 1, "env_ptr").unwrap();
        
        let fn_ptr = fn_ptr_val.into_pointer_value();
        let env_ptr = env_ptr_val.into_pointer_value();

        let fn_symbol = self.analyzer.symbol_table.get_value_symbol(function.value_id.unwrap()).unwrap();
        let is_closure = if let ValueSymbolKind::Function(_, captures) = &fn_symbol.kind { !captures.is_empty() } else { false };
        if is_closure {
            final_args.insert(0, env_ptr.into());
        }

        let mut return_ptr = None;
        let use_rvo = self.is_rvo_candidate(return_type);
        if use_rvo {
            let return_llvm_type = self.map_semantic_type(return_type).unwrap();
            let ptr = self.builder.build_alloca(return_llvm_type, "rvo_ret_val").unwrap();
            final_args.push(ptr.into());
            return_ptr = Some(ptr);
        }

        if *instance {
            let (instance_node, rest_args) = arguments.split_first().expect("Instance method call with no arguments");
            let instance_arg = self.compile_node(instance_node).unwrap();
            final_args.push(instance_arg.into());
            explicit_args = rest_args;
        }

        for (i, arg_node) in explicit_args.iter().enumerate() {
            let arg_val = self.compile_node(arg_node).unwrap();
            let arg_type = arg_node.type_id.as_ref().unwrap();

            if self.is_heap_type(arg_type) && !self.is_rvalue(arg_node) {
                let incref = self.get_incref();
                self.builder.build_call(incref, &[arg_val.into()], &format!("incref.arg{}", i)).unwrap();
            }
            final_args.push(arg_val.into());
        }

        let fn_type = self.map_semantic_fn_type(callee_type, is_closure);
        let call = self.builder.build_indirect_call(fn_type, fn_ptr, &final_args, "call").unwrap();

        if use_rvo {
            let loaded_val = self.builder.build_load(self.map_semantic_type(return_type).unwrap(), return_ptr.unwrap(), "rvo.load").unwrap();
            Some(loaded_val)
        } else {
            call.try_as_basic_value().left()
        }
    }

    fn compile_field_access(&mut self, stmt: &MIRNode) -> Option<BasicValueEnum<'ctx>> {
        let symbol = self.analyzer.symbol_table.get_value_symbol(stmt.value_id.unwrap()).unwrap();
        let name = self.analyzer.symbol_table.get_value_name(symbol.name_id);

        if let ValueSymbolKind::Function(_, _) = symbol.kind {
            let func_val = *self.functions.get(&symbol.id).unwrap();
            let closure_struct_type = self.map_semantic_type(stmt.type_id.as_ref().unwrap()).unwrap().into_struct_type();
            let closure_ptr = self.builder.build_alloca(closure_struct_type, &format!("{}.closure", name)).unwrap();
            
            let fn_ptr_field = self.builder.build_struct_gep(closure_struct_type, closure_ptr, 0, &format!("{}.fn_ptr.addr", name)).unwrap();
            self.builder.build_store(fn_ptr_field, func_val.as_global_value().as_pointer_value()).unwrap();

            let env_ptr_field = self.builder.build_struct_gep(closure_struct_type, closure_ptr, 1, &format!("{}.env_ptr.addr", name)).unwrap();
            let env_ptr_type = self.context.ptr_type(AddressSpace::default());
            self.builder.build_store(env_ptr_field, env_ptr_type.const_null()).unwrap();
            
            return Some(self.builder.build_load(closure_struct_type, closure_ptr, &format!("{}.closure.val", name)).unwrap());
        }

        let field_ptr = self.compile_place_expression(stmt).unwrap();
        let field_type = stmt.type_id.as_ref().unwrap();
        let llvm_field_type = self.map_semantic_type(field_type).unwrap();
        let loaded_val = self.builder.build_load(llvm_field_type, field_ptr, name).unwrap();
        
        if self.is_heap_type(field_type) {
            let incref = self.get_incref();
            self.builder.build_call(incref, &[loaded_val.into()], "field_access.incref").unwrap();
        }

        Some(loaded_val)
    }

    fn compile_compiler_directive(&mut self, directive: &MIRDirectiveKind) -> Option<BasicValueEnum<'ctx>> {
        match directive {
            MIRDirectiveKind::IsRefcounted(ty) => Some(self.context.bool_type().const_int(self.is_heap_type(ty) as u64, false).as_basic_value_enum())
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
            constants: HashMap::new(),
            closure_info: HashMap::new(),
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
    
        let time_fn = self.get_c_time();
        let srand_fn = self.get_c_srand();
        let null_ptr = self.context.ptr_type(AddressSpace::default()).const_null();
        let time_val = self.builder.build_call(time_fn, &[null_ptr.into()], "time").unwrap()
            .try_as_basic_value().left().unwrap().into_int_value();
        let time_val_i32 = self.builder.build_int_truncate(time_val, self.context.i32_type(), "time_i32").unwrap();
        self.builder.build_call(srand_fn, &[time_val_i32.into()], "").unwrap();

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
    fn compile_const_initializer(&mut self, node: &MIRNode) -> Option<BasicValueEnum<'ctx>> {
        match &node.kind {
            MIRNodeKind::IntegerLiteral(v) => Some(self.compile_integer_literal(*v)),
            MIRNodeKind::FloatLiteral(v) => Some(self.compile_float_literal(*v)),
            MIRNodeKind::BooleanLiteral(v) => Some(self.compile_bool_literal(*v)),
            MIRNodeKind::CharLiteral(v) => Some(self.compile_char_literal(*v)),
            MIRNodeKind::StringLiteral(v) => Some(self.compile_string_literal(v)),
            _ => {
                None
            }
        }
    }

    fn find_and_compile_string_literals(&mut self, stmt: &MIRNode) {
        if let MIRNodeKind::StringLiteral(value) = &stmt.kind {
            self.compile_string_literal(value);
        }

        for child in stmt.children() {
            self.find_and_compile_string_literals(child);
        }
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    fn compile_declarations_pass(&mut self, stmts: &'a [MIRNode]) -> Vec<&'a MIRNode> {
        let mut functions = vec![];

        for stmt in stmts {
            self.find_and_compile_string_literals(stmt);
        }

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
            MIRNodeKind::Function { captures, .. } => {
                self.compile_function_declaration(stmt);
                functions.push(stmt);

                let fn_id = stmt.value_id.unwrap();
                if !captures.is_empty() {
                    let info: Vec<_> = captures.iter().map(|c| {
                        let MIRNodeKind::EnvironmentCapture { strategy, .. } = c.kind else { unreachable!() };
                        (c.value_id.unwrap(), strategy)
                    }).collect();
                    self.closure_info.insert(fn_id, info);
                }
            },
            MIRNodeKind::StructDeclaration { .. } => self.compile_struct_declaration(stmt),
            MIRNodeKind::EnumDeclaration { .. } => self.compile_enum_declaration(stmt),
            MIRNodeKind::VariableDeclaration { mutable: false, initializer, .. } => {
                let const_val = self.compile_const_initializer(initializer).unwrap();
                self.constants.insert(stmt.value_id.unwrap(), const_val);
            },
            _ => {}
        }
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    fn compile_node(&mut self, stmt: &MIRNode) -> Option<BasicValueEnum<'ctx>> {
        let result = match &stmt.kind {
            MIRNodeKind::IntegerLiteral(value) => Some(self.compile_integer_literal(*value)),
            MIRNodeKind::FloatLiteral(value) => Some(self.compile_float_literal(*value)),
            MIRNodeKind::BooleanLiteral(value) => Some(self.compile_bool_literal(*value)),
            MIRNodeKind::CharLiteral(value) => Some(self.compile_char_literal(*value)),
            MIRNodeKind::StringLiteral(value) => Some(self.compile_string_literal(value)),
            MIRNodeKind::Identifier(_) => Some(self.compile_identifier(stmt.value_id.unwrap(), stmt.type_id.as_ref().unwrap())),
            MIRNodeKind::SelfExpr => Some(self.compile_identifier(stmt.value_id.unwrap(), stmt.type_id.as_ref().unwrap())),
            MIRNodeKind::VariableDeclaration { name, initializer, mutable: false, .. } => {
                let init_val = self.compile_node(initializer).unwrap();
                init_val.set_name(name);
                self.constants.insert(stmt.value_id.unwrap(), init_val);
                Some(init_val)
            },
            MIRNodeKind::VariableDeclaration { name, initializer, mutable: true, .. }
                => self.compile_variable_declaration(name, initializer, stmt.value_id.unwrap()),
            MIRNodeKind::UnaryOperation { operator, operand }
                => self.compile_unary_operation(*operator, operand, stmt),
            MIRNodeKind::BinaryOperation { operator, left, right }
                => self.compile_binary_operation(*operator, left, right),
            MIRNodeKind::ConditionalOperation { operator, left, right }
                => self.compile_conditional_operation(*operator, left, right),
            MIRNodeKind::Block(stmts) => self.compile_block(stmts, stmt.scope_id),
            MIRNodeKind::ExpressionStatement(expr) => {
                self.compile_node(expr);
                None
            },
            MIRNodeKind::Return(opt_expr) => {
                if let Some(expr) = opt_expr {
                    let value = self.compile_node(expr).unwrap();
                    let returned_var_id = get_base_variable(expr);
                    let expr_type = expr.type_id.as_ref().unwrap();

                    if self.is_heap_type(expr_type) && !self.is_rvalue(expr) {
                        let incref = self.get_incref();
                        self.builder.build_call(incref, &[value.into()], "ret.incref").unwrap();
                    }

                    let mut current_scope_id = Some(stmt.scope_id);
                    while let Some(scope_id) = current_scope_id {
                        let scope = self.analyzer.symbol_table.get_scope(scope_id).unwrap();
                        self.compile_scope_drop(scope_id, returned_var_id);
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
                        self.compile_scope_drop(scope_id, None);
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
                    self.compile_scope_drop(scope_id, None);

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
                    self.compile_scope_drop(scope_id, None);

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
            MIRNodeKind::SizeofExpression(ty) => {
                let llvm_ty = self.map_semantic_type(ty).unwrap();
                let size = llvm_ty.size_of().unwrap();
                Some(size.as_basic_value_enum())
            },
            MIRNodeKind::CompilerDirective(directive) => self.compile_compiler_directive(directive),
            kind => unimplemented!("cannot compile node of kind {:?}", kind)
        };
        
        let value = result?;
        let ty = stmt.type_id.as_ref().unwrap();

        if self.is_heap_type(ty) {
            let needs_wrapping = matches!(stmt.kind, 
                MIRNodeKind::IntegerLiteral(_) |
                MIRNodeKind::FloatLiteral(_) |
                MIRNodeKind::BooleanLiteral(_) |
                MIRNodeKind::CharLiteral(_) |
                MIRNodeKind::StructLiteral { .. }
            );

            if needs_wrapping {
                return Some(self.build_rc_wrap(value, ty).as_basic_value_enum());
            }
        }
        
        Some(value)
    }
}