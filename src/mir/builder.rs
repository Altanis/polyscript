use std::{borrow::Borrow, collections::{BTreeMap, HashMap, HashSet}, fmt::Write, rc::Rc};

use colored::Colorize;

use crate::{
    frontend::{
        semantics::analyzer::{ScopeId, ScopeKind, SemanticAnalyzer, Type, TypeSymbolId, TypeSymbolKind, ValueSymbol, ValueSymbolId, ValueSymbolKind},
        syntax::ast::{AstNode, AstNodeKind},
    },
    mir::ir_node::{CaptureStrategy, MIRDirectiveKind, MIRNode, MIRNodeKind},
    utils::kind::{DirectiveKind, QualifierKind, Span},
};

#[derive(Default)]
pub struct MonomorphizationContext {
    instantiations: HashMap<TypeSymbolId, HashSet<BTreeMap<TypeSymbolId, Type>>>,
    substitution_ctx: Option<Rc<BTreeMap<TypeSymbolId, Type>>>
}

pub struct MIRBuilder<'a> {
    analyzer: &'a mut SemanticAnalyzer,
    monomorphization_ctx: MonomorphizationContext,

    fn_template_map: HashMap<ValueSymbolId, (ValueSymbolId, Rc<BTreeMap<TypeSymbolId, Type>>)>,
    fn_param_remaps: HashMap<ValueSymbolId, HashMap<ValueSymbolId, ValueSymbolId>>,

    concretize_substitutions: Option<Rc<BTreeMap<TypeSymbolId, Type>>>,
    concretize_value_remap: HashMap<ValueSymbolId, ValueSymbolId>,
    
    hoisted_iifes: Vec<MIRNode>,
    hoisted_declarations: Vec<MIRNode>
}

fn find_node_by_span(node: &AstNode, target_span: Span) -> Option<&AstNode> {
    if node.span == target_span { return Some(node); }

    for child in node.children() {
        if let Some(found) = find_node_by_span(child, target_span) {
            return Some(found);
        }
    }
    
    None
}

fn find_node_by_span_mut(node: &mut AstNode, target_span: Span) -> Option<&mut AstNode> {
    if node.span == target_span {
        return Some(node);
    }

    for child in node.children_mut() {
        if let Some(found) = find_node_by_span_mut(child, target_span) {
            return Some(found);
        }
    }

    None
}


impl<'a> MIRBuilder<'a> {
    pub fn new(analyzer: &'a mut SemanticAnalyzer) -> Self {
        Self {
            analyzer,
            monomorphization_ctx: MonomorphizationContext::default(),
            fn_template_map: HashMap::new(),
            fn_param_remaps: HashMap::new(),
            concretize_substitutions: None,
            concretize_value_remap: HashMap::new(),
            hoisted_iifes: vec![],
            hoisted_declarations: vec![]
        }
    }

    fn apply_substitutions(ty: &Type, substitutions: &BTreeMap<TypeSymbolId, Type>) -> Type {
        if let Some(concrete_type) = substitutions.get(&ty.symbol) {
            return Self::apply_substitutions(concrete_type, substitutions);
        }

        let new_args = ty.args
            .iter()
            .map(|arg| Self::apply_substitutions(arg, substitutions))
            .collect();

        Type {
            symbol: ty.symbol,
            args: new_args,
        }
    }
}

impl<'a> MIRBuilder<'a> {
    fn find_trait_scope_from_signature(&self, fn_sig_symbol: &crate::frontend::semantics::analyzer::TypeSymbol) -> Option<ScopeId> {
        let TypeSymbolKind::FunctionSignature { params, return_type, .. } = &fn_sig_symbol.kind else { return None; };
        
        let has_trait_self = |ty: &Type| -> Option<ScopeId> {
            let base_symbol_id = ty.symbol;
            let mut current_id = base_symbol_id;
            loop {
                let base_symbol = self.analyzer.symbol_table.get_type_symbol(current_id).unwrap();
                match &base_symbol.kind {
                    &TypeSymbolKind::TraitSelf(id) => return Some(id),
                    TypeSymbolKind::TypeAlias((_, Some(alias))) => current_id = alias.symbol,
                    _ => return None
                }
            }
        };

        for ty in params.iter().chain(std::iter::once(return_type)) {
            if let Some(scope_id) = has_trait_self(ty) {
                return Some(scope_id);
            }
        }

        None
    }

    fn check_trait_impl_applicability_mir(&self, instance_type: &Type, imp: &crate::frontend::semantics::analyzer::TraitImpl) -> bool {
        let instance_args = &instance_type.args;
        
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

    pub fn type_is_fully_concrete(&self, ty: &Type) -> bool {
        let type_symbol = self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap();
        if matches!(type_symbol.kind, TypeSymbolKind::Generic(_) | TypeSymbolKind::TraitSelf(_)) {
            return false;
        }

        ty.args.iter().all(|arg| self.type_is_fully_concrete(arg))
    }

    fn get_type_from_ast(&self, node: &AstNode, scope_id: ScopeId) -> Result<Type, ()> {
        if let AstNodeKind::TypeReference { type_name, generic_types, .. } = &node.kind {
            let symbol = self.analyzer.symbol_table.find_type_symbol_from_scope(scope_id, type_name).ok_or(())?;
            let args = generic_types.iter().map(|arg| self.get_type_from_ast(arg, scope_id)).collect::<Result<Vec<_>, _>>()?;

            return Ok(Type { symbol: symbol.id, args });
        }

        Err(())
    }

    fn propagate_monomorphizations(&mut self, program: &mut AstNode) {
        let mut changed = true;
        while changed {
            changed = false;
            
            let instantiations_clone = self.monomorphization_ctx.instantiations.clone();
            
            for (template_symbol_id, specializations) in instantiations_clone.iter() {
                let template_symbol = self.analyzer.symbol_table.get_type_symbol(*template_symbol_id).unwrap().clone();

                if let TypeSymbolKind::FunctionSignature { .. } = &template_symbol.kind
                    && let Some(value_symbol) = self.analyzer.symbol_table.registry.value_symbols.values()
                        .find(|vs| vs.type_id.as_ref().is_some_and(|ty| ty.symbol == *template_symbol_id)).cloned()
                    && let Some(span) = value_symbol.span
                {
                    let func_node = find_node_by_span_mut(program, span).unwrap();
                    
                    for specialization_map in specializations.iter() {
                        let old_ctx = self.monomorphization_ctx.substitution_ctx.replace(Rc::new(specialization_map.clone()));
                        
                        let total_instantiations_before = self.monomorphization_ctx.instantiations.values().map(|s| s.len()).sum::<usize>();
                        self.collect_monomorphization_sites(func_node);
                        let total_instantiations_after = self.monomorphization_ctx.instantiations.values().map(|s| s.len()).sum::<usize>();

                        if total_instantiations_after > total_instantiations_before {
                            changed = true;
                        }

                        self.monomorphization_ctx.substitution_ctx = old_ctx;
                    }
                }

                if let TypeSymbolKind::Struct((_, inherent_impls)) = &template_symbol.kind {
                    let inherent_impls_clone = inherent_impls.clone();

                    for specialization_map in specializations.iter() {
                        for imp in &inherent_impls_clone {
                            if imp.generic_params.is_empty() {
                                continue;
                            }
                            
                            let impl_node = find_node_by_span(program, imp.span).unwrap();
                            let (impl_type_ref, associated_functions) = if let AstNodeKind::ImplDeclaration { type_reference, associated_functions, .. } = &impl_node.kind {
                                (type_reference, associated_functions)
                            } else {
                                unreachable!();
                            };
                            
                            let mut impl_substitutions = BTreeMap::new();
                            let generic_struct_params = &template_symbol.generic_parameters;
                            
                            let AstNodeKind::TypeReference { generic_types: impl_ref_generic_args, .. } = &impl_type_ref.kind else {
                                continue;
                            };
                            
                            let mut consistent = true;
                            for (i, struct_generic_id) in generic_struct_params.iter().enumerate() {
                                let impl_generic_arg_node = impl_ref_generic_args.get(i).unwrap();
                                let concrete_type_for_struct_generic = specialization_map.get(struct_generic_id).unwrap();
                                let impl_generic_type = self.get_type_from_ast(impl_generic_arg_node, imp.scope_id).unwrap();
                                
                                if imp.generic_params.contains(&impl_generic_type.symbol) {
                                    if let Some(existing) = impl_substitutions.get(&impl_generic_type.symbol) {
                                        if existing != concrete_type_for_struct_generic {
                                            consistent = false;
                                            break;
                                        }
                                    } else {
                                        impl_substitutions.insert(impl_generic_type.symbol, concrete_type_for_struct_generic.clone());
                                    }
                                } else if &impl_generic_type != concrete_type_for_struct_generic {
                                    consistent = false;
                                    break;
                                }
                            }

                            if !consistent || impl_substitutions.is_empty() {
                                continue;
                            }

                            let hash_map_substitutions: HashMap<_, _> = impl_substitutions.iter().map(|(k, v)| (*k, v.clone())).collect();
                            if !self.analyzer.check_impl_generic_constraints(&imp.generic_params, &hash_map_substitutions).unwrap_or(false) {
                                continue;
                            }

                            for func_node in associated_functions {
                                let func_value_id = func_node.value_id.unwrap();
                                let func_symbol = self.analyzer.symbol_table.get_value_symbol(func_value_id).unwrap();
                                let func_type_id = func_symbol.type_id.as_ref().unwrap().symbol;
                                
                                let instantiations_for_func = self.monomorphization_ctx.instantiations.entry(func_type_id).or_default();
                                if instantiations_for_func.insert(impl_substitutions.clone()) {
                                    changed = true;
                                }
                            }
                        }
                    }
                }

                let trait_registry_clone = self.analyzer.trait_registry.register.clone();
                for (_, impls_for_trait) in trait_registry_clone.iter() {
                    if let Some(trait_impls) = impls_for_trait.get(template_symbol_id) {
                        for trait_impl in trait_impls {
                            if trait_impl.impl_generic_params.is_empty() {
                                continue;
                            }

                            for specialization_map in specializations.iter() {
                                let concrete_args: Vec<Type> = template_symbol.generic_parameters
                                    .iter()
                                    .map(|gid| specialization_map.get(gid).unwrap().clone())
                                    .collect();
                                let concrete_instance_type = Type {
                                    symbol: *template_symbol_id,
                                    args: concrete_args,
                                };

                                let mut impl_substitutions = BTreeMap::new();
                                let mut is_applicable = true;

                                if concrete_instance_type.args.len() == trait_impl.type_specialization.len() {
                                    for (instance_arg, &impl_spec_id) in concrete_instance_type.args.iter().zip(&trait_impl.type_specialization) {
                                        if trait_impl.impl_generic_params.contains(&impl_spec_id) {
                                            impl_substitutions.insert(impl_spec_id, instance_arg.clone());
                                        } else if instance_arg.symbol != impl_spec_id {
                                            is_applicable = false;
                                            break;
                                        }
                                    }
                                } else {
                                    is_applicable = false;
                                }

                                if !is_applicable || impl_substitutions.is_empty() {
                                    continue;
                                }

                                let hash_map_substitutions: HashMap<_, _> = impl_substitutions.iter().map(|(k, v)| (*k, v.clone())).collect();
                                if !self.analyzer.check_impl_generic_constraints(&trait_impl.impl_generic_params, &hash_map_substitutions).unwrap_or(false) {
                                    continue;
                                }

                                let impl_scope = self.analyzer.symbol_table.get_scope(trait_impl.impl_scope_id).unwrap();
                                for &func_value_id in impl_scope.values.values() {
                                    let func_symbol = self.analyzer.symbol_table.get_value_symbol(func_value_id).unwrap();
                                    if let ValueSymbolKind::Function(_, _) = func_symbol.kind
                                        && let Some(func_type_id) = func_symbol.type_id.as_ref().map(|t| t.symbol)
                                    {
                                        let instantiations_for_func = self.monomorphization_ctx.instantiations.entry(func_type_id).or_default();
                                        if instantiations_for_func.insert(impl_substitutions.clone()) {
                                            changed = true;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn discover_monomorphic_sites(&mut self, program: &mut AstNode) {
        let AstNodeKind::Program(stmts) = &mut program.kind else { unreachable!(); };
        for stmt in stmts.iter_mut() {
            self.collect_monomorphization_sites(stmt);
        }
    }

    fn collect_generic_mappings(
        &self,
        concrete_ty: &Type,
        template_ty: &Type,
        substitutions: &mut HashMap<TypeSymbolId, Type>,
    ) {
        let concrete_ty = if let Some(ctx_subs) = &self.monomorphization_ctx.substitution_ctx {
            Self::apply_substitutions(concrete_ty, ctx_subs)
        } else {
            concrete_ty.clone()
        };

        let template_type_symbol = self.analyzer.symbol_table.get_type_symbol(template_ty.symbol).unwrap();

        if let TypeSymbolKind::Generic(_) = template_type_symbol.kind {
            substitutions.insert(template_ty.symbol, concrete_ty.clone());
            return;
        }

        if concrete_ty.symbol == template_ty.symbol && concrete_ty.args.len() == template_ty.args.len() {
            for (c_arg, t_arg) in concrete_ty.args.iter().zip(template_ty.args.iter()) {
                self.collect_generic_mappings(c_arg, t_arg, substitutions);
            }
        }
    }

    fn collect_generic_ids(&self, ty: &Type, out: &mut Vec<TypeSymbolId>) {
        match self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap().kind {
            TypeSymbolKind::Generic(_) => {
                if !out.contains(&ty.symbol) {
                    out.push(ty.symbol);
                }
            },
            _ => {
                for a in ty.args.iter() {
                    self.collect_generic_ids(a, out);
                }
            }
        }
    }

    fn collect_monomorphization_sites(&mut self, node: &mut AstNode) {
        for child in node.children_mut() {
            self.collect_monomorphization_sites(child);
        }

        match &mut node.kind {
            AstNodeKind::FunctionCall { function, arguments, monomorphized_generic_arguments } => {
                let Some(fn_value_symbol) = function.value_id.and_then(|id| self.analyzer.symbol_table.get_value_symbol(id)) else { return; };
                let Some(template_fn_type) = fn_value_symbol.type_id.as_ref() else { return; };

                let fn_symbol = self.analyzer.symbol_table.get_type_symbol(template_fn_type.symbol).unwrap();
                let TypeSymbolKind::FunctionSignature { params: template_params, return_type: template_return, .. } = &fn_symbol.kind else { return; };

                let mut generic_id_to_concrete_type = HashMap::new();
                
                let has_receiver = fn_symbol.generic_parameters.iter().any(|p| {
                    let sym = self.analyzer.symbol_table.get_type_symbol(*p).unwrap();
                    let name = self.analyzer.symbol_table.get_type_name(sym.name_id);
                    name == "Self"
                }) || (!template_params.is_empty() && arguments.len() < template_params.len());

                if has_receiver
                    && let AstNodeKind::FieldAccess { left, .. } = &function.kind
                    && let Some(instance_type) = &left.type_id
                {
                    let mut concrete_receiver_ty = instance_type.clone();
                    if let Some(subs) = &self.monomorphization_ctx.substitution_ctx {
                        concrete_receiver_ty = Self::apply_substitutions(&concrete_receiver_ty, subs);
                    }

                    let template_receiver_ty = &template_params[0];
                    let base_template_receiver_ty = template_receiver_ty;
                
                    self.collect_generic_mappings(
                        &concrete_receiver_ty,
                        base_template_receiver_ty,
                        &mut generic_id_to_concrete_type,
                    );
                }

                let params_to_zip = if has_receiver {
                    &template_params[1..]
                } else {
                    template_params
                };

                for (arg_node, template_param) in arguments.iter().zip(params_to_zip.iter()) {
                    if let Some(concrete_type) = &arg_node.type_id {
                        let mut final_concrete_type = concrete_type.clone();
                        if let Some(subs) = &self.monomorphization_ctx.substitution_ctx {
                            final_concrete_type = Self::apply_substitutions(&final_concrete_type, subs);
                        }
                        self.collect_generic_mappings(&final_concrete_type, template_param, &mut generic_id_to_concrete_type);
                    }
                }
                
                if let Some(call_site_return_type) = &node.type_id {
                    let mut final_return_type = call_site_return_type.clone();
                    if let Some(subs) = &self.monomorphization_ctx.substitution_ctx {
                        final_return_type = Self::apply_substitutions(&final_return_type, subs);
                    }
                    self.collect_generic_mappings(
                        &final_return_type,
                        template_return,
                        &mut generic_id_to_concrete_type,
                    );
                }

                let mut ordered_generic_ids: Vec<TypeSymbolId> = vec![];

                if has_receiver {
                    let template_receiver_ty = &template_params[0];
                    let base_template_receiver_ty = template_receiver_ty;
                    self.collect_generic_ids(base_template_receiver_ty, &mut ordered_generic_ids);
                }

                for template_param in params_to_zip.iter() {
                    self.collect_generic_ids(template_param, &mut ordered_generic_ids);
                }

                self.collect_generic_ids(template_return, &mut ordered_generic_ids);

                ordered_generic_ids.retain(|&gid| {
                    let sym = self.analyzer.symbol_table.get_type_symbol(gid).unwrap();
                    let name = self.analyzer.symbol_table.get_type_name(sym.name_id);
                    name != "Self"
                });

                let ordered_args_option: Option<Vec<Type>> = ordered_generic_ids
                    .iter()
                    .map(|gid| {
                        let ty = generic_id_to_concrete_type.get(gid)?;
                        if !self.type_is_fully_concrete(ty) { return None; }

                        Some(ty.clone())
                    })
                    .collect();

                let Some(ordered_args) = ordered_args_option else { return };

                if !ordered_args.is_empty() {
                    let instantiation_map: BTreeMap<TypeSymbolId, Type> = ordered_generic_ids
                        .iter()
                        .cloned()
                        .zip(ordered_args.iter().cloned())
                        .collect();
                    
                    let key = self.monomorphization_ctx.substitution_ctx.clone().unwrap_or_else(|| Rc::new(BTreeMap::new()));
                    monomorphized_generic_arguments.insert(key, ordered_args);

                    self.monomorphization_ctx
                        .instantiations
                        .entry(template_fn_type.symbol)
                        .or_default()
                        .insert(instantiation_map);
                }
            },
            AstNodeKind::StructLiteral { generic_arguments, .. } | AstNodeKind::TypeReference { generic_arguments, .. } => {
                if let Some(ty) = &node.type_id {
                    let type_symbol = self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap();
                    
                    if type_symbol.generic_parameters.is_empty() || ty.args.is_empty() {
                        return;
                    }

                    if ty.args.iter().all(|arg| self.type_is_fully_concrete(arg)) {
                        *generic_arguments = ty.args.clone();

                        let instantiation_map: BTreeMap<TypeSymbolId, Type> = type_symbol
                            .generic_parameters
                            .iter()
                            .zip(ty.args.iter())
                            .map(|(&gid, ty)| (gid, ty.clone()))
                            .collect();
                        
                        if !instantiation_map.is_empty() {
                            self.monomorphization_ctx
                                .instantiations
                                .entry(ty.symbol)
                                .or_default()
                                .insert(instantiation_map);
                        }
                    }
                }
            },
            _ => {}
        }
    }
}

impl<'a> MIRBuilder<'a> {
    fn monomorphize(&mut self, program: &mut AstNode) -> MIRNode {
        let mut mir_stmts = vec![];

        let AstNodeKind::Program(stmts) = &mut program.kind else { unreachable!(); };
        for stmt in stmts.iter_mut() {
            match &mut stmt.kind {
                AstNodeKind::ImplDeclaration { associated_functions, generic_parameters, .. } => {
                    if !generic_parameters.is_empty() {
                        for func in associated_functions {
                            mir_stmts.extend(self.build_concrete_stmt(func));
                        }
                    }
                },
                _ => mir_stmts.extend(self.build_concrete_stmt(stmt))
            }
        }

        MIRNode {
            kind: MIRNodeKind::Program(mir_stmts),
            span: program.span,
            value_id: None,
            type_id: None,
            scope_id: 0
        }
    }

    fn mangle_name<I>(&self, id: TypeSymbolId, concrete_types: I) -> String
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

    fn mangle_value_name(&self, symbol: &ValueSymbol) -> String {
        let name = self.analyzer.symbol_table.get_value_name(symbol.name_id);
        format!("{}_{}", name, symbol.id)
    }

    fn substitute_type(&mut self, generic_type: &Type, substitutions: &BTreeMap<TypeSymbolId, Type>) -> Type {
        if let Some(concrete_type) = substitutions.get(&generic_type.symbol) {
            return concrete_type.clone();
        }

        let type_symbol = self.analyzer.symbol_table.get_type_symbol(generic_type.symbol).unwrap().clone();
        if let TypeSymbolKind::OpaqueTypeProjection { ty, tr, member } = &type_symbol.kind {
            let substituted_ty = self.substitute_type(ty, substitutions);
            let substituted_tr = self.substitute_type(tr, substitutions);

            if &substituted_ty != ty || &substituted_tr != tr {
                let new_opaque_type_name = format!(
                    "[{} as {}].{}",
                    self.analyzer.symbol_table.display_type(&substituted_ty),
                    self.analyzer.symbol_table.display_type(&substituted_tr),
                    member
                );
                
                let new_symbol_id = if let Some(sym) = self.analyzer.symbol_table.find_type_symbol(&new_opaque_type_name) {
                    sym.id
                } else {
                    self.analyzer.symbol_table.add_type_symbol(
                        &new_opaque_type_name,
                        TypeSymbolKind::OpaqueTypeProjection {
                            ty: substituted_ty, 
                            tr: substituted_tr,
                            member: member.clone()
                        },
                        vec![],
                        QualifierKind::Private,
                        type_symbol.span
                    ).unwrap()
                };

                return Type::from_no_args(new_symbol_id);
            }
        }

        let new_args = generic_type.args
            .iter()
            .map(|arg| self.substitute_type(arg, substitutions))
            .collect();

        Type {
            symbol: generic_type.symbol,
            args: new_args,
        }
    }

    fn build_concrete_stmt(&mut self, node: &mut AstNode) -> Vec<MIRNode> {
        let mut concrete_ir_nodes = vec![];

        for child in node.children_mut() {
            concrete_ir_nodes.extend(self.build_concrete_stmt(child));
        }

        let template_symbol_id = match &node.kind {
            AstNodeKind::StructDeclaration { name, .. } => self
                .analyzer
                .symbol_table
                .find_type_symbol_in_scope(name, node.scope_id.unwrap())
                .unwrap()
                .id,
            AstNodeKind::Function { .. } => {
                let value_symbol = self
                    .analyzer
                    .symbol_table
                    .get_value_symbol(node.value_id.unwrap())
                    .unwrap();
                value_symbol.type_id.as_ref().unwrap().symbol
            }
            _ => return concrete_ir_nodes,
        };
        let Some(concrete_types_set) = self.monomorphization_ctx.instantiations.get(&template_symbol_id).cloned() else { return concrete_ir_nodes; };

        match &node.kind {
            AstNodeKind::StructDeclaration { .. } | AstNodeKind::Function { .. } => {
                for concrete_types in concrete_types_set {
                    self.monomorphization_ctx.substitution_ctx = Some(Rc::new(concrete_types));
                    if let Some(ir_node) = self.lower_node(node) {
                        concrete_ir_nodes.push(ir_node);
                    }
                    self.monomorphization_ctx.substitution_ctx = None;
                }
            }
            _ => {}
        }

        concrete_ir_nodes
    }
}

impl<'a> MIRBuilder<'a> {
    fn lower_node(&mut self, node: &mut AstNode) -> Option<MIRNode> {
        let kind = match &mut node.kind {
            AstNodeKind::IntegerLiteral(v) => MIRNodeKind::IntegerLiteral(*v),
            AstNodeKind::FloatLiteral(v) => MIRNodeKind::FloatLiteral(*v),
            AstNodeKind::BooleanLiteral(v) => MIRNodeKind::BooleanLiteral(*v),
            AstNodeKind::StringLiteral(v) => MIRNodeKind::StringLiteral(v.clone()),
            AstNodeKind::CharLiteral(v) => MIRNodeKind::CharLiteral(*v),

            AstNodeKind::Identifier(name) => MIRNodeKind::Identifier(name.clone()),
            AstNodeKind::SelfExpr => MIRNodeKind::SelfExpr,
            AstNodeKind::ExpressionStatement(expr) => {
                MIRNodeKind::ExpressionStatement(Box::new(self.lower_node(expr)?))
            }

            AstNodeKind::AssociatedConstant { name, initializer, .. } => {
                let (mangled_name, sym_id) = {
                    let sym = self.analyzer.symbol_table.find_value_symbol_in_scope(name, node.scope_id.unwrap()).unwrap();
                    (self.mangle_value_name(sym), sym.id)
                };

                let new_name_id = self.analyzer.symbol_table.value_names.intern(&mangled_name);
                self.analyzer.symbol_table.get_value_symbol_mut(sym_id).unwrap().name_id = new_name_id;

                MIRNodeKind::VariableDeclaration {
                    name: mangled_name,
                    mutable: false,
                    initializer: Box::new(self.lower_node(initializer)?),
                }
            },
            AstNodeKind::VariableDeclaration { name, mutable, initializer, .. } => {
                MIRNodeKind::VariableDeclaration {
                    name: name.clone(),
                    mutable: *mutable,
                    initializer: Box::new(self.lower_node(initializer)?),
                }
            },
            AstNodeKind::UnaryOperation { operator, operand } => MIRNodeKind::UnaryOperation {
                operator: *operator,
                operand: Box::new(self.lower_node(operand)?),
            },
            AstNodeKind::BinaryOperation { operator, left, right } => MIRNodeKind::BinaryOperation {
                operator: *operator,
                left: Box::new(self.lower_node(left)?),
                right: Box::new(self.lower_node(right)?),
            },
            AstNodeKind::ConditionalOperation { operator, left, right } => {
                MIRNodeKind::ConditionalOperation {
                    operator: *operator,
                    left: Box::new(self.lower_node(left)?),
                    right: Box::new(self.lower_node(right)?),
                }
            }

            AstNodeKind::TypeCast { expr, .. } => MIRNodeKind::TypeCast {
                expr: Box::new(self.lower_node(expr)?),
                target_type: node.type_id.clone()?,
            },

            AstNodeKind::Block(stmts) => {
                MIRNodeKind::Block(stmts.iter_mut().filter_map(|s| self.lower_node(s)).collect())
            },
            AstNodeKind::IfStatement { condition, then_branch, else_if_branches, else_branch } => {
                MIRNodeKind::IfStatement {
                    condition: Box::new(self.lower_node(condition)?),
                    then_branch: Box::new(self.lower_node(then_branch)?),
                    else_if_branches: else_if_branches
                        .iter_mut()
                        .filter_map(|(c, b)| {
                            Some((Box::new(self.lower_node(c)?), Box::new(self.lower_node(b)?)))
                        })
                        .collect(),
                    else_branch: else_branch.as_mut().map(|b| Box::new(self.lower_node(b).unwrap())),
                }
            },
            AstNodeKind::WhileLoop { condition, body } => MIRNodeKind::WhileLoop {
                condition: Box::new(self.lower_node(condition)?),
                body: Box::new(self.lower_node(body)?),
            },
            AstNodeKind::ForLoop { initializer, condition, increment, body } => {
                MIRNodeKind::ForLoop {
                    initializer: initializer.as_mut().map(|n| Box::new(self.lower_node(n).unwrap())),
                    condition: condition.as_mut().map(|n| Box::new(self.lower_node(n).unwrap())),
                    increment: increment.as_mut().map(|n| Box::new(self.lower_node(n).unwrap())),
                    body: Box::new(self.lower_node(body)?),
                }
            }
            AstNodeKind::Return(expr) => {
                MIRNodeKind::Return(expr.as_mut().map(|e| Box::new(self.lower_node(e).unwrap())))
            }
            AstNodeKind::Break => MIRNodeKind::Break,
            AstNodeKind::Continue => MIRNodeKind::Continue,

            AstNodeKind::Function { parameters, instance, body, generic_parameters, .. } => {
                if let Some(substitutions) = self.monomorphization_ctx.substitution_ctx.clone() {
                    let template_value_symbol = self.analyzer.symbol_table.get_value_symbol(node.value_id.unwrap()).unwrap().clone();
                    let template_type = template_value_symbol.type_id.as_ref().unwrap();
                    let template_fn_sig_symbol = self.analyzer.symbol_table.get_type_symbol(template_type.symbol).unwrap().clone();
                    let TypeSymbolKind::FunctionSignature { params: template_params, return_type: template_return_type, .. } = &template_fn_sig_symbol.kind else { unreachable!() };

                    let mangled_name = self.mangle_name(template_fn_sig_symbol.id, substitutions.values());
                    let parent_scope_id = self.analyzer.symbol_table.get_scope(template_value_symbol.scope_id).unwrap().id;
                    if self.analyzer.symbol_table.find_value_symbol_from_scope(parent_scope_id, &mangled_name).is_some() {
                        return None;
                    }

                    let concrete_params_unresolved: Vec<Type> = template_params.iter().map(|p| self.substitute_type(p, &substitutions)).collect();
                    let concrete_return_type_unresolved = self.substitute_type(template_return_type, &substitutions);

                    let concrete_params: Vec<Type> = concrete_params_unresolved
                        .iter()
                        .map(|p| self.resolve_concrete_type_recursively(p))
                        .collect();
                    let concrete_return_type = self.resolve_concrete_type_recursively(&concrete_return_type_unresolved);

                    let original_scope = self.analyzer.symbol_table.current_scope_id;
                    self.analyzer.symbol_table.current_scope_id = parent_scope_id;

                    let concrete_fn_sig_id = self.analyzer.symbol_table.add_type_symbol(
                        &mangled_name,
                        TypeSymbolKind::FunctionSignature {
                            params: concrete_params.clone(),
                            return_type: concrete_return_type.clone(),
                            instance: *instance,
                        },
                        vec![],
                        template_fn_sig_symbol.qualifier,
                        Some(node.span),
                    ).unwrap();

                    let new_fn_body_scope_id = self.analyzer.symbol_table.enter_scope(ScopeKind::Function);

                    let mut mir_params = vec![];
                    let mut param_remap = HashMap::new();

                    for (i, param_node) in parameters.iter_mut().enumerate() {
                        let AstNodeKind::FunctionParameter { name: param_name, mutable, .. } = &param_node.kind else { unreachable!() };
                        
                        let param_type = &concrete_params[i];
                        let param_value_id = self.analyzer.symbol_table.add_value_symbol(
                            param_name,
                            ValueSymbolKind::Variable,
                            *mutable,
                            QualifierKind::Private,
                            Some(param_type.clone()),
                            Some(param_node.span),
                        ).unwrap();

                        param_remap.insert(param_node.value_id.unwrap(), param_value_id);
                        
                        mir_params.push(MIRNode {
                            kind: MIRNodeKind::FunctionParameter {
                                name: param_name.clone(),
                                mutable: *mutable,
                            },
                            span: param_node.span,
                            value_id: Some(param_value_id),
                            type_id: Some(param_type.clone()),
                            scope_id: node.scope_id.unwrap()
                        });
                    }

                    let mir_body = body.as_mut().map(|b| Box::new(self.lower_node(b).unwrap()));

                    self.analyzer.symbol_table.exit_scope();

                    let concrete_fn_value_id = self.analyzer.symbol_table.add_value_symbol(
                        &mangled_name,
                        ValueSymbolKind::Function(new_fn_body_scope_id, HashSet::new()),
                        false,
                        template_value_symbol.qualifier,
                        Some(Type::from_no_args(concrete_fn_sig_id)),
                        Some(node.span),
                    ).unwrap();

                    self.fn_template_map.insert(concrete_fn_value_id, (template_value_symbol.id, substitutions.clone()));
                    self.fn_param_remaps.insert(concrete_fn_value_id, param_remap);

                    self.analyzer.symbol_table.current_scope_id = original_scope;

                    return Some(MIRNode {
                        kind: MIRNodeKind::Function { name: mangled_name, parameters: mir_params, instance: *instance, body: mir_body, captures: vec![] },
                        span: node.span,
                        value_id: Some(concrete_fn_value_id),
                        type_id: Some(Type::from_no_args(concrete_fn_sig_id)),
                        scope_id: node.scope_id.unwrap()
                    });
                }

                if generic_parameters.is_empty() {
                    let (mangled_name, sym_id, scope_id, captures) = {
                        let sym = self.analyzer.symbol_table.get_value_symbol(node.value_id.unwrap()).unwrap();
                        let ValueSymbolKind::Function(scope_id, captures) = &sym.kind else { unreachable!(); };

                        (self.mangle_value_name(sym), sym.id, *scope_id, captures.clone())
                    };

                    let new_name_id = self.analyzer.symbol_table.value_names.intern(&mangled_name);
                    self.analyzer.symbol_table.get_value_symbol_mut(sym_id).unwrap().name_id = new_name_id;

                    MIRNodeKind::Function {
                        name: mangled_name.clone(),
                        parameters: parameters.iter_mut().filter_map(|p| self.lower_node(p)).collect(),
                        instance: *instance,
                        body: body.as_mut().map(|b| Box::new(self.lower_node(b).unwrap())),
                        captures: captures.into_iter().map(|capture| {
                            let sym = self.analyzer.symbol_table.get_value_symbol(capture).unwrap();
                            MIRNode {
                                kind: MIRNodeKind::EnvironmentCapture {
                                    name: self.analyzer.symbol_table.get_value_name(sym.name_id).to_string(),
                                    strategy: CaptureStrategy::Copy
                                },
                                value_id: Some(capture),
                                type_id: sym.type_id.clone(),
                                span: sym.span.unwrap(),
                                scope_id
                            }
                        }).collect()
                    }
                } else {
                    return None;
                }
            },
            AstNodeKind::FunctionParameter { name, mutable, .. } => MIRNodeKind::FunctionParameter {
                name: name.clone(),
                mutable: *mutable,
            },
            AstNodeKind::FunctionCall { function, arguments, monomorphized_generic_arguments } => {
                if let AstNodeKind::Function { .. } = &mut function.kind {
                    let function_mir = self.lower_node(function).unwrap();
                    let hoisted_name = if let MIRNodeKind::Function { name, .. } = &function_mir.kind { name.clone() } else { unreachable!(); };
                    
                    self.hoisted_iifes.push(function_mir);

                    let mir_function_expr = MIRNode {
                        kind: MIRNodeKind::Identifier(hoisted_name),
                        span: function.span,
                        value_id: function.value_id,
                        type_id: function.type_id.clone(),
                        scope_id: function.scope_id.unwrap()
                    };

                    let mir_arguments = arguments.iter_mut().filter_map(|a| self.lower_node(a)).collect();
                    
                    MIRNodeKind::FunctionCall {
                        function: Box::new(mir_function_expr),
                        arguments: mir_arguments,
                    }
                } else if let Some(fn_value_symbol) = function.value_id.and_then(|id| self.analyzer.symbol_table.get_value_symbol(id).cloned()) {
                    let mut mir_arguments: Vec<MIRNode> = arguments.iter_mut().filter_map(|a| self.lower_node(a)).collect();

                    let fn_type = fn_value_symbol.type_id.as_ref().unwrap();

                    let is_instance_method_call = if let AstNodeKind::FieldAccess { left, .. } = &function.kind {
                        match &left.kind {
                            AstNodeKind::Identifier(name) => self.analyzer.symbol_table.find_type_symbol_from_scope(left.scope_id.unwrap(), name).is_none(),
                            AstNodeKind::PathQualifier { .. } => false,
                            _ => true
                        }
                    } else {
                        false
                    };

                    let mut needs_monomorphization = !monomorphized_generic_arguments.is_empty();
                    if !needs_monomorphization
                        && let AstNodeKind::FieldAccess { left, .. } = &function.kind
                        && let Some(base_type) = &left.type_id
                    {
                        needs_monomorphization = !base_type.args.is_empty();
                    }

                    if fn_value_symbol.is_intrinsic {
                        needs_monomorphization = false;
                    } 
                    
                    let (mut mir_fn_name, mut mir_fn_value_id, mut mir_fn_type) = if needs_monomorphization && !fn_value_symbol.is_intrinsic {
                        (|| {
                            let key = self.monomorphization_ctx.substitution_ctx.clone().unwrap_or_else(|| Rc::new(BTreeMap::new()));
                            let concrete_types_for_mangling = if let Some(args) = monomorphized_generic_arguments.get(&key) {
                                args.clone()
                            } else if let AstNodeKind::FieldAccess { left, .. } = &function.kind {
                                let mut base_type = left.type_id.as_ref()?.clone();
                                if let Some(substitutions) = &self.monomorphization_ctx.substitution_ctx.clone() {
                                    base_type = self.substitute_type(&base_type, substitutions);
                                }
    
                                base_type.args.clone()
                            } else {
                                return None;
                            };
    
                            let mangled_name = self.mangle_name(fn_type.symbol, &concrete_types_for_mangling);
                            let parent_scope_id = self.analyzer.symbol_table.get_scope(fn_value_symbol.scope_id)?.id;
                            let monomorphized_fn_value_symbol = self.analyzer.symbol_table.find_value_symbol_from_scope(parent_scope_id, &mangled_name)?.clone();
                            let fn_type = monomorphized_fn_value_symbol.type_id?;
                            Some((mangled_name, monomorphized_fn_value_symbol.id, fn_type))
                        })()
                        .unwrap_or_else(|| {
                            let name = self.analyzer.symbol_table.get_value_name(fn_value_symbol.name_id).to_string();
                            (name, fn_value_symbol.id, fn_type.clone())
                        })
                    } else {
                        let name = self.analyzer.symbol_table.get_value_name(fn_value_symbol.name_id).to_string();
                        (name, fn_value_symbol.id, fn_type.clone())
                    };
                    
                    if let Some(substitutions) = &self.monomorphization_ctx.substitution_ctx.clone()
                        && let AstNodeKind::FieldAccess { left, .. } = &function.kind
                        && let AstNodeKind::PathQualifier { ty: generic_ty_node, tr: trait_ty_node, .. } = &left.kind
                        && trait_ty_node.is_some()
                    {
                        let generic_base_type = generic_ty_node.type_id.as_ref().unwrap();
                        let concrete_base_type = self.substitute_type(generic_base_type, substitutions);

                        if self.type_is_fully_concrete(&concrete_base_type) {
                            let trait_type = trait_ty_node.as_ref().unwrap().type_id.as_ref().unwrap();
                            let trait_id = trait_type.symbol;
                            let concrete_type_id = concrete_base_type.symbol;

                            let fn_symbol = self.analyzer.symbol_table.get_value_symbol(function.value_id.unwrap()).unwrap();
                            let method_name = self.analyzer.symbol_table.get_value_name(fn_symbol.name_id);
                            let impl_scope = self.analyzer.symbol_table.get_scope(fn_symbol.scope_id).unwrap();
                            
                            let clone_trait_id = *self.analyzer.trait_registry.default_traits.get("Clone").unwrap();
                            let TypeSymbolKind::Trait(clone_scope_id) = self.analyzer.symbol_table.get_type_symbol(clone_trait_id).unwrap().kind else { unreachable!(); };
                            let is_clone = if let Some(trait_id) = impl_scope.trait_id { trait_id == clone_trait_id } else { impl_scope.id == clone_scope_id };

                            if is_clone && self.analyzer.is_copy_type(&concrete_base_type) {
                                let clone_arg = arguments.get_mut(0).unwrap();
                                return self.lower_node(clone_arg);
                            } else if let Some(impls_for_trait) = self.analyzer.trait_registry.register.get(&trait_id)
                                && let Some(impls_for_type) = impls_for_trait.get(&concrete_type_id)
                                && let Some(imp) = impls_for_type.iter().find(|imp| self.check_trait_impl_applicability_mir(&concrete_base_type, imp))
                                && let Some(concrete_fn_symbol) = self.analyzer.symbol_table.find_value_symbol_in_scope(method_name, imp.impl_scope_id)
                            {
                                mir_fn_name = self.analyzer.symbol_table.get_value_name(concrete_fn_symbol.name_id).to_string();
                                mir_fn_value_id = concrete_fn_symbol.id;
                                mir_fn_type = concrete_fn_symbol.type_id.as_ref().unwrap().clone();
                            }
                        }
                    }

                    let mir_function_expr = if is_instance_method_call {
                        let AstNodeKind::FieldAccess { left, .. } = &mut function.kind else { unreachable!(); };

                        let instance_mir = self.lower_node(left).unwrap();                        
                        mir_arguments.insert(0, instance_mir);

                        MIRNode {
                            kind: MIRNodeKind::Identifier(mir_fn_name),
                            span: function.span,
                            value_id: Some(mir_fn_value_id),
                            type_id: Some(mir_fn_type),
                            scope_id: node.scope_id.unwrap()
                        }
                    } else {
                        MIRNode {
                            kind: MIRNodeKind::Identifier(mir_fn_name),
                            span: function.span,
                            value_id: Some(mir_fn_value_id),
                            type_id: Some(mir_fn_type),
                            scope_id: node.scope_id.unwrap()
                        }
                    };

                    MIRNodeKind::FunctionCall {
                        function: Box::new(mir_function_expr),
                        arguments: mir_arguments,
                    }
                } else {
                    let mir_function_expr = self.lower_node(function)?;
                    let mir_arguments = arguments.iter_mut().filter_map(|a| self.lower_node(a)).collect();
                    
                    MIRNodeKind::FunctionCall {
                        function: Box::new(mir_function_expr),
                        arguments: mir_arguments,
                    }
                }
            },
            AstNodeKind::SizeofExpression(ty_node) => {
                let generic_ty = ty_node.type_id.as_ref().unwrap();

                let concrete_ty = if let Some(substitutions) = &self.monomorphization_ctx.substitution_ctx.clone() {
                    self.substitute_type(generic_ty, substitutions)
                } else {
                    generic_ty.clone()
                };

                let fully_concrete_ty = self.resolve_concrete_type_recursively(&concrete_ty);

                if !self.type_is_fully_concrete(&fully_concrete_ty) {
                    panic!("This shouldn't happen. [2]");
                }

                MIRNodeKind::SizeofExpression(fully_concrete_ty)
            },
            AstNodeKind::FieldAccess { left, right } => {
                let is_static_access = match &left.kind {
                    AstNodeKind::PathQualifier { .. } => true,
                    AstNodeKind::Identifier(name) => self.analyzer.symbol_table
                        .find_type_symbol_from_scope(left.scope_id.unwrap(), name)
                        .is_some(),
                    _ => false,
                };

                if is_static_access {
                    let resolved_symbol = self.analyzer.symbol_table.get_value_symbol(node.value_id.unwrap()).unwrap();
                    let resolved_name = self.analyzer.symbol_table.get_value_name(resolved_symbol.name_id);
                    MIRNodeKind::Identifier(resolved_name.to_string())
                } else {
                    MIRNodeKind::FieldAccess {
                        left: Box::new(self.lower_node(left)?),
                        right: Box::new(self.lower_node(right)?),
                    }
                }
            },

            AstNodeKind::StructDeclaration { name, fields, generic_parameters } => {
                if let Some(substitutions) = &self.monomorphization_ctx.substitution_ctx.clone() {
                    let template_symbol = self.analyzer.symbol_table.find_type_symbol_in_scope(name, node.scope_id.unwrap()).unwrap().clone();
                    let declaration_scope_id = template_symbol.scope_id;

                    let mangled_name = self.mangle_name(template_symbol.id, substitutions.values());
                    
                    if self.analyzer.symbol_table.find_type_symbol_from_scope(declaration_scope_id, &mangled_name).is_some() {
                        return None;
                    }

                    let original_scope = self.analyzer.symbol_table.current_scope_id;
                    self.analyzer.symbol_table.current_scope_id = declaration_scope_id;
                    let new_scope_id = self.analyzer.symbol_table.enter_scope(ScopeKind::Struct);

                    let ir_fields = fields.iter_mut()
                        .map(|field| self.lower_node(field).unwrap())
                        .collect();

                    self.analyzer.symbol_table.exit_scope();
                    
                    let new_type_symbol_id = self.analyzer.symbol_table.add_type_symbol(
                        &mangled_name,
                        TypeSymbolKind::Struct((new_scope_id, vec![])),
                        vec![],
                        template_symbol.qualifier,
                        Some(node.span),
                    ).unwrap();

                    self.analyzer.symbol_table.registry.struct_template_map.insert(new_type_symbol_id, (template_symbol.id, substitutions.clone()));
                    self.analyzer.symbol_table.current_scope_id = original_scope;

                    let mir_node = MIRNode {
                        kind: MIRNodeKind::StructDeclaration { name: mangled_name, fields: ir_fields },
                        span: node.span,
                        value_id: node.value_id,
                        type_id: Some(Type::from_no_args(new_type_symbol_id)),
                        scope_id: node.scope_id.unwrap()
                    };

                    self.hoisted_declarations.push(mir_node);
                    return None;
                } else if generic_parameters.is_empty() {
                    let mir_node = MIRNode {
                        kind: MIRNodeKind::StructDeclaration {
                            name: name.clone(),
                            fields: fields.iter_mut().filter_map(|f| self.lower_node(f)).collect(),
                        },
                        span: node.span,
                        value_id: node.value_id,
                        type_id: node.type_id.clone(),
                        scope_id: node.scope_id.unwrap()
                    };

                    self.hoisted_declarations.push(mir_node);
                    return None;
                } else {
                    return None;
                }
            },
            AstNodeKind::StructField { name, qualifier, .. } => {
                let kind = MIRNodeKind::StructField { name: name.clone() };

                if let Some(substitutions) = &self.monomorphization_ctx.substitution_ctx.clone() {
                    let generic_field_type = self.analyzer.symbol_table
                        .find_value_symbol_in_scope(name, node.scope_id.unwrap())
                        .unwrap()
                        .type_id
                        .as_ref()
                        .unwrap()
                        .clone();

                    let concrete_field_type = self.substitute_type(&generic_field_type, substitutions);

                    let new_value_symbol_id = self.analyzer.symbol_table.add_value_symbol(
                        name,
                        ValueSymbolKind::StructField,
                        false,
                        *qualifier,
                        Some(concrete_field_type.clone()),
                        Some(node.span),
                    ).unwrap();

                    return Some(MIRNode {
                        kind,
                        span: node.span,
                        value_id: Some(new_value_symbol_id),
                        type_id: Some(concrete_field_type.clone()),
                        scope_id: node.scope_id.unwrap()
                    });
                } else {
                    kind
                }
            },
            AstNodeKind::StructLiteral { name, fields, generic_arguments } => {
                if !generic_arguments.is_empty() {
                    let generic_type_symbol_id = self.analyzer.symbol_table.find_type_symbol_from_scope(
                        node.scope_id.unwrap(),
                        name
                    ).unwrap().id;

                    let mangled_name = self.mangle_name(generic_type_symbol_id, generic_arguments);

                    let concrete_type_symbol_id = self.analyzer.symbol_table.find_type_symbol_from_scope(
                        node.scope_id.unwrap(),
                        &mangled_name
                    ).unwrap().id;

                    return Some(MIRNode {
                        span: node.span,
                        value_id: None,
                        type_id: Some(Type::from_no_args(concrete_type_symbol_id)),
                        scope_id: node.scope_id.unwrap(),
                        kind: MIRNodeKind::StructLiteral {
                            name: mangled_name,
                            fields: fields
                                .iter_mut()
                                .map(|(k, v)| (k.clone(), self.lower_node(v).unwrap()))
                                .collect()
                        },
                    });
                } else {
                    MIRNodeKind::StructLiteral {
                        name: name.clone(),
                        fields: fields
                            .iter_mut()
                            .map(|(k, v)| (k.clone(), self.lower_node(v).unwrap()))
                            .collect()
                    }
                }
            },

            AstNodeKind::EnumDeclaration { name, variants } => {
                let mir_node = MIRNode {
                    kind: MIRNodeKind::EnumDeclaration {
                        name: name.clone(),
                        variants: variants
                            .iter_mut()
                            .map(|(k, (v, e))| {
                                (
                                    k.clone(),
                                    (self.lower_node(v).unwrap(), *e),
                                )
                            })
                            .collect(),
                    },
                    span: node.span,
                    value_id: node.value_id,
                    type_id: node.type_id.clone(),
                    scope_id: node.scope_id.unwrap()
                };
                self.hoisted_declarations.push(mir_node);
                return None;
            },
            AstNodeKind::EnumVariant(name) => MIRNodeKind::EnumVariant(name.clone()),

            AstNodeKind::Program(stmts) => {
                let mut ir_nodes = vec![];

                for stmt in stmts.iter_mut() {
                    if let AstNodeKind::ImplDeclaration { associated_functions, associated_constants, generic_parameters, .. } = &mut stmt.kind {
                        for konst in associated_constants {
                            if let Some(ir_const) = self.lower_node(konst) {
                                ir_nodes.push(ir_const);
                            }
                        }
                    
                        if generic_parameters.is_empty() {
                            for func in associated_functions {
                                if let Some(ir_func) = self.lower_node(func) {
                                    ir_nodes.push(ir_func);
                                }
                            }
                        }
                    }
                }

                for stmt in stmts.iter_mut() {
                    if !matches!(stmt.kind, AstNodeKind::ImplDeclaration { .. }) && let Some(ir_node) = self.lower_node(stmt) {
                        ir_nodes.push(ir_node);
                    }
                }

                MIRNodeKind::Program(ir_nodes)
            },
            
            AstNodeKind::CompilerDirective { directive, nodes } => {
                let rich_directive = match directive { 
                    DirectiveKind::IsRefcounted => {
                        let generic_ty = nodes[0].type_id.as_ref().unwrap();

                        let concrete_ty = if let Some(substitutions) = &self.monomorphization_ctx.substitution_ctx.clone() {
                            self.substitute_type(generic_ty, substitutions)
                        } else {
                            generic_ty.clone()
                        };

                        let fully_concrete_ty = self.resolve_concrete_type_recursively(&concrete_ty);
                        if !self.type_is_fully_concrete(&fully_concrete_ty) {
                            panic!("MIR Builder: Type for #IS_REFCOUNTED# is not fully concrete: {}", self.analyzer.symbol_table.display_type(&fully_concrete_ty));
                        }
                        
                        MIRDirectiveKind::IsRefcounted(fully_concrete_ty)
                    }
                };

                MIRNodeKind::CompilerDirective(rich_directive)
            },

            AstNodeKind::ImplDeclaration { .. }
            | AstNodeKind::TraitDeclaration { .. }
            | AstNodeKind::TypeDeclaration { .. }
            | AstNodeKind::AssociatedType { .. }
            | AstNodeKind::TraitConstant { .. }
            | AstNodeKind::TraitType(_)
            | AstNodeKind::PathQualifier { .. }
            | AstNodeKind::TypeReference { .. }
            | AstNodeKind::FunctionPointer { .. }
            | AstNodeKind::SelfType
            | AstNodeKind::GenericParameter { .. } 
            | AstNodeKind::ImportStatement { .. }
            | AstNodeKind::ExportStatement { .. } => return None,
        };

        Some(MIRNode {
            kind,
            span: node.span,
            value_id: node.value_id,
            type_id: node.type_id.clone(),
            scope_id: node.scope_id.unwrap()
        })
    }
}

impl<'a> MIRBuilder<'a> {
    fn find_concrete_associated_type(&mut self, ty: &Type, tr: &Type, member_name: &str) -> Option<Type> {
        let type_id = ty.symbol;
        let trait_id = tr.symbol;
        
        let impls_for_trait = self.analyzer.trait_registry.register.get(&trait_id)?;
        let impls_for_type = impls_for_trait.get(&type_id)?;

        for imp in impls_for_type {
            let mut substitutions: BTreeMap<TypeSymbolId, Type> = BTreeMap::new();
            
            let instance_args = &ty.args;
            if instance_args.len() != imp.type_specialization.len() { continue; }
            let mut valid_impl = true;
            for (instance_arg, &impl_spec_id) in instance_args.iter().zip(&imp.type_specialization) {
                if imp.impl_generic_params.contains(&impl_spec_id) {
                    substitutions.insert(impl_spec_id, instance_arg.clone());
                } else if instance_arg.symbol != impl_spec_id { 
                    valid_impl = false;
                    break;
                }
            }

            if !valid_impl { continue; }
            
            let trait_args = &tr.args;
            if trait_args.len() != imp.trait_generic_specialization.len() { continue; }
            for (trait_arg, &impl_spec_id) in trait_args.iter().zip(&imp.trait_generic_specialization) {
                if imp.impl_generic_params.contains(&impl_spec_id) {
                    if let Some(existing) = substitutions.get(&impl_spec_id) {
                        if existing != trait_arg { valid_impl = false; break; }
                    } else {
                        substitutions.insert(impl_spec_id, trait_arg.clone());
                    }
                } else if trait_arg.symbol != impl_spec_id {
                    valid_impl = false;
                    break;
                }
            }

            if !valid_impl { continue; }
            
            let assoc_type_symbol = self.analyzer.symbol_table.find_type_symbol_in_scope(member_name, imp.impl_scope_id)?.clone();
            let TypeSymbolKind::TypeAlias((_, Some(aliased_type_template))) = &assoc_type_symbol.kind else { return None; };
            
            let concrete_associated_type = self.substitute_type(aliased_type_template, &substitutions);
            return Some(self.resolve_concrete_type_recursively(&concrete_associated_type));
        }
        None
    }

    fn resolve_concrete_type_recursively(&mut self, ty: &Type) -> Type {
        let type_symbol = self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap();
        if let TypeSymbolKind::OpaqueTypeProjection { ty: opaque_ty, tr, member } = &type_symbol.kind.clone()
            && let Some(resolved_type) = self.find_concrete_associated_type(opaque_ty, tr, member)
        {
            return self.resolve_concrete_type_recursively(&resolved_type);
        }

        let new_args: Vec<_> = ty.args.iter().map(|a| self.resolve_concrete_type_recursively(a)).collect();
        
        let type_symbol = self.analyzer.symbol_table.get_type_symbol(ty.symbol).unwrap();
        if !type_symbol.generic_parameters.is_empty() && !new_args.is_empty()
            && new_args.iter().all(|a| self.type_is_fully_concrete(a))
        {
            let mangled_name = self.mangle_name(ty.symbol, &new_args);
            let decl_scope_id = self.analyzer.symbol_table.get_scope(type_symbol.scope_id).unwrap().id;
            
            if let Some(concrete_symbol) = self.analyzer.symbol_table.find_type_symbol_from_scope(decl_scope_id, &mangled_name) {
                return Type::from_no_args(concrete_symbol.id);
            }
        }
        
        Type { symbol: ty.symbol, args: new_args }
    }

    fn concretize_node(&mut self, node: &mut MIRNode) {
        let mut old_subs = None;
        let mut old_remap = HashMap::new();
        let mut is_new_context = false;

        if let MIRNodeKind::Function { .. } = &node.kind
            && let Some(fn_id) = node.value_id
            && let Some((_, subs)) = self.fn_template_map.get(&fn_id)
        {
            is_new_context = true;
            old_subs = self.concretize_substitutions.replace(subs.clone());
            
            if let Some(param_map) = self.fn_param_remaps.get(&fn_id) {
                old_remap = std::mem::replace(&mut self.concretize_value_remap, param_map.clone());
            }
        }

        for child in node.children_mut() {
            self.concretize_node(child);
        }
        
        if let Some(ty) = &mut node.type_id {
            let mut resolved_ty = ty.clone();
            if let Some(subs) = &self.concretize_substitutions.clone() {
                resolved_ty = self.substitute_type(&resolved_ty, subs);
            }
            *ty = self.resolve_concrete_type_recursively(&resolved_ty);
        }

        if let Some(subs) = &self.concretize_substitutions.clone() {
            if let Some(ty) = &mut node.type_id {
                let substituted = self.substitute_type(ty, subs);
                *ty = self.resolve_concrete_type_recursively(&substituted);
            }

            if let Some(val_id) = &mut node.value_id && let Some(remapped_id) = self.concretize_value_remap.get(val_id) {
                *val_id = *remapped_id;
            }
        }
        
        if let MIRNodeKind::FieldAccess { left, .. } = &mut node.kind {
            let base_ty = left.type_id.as_ref().unwrap();

            let generic_member_symbol = self.analyzer.symbol_table.get_value_symbol(node.value_id.unwrap()).unwrap();
            let generic_member_scope = self.analyzer.symbol_table.get_scope(generic_member_symbol.scope_id).unwrap();

            if generic_member_scope.kind == ScopeKind::Struct {
                let concrete_base_symbol = self.analyzer.symbol_table.get_type_symbol(base_ty.symbol).unwrap();
                if let TypeSymbolKind::Struct((concrete_scope_id, _)) = concrete_base_symbol.kind {
                    let field_name = self.analyzer.symbol_table.get_value_name(generic_member_symbol.name_id);
                    if let Some(concrete_field_symbol) = self.analyzer.symbol_table.find_value_symbol_in_scope(field_name, concrete_scope_id) {
                        node.value_id = Some(concrete_field_symbol.id);
                        node.type_id = concrete_field_symbol.type_id.clone();
                    }
                }
            } else {
                let concrete_member_type = node.type_id.as_ref().unwrap();

                let concrete_member_type_symbol = self.analyzer.symbol_table.get_type_symbol(concrete_member_type.symbol).unwrap();
                let concrete_member_name = self.analyzer.symbol_table.get_type_name(concrete_member_type_symbol.name_id);
                
                let mut search_scope = generic_member_scope;
                while search_scope.kind != ScopeKind::Impl {
                    search_scope = self.analyzer.symbol_table.get_scope(search_scope.parent.unwrap()).unwrap();
                }

                let parent_of_impl_scope_id = self.analyzer.symbol_table.get_scope(search_scope.id).unwrap().parent.unwrap();
                
                if let Some(concrete_member_value_symbol) = self.analyzer.symbol_table.find_value_symbol_from_scope(parent_of_impl_scope_id, concrete_member_name) {
                    node.value_id = Some(concrete_member_value_symbol.id);
                }
            }
        }

        if is_new_context {
            self.concretize_substitutions = old_subs;
            self.concretize_value_remap = old_remap;
        }
    }

    fn concretize_ids(&mut self, program: &mut MIRNode) {
        let MIRNodeKind::Program(stmts) = &mut program.kind else { unreachable!(); };
        for stmt in stmts.iter_mut() {
            self.concretize_node(stmt);
        }
    }

    fn concretize_symbol_table(&mut self) {
        let value_ids: Vec<ValueSymbolId> = self.analyzer.symbol_table.registry.value_symbols.keys().cloned().collect();

        for id in value_ids {
            let ty_to_resolve = self.analyzer.symbol_table.registry.value_symbols.get_mut(&id).unwrap().type_id.take();
            if let Some(ty) = ty_to_resolve {
                let resolved_ty = self.resolve_concrete_type_recursively(&ty);
                if let Some(symbol) = self.analyzer.symbol_table.registry.value_symbols.get_mut(&id) {
                    symbol.type_id = Some(resolved_ty);
                }
            }
        }

        let type_symbol_ids: Vec<TypeSymbolId> = self.analyzer.symbol_table.registry.type_symbols.keys().cloned().collect();

        for id in type_symbol_ids {
            let mut symbol_clone = self.analyzer.symbol_table.registry.type_symbols[&id].clone();
            let mut was_changed = false;

            let new_generics: Vec<TypeSymbolId> = symbol_clone.generic_parameters.iter()
                .map(|&p_id| self.resolve_concrete_type_recursively(&Type::from_no_args(p_id)).symbol)
                .collect();
            
            if symbol_clone.generic_parameters != new_generics {
                symbol_clone.generic_parameters = new_generics;
                was_changed = true;
            }

            match &mut symbol_clone.kind {
                TypeSymbolKind::FunctionSignature { params, return_type, .. } => {
                    let new_params: Vec<Type> = params.iter()
                        .map(|p| self.resolve_concrete_type_recursively(p))
                        .collect();
                    let new_return = self.resolve_concrete_type_recursively(return_type);

                    if *params != new_params || *return_type != new_return {
                        *params = new_params;
                        *return_type = new_return;
                        was_changed = true;
                    }
                }

                TypeSymbolKind::TypeAlias((_, Some(alias_ty))) => {
                    let new_alias = self.resolve_concrete_type_recursively(alias_ty);

                    if *alias_ty != new_alias {
                        *alias_ty = new_alias;
                        was_changed = true;
                    }
                }

                TypeSymbolKind::OpaqueTypeProjection { ty, tr, .. } => {
                    let new_ty = self.resolve_concrete_type_recursively(ty);
                    if *ty != new_ty {
                        *ty = new_ty;
                        was_changed = true;
                    }

                    let new_tr = self.resolve_concrete_type_recursively(tr);
                    if *tr != new_tr {
                        *tr = new_tr;
                        was_changed = true;
                    }
                }

                _ => {}
            }

            if was_changed && let Some(symbol) = self.analyzer.symbol_table.registry.type_symbols.get_mut(&id) {
                *symbol = symbol_clone;
            }
        }
    }
}

impl<'a> MIRBuilder<'a> {
    pub fn build(&mut self, program: &mut AstNode) -> MIRNode {
        self.discover_monomorphic_sites(program);
        self.propagate_monomorphizations(program);
        let mut mir_program = self.monomorphize(program);

        let mir_program_from_ast = self.lower_node(program).unwrap();
        let other_stmts = if let MIRNodeKind::Program(stmts) = mir_program_from_ast.kind { stmts } else { unreachable!(); };
        
        let mut final_stmts = std::mem::take(&mut self.hoisted_declarations);
        if let MIRNodeKind::Program(monomorphized_stmts) = &mut mir_program.kind {
            final_stmts.append(monomorphized_stmts);
        }
        final_stmts.extend(other_stmts);
        final_stmts.extend(std::mem::take(&mut self.hoisted_iifes));
        
        if let MIRNodeKind::Program(stmts_ref) = &mut mir_program.kind {
            *stmts_ref = final_stmts;
        }

        self.concretize_ids(&mut mir_program);
        self.concretize_symbol_table();

        mir_program
    }
}

impl std::fmt::Display for MIRBuilder<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "\n{}", "Monomorphization Sites:".bold().underline())?;
        if self.monomorphization_ctx.instantiations.is_empty() {
            return writeln!(f, "  {}", "(no monomorphization sites found)".dimmed());
        }

        let mut keys: Vec<_> = self.monomorphization_ctx.instantiations.keys().cloned().collect();
        keys.sort();

        for symbol_id in keys {
            let instantiations = &self.monomorphization_ctx.instantiations[&symbol_id];
            let symbol = self.analyzer.symbol_table.get_type_symbol(symbol_id).unwrap();
            let name = self.analyzer.symbol_table.get_type_name(symbol.name_id);
            
            let generic_params_str = symbol.generic_parameters
                .iter()
                .map(|&p_id| {
                    let param_symbol = self.analyzer.symbol_table.get_type_symbol(p_id).unwrap();
                    self.analyzer.symbol_table.get_type_name(param_symbol.name_id).yellow().to_string()
                })
                .collect::<Vec<_>>()
                .join(", ");

            if generic_params_str.is_empty() {
                 writeln!(f, "  {}", name.cyan())?;
            } else {
                 writeln!(f, "  {} <{}>", name.cyan(), generic_params_str)?;
            }
            
            let mut sorted_instantiations: Vec<_> = instantiations.iter().collect();
            sorted_instantiations.sort_by_key(|map| {
                let mut content = map.iter().collect::<Vec<_>>();
                content.sort_by_key(|(k, _)| *k);
                content.iter().map(|(_, t)| self.analyzer.symbol_table.display_type(t)).collect::<String>()
            });

            for instantiation_map in sorted_instantiations {
                write!(f, "    - ")?;
                if instantiation_map.is_empty() {
                    writeln!(f, "{}", "<>".dimmed())?;
                } else {
                    let mut items: Vec<_> = instantiation_map.iter().collect();
                    items.sort_by_key(|(k, _)| *k);

                    let args_str = items
                        .iter()
                        .map(|(gid, ty)| {
                            let g_sym = self.analyzer.symbol_table.get_type_symbol(**gid).unwrap();
                            let g_name = self.analyzer.symbol_table.get_type_name(g_sym.name_id);
                            format!("{}: {}", g_name.yellow(), self.analyzer.symbol_table.display_type(ty).bright_blue())
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    writeln!(f, "<{}>", args_str)?;
                }
            }
        }

        Ok(())
    }
}