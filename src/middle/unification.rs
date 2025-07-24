use std::collections::{HashMap, HashSet};

use crate::{
    frontend::ast::{AstNode, AstNodeKind},
    middle::semantic_analyzer::{
        Constraint, ConstraintInfo, InherentImpl, PrimitiveKind, ScopeId, SemanticAnalyzer, TraitImpl, Type, TypeSymbolId, TypeSymbolKind, ValueSymbolKind
    },
    utils::{error::{BoxedError, Error, ErrorKind}, kind::{Operation, QualifierKind, Span}},
};

// https://rustc-dev-guide.rust-lang.org/solve/canonicalization.html
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
enum CanonicalType {
    Concrete(TypeSymbolId),
    Generic(usize),
}

impl SemanticAnalyzer {
    pub fn inherent_impl_deduplication_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];

        if let AstNodeKind::Program(statements) = &mut program.kind {
            for statement in statements {
                errors.append(&mut self.inherent_impl_deduplication_check_node(statement));
            }
        } else {
            unreachable!();
        }

        errors
    }
    
    fn inherent_impl_deduplication_check_node(&mut self, statement: &mut AstNode) -> Vec<Error> {
        match &statement.kind {
            AstNodeKind::StructDeclaration { name, .. } 
                => self.inherent_impl_deduplication_handle_struct(name, statement.scope_id.unwrap()),
            AstNodeKind::EnumDeclaration { name, .. } 
                => self.inherent_impl_deduplication_handle_enum(name, statement.scope_id.unwrap()),
            _ => {
                let mut errors = vec![];

                for node in statement.children_mut() {
                    errors.append(&mut self.inherent_impl_deduplication_check_node(node));
                }

                errors
            }
        }
    }

    fn inherent_impl_deduplication_handle_struct(&mut self, name: &str, scope_id: ScopeId) -> Vec<Error> {
        let symbol = self.symbol_table.find_type_symbol_in_scope(name, scope_id).unwrap();
        let name = self.symbol_table.get_type_name(symbol.name_id).to_string();
        let TypeSymbolKind::Struct((_, inherent_impls)) = &symbol.kind else { unreachable!(); };

        self.inherent_impl_deduplication_find_duplicates(&name, inherent_impls)
    }

    fn inherent_impl_deduplication_handle_enum(&mut self, name: &str, scope_id: ScopeId) -> Vec<Error> {
        let symbol = self.symbol_table.find_type_symbol_in_scope(name, scope_id).unwrap();
        let name = self.symbol_table.get_type_name(symbol.name_id).to_string();
        let TypeSymbolKind::Enum((_, inherent_impls)) = &symbol.kind else { unreachable!(); };

        self.inherent_impl_deduplication_find_duplicates(&name, inherent_impls)
    }

    fn inherent_impl_deduplication_find_duplicates(&self, namespace: &str, inherent_impls: &[InherentImpl]) -> Vec<Error> {
        let mut errors = vec![];
        let mut impls_by_canonical_spec: HashMap<Vec<CanonicalType>, Vec<&InherentImpl>> = HashMap::new();

        for inherent_impl in inherent_impls.iter() {
            let generic_map: HashMap<TypeSymbolId, usize> = inherent_impl.generic_params
                .iter()
                .enumerate()
                .map(|(i, &id)| (id, i))
                .collect();
            
            let canonical_spec: Vec<CanonicalType> = inherent_impl.specialization
                .iter()
                .map(|&spec_id| {
                    if let Some(&generic_index) = generic_map.get(&spec_id) {
                        CanonicalType::Generic(generic_index + 1)
                    } else {
                        CanonicalType::Concrete(spec_id)
                    }
                })
                .collect();
            
            impls_by_canonical_spec.entry(canonical_spec)
                .or_default()
                .push(inherent_impl);
        }

        for (canonical_spec, impls) in impls_by_canonical_spec.iter() {
            let mut symbols: HashMap<String, Vec<Span>> = HashMap::new();

            for inherent_impl in impls.iter() {
                let scope = self.symbol_table.get_scope(inherent_impl.scope_id).unwrap();

                for (&value_name_id, &value_symbol_id) in scope.values.iter() {
                    let value_name = self.symbol_table.get_value_name(value_name_id);
                    let value_span = self.symbol_table.get_value_symbol(value_symbol_id).unwrap().span.unwrap();

                    symbols.entry(value_name.to_string()).or_default().push(value_span);
                }

                for (&type_name_id, &type_symbol_id) in scope.types.iter() {
                    let type_name = self.symbol_table.get_type_name(type_name_id);
                    let type_span = self.symbol_table.get_type_symbol(type_symbol_id).unwrap().span;
                    
                    if let Some(type_span) = type_span {
                        symbols.entry(type_name.to_string()).or_default().push(type_span);
                    }
                }
            }

            let spec_str = canonical_spec.iter().map(|ct| {
                match ct {
                    CanonicalType::Concrete(id) => {
                        let symbol = self.symbol_table.get_type_symbol(*id).unwrap();
                        self.symbol_table.get_type_name(symbol.name_id).to_string()
                    },
                    CanonicalType::Generic(i) => {
                        format!("T{}", i)
                    },
                }
            }).collect::<Vec<_>>().join(", ");
            
            let full_type_name = if spec_str.is_empty() {
                namespace.to_string()
            } else {
                format!("{}<{}>", namespace, spec_str)
            };

            for (name, spans) in symbols.iter() {
                if spans.len() > 1 {
                     errors.push(*self.create_error(
                        ErrorKind::DuplicateSymbolsInInherentImpl(name.to_string(), full_type_name.clone()),
                        spans[0], 
                        &spans[0..spans.len()]
                    ))
                }
            }
        }
        
        errors
    }
}

impl SemanticAnalyzer {
    fn is_uv(&self, symbol_id: TypeSymbolId) -> bool {
        matches!(
            self.symbol_table.get_type_symbol(symbol_id).unwrap().kind,
            TypeSymbolKind::UnificationVariable(_)
        )
    }

    fn is_never(&self, symbol_id: TypeSymbolId) -> bool {
        matches!(
            self.symbol_table.get_type_symbol(symbol_id).unwrap().kind,
            TypeSymbolKind::Primitive(PrimitiveKind::Never)
        )
    }

    fn is_opaque_type_projection(&self, symbol_id: TypeSymbolId) -> bool {
        matches!(
            self.symbol_table.get_type_symbol(symbol_id).unwrap().kind,
            TypeSymbolKind::OpaqueTypeProjection { .. }
        )
    }

    /// Creates a substitution map from an impl's generic parameters to a concrete type's arguments.
    ///
    /// `impl<T, U> for MyStruct<T, U>` on `MyStruct<i32, bool>`
    /// returns a map `{ T -> i32, U -> bool }`.
    fn create_generic_substitution_map(
        &self,
        impl_generic_params: &[TypeSymbolId],
        concrete_args: &[Type],
    ) -> HashMap<TypeSymbolId, Type> {
        impl_generic_params
            .iter()
            .zip(concrete_args.iter())
            .map(|(param_id, concrete_type)| (*param_id, concrete_type.clone()))
            .collect()
    }

    /// Applies a substitution map to a type.
    fn apply_substitution(
        &mut self,
        ty: &Type,
        substitutions: &HashMap<TypeSymbolId, Type>
    ) -> Type {
        match ty {
            Type::Base { symbol: base_symbol_id, args } => {
                if let Some(substituted_type) = substitutions.get(base_symbol_id) {
                    return substituted_type.clone();
                }

                let base_symbol = self.symbol_table.get_type_symbol(*base_symbol_id).unwrap().clone();

                match &base_symbol.kind {
                    TypeSymbolKind::TypeAlias((_, Some(aliased_type))) => {
                        let alias_generic_params = &base_symbol.generic_parameters;
                        let concrete_alias_args = args;

                        let mut local_substitutions = self.create_generic_substitution_map(
                            alias_generic_params,
                            concrete_alias_args
                        );

                        for (key, value) in substitutions {
                            local_substitutions.entry(*key).or_insert_with(|| value.clone());
                        }

                        self.apply_substitution(aliased_type, &local_substitutions)
                    },
                    TypeSymbolKind::FunctionSignature { params, return_type, instance } => {
                        let substituted_params = params
                            .iter()
                            .map(|p| self.apply_substitution(p, substitutions))
                            .collect();

                        let substituted_return_type = self.apply_substitution(return_type, substitutions);

                        let relevant_substitutions: HashMap<_, _> = substitutions
                            .iter()
                            .filter(|(k, _)| base_symbol.generic_parameters.contains(k))
                            .collect();

                        let mut sorted_subs: Vec<_> = relevant_substitutions.iter().collect();
                        sorted_subs.sort_by_key(|(k, _)| **k);
                        
                        let specialization_key = sorted_subs
                            .iter()
                            .map(|(k, v)| format!("{}-{}", k, v))
                            .collect::<Vec<_>>()
                            .join("_");
                        
                        let signature_name = format!("#fn_sig_specialized_{}_{}", base_symbol.id, specialization_key);
                        
                        let specialized_sig_id = if let Some(symbol) =
                            self.symbol_table.find_type_symbol_in_scope(&signature_name, base_symbol.scope_id)
                        {
                            symbol.id
                        } else {
                            self.symbol_table.add_type_symbol(
                                &signature_name,
                                TypeSymbolKind::FunctionSignature {
                                    params: substituted_params,
                                    return_type: substituted_return_type,
                                    instance: *instance,
                                },
                                vec![],
                                QualifierKind::Private,
                                None
                            ).unwrap()
                        };
                        
                        Type::new_base(specialized_sig_id)
                    },
                    _ => {
                        let substituted_args = args
                            .iter()
                            .map(|arg| self.apply_substitution(arg, substitutions))
                            .collect();

                        Type::Base {
                            symbol: *base_symbol_id,
                            args: substituted_args,
                        }
                    }
                }
            },
            Type::Reference(inner) => {
                Type::Reference(Box::new(self.apply_substitution(inner, substitutions)))
            },
            Type::MutableReference(inner) => {
                Type::MutableReference(Box::new(self.apply_substitution(inner, substitutions)))
            }
        }
    }

    /// Recursively resolves a type by applying substitutions for unification variables
    /// and expanding type aliases until a concrete type or a unification variable is reached.
    fn resolve_type(&mut self, ty: &Type) -> Type {
        let uc_substitutions = self.unification_context.substitutions.clone();
        let mut current_ty = self.apply_substitution(ty, &uc_substitutions);

        loop {
            let Type::Base { symbol, args } = &current_ty else { break; };

            if self.is_uv(*symbol) {
                break;
            }

            let type_symbol = self.symbol_table.get_type_symbol(*symbol).unwrap().clone();

            if let TypeSymbolKind::TypeAlias((_, Some(aliased_type))) = &type_symbol.kind {
                let substitutions = self.create_generic_substitution_map(
                    &type_symbol.generic_parameters,
                    args
                );

                let substituted_alias = self.apply_substitution(aliased_type, &substitutions);
                current_ty = self.apply_substitution(&substituted_alias, &uc_substitutions);
            } else {
                break;
            }
        }

        current_ty
    }

    /// Checks if a unification variable `uv_id` occurs within a type `ty`.
    /// https://en.wikipedia.org/wiki/Occurs_check
    fn occurs_check(&mut self, uv_id: TypeSymbolId, ty: &Type) -> bool {
        let resolved_ty = self.resolve_type(ty);

        match &resolved_ty {
            Type::Base { symbol, args } => {
                if *symbol == uv_id {
                    return true;
                }
                // No need to check substitutions here because resolve_type already did it.
                args.iter().any(|arg| self.occurs_check(uv_id, arg))
            }
            Type::Reference(inner) | Type::MutableReference(inner) => self.occurs_check(uv_id, inner),
        }
    }

    /// Unifies a metavariable with a type.
    fn unify_variable(
        &mut self,
        uv_id: TypeSymbolId,
        ty: Type,
        info: ConstraintInfo,
    ) -> Result<Type, BoxedError> {
        if self.occurs_check(uv_id, &ty) {
            return Err(self.type_mismatch_error(
                &Type::new_base(uv_id),
                &ty,
                info,
                Some("infinite type detected: a metavariable occurs within its own definition".to_string()),
            ));
        }

        self.unification_context.substitutions.insert(uv_id, ty.clone());
        Ok(ty)
    }

    /// Generates a mismatch error between types `t1` and `t2`.
    fn type_mismatch_error(
        &self,
        t1: &Type,
        t2: &Type,
        info: ConstraintInfo,
        specifics: Option<String>,
    ) -> BoxedError {
        self.create_error(
            ErrorKind::TypeMismatch(
                self.symbol_table.display_type(t1),
                self.symbol_table.display_type(t2),
                specifics,
            ),
            info.span,
            &[info.span],
        )
    }

    /// Checks if an `impl` block is applicable to a given concrete instance type.
    ///
    /// If it is applicable, it returns a substitution map for the `impl`'s generic
    /// parameters. If not, it returns `None`.
    fn check_impl_applicability(
        &mut self,
        instance_type: &Type,
        imp: &InherentImpl,
    ) -> Option<HashMap<TypeSymbolId, Type>> {
        let instance_args = if let Type::Base { args, .. } = instance_type {
            args
        } else {
            return None; // instance type is not a base type
        };

        let impl_target_arg_ids = &imp.specialization;

        if instance_args.len() != impl_target_arg_ids.len() {
            return None; // arity mismatch
        }

        let mut substitutions = HashMap::new();

        for (instance_arg, &impl_target_arg_id) in instance_args.iter().zip(impl_target_arg_ids) {
            let target_symbol = self.symbol_table.get_type_symbol(impl_target_arg_id).unwrap();

            if imp.generic_params.contains(&target_symbol.id) {
                substitutions.insert(target_symbol.id, instance_arg.clone());
            } else {
                let resolved_instance_arg = self.resolve_type(instance_arg);
                let resolved_impl_arg = self.resolve_type(&Type::new_base(impl_target_arg_id));

                if resolved_instance_arg != resolved_impl_arg {
                    return None;
                }
            }
        }

        Some(substitutions)
    }

    fn check_trait_impl_applicability(
        &mut self,
        instance_type: &Type,
        imp: &TraitImpl,
    ) -> Option<HashMap<TypeSymbolId, Type>> {
        let instance_args = if let Type::Base { args, .. } = instance_type {
            args
        } else {
            return None; // instance type is not a base type
        };

        let impl_target_arg_ids = &imp.type_specialization;

        if instance_args.len() != impl_target_arg_ids.len() {
            return None; // arity mismatch
        }

        let mut substitutions = HashMap::new();

        for (instance_arg, &impl_target_arg_id) in instance_args.iter().zip(impl_target_arg_ids) {
            let target_symbol = self.symbol_table.get_type_symbol(impl_target_arg_id).unwrap();

            if imp.impl_generic_params.contains(&target_symbol.id) {
                substitutions.insert(target_symbol.id, instance_arg.clone());
            } else {
                let resolved_instance_arg = self.resolve_type(instance_arg);
                let resolved_impl_arg = self.resolve_type(&Type::new_base(impl_target_arg_id));

                if resolved_instance_arg != resolved_impl_arg {
                    return None;
                }
            }
        }
        
        Some(substitutions)
    }

    /// Checks if a type implements a trait.
    fn does_type_implement_trait(&mut self, ty: &Type, trait_id: TypeSymbolId) -> Result<bool, BoxedError> {
        let resolved_type = self.resolve_type(ty);
        if self.is_uv(resolved_type.get_base_symbol()) {
            return Ok(false);
        }
    
        let type_id = resolved_type.get_base_symbol();
        let mut impls = vec![];
        
        if let Some(impls_for_trait) = self.trait_registry.register.get(&trait_id) {
            if let Some(impls_for_type) = impls_for_trait.get(&type_id) {
                for imp in impls_for_type {
                    impls.push(imp.clone());
                }
            }
        }

        for imp in impls {
            if self.check_trait_impl_applicability(&resolved_type, &imp).is_some() {
                return Ok(true);
            }
        }
        
        let type_symbol = self.symbol_table.get_type_symbol(type_id).unwrap();
        if let TypeSymbolKind::Generic(constraints) = &type_symbol.kind {
            if constraints.contains(&trait_id) {
                return Ok(true);
            }
        }
        
        Ok(false)
    }

    /// Recursively traverses a type to find all of its constituent generic type variables.
    fn collect_signature_generics(&self, ty: &Type, generics: &mut HashSet<TypeSymbolId>) {
        match ty {
            Type::Base { symbol, args } => {
                let type_symbol = self.symbol_table.get_type_symbol(*symbol).unwrap();
                if let TypeSymbolKind::Generic(_) = type_symbol.kind {
                    generics.insert(*symbol);
                }

                for arg in args {
                    self.collect_signature_generics(arg, generics);
                }
            },
            Type::Reference(inner) | Type::MutableReference(inner) => {
                self.collect_signature_generics(inner, generics);
            }
        }
    }

    /// Recursively traverses a `call_site` type and a `signature` type to infer
    /// the concrete types for a function's generic parameters.
    fn collect_substitutions(
        &mut self,
        concrete_ty: &Type,
        template_ty: &Type,
        substitutions: &mut HashMap<TypeSymbolId, Type>,
        fn_generics: &HashSet<TypeSymbolId>,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let concrete_ty = self.resolve_type(concrete_ty);

        match (concrete_ty.clone(), template_ty.clone()) {
            (_, Type::Base { symbol: s, .. }) if fn_generics.contains(&s) => {
                if let Some(existing_sub) = substitutions.get(&s) {
                    self.unify(existing_sub.clone(), concrete_ty, info)?;
                } else {
                    substitutions.insert(s, concrete_ty);
                }

                Ok(())
            },
            (concrete_ty, Type::Base { symbol: ts, .. }) if self.is_opaque_type_projection(ts) => {
                let opaque_symbol = self.symbol_table.get_type_symbol(ts).unwrap().clone();
                if let TypeSymbolKind::OpaqueTypeProjection { ty: opaque_ty, tr: opaque_tr, member } = opaque_symbol.kind {
                    let substituted_opaque_ty = self.apply_substitution(&opaque_ty, substitutions);

                    if substituted_opaque_ty.contains_generics(fn_generics) {
                        return Ok(());
                    }

                    if let Some(resolved_member_type) = self.find_member_in_trait_impl(&substituted_opaque_ty, &opaque_tr, &member, info)? {
                        self.unify(concrete_ty, resolved_member_type, info)?;
                    } else {
                        return Err(self.create_error(
                            ErrorKind::UnimplementedTrait(
                                self.symbol_table.display_type(&opaque_tr),
                                self.symbol_table.display_type(&substituted_opaque_ty)
                            ),
                            info.span,
                            &[info.span]
                        ));
                    }
                }
                Ok(())
            },
            (Type::Base { symbol: cs, args: ca }, Type::Base { symbol: ts, args: ta}) => {
                if cs != ts || ca.len() != ta.len() {
                    return Ok(());
                }

                for (c_arg, t_arg) in ca.iter().zip(ta.iter()) {
                    self.collect_substitutions(c_arg, t_arg, substitutions, fn_generics, info)?;
                }

                Ok(())
            },
            (Type::Reference(ci), Type::Reference(ti)) => {
                self.collect_substitutions(&ci, &ti, substitutions, fn_generics, info)
            },
            (Type::MutableReference(ci), Type::MutableReference(ti)) => {
                self.collect_substitutions(&ci, &ti, substitutions, fn_generics, info)
            },
            _ => Ok(())
        }
    }
}

impl SemanticAnalyzer {
    /// Finds a member within an `impl` scope, checking if it matches the static/instance access type.
    fn find_member_in_impl_scope(
        &mut self,
        scope_id: ScopeId,
        member_name: &str,
        is_static_access: bool,
    ) -> Result<Option<Type>, BoxedError> {
        if let Some(value_symbol) = self.symbol_table.find_value_symbol_in_scope(member_name, scope_id).cloned() {
            let symbol_type = value_symbol.type_id.as_ref().unwrap().clone();
            
            let is_match = match value_symbol.kind {
                ValueSymbolKind::Function(_) => {
                    let resolved_type = self.resolve_type(&symbol_type);
                    if self.is_uv(resolved_type.get_base_symbol()) { 
                        return Ok(None); 
                    }
    
                    let fn_sig_symbol = self.symbol_table.get_type_symbol(resolved_type.get_base_symbol()).unwrap();
                    if let TypeSymbolKind::FunctionSignature { instance, .. } = fn_sig_symbol.kind {
                        is_static_access == instance.is_none()
                    } else { 
                        false 
                    }
                },
                ValueSymbolKind::Variable => is_static_access,
                _ => false
            };
            
            if is_match {
                return Ok(Some(symbol_type));
            }
        }
        
        if is_static_access {
            if let Some(type_symbol) = self.symbol_table.find_type_symbol_in_scope(member_name, scope_id) {
                return Ok(Some(Type::new_base(type_symbol.id)));
            }
        }
        
        Ok(None)
    }

    /// Finds a member within a set of inherent `impl` blocks for a given type.
    fn find_member_in_inherent_impls(
        &mut self,
        base_type: &Type,
        impls: &[InherentImpl],
        member_name: &str,
        is_static_access: bool,
    ) -> Result<Option<Type>, BoxedError> {
        for imp in impls {
            if let Some(substitutions) = self.check_impl_applicability(base_type, imp) {
                if let Some(member_type) = self.find_member_in_impl_scope(imp.scope_id, member_name, is_static_access)? {
                    let concrete_member_type = self.apply_substitution(&member_type, &substitutions);
                    return Ok(Some(concrete_member_type));
                }
            }
        }

        Ok(None)
    }

    /// Finds a member within all applicable trait `impl` blocks for a given type.
    fn find_member_in_trait_impls(
        &mut self,
        base_type: &Type,
        member_name: &str,
        is_static_access: bool,
    ) -> Result<Option<Type>, BoxedError> {
        let base_symbol_id = base_type.get_base_symbol();
        
        let all_trait_impls: Vec<_> = self.trait_registry.register.values()
            .filter_map(|impls_for_trait| impls_for_trait.get(&base_symbol_id))
            .flatten()
            .cloned().collect();
    
        for trait_impl in all_trait_impls {
            if let Some(substitutions) = self.check_trait_impl_applicability(base_type, &trait_impl) {
                if let Some(member_type) = self.find_member_in_impl_scope(trait_impl.impl_scope_id, member_name, is_static_access)? {
                    let concrete_member_type = self.apply_substitution(&member_type, &substitutions);
                    return Ok(Some(concrete_member_type));
                }
            }
        }

        Ok(None)
    }

    /// Finds a member (field, method, etc.) for a given type.
    fn find_member(
        &mut self,
        base_type: &Type,
        member_name: &str,
        is_static_access: bool,
        info: ConstraintInfo,
    ) -> Result<Option<Type>, BoxedError> {
        let (base_symbol_id, concrete_args) = match base_type {
            Type::Base { symbol, args } => (*symbol, args.clone()),
            _ => return Err(self.create_error(ErrorKind::InvalidFieldAccess(self.symbol_table.display_type(base_type)), info.span, &[info.span])),
        };
    
        if self.is_uv(base_symbol_id) {
            return Ok(None);
        }
    
        let base_symbol = self.symbol_table.get_type_symbol(base_symbol_id).unwrap().clone();
        
        match &base_symbol.kind {
            TypeSymbolKind::Struct((scope_id, impls)) => {
                if !is_static_access {
                    if let Some(field_symbol) = self.symbol_table.find_value_symbol_in_scope(member_name, *scope_id).cloned() {
                        let substitutions = self.create_generic_substitution_map(&base_symbol.generic_parameters, &concrete_args);
                        let concrete_field_type = self.apply_substitution(field_symbol.type_id.as_ref().unwrap(), &substitutions);
                        return Ok(Some(concrete_field_type));
                    }
                }

                if let Some(ty) = self.find_member_in_inherent_impls(base_type, impls, member_name, is_static_access)? {
                    return Ok(Some(ty));
                }
            },
            TypeSymbolKind::Enum((scope_id, impls)) => {
                if is_static_access && self.symbol_table.find_value_symbol_in_scope(member_name, *scope_id).is_some() {
                    return Ok(Some(base_type.clone()));
                }

                if let Some(ty) = self.find_member_in_inherent_impls(base_type, impls, member_name, is_static_access)? {
                    return Ok(Some(ty));
                }
            },
            TypeSymbolKind::Generic(trait_constraints) => {
                for &trait_id in trait_constraints {
                    let trait_symbol = self.symbol_table.get_type_symbol(trait_id).unwrap();
                    let TypeSymbolKind::Trait(trait_scope_id) = trait_symbol.kind else { continue; };
        
                    if let Some(member_in_trait) = self.find_member_in_impl_scope(trait_scope_id, member_name, is_static_access)? {
                        let self_in_trait_id = self.symbol_table.find_type_symbol_in_scope("Self", trait_scope_id).unwrap().id;
                        let substitutions = HashMap::from([(self_in_trait_id, base_type.clone())]);
                        let concrete_member_type = self.apply_substitution(&member_in_trait, &substitutions);
                        
                        return Ok(Some(concrete_member_type));
                    }
                }
            },
            TypeSymbolKind::TraitSelf => {
                if is_static_access {
                    let trait_scope_id = base_symbol.scope_id;
                    if let Some(member_type) = self.find_member_in_impl_scope(trait_scope_id, member_name, true)? {
                        return Ok(Some(member_type));
                    }
                }
            }
            _ => {}
        }
    
        if let Some(ty) = self.find_member_in_trait_impls(base_type, member_name, is_static_access)? {
            return Ok(Some(ty));
        }
    
        Ok(None)
    }
    
    /// Finds a member in a given trait implementation for a given type.
    fn find_member_in_trait_impl(&mut self, ty: &Type, tr: &Type, member_name: &str, info: ConstraintInfo) -> Result<Option<Type>, BoxedError> {
        let type_id = ty.get_base_symbol();
        let trait_id = tr.get_base_symbol();

        if self.is_uv(type_id) || self.is_uv(trait_id) {
            return Ok(None);
        }

        let trait_symbol = self.symbol_table.get_type_symbol(trait_id).unwrap();
        if !matches!(trait_symbol.kind, TypeSymbolKind::Trait(_)) {
            return Err(self.create_error(
                ErrorKind::InvalidConstraint(self.symbol_table.display_type(tr)),
                info.span,
                &[info.span],
            ));
        }

        let all_trait_impls: Vec<_> = self.trait_registry.register.get(&trait_id)
            .and_then(|impls_for_trait| impls_for_trait.get(&type_id))
            .map_or(vec![], |v| v.clone());

        for trait_impl in all_trait_impls {
            if let Some(substitutions) = self.check_trait_impl_applicability(ty, &trait_impl) {
                if let Some(member_type) = self.find_member_in_impl_scope(trait_impl.impl_scope_id, member_name, true)? {
                    let concrete_member_type = self.apply_substitution(&member_type, &substitutions);
                    return Ok(Some(concrete_member_type));
                }
            }
        }
        Ok(None)
    }
}

impl SemanticAnalyzer {
    pub fn unification_pass(&mut self, _program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];
        let mut constraints = std::mem::take(&mut self.unification_context.constraints);

        let mut iterations = 0;
        let limit = constraints.len() * 4 + 100;

        while let Some((constraint, info)) = constraints.pop_front() {
            if iterations > limit {
                // TODO: locate uvs that still have constraints attached
                break;
            }

            iterations += 1;

            match self.process_constraint(constraint.clone(), info) {
                Ok(success) if !success => constraints.push_back((constraint, info)),
                Err(e) => errors.push(*e),
                _ => (),
            }
        }

        errors
    }

    fn process_constraint(&mut self, constraint: Constraint, info: ConstraintInfo) -> Result<bool, BoxedError> {
        match constraint {
            Constraint::Equality(t1, t2) => {
                self.unify(t1, t2, info)?;
                Ok(true)
            },
            Constraint::FunctionSignature(callee_ty, params, return_ty) => {
                self.unify_function_signature(callee_ty, params, return_ty, info)
            },
            Constraint::MethodCall(instance_ty, callee_ty, params, return_ty) => {
                self.unify_method_call(instance_ty, callee_ty, params, return_ty, info)
            },
            Constraint::InstanceMemberAccess(result_ty, lhs_type, rhs_name) => {
                self.unify_member_access(result_ty, lhs_type, rhs_name, false, info)
            },
            Constraint::StaticMemberAccess(result_ty, lhs_type, rhs_name) => {
                self.unify_member_access(result_ty, lhs_type, rhs_name, true, info)
            },
            Constraint::FullyQualifiedAccess(result_ty, ty, tr_opt, member_name) => {
                self.unify_fully_qualified_access(result_ty, ty, tr_opt, member_name, info)
            },
            Constraint::Operation(uv_symbol_id, trait_type, lhs, rhs, operation) => {
                self.unify_operation(uv_symbol_id, trait_type, lhs, rhs, info, operation)
            },
            Constraint::Cast(source, target) => self.unify_cast(source, target, info)
        }
    }

    fn unify(&mut self, t1: Type, t2: Type, info: ConstraintInfo) -> Result<Type, BoxedError> {
        let t1 = self.resolve_type(&t1);
        let t2 = self.resolve_type(&t2);

        match (t1.clone(), t2.clone()) {
            (t1, t2) if t1 == t2 => Ok(t1),

            (Type::Base { symbol: s, .. }, other) | (other, Type::Base { symbol: s, .. }) 
                if self.is_uv(s) => self.unify_variable(s, other, info),
            
            (ref t @ Type::Base { symbol: s, .. }, _) | (_, ref t @ Type::Base { symbol: s, .. })
                if self.is_opaque_type_projection(s) => Ok(t.clone()),

            (Type::Base { symbol: s, .. }, other) | (other, Type::Base { symbol: s, .. })
                if self.is_never(s) => Ok(other.clone()),

            (ref t1 @ Type::Base { symbol: s1, args: ref a1 }, ref t2 @ Type::Base { symbol: s2, args: ref a2 }) => {
                let type_sym_s1 = self.symbol_table.get_type_symbol(s1).unwrap().clone();
                let type_sym_s2 = self.symbol_table.get_type_symbol(s2).unwrap().clone();
                
                if let Some(resultant_symbol) = type_sym_s1.unify(&type_sym_s2) {
                    if a1.len() != a2.len() {
                        return Err(self.type_mismatch_error(t1, t2, info, Some(format!("expected {} generic arguments, but found {}", a1.len(), a2.len()))));
                    }

                    let mut unified_args = vec![];
                    for (arg1, arg2) in a1.iter().zip(a2.iter()) {
                        unified_args.push(self.unify(arg1.clone(), arg2.clone(), info)?);
                    }

                    return Ok(Type::Base {
                        symbol: resultant_symbol,
                        args: unified_args,
                    });
                }

                Err(self.type_mismatch_error(t1, t2, info, None))
            },

            (Type::Reference(inner1), Type::Reference(inner2)) => {
                let unified = self.unify(*inner1, *inner2, info)?;
                Ok(Type::Reference(Box::new(unified)))
            },
            (Type::MutableReference(inner1), Type::MutableReference(inner2)) => {
                let unified = self.unify(*inner1, *inner2, info)?;
                Ok(Type::MutableReference(Box::new(unified)))
            },

            (t1, t2) => Err(self.type_mismatch_error(&t1, &t2, info, None)),
        }
    }

    fn unify_function_signature(
        &mut self,
        callee_ty: Type,
        params: Vec<Type>,
        return_ty: Type,
        info: ConstraintInfo,
    ) -> Result<bool, BoxedError> {
        let callee_ty = self.resolve_type(&callee_ty);

        match callee_ty.clone() {
            Type::Base { symbol, .. } => {
                if self.is_uv(symbol) {
                    return Ok(false);
                }

                let callee_symbol = self.symbol_table.get_type_symbol(symbol).unwrap().clone();

                if let TypeSymbolKind::FunctionSignature {
                    params: sig_params,
                    return_type: sig_return,
                    ..
                } = &callee_symbol.kind
                {
                    if params.len() != sig_params.len() {
                        return Err(self.create_error(
                            ErrorKind::ArityMismatch(sig_params.len(), params.len()),
                            info.span,
                            &[info.span],
                        ));
                    }

                    let mut fn_generic_param_ids = HashSet::new();

                    self.collect_signature_generics(sig_return, &mut fn_generic_param_ids);
                    for p in sig_params {
                        self.collect_signature_generics(p, &mut fn_generic_param_ids);
                    }

                    let mut substitutions = HashMap::new();
                    for (call_arg, sig_param) in params.iter().zip(sig_params.iter()) {
                        self.collect_substitutions(
                            call_arg,
                            sig_param,
                            &mut substitutions,
                            &fn_generic_param_ids,
                            info,
                        )?;
                    }

                    let concrete_sig_params = sig_params.iter().map(|p| self.apply_substitution(p, &substitutions)).collect::<Vec<_>>();
                    let concrete_return = self.apply_substitution(sig_return, &substitutions);

                    for (arg, expected) in params.iter().zip(concrete_sig_params.iter()) {
                        self.unify(arg.clone(), expected.clone(), info)?;
                    }

                    self.unify(return_ty, concrete_return, info)?;

                    Ok(true)
                } else {
                    Err(self.create_error(
                        ErrorKind::NotCallable(self.symbol_table.display_type(&callee_ty)),
                        info.span,
                        &[info.span],
                    ))
                }
            }
            _ => Err(self.create_error(
                ErrorKind::NotCallable(self.symbol_table.display_type(&callee_ty)),
                info.span,
                &[info.span],
            )),
        }
    }

    fn unify_method_call(
        &mut self,
        instance_ty: Type,
        callee_ty: Type,
        params: Vec<Type>,
        return_ty: Type,
        info: ConstraintInfo,
    ) -> Result<bool, BoxedError> {
        let callee_ty = self.resolve_type(&callee_ty);

        let callee_symbol_id = match callee_ty.clone() {
            Type::Base { symbol, .. } => {
                if self.is_uv(symbol) {
                    return Ok(false);
                }
                
                symbol
            }
            _ => {
                return Err(self.create_error(
                    ErrorKind::NotCallable(self.symbol_table.display_type(&callee_ty)),
                    info.span,
                    &[info.span],
                ))
            }
        };

        let callee_symbol = self.symbol_table.get_type_symbol(callee_symbol_id).unwrap().clone();

        if let TypeSymbolKind::FunctionSignature {
            params: expected_params_with_receiver,
            return_type: expected_return,
            instance: Some(_),
        } = callee_symbol.kind.clone()
        {
            if expected_params_with_receiver.is_empty() {
                panic!("This shouldn't happen. [1]");
            }

            let (expected_receiver_ty, expected_params) =
                expected_params_with_receiver.split_first().unwrap();

            if params.len() != expected_params.len() {
                return Err(self.create_error(
                    ErrorKind::ArityMismatch(expected_params.len(), params.len()),
                    info.span,
                    &[info.span],
                ));
            }

            let mut fn_generic_param_ids = HashSet::new();

            self.collect_signature_generics(&expected_return, &mut fn_generic_param_ids);
            for p in &expected_params_with_receiver {
                self.collect_signature_generics(p, &mut fn_generic_param_ids);
            }


            let mut substitutions = HashMap::new();

            self.collect_substitutions(
                &instance_ty,
                expected_receiver_ty,
                &mut substitutions,
                &fn_generic_param_ids,
                info,
            )?;

            for (call_arg, sig_param) in params.iter().zip(expected_params.iter()) {
                self.collect_substitutions(
                    call_arg,
                    sig_param,
                    &mut substitutions,
                    &fn_generic_param_ids,
                    info,
                )?;
            }

            let concrete_receiver = self.apply_substitution(expected_receiver_ty, &substitutions);
            let concrete_params = expected_params.iter().map(|p| self.apply_substitution(p, &substitutions)).collect::<Vec<_>>();
            let concrete_return = self.apply_substitution(&expected_return, &substitutions);

            for (arg, expected) in params.iter().zip(concrete_params.iter()) {
                self.unify(arg.clone(), expected.clone(), info)?;
            }

            if self.unify_receiver(instance_ty, concrete_receiver, info)?.is_none() {
                return Ok(false);
            }

            self.unify(return_ty, concrete_return, info)?;

            Ok(true)
        } else {
            Err(self.create_error(
                ErrorKind::NotCallable(self.symbol_table.display_type(&callee_ty)),
                info.span,
                &[info.span],
            ))
        }
    }

    fn unify_receiver(&mut self, passed: Type, expected: Type, info: ConstraintInfo) -> Result<Option<Type>, BoxedError> {
        let current_passed = self.resolve_type(&passed);
        let resolved_expected = self.resolve_type(&expected);

        if self.is_uv(current_passed.get_base_symbol()) || self.is_uv(resolved_expected.get_base_symbol()) {
            return Ok(None);
        }

        // Direct substitution.
        if let Ok(unified) = self.unify(current_passed.clone(), resolved_expected.clone(), info) {
            return Ok(Some(unified));
        }

        // `&mut T` -> `&T`
        if let (Type::MutableReference(p_inner), Type::Reference(e_inner)) = (current_passed.clone(), resolved_expected.clone()) {
            let unified_inner = self.unify(*p_inner, *e_inner, info)?;
            return Ok(Some(Type::Reference(Box::new(unified_inner))));
        }

        // `&^n T` | `&^n mut T` -> `T`
        let mut deref_passed = current_passed.clone();
        while let Type::Reference(inner) | Type::MutableReference(inner) = deref_passed {
            deref_passed = *inner;
            if let Ok(unified) = self.unify(deref_passed.clone(), resolved_expected.clone(), info) {
                return Ok(Some(unified));
            }
        }
        
        // `T` -> `&^n T` | `&^n mut T`
        if let p @ Type::Base { .. } = current_passed.clone() {
             match resolved_expected.clone() {
                e @ Type::Reference(_) => return self.unify(Type::Reference(Box::new(p)), e, info).map(Some),
                e @ Type::MutableReference(_) => return self.unify(Type::MutableReference(Box::new(p)), e, info).map(Some),
                _ => {}
            }
        }

        Err(self.type_mismatch_error(
            &current_passed,
            &resolved_expected,
            info,
            Some("receiver type mismatch".to_string()),
        ))
    }

    /// Unifies a member access operation (static or instance).
    fn unify_member_access(
        &mut self,
        result_ty: Type,
        lhs_type: Type,
        rhs_name: String,
        is_static: bool,
        info: ConstraintInfo,
    ) -> Result<bool, BoxedError> {
        let resolved_lhs = self.resolve_type(&lhs_type);

        let base_lhs_type = if !is_static {
            match &resolved_lhs {
                Type::Reference(inner) | Type::MutableReference(inner) => (**inner).clone(),
                _ => resolved_lhs.clone(),
            }
        } else {
            resolved_lhs.clone()
        };

        if self.is_uv(base_lhs_type.get_base_symbol()) {
            return Ok(false);
        }

        let member_ty_opt = self.find_member(&base_lhs_type, &rhs_name, is_static, info)?;

        if let Some(member_ty) = member_ty_opt {
            self.unify(result_ty, member_ty, info)?;
            Ok(true)
        } else {
            Err(self.create_error(
                ErrorKind::MemberNotFound(rhs_name, self.symbol_table.display_type(&base_lhs_type)),
                info.span,
                &[info.span],
            ))
        }
    }

    fn unify_fully_qualified_access(
        &mut self,
        result_ty: Type,
        ty: Type,
        tr_opt: Option<Type>,
        member_name: String,
        info: ConstraintInfo,
    ) -> Result<bool, BoxedError> {
        let resolved_ty = self.resolve_type(&ty);
        if self.is_uv(resolved_ty.get_base_symbol()) {
            return Ok(false);
        }

        let member_ty_opt = if let Some(tr) = tr_opt {
            let resolved_tr = self.resolve_type(&tr);
            if self.is_uv(resolved_tr.get_base_symbol()) {
                return Ok(false);
            }

            let ty_symbol = self.symbol_table.get_type_symbol(resolved_ty.get_base_symbol()).unwrap();
            if let TypeSymbolKind::Generic(_) = &ty_symbol.kind {
                let type_name = &format!(
                    "[{} as {}]::{}", 
                    self.symbol_table.display_type(&resolved_ty), 
                    self.symbol_table.display_type(&resolved_tr),
                    member_name
                );

                let symbol = if let Some(ty) = self.symbol_table.find_type_symbol_from_scope(self.symbol_table.get_current_scope_id(), type_name) {
                    ty.id
                } else {
                    self.symbol_table.add_type_symbol(
                        type_name, 
                        TypeSymbolKind::OpaqueTypeProjection {
                            ty: resolved_ty,
                            tr: resolved_tr,
                            member: member_name.clone()
                        }, 
                        vec![],
                        QualifierKind::Private, 
                        Some(info.span)
                    )?
                };

                self.unify(result_ty, Type::new_base(symbol), info)?;
                return Ok(true);
            }

            self.find_member_in_trait_impl(&resolved_ty, &resolved_tr, &member_name, info)?
        } else {
            self.find_member(&resolved_ty, &member_name, true, info)?
        };

        if let Some(member_ty) = member_ty_opt {
            self.unify(result_ty, member_ty, info)?;

            Ok(true)
        } else {
            let type_name = self.symbol_table.display_type(&resolved_ty);
            
            Err(self.create_error(
                ErrorKind::MemberNotFound(member_name, type_name),
                info.span,
                &[info.span],
            ))
        }
    }

    fn unify_operation(
        &mut self,
        result_ty: Type,
        trait_type: Type,
        lhs: Type,
        _rhs: Option<Type>,
        info: ConstraintInfo,
        _operation: Operation,
    ) -> Result<bool, BoxedError> {
        let resolved_lhs = self.resolve_type(&lhs);
        if self.is_uv(resolved_lhs.get_base_symbol()) {
            return Ok(false);
        }

        let (trait_id, trait_args) = match self.resolve_type(&trait_type) {
            Type::Base { symbol, args } => {
                if self.is_uv(symbol) { return Ok(false); }
                let resolved_args = args.iter().map(|a| self.resolve_type(a)).collect::<Vec<_>>();
                for arg in &resolved_args {
                    if self.is_uv(arg.get_base_symbol()) {
                        return Ok(false);
                    }
                }
                (symbol, resolved_args)
            },
            _ => unreachable!("trait type must be a base type for an operation"),
        };

        let lhs_type_id = resolved_lhs.get_base_symbol();
        let candidate_impls = self
            .trait_registry
            .register
            .get(&trait_id)
            .and_then(|impls_for_trait| impls_for_trait.get(&lhs_type_id))
            .cloned()
            .unwrap_or_default();

        let mut found_impl: Option<(TraitImpl, HashMap<TypeSymbolId, Type>)> = None;

        for imp in &candidate_impls {
            let Some(mut substitutions) = self.check_trait_impl_applicability(&resolved_lhs, imp) else {
                continue;
            };

            let impl_trait_template = Type::Base {
                symbol: trait_id,
                args: imp.trait_generic_specialization.iter().map(|id| Type::new_base(*id)).collect(),
            };
            let call_site_trait = Type::Base { symbol: trait_id, args: trait_args.clone() };
            let impl_generics_set: HashSet<TypeSymbolId> = imp.impl_generic_params.iter().cloned().collect();

            if self.collect_substitutions(&call_site_trait, &impl_trait_template, &mut substitutions, &impl_generics_set, info).is_err() {
                continue;
            }

            let substituted_impl_trait = self.apply_substitution(&impl_trait_template, &substitutions);
            if self.unify(call_site_trait.clone(), substituted_impl_trait, info).is_ok() {
                found_impl = Some((imp.clone(), substitutions));
                break;
            }
        }

        if let Some((imp, substitutions)) = found_impl {
            let output_type_symbol = self.symbol_table
                .find_type_symbol_in_scope("Output", imp.impl_scope_id)
                .ok_or_else(|| {
                    let trait_name = self.symbol_table.display_type(&Type::new_base(trait_id));
                    self.create_error(ErrorKind::UnknownIdentifier(format!("associated type 'Output' for trait '{}'", trait_name)), info.span, &[info.span])
                })?
                .clone();

            let TypeSymbolKind::TypeAlias((_, Some(output_type_template))) = &output_type_symbol.kind else {
                unreachable!("The 'Output' associated type in a trait impl must be a resolved alias");
            };

            let concrete_output_type = self.apply_substitution(output_type_template, &substitutions);
            
            self.unify(result_ty, concrete_output_type, info)?;
            
            Ok(true)
        } else {
            let trait_name = self.symbol_table.display_type(&Type::Base { symbol: trait_id, args: trait_args });
            let lhs_name = self.symbol_table.display_type(&resolved_lhs);
            Err(self.create_error(
                ErrorKind::UnimplementedTrait(trait_name, lhs_name),
                info.span,
                &[info.span],
            ))
        }
    }

    fn unify_cast(&mut self, source: Type, target: Type, info: ConstraintInfo) -> Result<bool, BoxedError> {
        let resolved_source = self.resolve_type(&source);
        let resolved_target = self.resolve_type(&target);

        if self.is_uv(resolved_source.get_base_symbol()) || self.is_uv(resolved_target.get_base_symbol()) {
            return Ok(false);
        }

        let source_sym = self.symbol_table.get_type_symbol(resolved_source.get_base_symbol()).unwrap();
        let target_sym = self.symbol_table.get_type_symbol(resolved_target.get_base_symbol()).unwrap();

        if source_sym.is_valid_cast(target_sym) {
            Ok(true)
        } else {
            Err(self.create_error(
                ErrorKind::InvalidCast(
                    self.symbol_table.display_type(&resolved_source),
                    self.symbol_table.display_type(&resolved_target),
                ),
                info.span,
                &[info.span],
            ))
        }
    }
}