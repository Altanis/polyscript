use std::collections::HashMap;

use crate::{
    frontend::ast::AstNode,
    middle::semantic_analyzer::{
        Constraint, ConstraintInfo, InherentImpl, SemanticAnalyzer, Type, TypeSymbolId, TypeSymbolKind, ValueSymbolKind
    },
    utils::{error::{BoxedError, Error, ErrorKind}, kind::QualifierKind},
};

impl SemanticAnalyzer {
    fn is_uv(&self, symbol_id: TypeSymbolId) -> bool {
        matches!(
            self.symbol_table.get_type_symbol(symbol_id).unwrap().kind,
            TypeSymbolKind::UnificationVariable(_)
        )
    }
}

impl SemanticAnalyzer {
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
        substitutions: &HashMap<TypeSymbolId, Type>,
        debug: bool
    ) -> Type {
        match ty {
            Type::Base { symbol: base_symbol_id, args } => {
                if let Some(substituted_type) = substitutions.get(base_symbol_id) {
                    return substituted_type.clone();
                }

                let base_symbol = self.symbol_table.get_type_symbol(*base_symbol_id).unwrap();

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

                        self.apply_substitution(aliased_type, &local_substitutions, debug)
                    },
                    TypeSymbolKind::FunctionSignature { params, return_type, instance } => {
                        let substituted_params = params
                            .iter()
                            .map(|p| self.apply_substitution(p, substitutions, debug))
                            .collect();

                        let substituted_return_type = self.apply_substitution(return_type, substitutions, debug);

                        let specialized_sig_id = self.symbol_table.add_type_symbol(
                            &format!("#fn_sig_specialized_{}", base_symbol.id),
                            TypeSymbolKind::FunctionSignature {
                                params: substituted_params,
                                return_type: substituted_return_type,
                                instance: *instance,
                            },
                            vec![],
                            QualifierKind::Private,
                            None,
                        ).unwrap();

                        Type::new_base(specialized_sig_id)
                    },
                    _ => {
                        let substituted_args = args
                            .iter()
                            .map(|arg| self.apply_substitution(arg, substitutions, debug))
                            .collect();

                        Type::Base {
                            symbol: *base_symbol_id,
                            args: substituted_args,
                        }
                    }
                }
            },
            Type::Reference(inner) => {
                Type::Reference(Box::new(self.apply_substitution(inner, substitutions, debug)))
            },
            Type::MutableReference(inner) => {
                Type::MutableReference(Box::new(self.apply_substitution(inner, substitutions, debug)))
            }
        }
    }

    /// Recursively resolves a type by applying substitutions for unification variables
    /// and expanding type aliases until a concrete type or a unification variable is reached.
    fn resolve_type(&mut self, ty: &Type) -> Type {
        let mut current_ty = self.apply_substitution(ty, &self.unification_context.substitutions, false);

        loop {
            let Type::Base { symbol, args } = &current_ty else { break; };

            if self.is_uv(*symbol) {
                break;
            }

            let type_symbol = self.symbol_table.get_type_symbol(*symbol).unwrap();

            if let TypeSymbolKind::TypeAlias((_, Some(aliased_type))) = &type_symbol.kind {
                let substitutions = self.create_generic_substitution_map(
                    &type_symbol.generic_parameters,
                    args
                );

                let substituted_alias = self.apply_substitution(aliased_type, &substitutions, false);
                current_ty = self.apply_substitution(&substituted_alias, &self.unification_context.substitutions, false);
            } else {
                break;
            }
        }

        current_ty
    }

    /// Checks if a unification variable `uv_id` occurs within a type `ty`.
    /// https://en.wikipedia.org/wiki/Occurs_check
    fn occurs_check(&self, uv_id: TypeSymbolId, ty: &Type) -> bool {
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
                self.unify_instance_member_access(result_ty, lhs_type, rhs_name, info)
            },
            Constraint::StaticMemberAccess(result_ty, lhs_type, rhs_name) => {
                self.unify_static_member_access(result_ty, lhs_type, rhs_name, info)
            },
            // Constraint::Operation(uv_symbol_id, trait_type, lhs, rhs)
            // => self.unify_operation(uv_symbol_id, trait_type, lhs, rhs, info),
            _ => unreachable!(),
        }
    }

    fn unify(&mut self, t1: Type, t2: Type, info: ConstraintInfo) -> Result<Type, BoxedError> {
        let t1 = self.resolve_type(&t1);
        let t2 = self.resolve_type(&t2);

        match (t1.clone(), t2.clone()) {
            (t1, t2) if t1 == t2 => Ok(t1),

            (Type::Base { symbol: s, .. }, other) if self.is_uv(s) => self.unify_variable(s, other, info),
            (other, Type::Base { symbol: s, .. }) if self.is_uv(s) => self.unify_variable(s, other, info),

            (Type::Base { symbol: s1, args: a1 }, Type::Base { symbol: s2, args: a2 }) => {
                let type_sym_s1 = self.symbol_table.get_type_symbol(s1).unwrap();
                let type_sym_s2 = self.symbol_table.get_type_symbol(s2).unwrap();

                let resultant_symbol = type_sym_s1.unify(type_sym_s2)
                    .ok_or_else(|| self.type_mismatch_error(&t1, &t2, info, None))?;

                if a1.len() != a2.len() {
                    return Err(self.type_mismatch_error(&t1, &t2, info, Some(format!("expected {} generic arguments, but found {}", a1.len(), a2.len()))));
                }

                let mut unified_args = vec![];
                for (arg1, arg2) in a1.iter().zip(a2.iter()) {
                    unified_args.push(self.unify(arg1.clone(), arg2.clone(), info)?);
                }

                Ok(Type::Base {
                    symbol: resultant_symbol,
                    args: unified_args,
                })
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
            Type::Base { symbol, args } => {
                if self.is_uv(symbol) {
                    return Ok(false);
                }
                let callee_symbol = self.symbol_table.get_type_symbol(symbol).unwrap();

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
                    
                    let substitutions = self.create_generic_substitution_map(&callee_symbol.generic_parameters, &args);

                    let expected_params = sig_params.iter().map(|p| self.apply_substitution(p, &substitutions, false)).collect::<Vec<_>>();
                    let expected_return = self.apply_substitution(sig_return, &substitutions, false);

                    for (arg, expected) in params.iter().zip(expected_params.iter()) {
                        self.unify(arg.clone(), expected.clone(), info)?;
                    }

                    self.unify(return_ty, expected_return, info)?;
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

        let (callee_symbol_id, callee_args) = match callee_ty.clone() {
            Type::Base { symbol, args } => {
                if self.is_uv(symbol) { return Ok(false); }
                (symbol, args)
            },
            _ => {
                return Err(self.create_error(
                    ErrorKind::NotCallable(self.symbol_table.display_type(&callee_ty)),
                    info.span,
                    &[info.span],
                ))
            }
        };

        let callee_symbol = self.symbol_table.get_type_symbol(callee_symbol_id).unwrap();

        if let TypeSymbolKind::FunctionSignature {
            params: expected_params_with_receiver,
            return_type: expected_return,
            instance: Some(_),
        } = callee_symbol.kind.clone()
        {
            if expected_params_with_receiver.is_empty() {
                panic!("This shouldn't happen. [1]");
            }

            let (expected_receiver_ty, expected_params) = expected_params_with_receiver.split_first().unwrap();

            if params.len() != expected_params.len() {
                return Err(self.create_error(
                    ErrorKind::ArityMismatch(expected_params.len(), params.len()),
                    info.span,
                    &[info.span],
                ));
            }

            let substitutions = self.create_generic_substitution_map(&callee_symbol.generic_parameters, &callee_args);
            let concrete_expected_params: Vec<Type> = expected_params.iter().map(|p| self.apply_substitution(p, &substitutions, false)).collect();
            let concrete_receiver = self.apply_substitution(expected_receiver_ty, &substitutions, false);
            let concrete_return = self.apply_substitution(&expected_return, &substitutions, false);

            for (arg, expected) in params.iter().zip(concrete_expected_params.iter()) {
                self.unify(arg.clone(), expected.clone(), info)?;
            }

            self.unify_receiver(instance_ty, concrete_receiver, info)?;
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

    fn unify_receiver(&mut self, passed: Type, expected: Type, info: ConstraintInfo) -> Result<Type, BoxedError> {
        let passed = self.resolve_type(&passed);
        let expected = self.resolve_type(&expected);

        if let Ok(unified) = self.unify(passed.clone(), expected.clone(), info) {
            return Ok(unified);
        }

        match (passed.clone(), expected.clone()) {
            (p @ Type::Base { .. }, e @ Type::Reference(_)) => {
                self.unify(Type::Reference(Box::new(p)), e, info)
            },
            (p @ Type::Base { .. }, e @ Type::MutableReference(_)) => {
                self.unify(Type::MutableReference(Box::new(p)), e, info)
            },
            (Type::Reference(p_inner), e @ Type::Base { .. }) => self.unify(*p_inner, e, info),
            (Type::MutableReference(p_inner), e @ Type::Base { .. }) => self.unify(*p_inner, e, info),
            (Type::MutableReference(p_inner), e @ Type::Reference(_)) => {
                self.unify(Type::Reference(p_inner), e, info)
            },
            _ => Err(self.type_mismatch_error(
                &passed,
                &expected,
                info,
                Some("receiver type mismatch".to_string()),
            )),
        }
    }

    fn unify_static_member_access(
        &mut self,
        result_ty: Type,
        lhs_type: Type,
        rhs_name: String,
        info: ConstraintInfo,
    ) -> Result<bool, BoxedError> {
        let lhs_type = self.resolve_type(&lhs_type);
        let lhs_type_id = lhs_type.get_base_symbol();

        if self.is_uv(lhs_type_id) {
            return Ok(false);
        }

        let lhs_symbol = self.symbol_table.get_type_symbol(lhs_type_id).unwrap().clone();

        let (inherent_impls, enum_scope_id) = match &lhs_symbol.kind {
            TypeSymbolKind::Struct((_, impls)) => (impls.clone(), None),
            TypeSymbolKind::Enum((scope_id, impls)) => (impls.clone(), Some(*scope_id)),
            _ => {
                return Err(self.create_error(
                    ErrorKind::InvalidFieldAccess(self.symbol_table.display_type(&lhs_type)),
                    info.span,
                    &[info.span],
                ));
            }
        };

        for imp in &inherent_impls {
            if let Some(value_symbol) = self.symbol_table.find_value_symbol_in_scope(&rhs_name, imp.scope_id) {
                let symbol_type = self.resolve_type(value_symbol.type_id.as_ref().unwrap());
                match &value_symbol.kind {
                    ValueSymbolKind::Function(_) | ValueSymbolKind::Variable => {
                        self.unify(result_ty, symbol_type, info)?;
                        return Ok(true);
                    }
                    _ => {}
                }
            }
        }

        for imp in &inherent_impls {
            if let Some(assoc_type_symbol) = self.symbol_table.find_type_symbol_in_scope(&rhs_name, imp.scope_id)
            {
                let aliased_type = self.resolve_type(&Type::new_base(assoc_type_symbol.id));
                self.unify(result_ty, aliased_type, info)?;
                return Ok(true);
            }
        }

        if let Some(scope_id) = enum_scope_id {
            if self.symbol_table.find_value_symbol_in_scope(&rhs_name, scope_id).is_some() {
                self.unify(result_ty, lhs_type, info)?;
                return Ok(true);
            }
        }

        Err(self.create_error(
            ErrorKind::MemberNotFound(rhs_name, self.symbol_table.display_type(&lhs_type)),
            info.span,
            &[info.span],
        ))
    }

    fn unify_instance_member_access(
        &mut self,
        result_ty: Type,
        lhs_type: Type,
        rhs_name: String,
        info: ConstraintInfo,
    ) -> Result<bool, BoxedError> {
        let lhs_type = self.resolve_type(&lhs_type);

        let base_lhs_type = match &lhs_type {
            Type::Reference(inner) | Type::MutableReference(inner) => (**inner).clone(),
            _ => lhs_type.clone(),
        };

        let (base_symbol_id, concrete_args) = match &base_lhs_type {
            Type::Base { symbol, args } => (*symbol, args.clone()),
            _ => {
                return Err(self.create_error(
                    ErrorKind::InvalidFieldAccess(self.symbol_table.display_type(&lhs_type)),
                    info.span,
                    &[info.span],
                ));
            }
        };

        if self.is_uv(base_symbol_id) {
            return Ok(false);
        }

        let lhs_symbol = self.symbol_table.get_type_symbol(base_symbol_id).unwrap().clone();

        let (struct_scope_id, inherent_impls) = match &lhs_symbol.kind {
            TypeSymbolKind::Struct((scope_id, impls)) => (Some(*scope_id), impls.clone()),
            TypeSymbolKind::Enum((_, impls)) => (None, impls.clone()),
            _ => {
                return Err(self.create_error(
                    ErrorKind::InvalidFieldAccess(self.symbol_table.display_type(&lhs_type)),
                    info.span,
                    &[info.span],
                ));
            }
        };

        if let Some(scope_id) = struct_scope_id {
            if let Some(field_symbol) = self.symbol_table.find_value_symbol_from_scope(scope_id, &rhs_name)
            {
                let substitutions =
                    self.create_generic_substitution_map(&lhs_symbol.generic_parameters, &concrete_args);
                    
                let concrete_field_type =
                    self.apply_substitution(field_symbol.type_id.as_ref().unwrap(), &substitutions, false);

                self.unify(result_ty, concrete_field_type, info)?;
                return Ok(true);
            }
        }

        for imp in &inherent_impls {
            if let Some(substitutions) = self.check_impl_applicability(&base_lhs_type, imp) {
                if let Some(value_symbol) = self.symbol_table.find_value_symbol_in_scope(&rhs_name, imp.scope_id) {
                    if let ValueSymbolKind::Function(_) = value_symbol.kind {
                        let symbol_type = self.resolve_type(value_symbol.type_id.as_ref().unwrap());
                        let specialized_fn_type = self.apply_substitution(&symbol_type, &substitutions, true);

                        self.unify(result_ty, specialized_fn_type, info)?;
                        
                        return Ok(true);
                    }
                }
            }
        }

        Err(self.create_error(
            ErrorKind::MemberNotFound(rhs_name, self.symbol_table.display_type(&lhs_type)),
            info.span,
            &[info.span],
        ))
    }
}