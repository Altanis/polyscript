use std::collections::HashMap;

use crate::{
    frontend::ast::AstNode,
    middle::semantic_analyzer::{
        Constraint, ConstraintInfo, SemanticAnalyzer, Type, TypeSymbolId, TypeSymbolKind, ValueSymbolKind
    },
    utils::error::{BoxedError, Error, ErrorKind},
};

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
    fn apply_substitution(ty: &Type, substitutions: &HashMap<TypeSymbolId, Type>) -> Type {
        match ty {
            Type::Base { symbol, args } => {
                if let Some(substituted_type) = substitutions.get(symbol) {
                    if let Type::Base { symbol: new_symbol, args: new_args } = substituted_type {
                        if new_args.is_empty() {
                            let final_args = args.iter().map(|arg| SemanticAnalyzer::apply_substitution(arg, substitutions)).collect();
                            return Type::Base { symbol: *new_symbol, args: final_args };
                        }
                    }
                    return substituted_type.clone();
                }

                let substituted_args = args.iter().map(|arg| SemanticAnalyzer::apply_substitution(arg, substitutions)).collect();
                Type::Base { symbol: *symbol, args: substituted_args }
            }
            Type::Reference(inner) => Type::Reference(Box::new(SemanticAnalyzer::apply_substitution(inner, substitutions))),
            Type::MutableReference(inner) => Type::MutableReference(Box::new(SemanticAnalyzer::apply_substitution(inner, substitutions))),
        }
    }

    /// Recursively substitutes any known unification variables within a type.
    fn substitute(&self, ty: &Type) -> Type {
        SemanticAnalyzer::apply_substitution(ty, &self.unification_context.substitutions)
    }

    /// Checks if a unification variable `uv_id` occurs within a type `ty`.
    /// https://en.wikipedia.org/wiki/Occurs_check
    fn occurs_check(&self, uv_id: TypeSymbolId, ty: &Type) -> bool {
        match ty {
            Type::Base { symbol, args } => {
                if *symbol == uv_id {
                    return true;
                }

                if self.is_uv(*symbol) {
                     if let Some(sub) = self.unification_context.substitutions.get(symbol) {
                         return self.occurs_check(uv_id, sub);
                     }
                }

                args.iter().any(|arg| self.occurs_check(uv_id, arg))
            },
            Type::Reference(inner) | Type::MutableReference(inner) => self.occurs_check(uv_id, inner),
        }
    }

    /// Unifies a metavariable with a type.
    fn unify_variable(&mut self, uv_id: TypeSymbolId, ty: Type, info: ConstraintInfo) -> Result<(), BoxedError> {
        if self.occurs_check(uv_id, &ty) {
            return Err(self.type_mismatch_error(
                &Type::new_base(uv_id),
                &ty,
                info,
                Some("[infinite type detected: a metavariable occurs within its own definition]".to_string()),
            ));
        }
        
        self.unification_context.substitutions.insert(uv_id, ty);
        Ok(())
    }

    /// Checks if a type is a metavariable.
    fn is_uv(&self, symbol_id: TypeSymbolId) -> bool {
        matches!(
            self.symbol_table.get_type_symbol(symbol_id).unwrap().kind,
            TypeSymbolKind::UnificationVariable(_)
        )
    }

    /// Generates a mismatch error between types `t1` and `t2`.
    fn type_mismatch_error(&self, t1: &Type, t2: &Type, info: ConstraintInfo, specifics: Option<String>) -> BoxedError {
        self.create_error(
            ErrorKind::TypeMismatch(
                self.symbol_table.display_type(t1),
                self.symbol_table.display_type(t2),
                specifics
            ),
            info.span,
            &[info.span]
        )
    }
}

impl SemanticAnalyzer {
    pub fn unification_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];
        let mut constraints = std::mem::take(&mut self.unification_context.constraints);

        let mut iterations = 0;
        let limit = constraints.len() * 4 + 100;

        while let Some((constraint, info)) = constraints.pop_front() {
            if iterations > limit {
                // TODO: locate uv's that still have constraints attached
                break;
            }

            iterations += 1;

            match self.process_constraint(constraint.clone(), info) {
                Ok(success) if !success => constraints.push_back((constraint, info)),
                Err(e) => errors.push(*e),
                _ => ()
            }
        }

        errors
    }

    fn process_constraint(&mut self, constraint: Constraint, info: ConstraintInfo) -> Result<bool, BoxedError> {
        match constraint {
            Constraint::Equality(uv_symbol_id, ty) => 
                self.unify(Type::new_base(uv_symbol_id), ty, info),
            Constraint::DereferenceEquality(uv_symbol_id, ty) => 
                self.unify_dereference(uv_symbol_id, ty, info),
            Constraint::FunctionSignature(uv_symbol_id, params, return_ty) => 
                self.unify_function_signature(uv_symbol_id, params, return_ty, info),
            Constraint::InstanceMemberAccess(uv_symbol_id, lhs_type, rhs_name) =>
                self.unify_instance_member_access(uv_symbol_id, lhs_type, rhs_name, info),
            Constraint::StaticMemberAccess(uv_symbol_id, lhs_type_id, rhs_name) =>
                self.unify_static_member_access(uv_symbol_id, lhs_type_id, rhs_name, info),
            // Constraint::Operation(uv_symbol_id, trait_type, lhs, rhs) 
                // => self.unify_operation(uv_symbol_id, trait_type, lhs, rhs, info),
            _ => unreachable!()
        }
    }

    fn unify(&mut self, t1: Type, t2: Type, info: ConstraintInfo) -> Result<bool, BoxedError> {
        let t1 = self.substitute(&t1);
        let t2 = self.substitute(&t2);

        match (t1, t2) {
            (t1, t2) if t1 == t2 => Ok(true),
            (Type::Base { symbol: s, .. }, other) if self.is_uv(s) => {
                self.unify_variable(s, other, info)?;
                Ok(true)
            }
            (other, Type::Base { symbol: s, .. }) if self.is_uv(s) => {
                self.unify_variable(s, other, info)?;
                Ok(true)
            }
            (Type::Base { symbol: s1, args: a1 }, Type::Base { symbol: s2, args: a2 }) => {
                let sym1 = self.symbol_table.get_type_symbol(s1).unwrap();
                let sym2 = self.symbol_table.get_type_symbol(s2).unwrap();

                if !sym1.can_unify_with(sym2) || a1.len() != a2.len() {
                    return Err(self.type_mismatch_error(
                        &Type::Base { symbol: s1, args: a1 },
                        &Type::Base { symbol: s2, args: a2 },
                        info,
                        None
                    ));
                }

                for (arg1, arg2) in a1.into_iter().zip(a2.into_iter()) {
                    self.unify(arg1, arg2, info)?;
                }

                Ok(true)
            }
            (Type::Reference(inner1), Type::Reference(inner2)) => self.unify(*inner1, *inner2, info),
            (Type::MutableReference(inner1), Type::MutableReference(inner2)) => self.unify(*inner1, *inner2, info),

            (t1, t2) => Err(self.type_mismatch_error(&t1, &t2, info, None)),
        }
    }

    fn unify_dereference(&mut self, uv_symbol_id: TypeSymbolId, ty: Type, info: ConstraintInfo) -> Result<bool, BoxedError> {
        let substituted_ty = self.substitute(&ty);

        match substituted_ty {
            Type::Base { symbol, .. } if self.is_uv(symbol) => Ok(false),
            Type::Reference(inner) | Type::MutableReference(inner) => 
                self.unify(Type::new_base(uv_symbol_id), *inner, info),
            _ => Err(self.create_error(
                ErrorKind::InvalidDereference(self.symbol_table.display_type(&substituted_ty)),
                info.span,
                &[info.span],
            )),
        }
    }

    fn unify_function_signature(&mut self, uv_symbol_id: TypeSymbolId, params: Vec<Type>, return_ty: Type, info: ConstraintInfo) -> Result<bool, BoxedError> {
        let callee_ty = self.substitute(&Type::new_base(uv_symbol_id));

        match callee_ty {
            Type::Base { symbol, .. } if self.is_uv(symbol) => Ok(false),
            Type::Base { symbol, .. } => {
                let callee_symbol = self.symbol_table.get_type_symbol(symbol).unwrap();

                if let TypeSymbolKind::FunctionSignature { params: expected_params, return_type: expected_return, .. } = &callee_symbol.kind {
                    if params.len() != expected_params.len() {
                        return Err(self.type_mismatch_error(
                            &callee_ty,
                            &Type::new_base(uv_symbol_id),
                            info,
                            Some(format!("[expected {} arguments, but got {}]", expected_params.len(), params.len()))
                        ));
                    }

                    let expected_return_clone = expected_return.clone();

                    for (arg, expected) in params.iter().zip(expected_params.clone().iter()) {
                        if !self.unify(arg.clone(), expected.clone(), info)? {
                            return Ok(false);
                        }
                    }

                    self.unify(return_ty.clone(), expected_return_clone, info)
                } else {
                    Err(self.create_error(ErrorKind::NotCallable(self.symbol_table.display_type(&callee_ty)), info.span, &[info.span]))
                }
            }
            _ => Err(self.create_error(ErrorKind::NotCallable(self.symbol_table.display_type(&callee_ty)), info.span, &[info.span]))
        }
    }

    fn unify_static_member_access(
        &mut self,
        uv_symbol_id: TypeSymbolId,
        lhs_type_id: TypeSymbolId,
        rhs_name: String,
        info: ConstraintInfo,
    ) -> Result<bool, BoxedError> {
        if self.is_uv(lhs_type_id) {
            return Ok(false);
        }

        let lhs_symbol = self.symbol_table.get_type_symbol(lhs_type_id).unwrap().clone();
        let lhs_type = Type::new_base(lhs_type_id);

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
            if let Some(value_symbol) = self
                .symbol_table
                .find_value_symbol_in_scope(&rhs_name, imp.scope_id)
            {
                let symbol_type = self.substitute(value_symbol.type_id.as_ref().unwrap());
                match &value_symbol.kind {
                    ValueSymbolKind::Function(_) | ValueSymbolKind::Variable => {
                        return self.unify(Type::new_base(uv_symbol_id), symbol_type, info);
                    }
                    _ => {}
                }
            }
        }

        for imp in &inherent_impls {
            if let Some(assoc_type_symbol) = self
                .symbol_table
                .find_type_symbol_in_scope(&rhs_name, imp.scope_id)
            {
                return self.unify(Type::new_base(uv_symbol_id), Type::new_base(assoc_type_symbol.id), info);
            }
        }

        if let Some(scope_id) = enum_scope_id {
            if self
                .symbol_table
                .find_value_symbol_in_scope(&rhs_name, scope_id)
                .is_some()
            {
                return self.unify(Type::new_base(uv_symbol_id), lhs_type, info);
            }
        }

        Err(self.create_error(
            ErrorKind::FieldNotFound(rhs_name, self.symbol_table.display_type(&lhs_type)),
            info.span,
            &[info.span],
        ))
    }

    fn unify_instance_member_access(
        &mut self,
        uv_symbol_id: TypeSymbolId,
        lhs_type: Type,
        rhs_name: String,
        info: ConstraintInfo,
    ) -> Result<bool, BoxedError> {
        let substituted_lhs = self.substitute(&lhs_type);

        let base_lhs_type = match &substituted_lhs {
            Type::Reference(inner) | Type::MutableReference(inner) => (**inner).clone(),
            _ => substituted_lhs.clone(),
        };
        
        let (base_symbol_id, concrete_args) = match &base_lhs_type {
            Type::Base { symbol, args } => (*symbol, args.clone()),
            _ => {
                return Err(self.create_error(
                    ErrorKind::InvalidFieldAccess(self.symbol_table.display_type(&substituted_lhs)),
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
                    ErrorKind::InvalidFieldAccess(self.symbol_table.display_type(&substituted_lhs)),
                    info.span,
                    &[info.span],
                ));
            }
        };

        if let Some(scope_id) = struct_scope_id {
            if let Some(field_symbol) = self
                .symbol_table
                .find_value_symbol_from_scope(scope_id, &rhs_name)
            {
                let substitutions = self.create_generic_substitution_map(&lhs_symbol.generic_parameters, &concrete_args);
                let concrete_field_type = SemanticAnalyzer::apply_substitution(field_symbol.type_id.as_ref().unwrap(), &substitutions);
                return self.unify(Type::new_base(uv_symbol_id), concrete_field_type, info);
            }
        }
        
        for imp in &inherent_impls {
            // TODO: Match against specific specializations.
            
            if let Some(value_symbol) = self
                .symbol_table
                .find_value_symbol_in_scope(&rhs_name, imp.scope_id)
            {
                if let ValueSymbolKind::Function(_) = value_symbol.kind {
                    let symbol_type = self.substitute(value_symbol.type_id.as_ref().unwrap());
                    let fn_sig_id = symbol_type.get_base_symbol();
                    let fn_sig_symbol = self.symbol_table.get_type_symbol(fn_sig_id).unwrap();

                    if let TypeSymbolKind::FunctionSignature { instance: Some(_), .. } = fn_sig_symbol.kind {
                        let mut substitutions = self.create_generic_substitution_map(&lhs_symbol.generic_parameters, &concrete_args);
                        let impl_substitutions = self.create_generic_substitution_map(&imp.generic_params, &concrete_args); // Assuming direct mapping for simplicity
                        substitutions.extend(impl_substitutions);

                        let concrete_fn_type = SemanticAnalyzer::apply_substitution(&symbol_type, &substitutions);
                        return self.unify(Type::new_base(uv_symbol_id), concrete_fn_type, info);
                    }
                }
            }
        }

        Err(self.create_error(
            ErrorKind::FieldNotFound(rhs_name, self.symbol_table.display_type(&substituted_lhs)),
            info.span,
            &[info.span],
        ))
    }
}