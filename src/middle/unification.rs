use crate::{
    frontend::ast::AstNode,
    middle::semantic_analyzer::{
        Constraint, ConstraintInfo, SemanticAnalyzer, Type, TypeSymbolId, TypeSymbolKind
    },
    utils::{
        error::{BoxedError, Error, ErrorKind}
    },
};

impl SemanticAnalyzer {
    /// Recursively substitutes any known unification variables within a type.
    fn substitute(&self, ty: &Type) -> Type {
        match ty {
            Type::Base { symbol, args } => {
                if self.is_uv(*symbol) {
                    let TypeSymbolKind::UnificationVariable(id) = self.symbol_table.type_symbols[symbol].kind else { unreachable!() };
                    if let Some(substitution) = self.unification_context.substitutions.get(&id) {
                        return self.substitute(substitution);
                    }
                }

                let new_args = args.iter().map(|arg| self.substitute(arg)).collect();
                Type::Base { symbol: *symbol, args: new_args }
            },
            Type::Reference(inner) => Type::Reference(Box::new(self.substitute(inner))),
            Type::MutableReference(inner) => Type::MutableReference(Box::new(self.substitute(inner))),
        }
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
                     let TypeSymbolKind::UnificationVariable(id) = self.symbol_table.type_symbols[symbol].kind else { unreachable!() };
                     if let Some(sub) = self.unification_context.substitutions.get(&id) {
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
        
        let TypeSymbolKind::UnificationVariable(id) = self.symbol_table.get_type_symbol(uv_id).unwrap().kind
        else {
            unreachable!();
        };

        self.unification_context.substitutions.insert(id, ty);
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
            // Constraint::MemberAccess(uv_symbol_id, lhs_type, rhs_name) =>
                // self.unify_member_access(uv_symbol_id, lhs_type, rhs_name, info),
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
}