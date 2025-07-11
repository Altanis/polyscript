use crate::{
    frontend::ast::AstNode,
    middle::semantic_analyzer::{
        Constraint, ConstraintInfo, SemanticAnalyzer, Type, TypeSymbolId, TypeSymbolKind,
    },
    utils::{
        error::{BoxedError, Error, ErrorKind},
        kind::Span,
    },
};

impl SemanticAnalyzer {
    pub fn unification_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];
        let mut constraints = std::mem::take(&mut self.unification_context.constraints);

        let mut iterations = 0;
        let limit = constraints.len() * 2 + 100;

        while let Some(constraint) = constraints.pop_front() {
            if iterations > limit {
                // TODO: locate uv's that still have constraints attached
                break;
            }

            iterations += 1;

            if let Err(e) = self.process_constraint(constraint.0, constraint.1) {
                errors.push(*e);
            }
        }

        errors
    }

    fn process_constraint(&mut self, constraint: Constraint, info: ConstraintInfo) -> Result<(), BoxedError> {
        match constraint {
            Constraint::Equality(uv_symbol_id, ty) => self.unify(Type::new_base(uv_symbol_id), ty)?,
            Constraint::SelfValue(uv_symbol_id, ty) => {}
            Constraint::FunctionSignature(uv_symbol_id, params, return_ty) => {}
            Constraint::MemberAccess(uv_symbol_id, lhs_type, rhs_name) => {}
            Constraint::Operation(uv_symbol_id, trait_type) => {}
        }

        Ok(())
    }

    fn unify(&mut self, t1: Type, t2: Type) -> Result<(), BoxedError> {
        match (t1, t2) {
            (t1, t2) if t1 == t2 => Ok(()),
            (Type::Base { symbol: s, .. }, other) if self.is_uv(s) => {
                self.unify_variable(s, other);
                Ok(())
            }
            (other, Type::Base { symbol: s, .. }) if self.is_uv(s) => {
                self.unify_variable(s, other);
                Ok(())
            }
            (Type::Base { symbol: s1, args: a1 }, Type::Base { symbol: s2, args: a2 }) => {
                // TODO: Unify similar types `s1` and `s2` without raw equality.
                if s1 != s2 || a1.len() != a2.len() {
                    return self.type_mismatch_error(
                        &Type::Base { symbol: s1, args: a1 },
                        &Type::Base { symbol: s2, args: a2 },
                    );
                }

                for (arg1, arg2) in a1.into_iter().zip(a2.into_iter()) {
                    self.unify(arg1, arg2)?;
                }

                Ok(())
            }
            (Type::Reference(inner1), Type::Reference(inner2)) => self.unify(*inner1, *inner2),
            (Type::MutableReference(inner1), Type::MutableReference(inner2)) => self.unify(*inner1, *inner2),

            (t1, t2) => self.type_mismatch_error(&t1, &t2),
        }
    }

    fn unify_variable(&mut self, uv_id: TypeSymbolId, ty: Type) {
        let TypeSymbolKind::UnificationVariable(id) = self.symbol_table.get_type_symbol(uv_id).unwrap().kind
        else {
            unreachable!();
        };

        self.unification_context.substitutions.insert(id, ty);
    }

    fn is_uv(&self, symbol_id: TypeSymbolId) -> bool {
        matches!(
            self.symbol_table.get_type_symbol(symbol_id).unwrap().kind,
            TypeSymbolKind::UnificationVariable(_)
        )
    }

    fn get_type_span(&self, id: TypeSymbolId) -> Option<Span> {
        self.symbol_table.get_type_symbol(id).unwrap().span
    }

    fn type_mismatch_error(&self, t1: &Type, t2: &Type) -> Result<(), BoxedError> {
        let span1 = self.get_type_span(t1.get_base_symbol()).unwrap_or_default();
        let span2 = self.get_type_span(t2.get_base_symbol()).unwrap_or(span1);

        Err(self.create_error(
            ErrorKind::TypeMismatch(
                self.symbol_table.display_type(t1),
                self.symbol_table.display_type(t2),
            ),
            span1,
            &[span1, span2],
        ))
    }
}
