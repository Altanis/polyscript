use crate::{frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, middle::semantic_analyzer::{Constraint, PrimitiveKind, SemanticAnalyzer, Type, TypeSymbol, TypeSymbolId, TypeSymbolKind}, utils::{error::{BoxedError, Error, ErrorKind}, kind::{Operation, QualifierKind, Span}}};

impl SemanticAnalyzer {
    fn get_primitive_type(&self, primitive: PrimitiveKind) -> TypeSymbolId {
        self.builtin_types[primitive as usize]
    }

    fn get_type_from_identifier(&self, name: &str, span: Span) -> Result<Type, BoxedError> {
        match self.symbol_table.find_value_symbol(name) {
            Some(value_symbol) => {
                match value_symbol.type_id.clone() {
                    Some(type_id) => Ok(type_id),
                    None => Err(self.create_error(ErrorKind::UnresolvedType(name.to_string()), span, &[span]))
                }
            },
            None => Err(self.create_error(ErrorKind::UnknownIdentifier(name.to_string()), span, &[span]))
        }
    }

    // fn find_impl_member_type(&mut self, name: String) -> Result<Type, BoxedError> {

    // }

    // fn resolve_static_member_access(&mut self, type_symbol: &TypeSymbol, right: &mut BoxedAstNode) -> Result<Type, BoxedError> {
    //     match type_symbol.kind {
    //         TypeSymbolKind::Enum((scope, impls)) => {

    //         }
    //     }
    // }

    // fn resolve_instance_member_access(&mut self, lhs_type: &Type, right: &mut BoxedAstNode) -> Result<Type, BoxedError> {
        
    // }

    /// SYNTHESIS: Infers the type of the expression, or assigns a unification variable if unknown.
    fn bidirectional_synthesis(&mut self, expr: &mut AstNode) -> Result<Type, BoxedError> {

        //             Operation::FieldAccess => None,
            // Operation::FunctionCall => None,
            // Operation::Assign => None

        use AstNodeKind::*;

        let unification_variable = self.unification_context.generate_uv_type(&mut self.symbol_table, expr.span);
        let uv_id = unification_variable.get_base_symbol();

        match &mut expr.kind {
            IntegerLiteral(_) => self.unification_context.register_constraint(Constraint::Equality(
                uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Int))
            )),
            FloatLiteral(_) => self.unification_context.register_constraint(Constraint::Equality(
                uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Float))
            )),
            BooleanLiteral(_) => self.unification_context.register_constraint(Constraint::Equality(
                uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Bool))
            )),
            StringLiteral(_) => self.unification_context.register_constraint(Constraint::Equality(
                uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::String))
            )),
            CharLiteral(_) => self.unification_context.register_constraint(Constraint::Equality(
                uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Char))
            )),

            Identifier(string) => self.unification_context.register_constraint(Constraint::Equality(
                uv_id, Type::new_base(self.get_type_from_identifier(string, expr.span)?.get_base_symbol())
            )),
            
            UnaryOperation { operator, operand } => {
                let uv_type = self.bidirectional_synthesis(operand)?;

                match operator.to_trait_data() {
                    Some((trait_name, _)) => {
                        self.unification_context.register_constraint(Constraint::Trait(
                            uv_type.get_base_symbol(), self.trait_registry.get_default_trait(&trait_name)
                        ));
                    },
                    None => match operator {
                        Operation::Dereference => ,
                        Operation::ImmutableAddressOf => self.unification_context.register_constraint(Constraint::Equality(
                            uv_id, Type::Reference(Box::new(uv_type))
                        )),
                        Operation::MutableAddressOf => self.unification_context.register_constraint(Constraint::Equality(
                            uv_id, Type::MutableReference(Box::new(uv_type))
                        )),
                        _ => {}
                    }
                }
            },

            // BinaryOperation { left, right, operator } => {
            //     match operator.to_trait_data() {
            //         Some(_) => Ok(self.unification_context.generate_uv_type(&mut self.symbol_table, expr.span)),
            //         None => match operator {
            //             Operation::FieldAccess => {
            //                 let AstNodeKind::Identifier(name) = &mut right.kind else {
            //                     return Err(self.create_error(ErrorKind::IncorrectFieldAccessRhs, right.span, &[right.span]));
            //                 };

            //                 if let AstNodeKind::Identifier(type_name) = &left.kind {
            //                     if let Some(type_symbol) = self.symbol_table.find_type_symbol(type_name) {
            //                         return self.resolve_static_member_access(type_symbol, right);
            //                     }
            //                 }
                            
            //                 let lhs_type = self.bidirectional_synthesis(left)?;
            //                 self.resolve_instance_member_access(&lhs_type, right)
            //             },
            //             // Operation::FunctionCall => {}
            //             _ => unreachable!()
            //         }
            //     }
            // },
            _ => return Err(self.create_error(ErrorKind::UnknownType, expr.span, &[expr.span]))
        }

        expr.type_id = Some(unification_variable.clone());
        Ok(unification_variable)
    }
}

impl SemanticAnalyzer {
    pub fn type_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];

        if let AstNodeKind::Program(statements) = &mut program.kind {
            for statement in statements {
                if let Err(err) = self.bidirectional_check(statement) {
                    errors.push(*err);
                }
            }
        } else {
            unreachable!();
        }
        
        errors
    }

    fn bidirectional_check(&mut self, statement: &mut AstNode) -> Result<Option<Type>, BoxedError> {
        use AstNodeKind::*;
        
        let type_annotation = match statement.kind {
            _ => {
                for child in statement.children_mut() {
                    self.bidirectional_check(child);
                }

                Ok(None)
            }
        };

        if let Ok(Some(type_id)) = type_annotation.clone() {
            statement.type_id = Some(type_id);
        }

        type_annotation
    }
}