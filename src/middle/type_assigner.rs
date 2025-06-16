use crate::{middle::semantic_analyzer::{Obligation, ObligationCause, PrimitiveKind, TraitObligation, Type, TypeSymbolId, TypeSymbolKind, ValueSymbolKind}, frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, utils::{error::*, kind::{Operation, QualifierKind, ReferenceKind, Span}}};
use super::semantic_analyzer::SemanticAnalyzer;

impl SemanticAnalyzer {
    fn get_primitive_type(&self, primitive: PrimitiveKind) -> TypeSymbolId {
        self.primitives[primitive as usize]
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

    fn get_type_from_unary_operation(&mut self, operator: Operation, operand: &mut BoxedAstNode, span: Span) -> Result<Type, BoxedError> {
        let operand_type = self.associate_node_with_type(operand)?;
        
        match operator {
            Operation::Dereference => {
                match operand_type {
                    Type::Base { .. } => Err(self.create_error(
                        ErrorKind::InvalidDereference,
                        span,
                        &[span]
                    )),
                    Type::Reference(ty) => Ok(*ty.clone()),
                    Type::MutableReference(ty) => Ok(*ty.clone())
                }
            },
            Operation::ImmutableAddressOf => Ok(Type::Reference(Box::new(operand_type.clone()))),
            Operation::MutableAddressOf => Ok(Type::MutableReference(Box::new(operand_type.clone()))),
            _ => {

                let (trait_name, _) = operator.to_trait_data().unwrap();
                let trait_id = self.symbol_table.find_type_symbol(&trait_name)
                    .map(|s| s.id)
                    .unwrap();

                let obligation_id = self.obligations.len();
                let obligation = Obligation {
                    id: obligation_id,
                    kind: TraitObligation {
                        trait_id,
                        self_type: operand_type,
                        trait_args: vec![]
                    },
                    cause: ObligationCause::UnaryOperation(operator),
                    cause_span: span,
                    resolved_type: None,
                };
                self.obligations.push(obligation);

                let obligation_type_name = format!("__unfulfilled_obligation_{}", obligation_id);
                let type_symbol_id = self.symbol_table.add_type_symbol(
                    &obligation_type_name,
                    TypeSymbolKind::UnfulfilledObligation(obligation_id),
                    vec![],
                    QualifierKind::Private,
                    Some(span),
                )?;

                Ok(Type::new_base(type_symbol_id))
            }
        }
    }

    fn resolve_instance_member_access(
        &mut self,
        lhs_type: &Type,
        rhs_node: &mut AstNode,
    ) -> Result<Type, BoxedError> {
        let base_type_symbol_id = lhs_type.get_base_symbol();
        let base_type_symbol = self.symbol_table.get_type_symbol(base_type_symbol_id).unwrap();

        let field_name = match &rhs_node.kind {
            AstNodeKind::Identifier(ident) => ident.clone(),
            _ => return Err(self.create_error(ErrorKind::IncorrectFieldAccessRhs, rhs_node.span, &[rhs_node.span]))
        };

        match &base_type_symbol.kind {
            TypeSymbolKind::Struct((scope_id, impls)) => {
                let scope_id = *scope_id;
                if let Some(field_symbol) = self.symbol_table.find_value_symbol_in_scope(&field_name, scope_id) {
                    let field_type = field_symbol.type_id.clone().ok_or_else(|| {
                        self.create_error(
                            ErrorKind::UnresolvedType(field_name.to_string()),
                            rhs_node.span,
                            &[rhs_node.span]
                        )
                    })?;

                    rhs_node.value_id = Some(field_symbol.id);
                    rhs_node.type_id = Some(field_type.clone());

                    Ok(field_type)
                } else if !impls.is_empty() {
                    for inherent_impl in impls.iter() {
                        let scope = self.symbol_table.get_scope(inherent_impl.scope_id).unwrap();
                        for (_, &v) in scope.values.iter() {
                            
                        }
                    }

                    unreachable!()
                } else {
                    Err(self.create_error(
                        ErrorKind::FieldNotFound(
                            field_name.to_string(),
                            self.symbol_table.display_type(lhs_type)
                        ),
                        rhs_node.span,
                        &[rhs_node.span]
                    ))
                }
            },
            _ => {
                Err(self.create_error(
                    ErrorKind::InvalidFieldAccess(self.symbol_table.get_type_name(lhs_type.get_base_symbol()).to_string()),
                    rhs_node.span,
                    &[rhs_node.span]
                ))
            }
        }
    }

    fn get_type_from_binary_operation(
        &mut self, 
        operator: Operation, 
        left: &mut BoxedAstNode, 
        right: &mut BoxedAstNode, 
        span: Span
    ) -> Result<Type, BoxedError> {
        match operator {
            Operation::FieldAccess => {
                if let AstNodeKind::Identifier(type_name) = &left.kind {
                    if let Some(type_symbol) = self.symbol_table.find_type_symbol(type_name) {
                        let type_id = type_symbol.id;
                        return self.resolve_static_member_access(type_id, right);
                    }
                }
                
                let lhs_type = self.associate_node_with_type(left)?;
                self.resolve_instance_member_access(&lhs_type, right)
            },
            _ => {
                let (trait_name, _) = operator.to_trait_data().unwrap();
                let trait_id = self.symbol_table.find_type_symbol(&trait_name)
                    .map(|s| s.id)
                    .unwrap();

                let obligation_id = self.obligations.len();
                let obligation = Obligation {
                    id: obligation_id,
                    kind: TraitObligation {
                        trait_id,
                        self_type: left_type,
                        trait_args: vec![right_type]
                    },
                    cause: ObligationCause::BinaryOperation(operator),
                    cause_span: span,
                    resolved_type: None,
                };
                self.obligations.push(obligation);

                let obligation_type_name = format!("__unfulfilled_obligation_{}", obligation_id);
                let type_symbol_id = self.symbol_table.add_type_symbol(
                    &obligation_type_name,
                    TypeSymbolKind::UnfulfilledObligation(obligation_id),
                    vec![],
                    QualifierKind::Private,
                    Some(span)
                )?;

                Ok(Type::new_base(type_symbol_id))
            }
        }
    }

    fn associate_node_with_type(&mut self, node: &mut AstNode) -> Result<Type, BoxedError> {
        use AstNodeKind::*;

        if let Some(id) = &node.type_id {
            return Ok(id.clone());
        }

        let id = match &mut node.kind {
            IntegerLiteral(_) => Ok(Type::new_base(self.get_primitive_type(PrimitiveKind::Int))),
            FloatLiteral(_) => Ok(Type::new_base(self.get_primitive_type(PrimitiveKind::Float))),
            BooleanLiteral(_) => Ok(Type::new_base(self.get_primitive_type(PrimitiveKind::Bool))),
            StringLiteral(_) => Ok(Type::new_base(self.get_primitive_type(PrimitiveKind::String))),
            CharLiteral(_) => Ok(Type::new_base(self.get_primitive_type(PrimitiveKind::Char))),
            Identifier(name) => self.get_type_from_identifier(name, node.span),
            UnaryOperation { operator, operand, .. } 
                => self.get_type_from_unary_operation(*operator, operand, node.span),
            BinaryOperation { operator, left, right }
                => self.get_type_from_binary_operation(*operator, left, right, node.span),
            _ => Err(self.create_error(ErrorKind::UnknownType, node.span, &[node.span])),
        }?;

        node.type_id = Some(id.clone());
        Ok(id)
    }
}

impl SemanticAnalyzer {
    pub fn type_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];

        if let AstNodeKind::Program(statements) = &mut program.kind {
            for statement in statements {
                if let Err(err) = self.collect_node_type(statement) {
                    errors.push(*err);
                }
            }
        } else {
            unreachable!();
        }

        errors
    }

    fn collect_node_type(&mut self, node: &mut AstNode) -> Result<Option<Type>, BoxedError> {
        // note: all functions have return types of `null`. make sure to update.
        // update all params in FunctionSignature 
        use AstNodeKind::*;
        
        let declared_type_opt: Result<Option<Type>, BoxedError> = match &mut node.kind {
            // VariableDeclaration { name, mutable, type_annotation, initializer } => 
                // self.collect_variable_type(name, *mutable, type_annotation, initializer),
            _ => {
                for child in node.children_mut() {
                    self.collect_node_type(child)?;
                }
                Ok(None)
            }
        };

        if let Ok(Some(type_id)) = declared_type_opt.clone() {
            node.type_id = Some(type_id);
        }

        declared_type_opt
    }

    // fn collect_variable_type(
    //     &mut self,
    //     name: &str, 
    //     mutable: bool, 
    //     type_annotation: &mut Option<BoxedAstNode>,
    //     initializer: &mut Option<BoxedAstNode>
    // ) -> Result<Option<Type>, BoxedError> {
    //     Ok(None)
    // }
}