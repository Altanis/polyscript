use crate::{backend::semantic_analyzer::{Obligation, ObligationCause, PrimitiveKind, TraitObligation, Type, TypeSymbolId, TypeSymbolKind, ValueSymbolKind}, frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, utils::{error::*, kind::{Operation, QualifierKind, ReferenceKind, Span}}};
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

    fn get_type_from_unconventional_unary_operator(&self, operator: Operation, operand: &mut BoxedAstNode) -> Result<Type, BoxedError> {
        Ok(Type { symbol: 0, generic_args: vec![], reference: ReferenceKind::Reference })
    }

    // fn get_type_from_unary_operation(&mut self, operator: Operation, operand: &mut BoxedAstNode, span: Span) -> Result<Type, BoxedError> {
    //     let type_id = self.associate_node_with_type(operand)?;
    //     // let type_name = self.symbol_table.get_type_name(type_id.symbol).to_string();

    //     let Some((trait_name, _)) = operator.to_trait_data() else {
    //         return self.get_type_from_unconventional_unary_operator(operator, operand);
    //     };

    //     let Some(trait_id) = self.symbol_table.find_type_symbol(&trait_name).map(|symbol| symbol.id) else {
    //         unreachable!();
    //     };

    //     let applicable_impl = self.trait_registry.find_applicable_impl(
    //         trait_id, 
    //         &type_id,
    //         self, 
    //         span
    //     )?;

    //     let impl_scope = self.symbol_table.get_scope(applicable_impl.impl_scope_id).unwrap();

    //     Ok(Type { symbol: 0, generic_args: vec![], reference: ReferenceKind::Reference })
    // }

    fn get_type_from_unary_operation(&mut self, operator: Operation, operand: &mut BoxedAstNode, span: Span) -> Result<Type, BoxedError> {
        /**
         *             Operation::FieldAccess => None,
            Operation::Dereference => None,
            Operation::ImmutableAddressOf => None,
            Operation::MutableAddressOf => None,
         */
        match operator {
            _ => {
                let operand_type = self.associate_node_with_type(operand)?;

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

                Ok(Type::new(type_symbol_id, vec![], ReferenceKind::Value))
            }
        }
    }

    fn associate_node_with_type(&mut self, node: &mut AstNode) -> Result<Type, BoxedError> {
        use AstNodeKind::*;

        if let Some(id) = &node.type_id {
            return Ok(id.clone());
        }

        let id = match &mut node.kind {
            IntegerLiteral(_) => Ok(Type::new(self.get_primitive_type(PrimitiveKind::Int), vec![], ReferenceKind::Value)),
            FloatLiteral(_) => Ok(Type::new(self.get_primitive_type(PrimitiveKind::Float), vec![], ReferenceKind::Value)),
            BooleanLiteral(_) => Ok(Type::new(self.get_primitive_type(PrimitiveKind::Bool), vec![], ReferenceKind::Value)),
            StringLiteral(_) => Ok(Type::new(self.get_primitive_type(PrimitiveKind::String), vec![], ReferenceKind::Value)),
            CharLiteral(_) => Ok(Type::new(self.get_primitive_type(PrimitiveKind::Char), vec![], ReferenceKind::Value)),
            Identifier(name) => self.get_type_from_identifier(name, node.span),
            UnaryOperation { operator, operand, .. } 
                => self.get_type_from_unary_operation(*operator, operand, node.span),
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
            VariableDeclaration { name, mutable, type_annotation, initializer } => 
                self.collect_variable_type(name, *mutable, type_annotation, initializer),
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

    fn collect_variable_type(
        &mut self,
        name: &str, 
        mutable: bool, 
        type_annotation: &mut Option<BoxedAstNode>,
        initializer: &mut Option<BoxedAstNode>
    ) -> Result<Option<Type>, BoxedError> {
        Ok(None)
    }
}