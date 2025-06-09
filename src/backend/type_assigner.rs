use crate::{backend::semantic_analyzer::{PrimitiveKind, TypeSymbolId}, frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, utils::{error::*, kind::Span}};
use super::semantic_analyzer::SemanticAnalyzer;

impl SemanticAnalyzer {
    fn get_builtin_type(&self, builtin: PrimitiveKind) -> TypeSymbolId {
        self.builtins[builtin as usize]
    }

    fn get_type_from_identifier(&self, name: &str, span: Span) -> Result<TypeSymbolId, BoxedError> {
        match self.symbol_table.find_value_symbol(name) {
            Some(value_symbol) => {
                match value_symbol.type_id {
                    Some(type_id) => Ok(type_id),
                    None => Err(self.create_error(ErrorKind::UnresolvedType(name.to_string()), span, &[span]))
                }
            },
            None => Err(self.create_error(ErrorKind::UnknownVariable(name.to_string()), span, &[span]))
        }
    }

    // fn get_type_from_unary_operation(&self, operator: Operation, operand: &mut BoxedAstNode) -> Result<TypeSymbolId, BoxedError> {
    //     let operand_type_id = self.associate_node_with_type(operand)?;
    //     ...
    // }

    fn associate_node_with_type(&mut self, node: &mut AstNode) -> Result<TypeSymbolId, BoxedError> {
        use AstNodeKind::*;

        if let Some(id) = node.type_id {
            return Ok(id);
        }

        let id = match &mut node.kind {
            IntegerLiteral(_) => Ok(self.get_builtin_type(PrimitiveKind::Int)),
            FloatLiteral(_) => Ok(self.get_builtin_type(PrimitiveKind::Float)),
            BooleanLiteral(_) => Ok(self.get_builtin_type(PrimitiveKind::Bool)),
            StringLiteral(_) => Ok(self.get_builtin_type(PrimitiveKind::String)),
            CharLiteral(_) => Ok(self.get_builtin_type(PrimitiveKind::Char)),
            Identifier(name) => self.get_type_from_identifier(name, node.span),
            // UnaryOperation { operator, operand, .. } 
                // => self.get_type_from_unary_operation(*operator, operand),
            _ => Err(self.create_error(ErrorKind::UnknownType, node.span, &[node.span])),
        }?;

        node.type_id = Some(id);
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

    fn collect_node_type(&mut self, node: &mut AstNode) -> Result<Option<TypeSymbolId>, BoxedError> {
        use AstNodeKind::*;
        
        let declared_type_opt: Result<Option<TypeSymbolId>, BoxedError> = match &mut node.kind {
            VariableDeclaration { name, mutable, type_annotation, initializer } => 
                self.collect_variable_type(name, *mutable, type_annotation, initializer),
            _ => {
                for child in node.children_mut() {
                    self.collect_node_type(child)?;
                }
                Ok(None)
            }
        };

        if let Ok(Some(type_id)) = declared_type_opt {
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
    ) -> Result<Option<TypeSymbolId>, BoxedError> {
        Ok(None)
    }
}