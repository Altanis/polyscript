use crate::{frontend::ast::{AstNode, AstNodeKind}, utils::{error::*, kind::*}};

use super::semantic_analyzer::{ReferenceKind, SemanticAnalyzer, Symbol, TypeInfo};

impl SemanticAnalyzer {
    fn primitive_type(&self, name: &str) -> TypeInfo {
        TypeInfo::new(name, vec![], ReferenceKind::Value)
    }

    fn lookup_type_from_symbol(&self, name: &str, span: Span) -> Result<TypeInfo, BoxedError> {
        match self.symbol_table.current_scope().find_symbol(name, &self.symbol_table) {
            Some(symbol) => {
                match &symbol.type_info {
                    Some(ty) => Ok(ty.clone()),
                    None => Err(self.create_error(
                        ErrorKind::UnresolvedType(name.to_string()),
                        span,
                        &[span],
                    ))
                }
            },
            None => Err(self.create_error(
                ErrorKind::UnknownVariable(name.to_string()),
                span,
                &[span],
            ))
        }
    }

    fn resolve_expression_pair(
        &mut self,
        left: &mut AstNode,
        right: &mut AstNode,
    ) -> Result<TypeInfo, BoxedError> {
        let lhs = self.get_type_from_node(left)?;
        let rhs = self.get_type_from_node(right)?;

        if lhs != rhs {
            Err(self.create_error(
                ErrorKind::MismatchedTypes(lhs, rhs),
                right.span,
                &[left.span, right.span],
            ))
        } else {
            Ok(lhs)
        }
    }

    fn get_type_from_node(&mut self, node: &mut AstNode) -> Result<TypeInfo, BoxedError> {
        use AstNodeKind::*;

        match &mut node.kind {
            IntegerLiteral(_) => Ok(self.primitive_type(INT_TYPE)),
            FloatLiteral(_) => Ok(self.primitive_type(FLOAT_TYPE)),
            BooleanLiteral(_) => Ok(self.primitive_type(BOOL_TYPE)),
            StringLiteral(_) => Ok(self.primitive_type(STRING_TYPE)),
            CharLiteral(_) => Ok(self.primitive_type(CHAR_TYPE)),
            Identifier(name) => self.lookup_type_from_symbol(name, node.span),
            ConditionalOperation { .. } => Ok(self.primitive_type(BOOL_TYPE)),
            UnaryOperation { operand, .. } => self.get_type_from_node(operand),
            BinaryOperation { left, right, .. } => self.resolve_expression_pair(left, right),
            _ => return Err(self.create_error(ErrorKind::UnknownType, node.span, &[node.span])),
        }
    }
}

impl SemanticAnalyzer {
    pub fn type_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let errors: Vec<Error> = vec![];

        let mut errors = vec![];

        let AstNodeKind::Program(statements) = &mut program.kind else { panic!("fed node that is not a Program"); };
        for statement in statements {
            match self.solve_type(statement) {
                Ok(ty) => statement.ty = ty,
                Err(err) => errors.push(*err),
            }
        }

        errors
    }

    fn solve_type(&mut self, statement: &mut AstNode) -> Result<Option<TypeInfo>, BoxedError> {
        match &mut statement.kind {
            _ => Ok(None)
        }
    }
}