use crate::{frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, utils::{error::*, kind::*}};
use super::semantic_analyzer::{FunctionTypeData, ReferenceKind, SemanticAnalyzer, TypeInfo};

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
        &self,
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

    fn resolve_returns(
        &self,
        stmts: &mut [AstNode],
    ) -> Result<TypeInfo, BoxedError> {
        let mut return_type: Option<TypeInfo> = None;
        
        for stmt in stmts {
            if let AstNodeKind::Return(expr) = &mut stmt.kind {
                let ty = expr.as_mut().map_or_else(
                    || Ok(self.primitive_type(NULL_TYPE)),
                    |e| self.get_type_from_node(e),
                )?;

                if let Some(existing) = &return_type {
                    if existing != &ty {
                        return Err(self.create_error(
                            ErrorKind::MismatchedTypes(existing.clone(), ty),
                            stmt.span,
                            &[stmt.span],
                        ));
                    }
                } else {
                    return_type = Some(ty);
                }
            }
        }

        Ok(return_type.unwrap_or_else(|| self.primitive_type(NULL_TYPE)))
    }

    fn resolve_if_statement(
        &self,
        then_branch: &mut AstNode,
        else_if_branches: &mut [(BoxedAstNode, BoxedAstNode)],
        else_branch: &mut Option<BoxedAstNode>
    ) -> Result<TypeInfo, BoxedError> {
        let then_type = self.get_type_from_node(then_branch)?;
        let else_type = else_branch.as_mut().map_or_else(
            || Ok(then_type.clone()),
            |else_node| self.get_type_from_node(else_node)
        )?;

        if then_type != else_type {
            return Err(self.create_error(
                ErrorKind::MismatchedTypes(then_type, else_type),
                else_branch.as_ref().unwrap().span,
                &[then_branch.span, else_branch.as_ref().unwrap().span]
            ));
        }

        for (_, branch) in else_if_branches {
            let branch_type = self.get_type_from_node(branch)?;
            if branch_type != then_type {
                return Err(self.create_error(
                    ErrorKind::MismatchedTypes(then_type.clone(), branch_type),
                    branch.span,
                    &[then_branch.span, branch.span]
                ));
            }
        }

        Ok(then_type)
    }

    // fn resolve_fn_expr(&self, signature: &mut BoxedAstNode) -> Result<TypeInfo, BoxedError> {
    //     let AstNodeKind::FunctionSignature { generic_parameters, parameters, return_type, .. } = &mut signature.kind else {
    //         panic!("fnexpr does not hold FunctionSignature node");
    //     };

    //     let resolved_generics: Vec<TypeInfo> = generic_parameters
    //         .iter_mut()
    //         .map(|node| self.get_type_from_node(node))
    //         .collect::<Result<_, _>>()?;

    //     let resolved_parameters: Vec<TypeInfo> = parameters
    //         .iter_mut()
    //         .map(|node| self.get_type_from_node(node))
    //         .collect::<Result<_, _>>()?;

    //     let resolved_return_type: Option<Box<TypeInfo>> = match return_type {
    //         Some(node) => Some(Box::new(self.get_type_from_node(node)?)),
    //         None => None,
    //     };

    //     Ok(TypeInfo::from_function_expression(
    //         resolved_generics,
    //         FunctionTypeData {
    //             params: resolved_parameters,
    //             return_type: resolved_return_type,
    //         }
    //     ))
    // }

    fn get_type_from_node(&self, node: &mut AstNode) -> Result<TypeInfo, BoxedError> {
        use AstNodeKind::*;

        match &mut node.kind {
            IntegerLiteral(_) => Ok(self.primitive_type(INT_TYPE)),
            FloatLiteral(_) => Ok(self.primitive_type(FLOAT_TYPE)),
            BooleanLiteral(_) => Ok(self.primitive_type(BOOL_TYPE)),
            StringLiteral(_) => Ok(self.primitive_type(STRING_TYPE)),
            CharLiteral(_) => Ok(self.primitive_type(CHAR_TYPE)),
            Identifier(name) => self.lookup_type_from_symbol(name, node.span),
            Block(statements) => self.resolve_returns(statements),
            IfStatement { then_branch, else_if_branches, else_branch, .. }
                => self.resolve_if_statement(then_branch, else_if_branches, else_branch),
            _ => return Err(self.create_error(ErrorKind::UnknownType, node.span, &[node.span])),
        }
    }

    fn associate_node_with_type(&mut self, node: &mut AstNode, type_info: TypeInfo) {
        node.ty = Some(type_info.clone());
        if let Some((scope_id, name)) = &node.symbol {
            if let Some(sym) = self.symbol_table.direct_symbol_lookup(*scope_id, name) {
                sym.type_info = Some(type_info);
            }
        }
    }
}

impl SemanticAnalyzer {
    pub fn type_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
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