use std::rc::Rc;
use crate::utils::{error::*, kind::*};

use crate::frontend::ast::{AstNode, AstNodeKind};



impl SemanticAnalyzer {
    fn primitive_type(&self, name: &str) -> TypeInfo {
        TypeInfo::new(name, vec![], ReferenceKind::Value)
    }

    fn lookup_symbol(&self, name: &str, span: Span) -> Result<&Symbol, BoxedError> {
        self.symbol_table.find_symbol(name).ok_or_else(|| {
            self.create_error(
                ErrorKind::UnknownVariable(name.to_string()),
                span,
                &[span],
            )
        })
    }

    fn resolve_expression_pair(
        &self,
        left: &mut AstNode,
        right: &mut AstNode,
    ) -> Result<TypeInfo, BoxedError> {
        let lhs = self.annotate_node(left)?.0;
        let rhs = self.annotate_node(right)?.0;

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
                    |e| self.annotate_node(e).map(|(t, _)| t),
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
        let then_type = self.annotate_node(then_branch)?;
        let else_type = else_branch.as_mut().map_or_else(
            || Ok(then_type.clone()),
            |else_node| self.annotate_node(else_node)
        )?;

        if then_type.0 != else_type.0 {
            return Err(self.create_error(
                ErrorKind::MismatchedTypes(then_type.0, else_type.0),
                else_branch.as_ref().unwrap().span,
                &[then_branch.span, else_branch.as_ref().unwrap().span]
            ));
        }

        for (_, branch) in else_if_branches {
            let branch_type = self.annotate_node(branch)?;
            if branch_type.0 != then_type.0 {
                return Err(self.create_error(
                    ErrorKind::MismatchedTypes(then_type.clone().0, branch_type.0),
                    branch.span,
                    &[then_branch.span, branch.span]
                ));
            }
        }

        Ok(then_type.0)
    }

    fn resolve_function_type(
        &self,
        parameters: &mut [AstNode],
        return_type: &mut Option<BoxedAstNode>,
    ) -> Result<TypeInfo, BoxedError> {
        let params = parameters
            .iter_mut()
            .map(|p| self.annotate_node(p).map(|(t, _)| t))
            .collect::<Result<Vec<_>, _>>()?;

        let return_ty = match return_type {
            Some(rt) => self.annotate_node(rt)?.0,
            None => self.primitive_type(NULL_TYPE),
        };

        Ok(TypeInfo::from_function_expression(
            vec![],
            FunctionTypeData {
                params,
                return_type: Box::new(return_ty),
            },
            ReferenceKind::Value,
        ))
    }

    fn annotate_node(&self, node: &mut AstNode) -> Result<(TypeInfo, Option<Symbol>), BoxedError> {
        use AstNodeKind::*;

        let (type_info, symbol) = match &mut node.kind {
            IntegerLiteral(_) => (self.primitive_type(INT_TYPE), None),
            FloatLiteral(_) => (self.primitive_type(FLOAT_TYPE), None),
            BooleanLiteral(_) => (self.primitive_type(BOOL_TYPE), None),
            StringLiteral(_) => (self.primitive_type(STRING_TYPE), None),
            CharLiteral(_) => (self.primitive_type(CHAR_TYPE), None),
            ConditionalOperation { .. } => (self.primitive_type(BOOL_TYPE), None),

            Identifier(name) => {
                let symbol = self.lookup_symbol(name, node.span)?;
                (symbol.type_info.clone(), Some(symbol.clone()))
            }

            UnaryOperation { operand, .. } => (self.annotate_node(operand)?.0, None),
            BinaryOperation { left, right, .. } => (self.resolve_expression_pair(left, right)?, None),

            Block(stmts) => (self.resolve_returns(stmts)?, None),

            IfStatement { then_branch, else_if_branches, else_branch, .. } => {
                (self.resolve_if_statement(then_branch, else_if_branches, else_branch)?, None)
            }

            FunctionExpression { signature, .. } => {
                let (params, return_type) = match &mut signature.kind {
                    FunctionSignature { parameters, return_type, .. } => (parameters, return_type),
                    _ => unreachable!("Invalid AST structure"),
                };
                (self.resolve_function_type(params, return_type)?, None)
            }

            FunctionPointer { params, return_type } => {
                (self.resolve_function_type(params, return_type)?, None)
            }

            TypeReference { type_name, generic_types } => {
                let generic_params = generic_types
                    .iter_mut()
                    .map(|gt| self.annotate_node(gt).map(|(t, _)| t))
                    .collect::<Result<_, _>>()?;

                let type_info = TypeInfo::new(
                    type_name.clone(),
                    generic_params,
                    ReferenceKind::Value,
                );

                let symbol = self.symbol_table.find_symbol(type_name).cloned();
                (type_info, symbol)
            }

            // structliteral, selfvalue, fieldaccess, function call

            _ => return Err(self.create_error(ErrorKind::UnknownType, node.span, &[node.span])),
        };

        node.ty = Some(type_info.clone());
        node.symbol = symbol.clone();

        Ok((type_info, symbol))
    }
}

impl SemanticAnalyzer {
    pub fn analyze(&mut self, mut program: AstNode) -> Result<AstNode, Vec<Error>> {
        // PASS 1: TYPE/SYMBOL COLLECTION //
        let AstNodeKind::Program(ref mut stmts) = program.kind else { unreachable!(); };
        for stmt in stmts {
            if let Err(e) = self.visit_node(stmt) {
                self.errors.push(*e);
            }
        }

        if !self.errors.is_empty() {
            return Err(self.errors.clone());
        }

        // PASS 2: NODE ANNOTATION //

        Ok(program)
    }

    pub fn visit_node(&mut self, node: &mut AstNode) -> Result<(), BoxedError> {
        // forloop, while loop, function declaration, struct declaration, enum declaration
        match &mut node.kind {
            AstNodeKind::VariableDeclaration { mutable, name, type_annotation, initializer }
                => self.visit_variable_declaration_node(*mutable, name.clone(), type_annotation, initializer, node.span),

            _ => self.annotate_node(node).map(|_| ())
        }
    }

    fn visit_variable_declaration_node(&mut self, mutable: bool, name: String, type_annotation: &mut Option<BoxedAstNode>, initializer: &mut Option<BoxedAstNode>, span: Span) -> Result<(), BoxedError> {
        let annotation_info = type_annotation.as_mut().map(|ty| self.annotate_node(ty));
        let initializer_info = initializer.as_mut().map(|ty| self.annotate_node(ty));

        let type_info = match (annotation_info, initializer_info) {
            (None, None) => {
                return Err(self.create_error(
                    ErrorKind::BadVariableDeclaration,
                    span,
                    &[span],
                ));
            }

            (Some(ann_res), None) => ann_res?.0,
            (None, Some(init_res)) => init_res?.0,

            (Some(ann_res), Some(init_res)) => {
                let ann = ann_res?.0;
                let init = init_res?.0;

                if ann != init {
                    return Err(self.create_error(
                        ErrorKind::MismatchedTypes(ann, init),
                        span,
                        &[span],
                    ));
                }

                ann
            }
        };

        self.symbol_table.add_symbol(Symbol {
            name,
            kind: SymbolKind::Variable,
            type_info,
            mutable,
            span,
            public: None,
            generic_parameters: vec![]
        })
    }
}