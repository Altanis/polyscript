use crate::{
    frontend::{
        semantics::analyzer::SemanticAnalyzer,
        syntax::ast::{AstNode, AstNodeKind},
    },
    mir::ir_node::{IRNode, IRNodeKind},
};

pub struct IRBuilder<'a> {
    analyzer: &'a SemanticAnalyzer,
}

impl<'a> IRBuilder<'a> {
    pub fn new(analyzer: &'a SemanticAnalyzer) -> Self {
        Self { analyzer }
    }

    pub fn build(&mut self, ast: &AstNode) -> Option<IRNode> {
        self.lower_node(ast)
    }

    fn lower_node(&mut self, node: &AstNode) -> Option<IRNode> {
        let kind = match &node.kind {
            AstNodeKind::IntegerLiteral(v) => IRNodeKind::IntegerLiteral(*v),
            AstNodeKind::FloatLiteral(v) => IRNodeKind::FloatLiteral(*v),
            AstNodeKind::BooleanLiteral(v) => IRNodeKind::BooleanLiteral(*v),
            AstNodeKind::StringLiteral(v) => IRNodeKind::StringLiteral(v.clone()),
            AstNodeKind::CharLiteral(v) => IRNodeKind::CharLiteral(*v),

            AstNodeKind::Identifier(name) => IRNodeKind::Identifier(name.clone()),
            AstNodeKind::SelfExpr => IRNodeKind::SelfExpr,
            AstNodeKind::HeapExpression(expr) => IRNodeKind::HeapExpression(Box::new(self.lower_node(expr)?)),
            AstNodeKind::ExpressionStatement(expr) => {
                IRNodeKind::ExpressionStatement(Box::new(self.lower_node(expr)?))
            }

            AstNodeKind::VariableDeclaration { name, mutable, initializer, .. } => {
                IRNodeKind::VariableDeclaration {
                    name: name.clone(),
                    mutable: *mutable,
                    initializer: Box::new(self.lower_node(initializer)?),
                }
            }

            AstNodeKind::UnaryOperation { operator, operand } => IRNodeKind::UnaryOperation {
                operator: *operator,
                operand: Box::new(self.lower_node(operand)?),
            },
            AstNodeKind::BinaryOperation { operator, left, right } => IRNodeKind::BinaryOperation {
                operator: *operator,
                left: Box::new(self.lower_node(left)?),
                right: Box::new(self.lower_node(right)?),
            },
            AstNodeKind::ConditionalOperation { operator, left, right } => {
                IRNodeKind::ConditionalOperation {
                    operator: *operator,
                    left: Box::new(self.lower_node(left)?),
                    right: Box::new(self.lower_node(right)?),
                }
            }

            AstNodeKind::TypeCast { expr, .. } => IRNodeKind::TypeCast {
                expr: Box::new(self.lower_node(expr)?),
                target_type: node.type_id.clone()?,
            },

            AstNodeKind::Block(stmts) => {
                IRNodeKind::Block(stmts.iter().filter_map(|s| self.lower_node(s)).collect())
            }
            AstNodeKind::IfStatement { condition, then_branch, else_if_branches, else_branch } => {
                IRNodeKind::IfStatement {
                    condition: Box::new(self.lower_node(condition)?),
                    then_branch: Box::new(self.lower_node(then_branch)?),
                    else_if_branches: else_if_branches
                        .iter()
                        .filter_map(|(c, b)| {
                            Some((Box::new(self.lower_node(c)?), Box::new(self.lower_node(b)?)))
                        })
                        .collect(),
                    else_branch: else_branch.as_ref().map(|b| Box::new(self.lower_node(b).unwrap())),
                }
            }
            AstNodeKind::WhileLoop { condition, body } => IRNodeKind::WhileLoop {
                condition: Box::new(self.lower_node(condition)?),
                body: Box::new(self.lower_node(body)?),
            },
            AstNodeKind::ForLoop { initializer, condition, increment, body } => {
                IRNodeKind::ForLoop {
                    initializer: initializer.as_ref().map(|n| Box::new(self.lower_node(n).unwrap())),
                    condition: condition.as_ref().map(|n| Box::new(self.lower_node(n).unwrap())),
                    increment: increment.as_ref().map(|n| Box::new(self.lower_node(n).unwrap())),
                    body: Box::new(self.lower_node(body)?),
                }
            }
            AstNodeKind::Return(expr) => {
                IRNodeKind::Return(expr.as_ref().map(|e| Box::new(self.lower_node(e).unwrap())))
            }
            AstNodeKind::Break => IRNodeKind::Break,
            AstNodeKind::Continue => IRNodeKind::Continue,

            AstNodeKind::Function { name, parameters, instance, body, generic_parameters, .. } => {
                if !generic_parameters.is_empty() {
                    return None;
                }

                IRNodeKind::Function {
                    name: name.clone(),
                    parameters: parameters.iter().filter_map(|p| self.lower_node(p)).collect(),
                    instance: *instance,
                    body: body.as_ref().map(|b| Box::new(self.lower_node(b).unwrap())),
                }
            }
            AstNodeKind::FunctionParameter { name, mutable, .. } => IRNodeKind::FunctionParameter {
                name: name.clone(),
                mutable: *mutable,
            },
            AstNodeKind::FunctionCall { function, arguments } => IRNodeKind::FunctionCall {
                function: Box::new(self.lower_node(function)?),
                arguments: arguments.iter().filter_map(|a| self.lower_node(a)).collect(),
            },
            AstNodeKind::FieldAccess { left, right } => IRNodeKind::FieldAccess {
                left: Box::new(self.lower_node(left)?),
                right: Box::new(self.lower_node(right)?),
            },

            AstNodeKind::StructDeclaration { name, fields, generic_parameters } => {
                if !generic_parameters.is_empty() {
                    return None;
                }

                IRNodeKind::StructDeclaration {
                    name: name.clone(),
                    fields: fields.iter().filter_map(|f| self.lower_node(f)).collect(),
                }
            }
            AstNodeKind::StructField { name, .. } => IRNodeKind::StructField { name: name.clone() },
            AstNodeKind::StructLiteral { fields, .. } => {
                let concrete_struct_type = node.type_id.as_ref().unwrap();
                let mangled_name = self.analyzer.symbol_table.display_type(concrete_struct_type);

                IRNodeKind::StructLiteral {
                    name: mangled_name,
                    fields: fields
                        .iter()
                        .map(|(k, v)| (k.clone(), self.lower_node(v).unwrap()))
                        .collect(),
                }
            }

            AstNodeKind::EnumDeclaration { name, variants } => IRNodeKind::EnumDeclaration {
                name: name.clone(),
                variants: variants
                    .iter()
                    .map(|(k, (v, e))| {
                        (
                            k.clone(),
                            (self.lower_node(v).unwrap(), e.as_ref().map(|expr| self.lower_node(expr).unwrap())),
                        )
                    })
                    .collect(),
            },
            AstNodeKind::EnumVariant(name) => IRNodeKind::EnumVariant(name.clone()),

            AstNodeKind::Program(stmts) => {
                IRNodeKind::Program(stmts.iter().filter_map(|s| self.lower_node(s)).collect())
            }

            AstNodeKind::ImplDeclaration { .. }
            | AstNodeKind::TraitDeclaration { .. }
            | AstNodeKind::TypeDeclaration { .. }
            | AstNodeKind::AssociatedConstant { .. }
            | AstNodeKind::AssociatedType { .. }
            | AstNodeKind::TraitConstant { .. }
            | AstNodeKind::TraitType(_)
            | AstNodeKind::PathQualifier { .. }
            | AstNodeKind::TypeReference { .. }
            | AstNodeKind::FunctionPointer { .. }
            | AstNodeKind::SelfType(_)
            | AstNodeKind::GenericParameter { .. } => return None,
        };

        Some(IRNode {
            kind,
            span: node.span,
            value_id: node.value_id,
            type_id: node.type_id.clone(),
        })
    }
}

/*
1. associate astnodes with ids
2. traverse ast, find sites for monomorphization
3. build ir tree, for template nodes lookup monomorphs and implement
*/