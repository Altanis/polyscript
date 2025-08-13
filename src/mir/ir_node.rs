use std::fmt::Write;

use crate::{
    frontend::semantics::analyzer::{PrimitiveKind, SymbolTable, Type, TypeSymbolKind, ValueSymbolId},
    utils::kind::*,
};
use colored::Colorize;
use indexmap::IndexMap;

#[derive(Debug, Clone)]
pub enum IRNodeKind {
    IntegerLiteral(i64),
    FloatLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(String),
    CharLiteral(char),

    Identifier(String),
    VariableDeclaration {
        name: String,
        mutable: bool,
        initializer: Box<IRNode>,
    },

    UnaryOperation {
        operator: Operation,
        operand: Box<IRNode>,
    },
    BinaryOperation {
        operator: Operation,
        left: Box<IRNode>,
        right: Box<IRNode>,
    },
    ConditionalOperation {
        operator: Operation,
        left: Box<IRNode>,
        right: Box<IRNode>,
    },
    HeapExpression(Box<IRNode>),

    TypeCast {
        expr: Box<IRNode>,
        target_type: Type
    },

    Block(Vec<IRNode>),
    IfStatement {
        condition: Box<IRNode>,
        then_branch: Box<IRNode>,
        else_if_branches: Vec<(Box<IRNode>, Box<IRNode>)>,
        else_branch: Option<Box<IRNode>>,
    },
    ForLoop {
        initializer: Option<Box<IRNode>>,
        condition: Option<Box<IRNode>>,
        increment: Option<Box<IRNode>>,
        body: Box<IRNode>,
    },
    WhileLoop {
        condition: Box<IRNode>,
        body: Box<IRNode>,
    },
    Return(Option<Box<IRNode>>),
    Break,
    Continue,

    Function {
        name: String,
        parameters: Vec<IRNode>,
        instance: Option<ReferenceKind>,
        body: Option<Box<IRNode>>,
    },
    FunctionParameter {
        name: String,
        mutable: bool,
    },

    StructDeclaration {
        name: String,
        fields: Vec<IRNode>
    },
    StructField {
        name: String,
    },
    StructLiteral {
        name: String,
        fields: IndexMap<String, IRNode>
    },

    EnumDeclaration {
        name: String,
        variants: IndexMap<String, (IRNode, Option<IRNode>)>,
    },
    EnumVariant(String),

    SelfExpr,

    FieldAccess {
        left: Box<IRNode>,
        right: Box<IRNode>,
    },
    FunctionCall {
        function: Box<IRNode>,
        arguments: Vec<IRNode>,
    },

    ExpressionStatement(Box<IRNode>),

    Program(Vec<IRNode>),
}

#[derive(Debug, Clone)]
pub struct IRNode {
    pub kind: IRNodeKind,
    pub span: Span,
    pub value_id: Option<ValueSymbolId>,
    pub type_id: Option<Type>
}

impl std::fmt::Display for IRNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_with_indent(f, 0, None)
    }
}

impl IRNode {
    pub fn fmt_with_indent<W: Write>(
        &self,
        f: &mut W,
        indent: usize,
        table: Option<&SymbolTable>,
    ) -> std::fmt::Result {
        let indent_str = " ".repeat(indent);
        let child_indent = indent + 4;

        match &self.kind {
            IRNodeKind::Program(nodes) => {
                let header = format!(
                    "{} ({} top-level items)",
                    "IR Program".bright_blue().bold(),
                    nodes.len()
                );
                writeln!(f, "{}", header)?;
                for node in nodes {
                    node.fmt_with_indent(f, child_indent, table)?;
                    writeln!(f)?;
                }
            }
            IRNodeKind::IntegerLiteral(val) => write!(f, "{}{}", indent_str, val.to_string().blue())?,
            IRNodeKind::FloatLiteral(val) => write!(f, "{}{}", indent_str, val.to_string().blue())?,
            IRNodeKind::BooleanLiteral(val) => {
                write!(f, "{}{}", indent_str, val.to_string().magenta())?
            }
            IRNodeKind::StringLiteral(s) => {
                write!(f, "{}{}", indent_str, format!("\"{s}\"").green())?
            }
            IRNodeKind::CharLiteral(c) => write!(f, "{}\'{}\'", indent_str, c.to_string().red())?,
            IRNodeKind::Identifier(name) => write!(f, "{}{}", indent_str, name.yellow())?,
            IRNodeKind::VariableDeclaration {
                name,
                mutable,
                initializer,
            } => {
                write!(f, "{}", indent_str)?;
                let decl_type = if *mutable {
                    "let".bright_green()
                } else {
                    "const".green()
                };
                write!(f, "{} {}", decl_type, name.yellow())?;
                write!(f, " = ")?;
                initializer.fmt_with_indent(f, 0, table)?;
            }
            IRNodeKind::UnaryOperation { operator, operand } => {
                write!(f, "{}(", indent_str)?;
                write!(f, "{}", operator)?;
                operand.fmt_with_indent(f, 0, table)?;
                write!(f, ")")?;
            }
            IRNodeKind::BinaryOperation {
                operator,
                left,
                right,
            } => {
                write!(f, "{}(", indent_str)?;
                left.fmt_with_indent(f, 0, table)?;
                write!(f, " {} ", operator)?;
                right.fmt_with_indent(f, 0, table)?;
                write!(f, ")")?;
            }
            IRNodeKind::ConditionalOperation {
                operator,
                left,
                right,
            } => {
                write!(f, "{}(", indent_str)?;
                left.fmt_with_indent(f, 0, table)?;
                write!(f, " {} ", operator)?;
                right.fmt_with_indent(f, 0, table)?;
                write!(f, ")")?;
            }
            IRNodeKind::HeapExpression(expr) => {
                write!(f, "{}heap ", indent_str)?;
                expr.fmt_with_indent(f, 0, table)?;
            }
            IRNodeKind::TypeCast { expr, target_type } => {
                write!(f, "{}(", indent_str)?;
                expr.fmt_with_indent(f, 0, table)?;
                write!(f, " {} ", "as".yellow())?;
                if let Some(t) = table {
                    write!(f, "{}", t.display_type(target_type).bright_blue())?;
                } else {
                    write!(f, "{}", target_type.to_string().bright_blue())?;
                }
                write!(f, ")")?;
            }

            IRNodeKind::Block(nodes) => {
                write!(f, "{}", "{".dimmed())?;
                if !nodes.is_empty() {
                    writeln!(f)?;
                    for node in nodes {
                        node.fmt_with_indent(f, child_indent, table)?;
                        writeln!(f)?;
                    }
                    write!(f, "{}", indent_str)?;
                }
                write!(f, "{}", "}".dimmed())?;
            }

            IRNodeKind::Function {
                name,
                parameters,
                body,
                ..
            } => {
                write!(f, "{}", indent_str)?;
                write!(
                    f,
                    "{} {}",
                    "fn".bright_blue(),
                    if name.is_empty() {
                        "".white()
                    } else {
                        name.yellow()
                    }
                )?;

                write!(f, "(")?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    param.fmt_with_indent(f, 0, table)?;
                }
                write!(f, ")")?;

                if let Some(b) = body {
                    write!(f, " ")?;
                    b.fmt_with_indent(f, indent, table)?;
                } else {
                    write!(f, ";")?;
                }
            }

            IRNodeKind::SelfExpr => write!(f, "{}self", indent_str)?,

            IRNodeKind::IfStatement {
                condition,
                then_branch,
                else_if_branches,
                else_branch,
            } => {
                write!(f, "{}if ", indent_str)?;
                condition.fmt_with_indent(f, 0, table)?;
                write!(f, " ")?;
                then_branch.fmt_with_indent(f, indent, table)?;

                for (cond, branch) in else_if_branches {
                    write!(f, " else if ")?;
                    cond.fmt_with_indent(f, 0, table)?;
                    write!(f, " ")?;
                    branch.fmt_with_indent(f, indent, table)?;
                }

                if let Some(else_node) = else_branch {
                    write!(f, " else ")?;
                    else_node.fmt_with_indent(f, indent, table)?;
                }
            }

            IRNodeKind::ForLoop {
                initializer,
                condition,
                increment,
                body,
            } => {
                write!(f, "{}for (", indent_str)?;
                if let Some(init) = initializer {
                    init.fmt_with_indent(f, 0, table)?;
                }
                write!(f, "; ")?;
                if let Some(cond) = condition {
                    cond.fmt_with_indent(f, 0, table)?;
                }
                write!(f, "; ")?;
                if let Some(inc) = increment {
                    inc.fmt_with_indent(f, 0, table)?;
                }
                write!(f, ") ")?;
                body.fmt_with_indent(f, indent, table)?;
            }

            IRNodeKind::WhileLoop { condition, body } => {
                write!(f, "{}while (", indent_str)?;
                condition.fmt_with_indent(f, 0, table)?;
                write!(f, ") ")?;
                body.fmt_with_indent(f, indent, table)?;
            }

            IRNodeKind::Return(Some(expr)) => {
                write!(f, "{}return ", indent_str)?;
                expr.fmt_with_indent(f, 0, table)?;
            }
            IRNodeKind::Return(None) => write!(f, "{}return", indent_str)?,
            IRNodeKind::Break => write!(f, "{}break", indent_str)?,
            IRNodeKind::Continue => write!(f, "{}continue", indent_str)?,

            IRNodeKind::FunctionParameter { name, mutable } => {
                write!(f, "{}", indent_str)?;
                write!(
                    f,
                    "{}{}",
                    if *mutable { "mut ".purple() } else { "".white() },
                    name.yellow(),
                )?;
            }

            IRNodeKind::StructDeclaration { name, fields } => {
                write!(f, "{}struct {}", indent_str, name.yellow())?;
                writeln!(f, " {}", "{".dimmed())?;

                for field in fields {
                    field.fmt_with_indent(f, child_indent, table)?;
                    writeln!(f)?;
                }

                write!(f, "{}{}", indent_str, "}".dimmed())?;
            }
            IRNodeKind::StructField { name } => {
                write!(f, "{}", indent_str)?;
                write!(f, "{}", name.yellow())?;
            }
            IRNodeKind::StructLiteral { name, fields } => {
                write!(f, "{}{}{}", indent_str, name.yellow(), " ".dimmed())?;
                write!(f, "{}", "{".dimmed())?;

                let mut first = true;
                for (field_name, expr) in fields.iter() {
                    if !first {
                        write!(f, ",")?;
                    }
                    first = false;

                    write!(f, " ")?;
                    write!(f, "{}: ", field_name.yellow())?;
                    expr.fmt_with_indent(f, 0, table)?;
                }

                if !fields.is_empty() {
                    write!(f, " ")?;
                }
                write!(f, "{}", "}".dimmed())?;
            }
            IRNodeKind::EnumDeclaration { name, variants } => {
                write!(f, "{}enum {}", indent_str, name.yellow())?;
                writeln!(f, " {}", "{".dimmed())?;

                for (_, (variant, expr)) in variants {
                    variant.fmt_with_indent(f, child_indent, table)?;

                    if let Some(expr) = expr {
                        write!(f, " = ")?;
                        expr.fmt_with_indent(f, 0, table)?;
                    }
                    writeln!(f, ",")?;
                }

                write!(f, "{}{}", indent_str, "}".dimmed())?;
            }
            IRNodeKind::EnumVariant(name) => write!(f, "{}", name)?,

            IRNodeKind::FieldAccess { left, right } => {
                write!(f, "{}(", indent_str)?;
                left.fmt_with_indent(f, 0, table)?;
                write!(f, ".")?;
                right.fmt_with_indent(f, 0, table)?;
                write!(f, ")")?;
            }
            IRNodeKind::FunctionCall {
                function,
                arguments,
            } => {
                write!(f, "{}", indent_str)?;
                function.fmt_with_indent(f, 0, table)?;
                write!(f, "(")?;
                for (i, param) in arguments.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    param.fmt_with_indent(f, 0, table)?;
                }
                write!(f, ")")?;
            }

            IRNodeKind::ExpressionStatement(expr) => {
                expr.fmt_with_indent(f, indent, table)?;
                write!(f, ";")?;
            }
        }

        if let (Some(ty), Some(table)) = (&self.type_id, table) {
            if let Some(type_symbol) = table.get_type_symbol(ty.get_base_symbol())
                && matches!(type_symbol.kind, TypeSymbolKind::Primitive(PrimitiveKind::Void | PrimitiveKind::Never))
            {
                return Ok(());
            }

            let type_str = table.display_type(ty);
            write!(f, " {}", format!("<{}>", type_str).cyan())?;
        } else if let Some(ty) = &self.type_id {
            if ty.get_base_symbol() == PrimitiveKind::Void as usize
                || ty.get_base_symbol() == PrimitiveKind::Never as usize
            {
                return Ok(());
            }

            write!(f, " {}", format_args!("[{}]", ty))?;
        }

        if let Some(id) = self.value_id {
            write!(f, " {}", format!("[Symbol({})]", id).dimmed())?;
        }

        Ok(())
    }
}