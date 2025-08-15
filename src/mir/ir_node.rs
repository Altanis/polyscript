use std::fmt::Write;

use crate::{
    frontend::semantics::analyzer::{PrimitiveKind, SymbolTable, Type, TypeSymbolKind, ValueSymbolId},
    utils::kind::*,
};
use colored::Colorize;
use indexmap::IndexMap;

#[derive(Debug, Clone)]
pub enum MIRNodeKind {
    IntegerLiteral(i64),
    FloatLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(String),
    CharLiteral(char),

    Identifier(String),
    VariableDeclaration {
        name: String,
        mutable: bool,
        initializer: Box<MIRNode>,
    },

    UnaryOperation {
        operator: Operation,
        operand: Box<MIRNode>,
    },
    BinaryOperation {
        operator: Operation,
        left: Box<MIRNode>,
        right: Box<MIRNode>,
    },
    ConditionalOperation {
        operator: Operation,
        left: Box<MIRNode>,
        right: Box<MIRNode>,
    },
    HeapExpression(Box<MIRNode>),

    TypeCast {
        expr: Box<MIRNode>,
        target_type: Type
    },

    Block(Vec<MIRNode>),
    IfStatement {
        condition: Box<MIRNode>,
        then_branch: Box<MIRNode>,
        else_if_branches: Vec<(Box<MIRNode>, Box<MIRNode>)>,
        else_branch: Option<Box<MIRNode>>,
    },
    ForLoop {
        initializer: Option<Box<MIRNode>>,
        condition: Option<Box<MIRNode>>,
        increment: Option<Box<MIRNode>>,
        body: Box<MIRNode>,
    },
    WhileLoop {
        condition: Box<MIRNode>,
        body: Box<MIRNode>,
    },
    Return(Option<Box<MIRNode>>),
    Break,
    Continue,

    Function {
        name: String,
        parameters: Vec<MIRNode>,
        instance: Option<ReferenceKind>,
        body: Option<Box<MIRNode>>,
    },
    FunctionParameter {
        name: String,
        mutable: bool,
    },

    StructDeclaration {
        name: String,
        fields: Vec<MIRNode>
    },
    StructField {
        name: String,
    },
    StructLiteral {
        name: String,
        fields: IndexMap<String, MIRNode>
    },

    EnumDeclaration {
        name: String,
        variants: IndexMap<String, (MIRNode, Option<MIRNode>)>,
    },
    EnumVariant(String),

    SelfExpr,

    FieldAccess {
        left: Box<MIRNode>,
        right: Box<MIRNode>,
    },
    FunctionCall {
        function: Box<MIRNode>,
        arguments: Vec<MIRNode>,
    },

    ExpressionStatement(Box<MIRNode>),

    Program(Vec<MIRNode>),
}

#[derive(Debug, Clone)]
pub struct MIRNode {
    pub kind: MIRNodeKind,
    pub span: Span,
    pub value_id: Option<ValueSymbolId>,
    pub type_id: Option<Type>
}

impl std::fmt::Display for MIRNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_with_indent(f, 0, None)
    }
}

impl MIRNode {
    pub fn fmt_with_indent<W: Write>(
        &self,
        f: &mut W,
        indent: usize,
        table: Option<&SymbolTable>,
    ) -> std::fmt::Result {
        let indent_str = " ".repeat(indent);
        let child_indent = indent + 4;

        match &self.kind {
            MIRNodeKind::Program(nodes) => {
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
            MIRNodeKind::IntegerLiteral(val) => write!(f, "{}{}", indent_str, val.to_string().blue())?,
            MIRNodeKind::FloatLiteral(val) => write!(f, "{}{}", indent_str, val.to_string().blue())?,
            MIRNodeKind::BooleanLiteral(val) => {
                write!(f, "{}{}", indent_str, val.to_string().magenta())?
            }
            MIRNodeKind::StringLiteral(s) => {
                write!(f, "{}{}", indent_str, format!("\"{s}\"").green())?
            }
            MIRNodeKind::CharLiteral(c) => write!(f, "{}\'{}\'", indent_str, c.to_string().red())?,
            MIRNodeKind::Identifier(name) => write!(f, "{}{}", indent_str, name.yellow())?,
            MIRNodeKind::VariableDeclaration {
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
            MIRNodeKind::UnaryOperation { operator, operand } => {
                write!(f, "{}(", indent_str)?;
                write!(f, "{}", operator)?;
                operand.fmt_with_indent(f, 0, table)?;
                write!(f, ")")?;
            }
            MIRNodeKind::BinaryOperation {
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
            MIRNodeKind::ConditionalOperation {
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
            MIRNodeKind::HeapExpression(expr) => {
                write!(f, "{}heap ", indent_str)?;
                expr.fmt_with_indent(f, 0, table)?;
            }
            MIRNodeKind::TypeCast { expr, target_type } => {
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

            MIRNodeKind::Block(nodes) => {
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

            MIRNodeKind::Function {
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

            MIRNodeKind::SelfExpr => write!(f, "{}self", indent_str)?,

            MIRNodeKind::IfStatement {
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

            MIRNodeKind::ForLoop {
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

            MIRNodeKind::WhileLoop { condition, body } => {
                write!(f, "{}while (", indent_str)?;
                condition.fmt_with_indent(f, 0, table)?;
                write!(f, ") ")?;
                body.fmt_with_indent(f, indent, table)?;
            }

            MIRNodeKind::Return(Some(expr)) => {
                write!(f, "{}return ", indent_str)?;
                expr.fmt_with_indent(f, 0, table)?;
            }
            MIRNodeKind::Return(None) => write!(f, "{}return", indent_str)?,
            MIRNodeKind::Break => write!(f, "{}break", indent_str)?,
            MIRNodeKind::Continue => write!(f, "{}continue", indent_str)?,

            MIRNodeKind::FunctionParameter { name, mutable } => {
                write!(f, "{}", indent_str)?;
                write!(
                    f,
                    "{}{}",
                    if *mutable { "mut ".purple() } else { "".white() },
                    name.yellow(),
                )?;
            }

            MIRNodeKind::StructDeclaration { name, fields } => {
                write!(f, "{}struct {}", indent_str, name.yellow())?;
                writeln!(f, " {}", "{".dimmed())?;

                for field in fields {
                    field.fmt_with_indent(f, child_indent, table)?;
                    writeln!(f)?;
                }

                write!(f, "{}{}", indent_str, "}".dimmed())?;
            }
            MIRNodeKind::StructField { name } => {
                write!(f, "{}", indent_str)?;
                write!(f, "{}", name.yellow())?;
            }
            MIRNodeKind::StructLiteral { name, fields } => {
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
            MIRNodeKind::EnumDeclaration { name, variants } => {
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
            MIRNodeKind::EnumVariant(name) => write!(f, "{}", name)?,

            MIRNodeKind::FieldAccess { left, right } => {
                write!(f, "{}(", indent_str)?;
                left.fmt_with_indent(f, 0, table)?;
                write!(f, ".")?;
                right.fmt_with_indent(f, 0, table)?;
                write!(f, ")")?;
            }
            MIRNodeKind::FunctionCall {
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

            MIRNodeKind::ExpressionStatement(expr) => {
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