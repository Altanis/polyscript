use std::collections::HashMap;

use colored::*;
use indexmap::IndexMap;
use crate::utils::kind::{Operation, QualifierKind, Span};

#[derive(Debug, Clone)]
pub enum NodeKind {
    // LITERALS //
    IntegerLiteral(i64),
    FloatLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(String),
    CharLiteral(char),

    // VARIABLES //
    Identifier(String),
    VariableDeclaration {
        mutable: bool,
        name: String,
        type_annotation: Option<Box<Node>>,
        initializer: Option<Box<Node>>,
    },
    
    // OPERATORS //
    UnaryOperation {
        operator: Operation,
        operand: Box<Node>,
        prefix: bool
    },
    BinaryOperation {
        operator: Operation,
        left: Box<Node>,
        right: Box<Node>,
    },
    ConditionalOperation {
        operator: Operation,
        left: Box<Node>,
        right: Box<Node>,
    },
    
    // CONTROL FLOW //
    Block(Vec<Node>),
    IfStatement {
        condition: Box<Node>,
        then_branch: Box<Node>,
        else_if_branches: Vec<(Box<Node>, Box<Node>)>,
        else_branch: Option<Box<Node>>,
    },
    ForLoop {
        initializer: Option<Box<Node>>,
        condition: Option<Box<Node>>,
        increment: Option<Box<Node>>,
        body: Box<Node>,
    },
    WhileLoop {
        condition: Box<Node>,
        body: Box<Node>,
    },
    Return(Option<Box<Node>>),
    Break,
    Continue,
    Throw(Box<Node>),
    
    // FUNCTIONS //
    FunctionSignature {
        name: String,
        parameters: Vec<Node>,
        return_type: Option<Box<Node>>,
        instance: Option<bool>
    },
    FunctionDeclaration {
        signature: Box<Node>,
        body: Box<Node>,
    },
    FunctionParameter {
        name: String,
        type_annotation: Box<Node>,
        initializer: Option<Box<Node>>,
    },
    
    // STRUCTS //
    StructDeclaration {
        name: String,
        fields: Vec<Node>
    },
    StructField {
        qualifier: QualifierKind,
        name: String,
        type_annotation: Box<Node>
    },
    StructLiteral {
        name: String,
        fields: HashMap<String, Node>
    },

    // ENUMS //
    EnumDeclaration {
        name: String,
        variants: IndexMap<String, Option<Node>>
    },


    // IMPLEMENTATIONS //
    ImplDeclaration {
        name: String,
        parent: Option<Box<Node>>,
        associated_constants: Vec<Node>,
        associated_functions: Vec<Node>
    },
    AssociatedConstant {
        qualifier: QualifierKind,
        name: String,
        type_annotation: Option<Box<Node>>,
        initializer: Box<Node>
    },
    AssociatedFunction {
        qualifier: QualifierKind,
        name: String,
        parameters: Vec<Node>,
        return_type: Option<Box<Node>>,
        body: Box<Node>,
        instance: bool
    },
    SelfType,

    FunctionCall {
        function: Box<Node>,
        arguments: Vec<Node>
    },

    // TRAITS //
    TraitDeclaration {
        name: String,
        signatures: Vec<Node>
    },

    // TYPES //
    TypeReference(String),
    
    // PROGRAM //
    Program(Vec<Node>),
    
    Error,
}

#[derive(Debug, Clone)]
pub struct Node {
    pub kind: NodeKind,
    pub span: Span,
}

impl std::fmt::Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_with_indent(f, 0)
    }
}

impl Node {
    fn fmt_with_indent(&self, f: &mut std::fmt::Formatter<'_>, indent: usize) -> std::fmt::Result {
        let indent_str = " ".repeat(indent);
        let child_indent = indent + 4;

        match &self.kind {
            NodeKind::Program(nodes) => {
                let header = format!(
                    "{} ({} top-level items)",
                    "Program".bright_blue().bold(),
                    nodes.len()
                );
                writeln!(f, "{}", header)?;
                for node in nodes {
                    node.fmt_with_indent(f, indent)?;
                    writeln!(f)?;
                }
                Ok(())
            }
            NodeKind::IntegerLiteral(val) => write!(f, "{}{}", indent_str, val.to_string().blue()),
            NodeKind::FloatLiteral(val) => write!(f, "{}{}", indent_str, val.to_string().blue()),
            NodeKind::BooleanLiteral(val) => write!(f, "{}{}", indent_str, val.to_string().magenta()),
            NodeKind::StringLiteral(s) => write!(f, "{}{}", indent_str, format!("\"{s}\"").green()),
            NodeKind::CharLiteral(c) => write!(f, "{}\"{}\"", indent_str, c.to_string().red()),
            NodeKind::Identifier(name) => write!(f, "{}{}", indent_str, name.yellow()),
            NodeKind::VariableDeclaration {
                mutable,
                name,
                type_annotation,
                initializer,
            } => {
                write!(f, "{}", indent_str)?;
                let decl_type = if *mutable {
                    "let".bright_green()
                } else {
                    "const".green()
                };
                write!(f, "{} {}", decl_type, name.yellow())?;
                if let Some(ty) = type_annotation {
                    write!(f, ": {}", ty)?;
                }
                if let Some(init) = initializer {
                    write!(f, " = {}", init)?;
                }
                Ok(())
            }
            NodeKind::UnaryOperation { operator, operand, prefix } => {
                write!(f, "{}", indent_str)?;
                if *prefix {
                    write!(f, "{}{}", operator, operand)
                } else {
                    write!(f, "{}{}", operand, operator)
                }
            }
            NodeKind::BinaryOperation { operator, left, right } => {
                write!(f, "{}(", indent_str)?;
                left.fmt_with_indent(f, 0)?;
                write!(f, " {} ", operator)?;
                right.fmt_with_indent(f, 0)?;
                write!(f, ")")
            }
            NodeKind::ConditionalOperation { operator, left, right } => {
                write!(f, "{}(", indent_str)?;
                left.fmt_with_indent(f, 0)?;
                write!(f, " {} ", operator)?;
                right.fmt_with_indent(f, 0)?;
                write!(f, ")")
            }

            NodeKind::Block(nodes) => {
                write!(f, "{}", "{".dimmed())?;
                if !nodes.is_empty() {
                    writeln!(f)?;
                    for node in nodes {
                        write!(f, "{}", " ".repeat(child_indent))?;
                        node.fmt_with_indent(f, child_indent)?;
                        writeln!(f)?;
                    }
                    write!(f, "{}", indent_str)?;
                }
                write!(f, "{}", " ".repeat(child_indent))?;
                write!(f, "{}", "}".dimmed())
            }

            NodeKind::FunctionSignature {
                name,
                parameters,
                return_type,
                ..
            } => {
                write!(f, "{}fn {}(", indent_str, name.yellow())?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    param.fmt_with_indent(f, 0)?;
                }
                write!(f, ")")?;
                if let Some(ret_ty) = return_type {
                    write!(f, ": {}", ret_ty)?;
                }
                
                Ok(())
            }

            NodeKind::FunctionDeclaration {
                signature,
                body,
            } => {
                write!(f, "{}", signature)?;
                write!(f, " ")?;
                body.fmt_with_indent(f, indent)
            }

            NodeKind::ImplDeclaration {
                name,
                parent,
                associated_constants,
                associated_functions
            } => {
                write!(f, "{} {}", "class".bright_cyan(), name.yellow())?;
                if let Some(parent_node) = parent {
                    write!(f, " {} {}", ":".bright_cyan(), parent_node)?;
                }
                writeln!(f, " {}", "{".dimmed())?;
                for constant in associated_constants {
                    writeln!(f, "    {}", constant)?;
                }
                for function in associated_functions {
                    writeln!(f, "    {}", function)?;
                }
                write!(f, "{}", "}".dimmed())
            }

            NodeKind::AssociatedConstant {
                qualifier,
                name,
                type_annotation,
                initializer
            } => {
                write!(f, "{} ", match qualifier {
                    QualifierKind::Public => "public",
                    QualifierKind::Private => "private"
                }.purple())?;

                write!(f, "const ")?;
                write!(f, "{}", name.yellow())?;

                if let Some(type_annotation) = type_annotation {
                    write!(f, ": {}", type_annotation)?;
                }

                write!(f, " = {}", initializer)?;

                Ok(())
            }

            NodeKind::AssociatedFunction {
                qualifier,
                name,
                parameters,
                return_type,
                body,
                ..
            } => {
                write!(f, "{}", indent_str)?;
                write!(f, "{} ", match qualifier {
                    QualifierKind::Public => "public".purple(),
                    QualifierKind::Private => "private".purple()
                })?;

                write!(f, "fn {}(", name.yellow())?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    param.fmt_with_indent(f, 0)?;
                }
                write!(f, ")")?;
                if let Some(ret_ty) = return_type {
                    write!(f, ": {}", ret_ty)?;
                }
                write!(f, " ")?;
                body.fmt_with_indent(f, indent)  // Don't increase indent for the block
            }

            NodeKind::SelfType => write!(f, "{}Self", indent_str),

            NodeKind::IfStatement {
                condition,
                then_branch,
                else_if_branches,
                else_branch,
            } => {
                write!(f, "{}if (", indent_str)?;
                condition.fmt_with_indent(f, 0)?;
                write!(f, ") ")?;
                then_branch.fmt_with_indent(f, indent)?;  // Same indent for block
                
                for (cond, branch) in else_if_branches {
                    write!(f, "{}else if (", indent_str)?;
                    cond.fmt_with_indent(f, 0)?;
                    write!(f, ") ")?;
                    branch.fmt_with_indent(f, indent)?;  // Same indent for block
                }
                
                if let Some(else_node) = else_branch {
                    write!(f, "{}else ", indent_str)?;
                    else_node.fmt_with_indent(f, indent)?;  // Same indent for block
                }
                Ok(())
            }

            NodeKind::ForLoop {
                initializer,
                condition,
                increment,
                body,
            } => {
                write!(f, "{}for (", indent_str)?;
                if let Some(init) = initializer {
                    init.fmt_with_indent(f, 0)?;
                }
                write!(f, "; ")?;
                if let Some(cond) = condition {
                    cond.fmt_with_indent(f, 0)?;
                }
                write!(f, "; ")?;
                if let Some(inc) = increment {
                    inc.fmt_with_indent(f, 0)?;
                }
                write!(f, ") ")?;
                body.fmt_with_indent(f, indent)  // Same indent for block
            }

            NodeKind::WhileLoop { condition, body } => {
                write!(f, "{}while (", indent_str)?;
                condition.fmt_with_indent(f, 0)?;
                write!(f, ") ")?;
                body.fmt_with_indent(f, indent)  // Same indent for block
            }

            NodeKind::Return(Some(expr)) => {
                write!(f, "{}return ", indent_str)?;
                expr.fmt_with_indent(f, 0)
            }
            NodeKind::Return(None) => write!(f, "{}return", indent_str),
            NodeKind::Break => write!(f, "{}break", indent_str),
            NodeKind::Continue => write!(f, "{}continue", indent_str),
            NodeKind::Throw(expr) => {
                write!(f, "{}throw ", indent_str)?;
                expr.fmt_with_indent(f, 0)
            }

            NodeKind::FunctionParameter {
                name,
                type_annotation,
                initializer,
            } => {
                write!(f, "{}", indent_str)?;
                write!(f, "{}: {}", name.yellow(), type_annotation)?;
                if let Some(default) = initializer {
                    write!(f, " = ")?;
                    default.fmt_with_indent(f, 0)?;
                }
                Ok(())
            }

            NodeKind::StructDeclaration {
                name,
                fields,
            } => {
                write!(f, "{}struct {}", indent_str, name.yellow())?;
                writeln!(f, " {}", "{".dimmed())?;
                
                for field in fields {
                    field.fmt_with_indent(f, child_indent)?;
                    writeln!(f)?;
                }
                
                write!(f, "{}{}", indent_str, "}".dimmed())
            }
            NodeKind::StructField {
                qualifier,
                name,
                type_annotation,
            } => {
                write!(f, "{}", indent_str)?;
                write!(f, "{} ", match qualifier {
                    QualifierKind::Public => "public".purple(),
                    QualifierKind::Private => "private".purple()
                })?;

                write!(f, "{}", name.yellow())?;
                write!(f, ": {}", type_annotation)?;

                Ok(())
            }
            NodeKind::StructLiteral { name, fields } => {
                write!(f, "{}{}{}", indent_str, name.yellow(), " ".dimmed())?;
                write!(f, "{}", "{".dimmed())?;
            
                for (i, (field_name, expr)) in fields.iter().enumerate() {
                    write!(f, " ")?;
                    write!(f, "{}: ", field_name.yellow())?;
                    write!(f, "{}", expr)?;

                    write!(f, "{}", if i + 1 < fields.len() { "," } else { " " })?;
                }
            
                write!(f, "{}{}", indent_str, "}".dimmed())
            }      
            NodeKind::EnumDeclaration { name, variants } => {
                write!(f, "{}enum {}", indent_str, name.yellow())?;
                writeln!(f, " {}", "{".dimmed())?;
                
                for (variant, expr) in variants {
                    write!(f, "{}", " ".repeat(child_indent + 4))?;
                    write!(f, "{}", variant)?;
                    if let Some(expr) = expr {
                        write!(f, " = {}", expr)?;
                    }
                    writeln!(f)?;
                }
                
                write!(f, "{}{}", indent_str, "}".dimmed())
            },
            NodeKind::TypeReference(name) => {
                write!(f, "{}{}", indent_str, name.bright_blue())
            }
            NodeKind::Error => {
                write!(f, "{}", indent_str)?;
                write!(f, "{}", "ERROR".red().bold())
            }
            NodeKind::FunctionCall { function, arguments } => {
                write!(f, "{}", indent_str)?;
                function.fmt_with_indent(f, 0)?;
                write!(f, "(")?;
                for (i, param) in arguments.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    param.fmt_with_indent(f, 0)?;
                }
                write!(f, ")")
            }
            NodeKind::TraitDeclaration { name, signatures } => {
                write!(f, "{}trait {}", indent_str, name.yellow())?;
                writeln!(f, " {}", "{".dimmed())?;
                
                for signature in signatures {
                    signature.fmt_with_indent(f, child_indent)?;
                    writeln!(f)?;
                }
                
                write!(f, "{}{}", indent_str, "}".dimmed())
            }
        }
    }
}