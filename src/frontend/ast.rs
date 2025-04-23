use colored::*;
use crate::utils::token::{Operation, Span, TypeKind};

#[derive(Debug, Clone)]
pub enum NodeKind {
    // LITERALS //
    IntegerLiteral(i64),
    FloatLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(String),
    
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
    Assignment {
        target: Box<Node>, 
        value: Box<Node>,
    },
    CompoundAssignment {
        operator: Operation,
        target: Box<Node>,
        value: Box<Node>,
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
    FunctionDeclaration {
        name: String,
        parameters: Vec<FunctionParameter>,
        return_type: Option<Box<Node>>,
        body: Box<Node>,
    },
    FunctionCall {
        callee: Box<Node>,
        arguments: Vec<Node>,
    },
    
    // CLASSES //
    ClassDeclaration {
        name: String,
        parent: Option<Box<Node>>,
        methods: Vec<Node>,
        properties: Vec<Node>,
    },
    MethodDeclaration {
        name: String,
        parameters: Vec<FunctionParameter>,
        return_type: Option<Box<Node>>,
        body: Box<Node>,
        is_override: bool,
    },
    PropertyAccess {
        object: Box<Node>,
        property: Box<Node>,
    },
    
    // TYPES //
    TypeReference(TypeKind),
    
    // PROGRAM //
    Program(Vec<Node>),
    
    Error,
}

#[derive(Debug, Clone)]
pub struct Node {
    pub kind: NodeKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FunctionParameter {
    pub name: String,
    pub type_annotation: Node,
    pub default_value: Option<Node>,
}

impl std::fmt::Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            NodeKind::Program(nodes) => {
                let header = format!(
                    "{} ({} top-level items)",
                    "Program".bright_blue().bold(),
                    nodes.len()
                );
                write!(f, "{}", header)?;
                for node in nodes {
                    write!(f, "\n  {}", node)?;
                }
                Ok(())
            }
            NodeKind::IntegerLiteral(val) => write!(f, "{}", val.to_string().blue()),
            NodeKind::FloatLiteral(val) => write!(f, "{}", val.to_string().blue()),
            NodeKind::BooleanLiteral(val) => write!(f, "{}", val.to_string().magenta()),
            NodeKind::StringLiteral(s) => write!(f, "\"{}\"", s.green()),
            NodeKind::Identifier(name) => write!(f, "{}", name.yellow()),
            NodeKind::VariableDeclaration {
                mutable,
                name,
                type_annotation,
                initializer,
            } => {
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
                if *prefix {
                    write!(f, "{}{}", operator, operand)
                } else {
                    write!(f, "{}{}", operand, operator)
                }
            }
            NodeKind::BinaryOperation {
                operator,
                left,
                right,
            } => write!(f, "({} {} {})", left, operator, right),
            NodeKind::ConditionalOperation {
                operator,
                left,
                right,
            } => write!(f, "({} {} {})", left, operator, right),
            NodeKind::Assignment { target, value } => write!(f, "{} = {}", target, value),
            NodeKind::CompoundAssignment {
                operator,
                target,
                value,
            } => write!(f, "{} {}= {}", target, operator, value),
            NodeKind::Block(nodes) => {
                writeln!(f, "{}", "{{".dimmed())?;
                for node in nodes {
                    writeln!(f, "    {}", node)?;
                }
                write!(f, "{}", "}}".dimmed())
            }
            NodeKind::IfStatement {
                condition,
                then_branch,
                else_if_branches,
                else_branch,
            } => {
                write!(f, "{} ({}) {}", "if".purple(), condition, then_branch)?;

                for (branch_cond, branch_then) in else_if_branches {
                    write!(f, " {} ({}) {}", "else if".purple(), branch_cond, branch_then)?;
                }

                if let Some(else_node) = else_branch {
                    write!(f, " {} {}", "else".purple(), else_node)?;
                }
                Ok(())
            }
            NodeKind::ForLoop {
                initializer,
                condition,
                increment,
                body,
            } => {
                write!(f, "{} (", "for".cyan())?;
                if let Some(init) = initializer {
                    write!(f, "{}; ", init)?;
                } else {
                    write!(f, "; ")?;
                }
                if let Some(cond) = condition {
                    write!(f, "{}; ", cond)?;
                } else {
                    write!(f, "; ")?;
                }
                if let Some(inc) = increment {
                    write!(f, "{}", inc)?;
                }
                write!(f, ") {}", body)
            }
            NodeKind::WhileLoop { condition, body } => {
                write!(f, "{} ({}) {}", "while".cyan(), condition, body)
            }
            NodeKind::Return(Some(expr)) => write!(f, "{} {}", "return".red(), expr),
            NodeKind::Return(None) => write!(f, "{}", "return".red()),
            NodeKind::Break => write!(f, "{}", "break".red()),
            NodeKind::Continue => write!(f, "{}", "continue".red()),
            NodeKind::Throw(expr) => write!(f, "{} {}", "throw".red(), expr),
            NodeKind::FunctionDeclaration {
                name,
                parameters,
                return_type,
                body,
            } => {
                write!(f, "{} {}", "fn".bright_red(), name.yellow())?;
                write!(f, "(")?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", param.name.yellow(), param.type_annotation)?;
                    if let Some(default) = &param.default_value {
                        write!(f, " = {}", default)?;
                    }
                }
                write!(f, ")")?;
                if let Some(ret_ty) = return_type {
                    write!(f, ": {}", ret_ty)?;
                }
                write!(f, " {}", body)
            }
            NodeKind::FunctionCall { callee, arguments } => {
                write!(f, "{}(", callee)?;
                for (i, arg) in arguments.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
            NodeKind::ClassDeclaration {
                name,
                parent,
                methods,
                properties,
            } => {
                write!(f, "{} {}", "class".bright_cyan(), name.yellow())?;
                if let Some(parent_node) = parent {
                    write!(f, " {} {}", "extends".bright_cyan(), parent_node)?;
                }
                write!(f, " {}", "{{".dimmed())?;
                for prop in properties {
                    write!(f, "\n    {}", prop)?;
                }
                for method in methods {
                    write!(f, "\n    {}", method)?;
                }
                write!(f, "\n{}", "}}".dimmed())
            }
            NodeKind::MethodDeclaration {
                name,
                parameters,
                return_type,
                body,
                is_override,
            } => {
                if *is_override {
                    write!(f, "{} ", "override".bright_black())?;
                }
                write!(f, "{} {}", "fn".bright_red(), name.yellow())?;
                write!(f, "(")?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", param.name.yellow(), param.type_annotation)?;
                }
                write!(f, ")")?;
                if let Some(ret_ty) = return_type {
                    write!(f, ": {}", ret_ty)?;
                }
                write!(f, " {}", body)
            }
            NodeKind::PropertyAccess { object, property } => {
                write!(f, "{}.{}", object, property)
            }
            NodeKind::TypeReference(name) => write!(f, "{}", format!("{:?}", name).bright_blue()),
            NodeKind::Error => write!(f, "{}", "ERROR".red().bold()),
        }
    }
}