use colored::*;
use indexmap::IndexMap;
use crate::utils::kind::*;

#[derive(Debug, Clone)]
pub enum AstNodeKind {
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
        type_annotation: Option<Box<AstNode>>,
        initializer: Option<Box<AstNode>>,
    },
    
    // OPERATIONS //
    UnaryOperation {
        operator: Operation,
        operand: Box<AstNode>,
        prefix: bool
    },
    BinaryOperation {
        operator: Operation,
        left: Box<AstNode>,
        right: Box<AstNode>,
    },
    ConditionalOperation {
        operator: Operation,
        left: Box<AstNode>,
        right: Box<AstNode>,
    },
    
    // CONTROL FLOW //
    Block(Vec<AstNode>),
    IfStatement {
        condition: Box<AstNode>,
        then_branch: Box<AstNode>,
        else_if_branches: Vec<(Box<AstNode>, Box<AstNode>)>,
        else_branch: Option<Box<AstNode>>,
    },
    ForLoop {
        initializer: Option<Box<AstNode>>,
        condition: Option<Box<AstNode>>,
        increment: Option<Box<AstNode>>,
        body: Box<AstNode>,
    },
    WhileLoop {
        condition: Box<AstNode>,
        body: Box<AstNode>,
    },
    Return(Option<Box<AstNode>>),
    Break,
    Continue,
    Throw(Box<AstNode>),
    
    // FUNCTIONS //
    FunctionSignature {
        name: String,
        generic_parameters: Vec<AstNode>,
        parameters: Vec<AstNode>,
        return_type: Option<Box<AstNode>>,
        instance: Option<bool>
    },
    FunctionPointer {
        params: Vec<AstNode>,
        return_type: Option<Box<AstNode>>
    },
    FunctionDeclaration {
        signature: Box<AstNode>,
        body: Box<AstNode>,
    },
    FunctionParameter {
        name: String,
        type_annotation: Box<AstNode>,
        initializer: Option<Box<AstNode>>,
    },
    FunctionExpression {
        signature: Box<AstNode>,
        body: Box<AstNode>
    },

    // STRUCTS //
    StructDeclaration {
        name: String,
        generic_parameters: Vec<AstNode>,
        fields: Vec<AstNode>
    },
    StructField {
        qualifier: QualifierKind,
        name: String,
        type_annotation: Box<AstNode>
    },
    StructLiteral {
        name: String,
        fields: IndexMap<String, AstNode>
    },

    // ENUMS //
    EnumDeclaration {
        name: String,
        variants: IndexMap<String, Option<AstNode>>
    },


    // IMPLEMENTATIONS //
    ImplDeclaration {
        generic_parameters: Vec<AstNode>,
        type_reference: Box<AstNode>,
        trait_name: Option<String>,
        associated_constants: Vec<AstNode>,
        associated_functions: Vec<AstNode>
    },
    AssociatedConstant {
        qualifier: QualifierKind,
        name: String,
        type_annotation: Option<Box<AstNode>>,
        initializer: Box<AstNode>
    },
    AssociatedFunction {
        qualifier: QualifierKind,
        signature: Box<AstNode>,
        body: Box<AstNode>,
    },

    SelfValue,
    SelfType(Option<Operation>),

    FieldAccess {
        left: Box<AstNode>,
        right: Box<AstNode>,
    },
    FunctionCall {
        function: Box<AstNode>,
        arguments: Vec<AstNode>
    },

    // TRAITS //
    TraitDeclaration {
        name: String,
        signatures: Vec<AstNode>
    },

    // GENERICS //
    GenericParameter {
        name: String,
        constraints: Vec<String>
    },

    // TYPES //
    TypeReference {
        type_name: String,
        generic_types: Vec<AstNode>
    },
    TypeDeclaration {
        name: String,
        generic_parameters: Vec<AstNode>,
        value: Box<AstNode>,
    },

    // PROGRAM //
    Program(Vec<AstNode>)
}

#[derive(Debug, Clone)]
pub struct AstNode {
    pub kind: AstNodeKind,
    pub span: Span,
    pub ty: Option<TypeInfo>,
    pub symbol: Option<Symbol>
}

impl std::fmt::Display for AstNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_with_indent(f, 0)
    }
}

impl AstNode {
    fn fmt_with_indent(&self, f: &mut std::fmt::Formatter<'_>, indent: usize) -> std::fmt::Result {
        let indent_str = " ".repeat(indent);
        let child_indent = indent + 4;

        match &self.kind {
            AstNodeKind::Program(nodes) => {
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
            }
            AstNodeKind::IntegerLiteral(val) => write!(f, "{}{}", indent_str, val.to_string().blue())?,
            AstNodeKind::FloatLiteral(val) => write!(f, "{}{}", indent_str, val.to_string().blue())?,
            AstNodeKind::BooleanLiteral(val) => write!(f, "{}{}", indent_str, val.to_string().magenta())?,
            AstNodeKind::StringLiteral(s) => write!(f, "{}{}", indent_str, format!("\"{s}\"").green())?,
            AstNodeKind::CharLiteral(c) => write!(f, "{}\'{}\'", indent_str, c.to_string().red())?,
            AstNodeKind::Identifier(name) => write!(f, "{}{}", indent_str, name.yellow())?,
            AstNodeKind::VariableDeclaration {
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
            }
            AstNodeKind::UnaryOperation { operator, operand, prefix } => {
                write!(f, "{}", indent_str)?;
                if *prefix {
                    write!(f, "{}{}", operator, operand)?
                } else {
                    write!(f, "{}{}", operand, operator)?
                }
            }
            AstNodeKind::BinaryOperation { operator, left, right } => {
                write!(f, "{}(", indent_str)?;
                left.fmt_with_indent(f, 0)?;
                write!(f, " {} ", operator)?;
                right.fmt_with_indent(f, 0)?;
                write!(f, ")")?
            }
            AstNodeKind::ConditionalOperation { operator, left, right } => {
                write!(f, "{}(", indent_str)?;
                left.fmt_with_indent(f, 0)?;
                write!(f, " {} ", operator)?;
                right.fmt_with_indent(f, 0)?;
                write!(f, ")")?
            }

            AstNodeKind::Block(nodes) => {
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
                write!(f, "{}", "}".dimmed())?
            }

            AstNodeKind::FunctionSignature {
                name,
                generic_parameters,
                parameters,
                return_type,
                ..
            } => {
                write!(f, "{}fn {}", indent_str, name.yellow())?;

                if !generic_parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in generic_parameters.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        param.fmt_with_indent(f, 0)?;
                    }
                    write!(f, "]")?;
                }

                write!(f, "(")?;

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
            }

            AstNodeKind::FunctionDeclaration {
                signature,
                body,
            } => {
                write!(f, "{}", signature)?;
                write!(f, " ")?;
                body.fmt_with_indent(f, indent)?
            }

            AstNodeKind::ImplDeclaration {
                generic_parameters,
                type_reference: name,
                trait_name,
                associated_constants,
                associated_functions
            } => {
                write!(f, "{}{} ", indent_str, "impl".bright_cyan())?;
                if !generic_parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in generic_parameters.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        param.fmt_with_indent(f, 0)?;
                    }
                    write!(f, "]")?;
                }

                if let Some(trait_name) = trait_name {
                    write!(f, "{} for ", trait_name)?;
                }
                write!(f, "{}", name)?;

                writeln!(f, " {}", "{".dimmed())?;
                for constant in associated_constants {
                    writeln!(f, "    {}", constant)?;
                }
                for function in associated_functions {
                    writeln!(f, "    {}", function)?;
                }
                write!(f, "{}", "}".dimmed())?
            }

            AstNodeKind::AssociatedConstant {
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
            }

            AstNodeKind::AssociatedFunction {
                qualifier,
                signature,
                body
            } => {
                write!(f, "{}", indent_str)?;
                write!(f, "{} ", match qualifier {
                    QualifierKind::Public => "public".purple(),
                    QualifierKind::Private => "private".purple()
                })?;

                write!(f, "{}", signature)?;
                write!(f, " ")?;
                body.fmt_with_indent(f, indent)?
            }

            AstNodeKind::SelfValue => write!(f, "{}this", indent_str)?,
            AstNodeKind::SelfType(operation) => {
                let operation_str = match operation {
                    Some(Operation::ImmutableAddressOf) => "&",
                    Some(Operation::MutableAddressOf) => "&mut ",
                    _ => ""
                };

                write!(f, "{}{operation_str}Self", indent_str)?
            },

            AstNodeKind::IfStatement {
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
            }

            AstNodeKind::ForLoop {
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
                body.fmt_with_indent(f, indent)?  // Same indent for block
            }

            AstNodeKind::WhileLoop { condition, body } => {
                write!(f, "{}while (", indent_str)?;
                condition.fmt_with_indent(f, 0)?;
                write!(f, ") ")?;
                body.fmt_with_indent(f, indent)?  // Same indent for block
            }

            AstNodeKind::Return(Some(expr)) => {
                write!(f, "{}return ", indent_str)?;
                expr.fmt_with_indent(f, 0)?
            }
            AstNodeKind::Return(None) => write!(f, "{}return", indent_str)?,
            AstNodeKind::Break => write!(f, "{}break", indent_str)?,
            AstNodeKind::Continue => write!(f, "{}continue", indent_str)?,
            AstNodeKind::Throw(expr) => {
                write!(f, "{}throw ", indent_str)?;
                expr.fmt_with_indent(f, 0)?
            }

            AstNodeKind::FunctionParameter {
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
            }

            AstNodeKind::FunctionExpression {
                signature,
                body
            } => {
                write!(f, "{}", signature)?;
                write!(f, " ")?;
                body.fmt_with_indent(f, indent)?
            }

            AstNodeKind::StructDeclaration {
                name,
                generic_parameters,
                fields,
            } => {
                write!(f, "{}struct {}", indent_str, name.yellow())?;

                if !generic_parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in generic_parameters.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        param.fmt_with_indent(f, 0)?;
                    }
                    write!(f, "]")?;
                }

                writeln!(f, " {}", "{".dimmed())?;
                
                for field in fields {
                    field.fmt_with_indent(f, child_indent)?;
                    writeln!(f)?;
                }
                
                write!(f, "{}{}", indent_str, "}".dimmed())?
            }
            AstNodeKind::StructField {
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
            }
            AstNodeKind::StructLiteral { name, fields } => {
                write!(f, "{}{}{}", indent_str, name.yellow(), " ".dimmed())?;
                write!(f, "{}", "{".dimmed())?;
            
                for (i, (field_name, expr)) in fields.iter().enumerate() {
                    write!(f, " ")?;
                    write!(f, "{}: ", field_name.yellow())?;
                    write!(f, "{}", expr)?;

                    write!(f, "{}", if i + 1 < fields.len() { "," } else { " " })?;
                }
            
                write!(f, "{}{}", indent_str, "}".dimmed())?
            }      
            AstNodeKind::EnumDeclaration { name, variants } => {
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
                
                write!(f, "{}{}", indent_str, "}".dimmed())?
            },
            AstNodeKind::TypeReference { type_name, generic_types } => {
                write!(f, "{}{}", indent_str, type_name.bright_blue())?;
                if !generic_types.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in generic_types.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        param.fmt_with_indent(f, 0)?;
                    }
                    write!(f, "]")?;
                }
            }
            AstNodeKind::TypeDeclaration { name, generic_parameters, value } => {
                write!(f, "{}", "type ".purple())?;
                write!(f, "{}", name)?;
                
                if !generic_parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in generic_parameters.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        param.fmt_with_indent(f, 0)?;
                    }
                    write!(f, "]")?;
                }

                write!(f, "= ")?;
                write!(f, "{}", value)?
            }
            AstNodeKind::FieldAccess { left, right } => {
                write!(f, "{}(", indent_str)?;
                left.fmt_with_indent(f, 0)?;
                write!(f, ".")?;
                right.fmt_with_indent(f, 0)?;
                write!(f, ")")?
            }
            AstNodeKind::FunctionCall { function, arguments } => {
                write!(f, "{}", indent_str)?;
                function.fmt_with_indent(f, 0)?;
                write!(f, "(")?;
                for (i, param) in arguments.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    param.fmt_with_indent(f, 0)?;
                }
                write!(f, ")")?
            }
            AstNodeKind::TraitDeclaration { name, signatures } => {
                write!(f, "{}trait {}", indent_str, name.yellow())?;
                writeln!(f, " {}", "{".dimmed())?;
                
                for signature in signatures {
                    signature.fmt_with_indent(f, child_indent)?;
                    writeln!(f)?;
                }
                
                write!(f, "{}{}", indent_str, "}".dimmed())?
            }
            AstNodeKind::GenericParameter { name, constraints } => {
                write!(f, "{}{}", indent_str, name.yellow())?;

                if !constraints.is_empty() {
                    write!(f, ": ")?;
                }

                for (i, constraint) in constraints.iter().enumerate() {
                    write!(f, "{}", constraint)?;
                    if i + 1 < constraints.len() {
                        write!(f, " + ")?;
                    }
                }
            },
            AstNodeKind::FunctionPointer { params, return_type } => {
                write!(f, "{}{}", indent_str, "fn".bright_blue())?;
                write!(f, "(")?;
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    param.fmt_with_indent(f, 0)?;
                }
                write!(f, ")")?;

                if let Some(return_type) = return_type {
                    write!(f, ": {}", return_type)?;
                }
            }
        }

        if let Some(ty) = &self.ty {
            write!(f, " {}",
                format_args!("[type: {}]", ty.to_string())
            )?;
        }

        if let Some(sym) = &self.symbol {
            write!(f, " [symbol: {}]", sym.name.magenta().bold())?;
        }

        Ok(())
    }
}