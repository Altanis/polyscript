use std::fmt::Write;

// frontend/ast.rs
use crate::{
    frontend::semantics::analyzer::{PrimitiveKind, ScopeId, SymbolTable, Type, ValueSymbolId},
    utils::kind::*,
};
use colored::*;
use indexmap::IndexMap;

/// The various denominations of an AstNode.
#[derive(Debug, Clone)]
pub enum AstNodeKind {
    IntegerLiteral(i64),
    FloatLiteral(f64),
    BooleanLiteral(bool),
    StringLiteral(String),
    CharLiteral(char),

    /// A named entity with no semantic meaning.
    Identifier(String),
    VariableDeclaration {
        name: String,
        mutable: bool,
        type_annotation: Option<BoxedAstNode>,
        initializer: BoxedAstNode,
    },

    UnaryOperation {
        operator: Operation,
        operand: BoxedAstNode,
    },
    BinaryOperation {
        operator: Operation,
        left: BoxedAstNode,
        right: BoxedAstNode,
    },
    ConditionalOperation {
        operator: Operation,
        left: BoxedAstNode,
        right: BoxedAstNode,
    },
    HeapExpression(BoxedAstNode),

    TypeCast {
        expr: BoxedAstNode,
        target_type: BoxedAstNode,
    },
    PathQualifier {
        ty: BoxedAstNode,
        tr: Option<BoxedAstNode>,
    },

    // A sequence of statements encapsulated by braces.
    Block(Vec<AstNode>),
    IfStatement {
        condition: BoxedAstNode,
        then_branch: BoxedAstNode,
        else_if_branches: Vec<(BoxedAstNode, BoxedAstNode)>,
        else_branch: Option<BoxedAstNode>,
    },
    ForLoop {
        initializer: Option<BoxedAstNode>,
        condition: Option<BoxedAstNode>,
        increment: Option<BoxedAstNode>,
        body: BoxedAstNode,
    },
    WhileLoop {
        condition: BoxedAstNode,
        body: BoxedAstNode,
    },
    Return(Option<BoxedAstNode>),
    Break,
    Continue,

    /// An expression or declaration that takes inputs and returns an output.
    Function {
        qualifier: Option<QualifierKind>,
        name: String,
        generic_parameters: Vec<AstNode>,
        parameters: Vec<AstNode>,
        return_type: Option<BoxedAstNode>,
        instance: Option<ReferenceKind>,
        body: Option<BoxedAstNode>,
    },
    /// A type that denotes the signature of a function.
    FunctionPointer {
        params: Vec<AstNode>,
        return_type: Option<BoxedAstNode>,
    },
    /// A parameter inside a function declaration or expression.
    FunctionParameter {
        name: String,
        type_annotation: BoxedAstNode,
        mutable: bool,
    },

    StructDeclaration {
        name: String,
        generic_parameters: Vec<AstNode>,
        fields: Vec<AstNode>,
    },
    StructField {
        qualifier: QualifierKind,
        name: String,
        type_annotation: BoxedAstNode,
    },
    StructLiteral {
        name: String,
        fields: IndexMap<String, AstNode>,
    },

    EnumDeclaration {
        name: String,
        variants: IndexMap<String, (AstNode, Option<AstNode>)>,
    },
    EnumVariant(String),

    ImplDeclaration {
        generic_parameters: Vec<AstNode>,
        type_reference: BoxedAstNode,
        trait_node: Option<BoxedAstNode>,
        associated_constants: Vec<AstNode>,
        associated_functions: Vec<AstNode>,
        associated_types: Vec<AstNode>,
    },
    AssociatedConstant {
        qualifier: QualifierKind,
        name: String,
        type_annotation: Option<BoxedAstNode>,
        initializer: BoxedAstNode,
    },
    AssociatedType {
        qualifier: QualifierKind,
        name: String,
        value: BoxedAstNode,
    },

    /// `self`
    SelfExpr,
    /// `Self`, used as the type annotation for `this`, `&this`, and `&mut this`
    /// in an associated function.
    SelfType(ReferenceKind),

    /// A member access operation (i.e. `x.y`).
    FieldAccess {
        left: BoxedAstNode,
        right: BoxedAstNode,
    },
    /// A function call (i.e. `f()`).
    FunctionCall {
        function: BoxedAstNode,
        arguments: Vec<AstNode>,
    },

    TraitDeclaration {
        name: String,
        generic_parameters: Vec<AstNode>,
        types: Vec<AstNode>,
        constants: Vec<AstNode>,
        signatures: Vec<AstNode>,
    },
    TraitConstant {
        name: String,
        type_annotation: BoxedAstNode,
    },
    TraitType(String),

    GenericParameter {
        name: String,
        constraints: Vec<AstNode>,
    },

    TypeReference {
        type_name: String,
        generic_types: Vec<AstNode>,
        reference_kind: ReferenceKind,
    },
    TypeDeclaration {
        name: String,
        generic_parameters: Vec<AstNode>,
        value: BoxedAstNode,
    },

    /// An expression node with a semicolon.
    ExpressionStatement(BoxedAstNode),

    // PROGRAM //
    Program(Vec<AstNode>),
}

#[derive(Debug, Clone)]
pub struct AstNode {
    /// The type of node.
    pub kind: AstNodeKind,
    /// The location of the node in the source file.
    pub span: Span,
    /// A pointer to the value it holds in the symbol table.
    pub value_id: Option<ValueSymbolId>,
    /// A pointer to the type it holds in the symbol table.
    pub type_id: Option<Type>,
    /// The scope the node lives in.
    pub scope_id: Option<ScopeId>,
}

pub type BoxedAstNode = Box<AstNode>;

impl AstNode {
    pub fn get_name(&self) -> Option<String> {
        match &self.kind {
            AstNodeKind::Identifier(name) => Some(name.clone()),

            AstNodeKind::VariableDeclaration { name, .. } => Some(name.clone()),
            AstNodeKind::Function { name, .. } => {
                if name.is_empty() {
                    None
                } else {
                    Some(name.clone())
                }
            }
            AstNodeKind::FunctionParameter { name, .. } => Some(name.clone()),

            AstNodeKind::StructDeclaration { name, .. } => Some(name.clone()),
            AstNodeKind::StructField { name, .. } => Some(name.clone()),
            AstNodeKind::StructLiteral { name, .. } => Some(name.clone()),

            AstNodeKind::EnumDeclaration { name, .. } => Some(name.clone()),
            AstNodeKind::EnumVariant(name) => Some(name.clone()),

            AstNodeKind::TraitDeclaration { name, .. } => Some(name.clone()),
            AstNodeKind::TraitConstant { name, .. } => Some(name.clone()),
            AstNodeKind::TraitType(name) => Some(name.clone()),

            AstNodeKind::AssociatedConstant { name, .. } => Some(name.clone()),
            AstNodeKind::AssociatedType { name, .. } => Some(name.clone()),

            AstNodeKind::GenericParameter { name, .. } => Some(name.clone()),

            AstNodeKind::TypeReference { type_name, .. } => Some(type_name.clone()),
            AstNodeKind::TypeDeclaration { name, .. } => Some(name.clone()),

            _ => None,
        }
    }
}

impl std::fmt::Display for AstNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_with_indent(f, 0, None)
    }
}

impl AstNode {
    pub fn fmt_with_indent<W: Write>(
        &self,
        f: &mut W,
        indent: usize,
        table: Option<&SymbolTable>,
    ) -> std::fmt::Result {
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
                    node.fmt_with_indent(f, indent, table)?;
                    writeln!(f)?;
                }
            }
            AstNodeKind::IntegerLiteral(val) => write!(f, "{}{}", indent_str, val.to_string().blue())?,
            AstNodeKind::FloatLiteral(val) => write!(f, "{}{}", indent_str, val.to_string().blue())?,
            AstNodeKind::BooleanLiteral(val) => {
                write!(f, "{}{}", indent_str, val.to_string().magenta())?
            }
            AstNodeKind::StringLiteral(s) => {
                write!(f, "{}{}", indent_str, format!("\"{s}\"").green())?
            }
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
                    write!(f, ": ")?;
                    ty.fmt_with_indent(f, 0, table)?;
                }
                write!(f, " = ")?;
                initializer.fmt_with_indent(f, 0, table)?;
            }
            AstNodeKind::UnaryOperation { operator, operand } => {
                write!(f, "{}", indent_str)?;
                write!(f, "{}", operator)?;
                operand.fmt_with_indent(f, 0, table)?;
            }
            AstNodeKind::BinaryOperation {
                operator,
                left,
                right,
            } => {
                write!(f, "{}(", indent_str)?;
                left.fmt_with_indent(f, 0, table)?;
                write!(f, " {} ", operator)?;
                right.fmt_with_indent(f, 0, table)?;
                write!(f, ")")?
            }
            AstNodeKind::ConditionalOperation {
                operator,
                left,
                right,
            } => {
                write!(f, "{}(", indent_str)?;
                left.fmt_with_indent(f, 0, table)?;
                write!(f, " {} ", operator)?;
                right.fmt_with_indent(f, 0, table)?;
                write!(f, ")")?
            }
            AstNodeKind::HeapExpression(expr) => {
                write!(f, "{}heap ", indent_str)?;
                expr.fmt_with_indent(f, 0, table)?;
            }
            AstNodeKind::TypeCast { expr, target_type } => {
                write!(f, "{}(", indent_str)?;
                expr.fmt_with_indent(f, 0, table)?;
                write!(f, " {} ", "as".yellow())?;
                target_type.fmt_with_indent(f, 0, table)?;
                write!(f, ")")?;
            }
            AstNodeKind::PathQualifier { ty, tr } => {
                write!(f, "{}{}", indent_str, "<".dimmed())?;
                ty.fmt_with_indent(f, 0, table)?;
                if let Some(tr_node) = tr {
                    write!(f, " {} ", "as".yellow())?;
                    tr_node.fmt_with_indent(f, 0, table)?;
                }
                write!(f, "{}", ">".dimmed())?;
            }

            AstNodeKind::Block(nodes) => {
                write!(f, "{}", "{".dimmed())?;
                if !nodes.is_empty() {
                    writeln!(f)?;
                    for node in nodes {
                        write!(f, "{}", " ".repeat(child_indent))?;
                        node.fmt_with_indent(f, child_indent, table)?;
                        writeln!(f)?;
                    }
                    write!(f, "{}", indent_str)?;
                }
                write!(f, "{}", " ".repeat(child_indent))?;
                write!(f, "{}", "}".dimmed())?
            }

            AstNodeKind::Function {
                qualifier,
                name,
                generic_parameters,
                parameters,
                return_type,
                body,
                ..
            } => {
                write!(f, "{}", indent_str)?;
                if let Some(q) = qualifier {
                    write!(
                        f,
                        "{} ",
                        match q {
                            QualifierKind::Public => "public".purple(),
                            QualifierKind::Private => "private".purple(),
                        }
                    )?;
                }
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

                if !generic_parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in generic_parameters.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        param.fmt_with_indent(f, 0, table)?;
                    }
                    write!(f, "]")?;
                }

                write!(f, "(")?;
                for (i, param) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    param.fmt_with_indent(f, 0, table)?;
                }
                write!(f, ")")?;

                if let Some(ret_ty) = return_type {
                    write!(f, ": ")?;
                    ret_ty.fmt_with_indent(f, 0, table)?;
                }

                if let Some(b) = body {
                    write!(f, " ")?;
                    b.fmt_with_indent(f, indent, table)?;
                } else {
                    write!(f, ";")?;
                }
            }

            AstNodeKind::ImplDeclaration {
                generic_parameters,
                type_reference: name,
                trait_node: trait_name,
                associated_constants,
                associated_functions,
                associated_types,
            } => {
                write!(f, "{}{} ", indent_str, "impl".bright_cyan())?;
                if !generic_parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in generic_parameters.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        param.fmt_with_indent(f, 0, table)?;
                    }
                    write!(f, "]")?;
                }

                if let Some(trait_name) = trait_name {
                    trait_name.fmt_with_indent(f, 0, table)?;
                    write!(f, " for ")?;
                }
                name.fmt_with_indent(f, 0, table)?;

                writeln!(f, " {}", "{".dimmed())?;
                for type_node in associated_types {
                    write!(f, "    ")?;
                    type_node.fmt_with_indent(f, 0, table)?;
                    writeln!(f)?;
                }
                for constant in associated_constants {
                    write!(f, "    ")?;
                    constant.fmt_with_indent(f, 0, table)?;
                    writeln!(f)?;
                }
                for function in associated_functions {
                    write!(f, "    ")?;
                    function.fmt_with_indent(f, 0, table)?;
                    writeln!(f)?;
                }
                write!(f, "{}", "}".dimmed())?
            }

            AstNodeKind::AssociatedType {
                qualifier,
                name,
                value,
            } => {
                write!(
                    f,
                    "{} ",
                    match qualifier {
                        QualifierKind::Public => "public",
                        QualifierKind::Private => "private",
                    }
                    .purple()
                )?;

                write!(f, "type ")?;
                write!(f, "{}", name.yellow())?;
                write!(f, " = ")?;
                value.fmt_with_indent(f, 0, table)?;
            }

            AstNodeKind::AssociatedConstant {
                qualifier,
                name,
                type_annotation,
                initializer,
            } => {
                write!(
                    f,
                    "{} ",
                    match qualifier {
                        QualifierKind::Public => "public",
                        QualifierKind::Private => "private",
                    }
                    .purple()
                )?;

                write!(f, "const ")?;
                write!(f, "{}", name.yellow())?;

                if let Some(type_annotation) = type_annotation {
                    write!(f, ": ")?;
                    type_annotation.fmt_with_indent(f, 0, table)?;
                }

                write!(f, " = ")?;
                initializer.fmt_with_indent(f, 0, table)?;
            }

            AstNodeKind::SelfExpr => write!(f, "{}self", indent_str)?,
            AstNodeKind::SelfType(operation) => {
                let operation_str = match operation {
                    ReferenceKind::Reference => "&",
                    ReferenceKind::MutableReference => "&mut ",
                    ReferenceKind::Value => "",
                };

                write!(f, "{}{operation_str}Self", indent_str)?
            }

            AstNodeKind::IfStatement {
                condition,
                then_branch,
                else_if_branches,
                else_branch,
            } => {
                write!(f, "{}if (", indent_str)?;
                condition.fmt_with_indent(f, 0, table)?;
                write!(f, ") ")?;
                then_branch.fmt_with_indent(f, indent, table)?;

                for (cond, branch) in else_if_branches {
                    write!(f, "{}else if (", indent_str)?;
                    cond.fmt_with_indent(f, 0, table)?;
                    write!(f, ") ")?;
                    branch.fmt_with_indent(f, indent, table)?;
                }

                if let Some(else_node) = else_branch {
                    write!(f, "{}else ", indent_str)?;
                    else_node.fmt_with_indent(f, indent, table)?;
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
                body.fmt_with_indent(f, indent, table)?
            }

            AstNodeKind::WhileLoop { condition, body } => {
                write!(f, "{}while (", indent_str)?;
                condition.fmt_with_indent(f, 0, table)?;
                write!(f, ") ")?;
                body.fmt_with_indent(f, indent, table)?
            }

            AstNodeKind::Return(Some(expr)) => {
                write!(f, "{}return ", indent_str)?;
                expr.fmt_with_indent(f, 0, table)?
            }
            AstNodeKind::Return(None) => write!(f, "{}return", indent_str)?,
            AstNodeKind::Break => write!(f, "{}break", indent_str)?,
            AstNodeKind::Continue => write!(f, "{}continue", indent_str)?,

            AstNodeKind::FunctionParameter {
                name,
                type_annotation,
                mutable,
            } => {
                write!(f, "{}", indent_str)?;
                write!(
                    f,
                    "{}{}: ",
                    if *mutable { "mut ".purple() } else { "".white() },
                    name.yellow(),
                )?;
                type_annotation.fmt_with_indent(f, 0, table)?;
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
                        param.fmt_with_indent(f, 0, table)?;
                    }
                    write!(f, "]")?;
                }

                writeln!(f, " {}", "{".dimmed())?;

                for field in fields {
                    field.fmt_with_indent(f, child_indent, table)?;
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
                write!(
                    f,
                    "{} ",
                    match qualifier {
                        QualifierKind::Public => "public".purple(),
                        QualifierKind::Private => "private".purple(),
                    }
                )?;

                write!(f, "{}", name.yellow())?;
                write!(f, ": ")?;
                type_annotation.fmt_with_indent(f, 0, table)?;
            }
            AstNodeKind::StructLiteral { name, fields } => {
                write!(f, "{}{}{}", indent_str, name.yellow(), " ".dimmed())?;
                write!(f, "{}", "{".dimmed())?;

                for (i, (field_name, expr)) in fields.iter().enumerate() {
                    write!(f, " ")?;
                    write!(f, "{}: ", field_name.yellow())?;
                    expr.fmt_with_indent(f, 0, table)?;

                    write!(f, "{}", if i + 1 < fields.len() { "," } else { " " })?;
                }

                write!(f, "{}{}", indent_str, "}".dimmed())?
            }
            AstNodeKind::EnumDeclaration { name, variants } => {
                write!(f, "{}enum {}", indent_str, name.yellow())?;
                writeln!(f, " {}", "{".dimmed())?;

                for (_, (variant, expr)) in variants {
                    write!(f, "{}", " ".repeat(child_indent + 4))?;
                    variant.fmt_with_indent(f, 0, table)?;

                    if let Some(expr) = expr {
                        write!(f, " = ")?;
                        expr.fmt_with_indent(f, 0, table)?;
                    }
                    writeln!(f)?;
                }

                write!(f, "{}{}", indent_str, "}".dimmed())?
            }
            AstNodeKind::EnumVariant(name) => write!(f, "{}", name)?,
            AstNodeKind::TypeReference {
                type_name,
                generic_types,
                reference_kind,
            } => {
                let type_name = match reference_kind {
                    ReferenceKind::Value => type_name.clone(),
                    ReferenceKind::MutableReference => format!("&mut {type_name}"),
                    ReferenceKind::Reference => format!("&{type_name}"),
                };

                write!(f, "{}{}", indent_str, type_name.bright_blue())?;
                if !generic_types.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in generic_types.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        param.fmt_with_indent(f, 0, table)?;
                    }
                    write!(f, "]")?;
                }
            }
            AstNodeKind::TypeDeclaration {
                name,
                generic_parameters,
                value,
            } => {
                write!(f, "{}", "type ".purple())?;
                write!(f, "{}", name)?;

                if !generic_parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in generic_parameters.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        param.fmt_with_indent(f, 0, table)?;
                    }
                    write!(f, "]")?;
                }

                write!(f, "= ")?;
                value.fmt_with_indent(f, 0, table)?;
            }
            AstNodeKind::FieldAccess { left, right } => {
                write!(f, "{}(", indent_str)?;
                left.fmt_with_indent(f, 0, table)?;
                write!(f, ".")?;
                right.fmt_with_indent(f, 0, table)?;
                write!(f, ")")?
            }
            AstNodeKind::FunctionCall { function, arguments } => {
                write!(f, "{}", indent_str)?;
                function.fmt_with_indent(f, 0, table)?;
                write!(f, "(")?;
                for (i, param) in arguments.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    param.fmt_with_indent(f, 0, table)?;
                }
                write!(f, ")")?
            }
            AstNodeKind::TraitDeclaration {
                name,
                generic_parameters,
                signatures,
                types,
                constants,
            } => {
                write!(f, "{}trait", indent_str)?;
                if !generic_parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in generic_parameters.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        param.fmt_with_indent(f, 0, table)?;
                    }
                    write!(f, "]")?;
                }

                write!(f, " {}", name.yellow())?;

                writeln!(f, " {}", "{".dimmed())?;

                for type_node in types {
                    write!(f, "{}    ", indent_str)?;
                    type_node.fmt_with_indent(f, 0, table)?;
                    writeln!(f)?;
                }

                for constant in constants {
                    write!(f, "{}    ", indent_str)?;
                    constant.fmt_with_indent(f, 0, table)?;
                    writeln!(f)?;
                }

                for signature in signatures {
                    signature.fmt_with_indent(f, child_indent, table)?;
                    writeln!(f)?;
                }

                write!(f, "{}{}", indent_str, "}".dimmed())?
            }
            AstNodeKind::TraitConstant {
                name,
                type_annotation,
            } => {
                write!(f, "{}const {}: ", indent_str, name.yellow())?;
                type_annotation.fmt_with_indent(f, 0, table)?;
            }
            AstNodeKind::TraitType(name) => {
                write!(f, "{}type {}", indent_str, name.bright_blue())?;
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
            }
            AstNodeKind::FunctionPointer { params, return_type } => {
                write!(f, "{}{}", indent_str, "fn".bright_blue())?;
                write!(f, "(")?;
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    param.fmt_with_indent(f, 0, table)?;
                }
                write!(f, ")")?;

                if let Some(return_type) = return_type {
                    write!(f, ": ")?;
                    return_type.fmt_with_indent(f, 0, table)?;
                }
            }
            AstNodeKind::ExpressionStatement(expr) => {
                expr.fmt_with_indent(f, indent, table)?;
                write!(f, ";")?;
            }
        }

        if let (Some(ty), Some(table)) = (&self.type_id, table) {
            if ty.get_base_symbol() == PrimitiveKind::Void as usize {
                return Ok(());
            }
            
            let type_str = table.display_type(ty);
            write!(f, " {}", format!("<{}>", type_str).cyan())?;
        } else if let Some(ty) = &self.type_id {
            if ty.get_base_symbol() == PrimitiveKind::Void as usize {
                return Ok(());
            }

            write!(f, " {}", format_args!("[{}]", ty))?;
        }

        if let Some(id) = self.value_id {
            write!(f, " [Symbol({})]", id)?;
        }

        Ok(())
    }
}

impl AstNode {
    pub fn children_mut(&mut self) -> Vec<&mut AstNode> {
        use AstNodeKind::*;

        match &mut self.kind {
            IntegerLiteral(_)
            | FloatLiteral(_)
            | BooleanLiteral(_)
            | StringLiteral(_)
            | CharLiteral(_)
            | Identifier(_)
            | EnumVariant(_)
            | SelfExpr
            | SelfType(_) => vec![],

            Program(statements) => statements.iter_mut().collect(),

            VariableDeclaration {
                type_annotation,
                initializer,
                ..
            } => {
                let mut children = vec![];

                if let Some(node) = type_annotation.as_mut() {
                    children.push(node.as_mut());
                }

                children.push(initializer);

                children
            }

            UnaryOperation { operand, .. } => vec![operand.as_mut()],

            BinaryOperation { left, right, .. } | ConditionalOperation { left, right, .. } => {
                vec![left.as_mut(), right.as_mut()]
            },
            HeapExpression(expr) => vec![expr.as_mut()],

            TypeCast { expr, target_type } => vec![expr.as_mut(), target_type.as_mut()],
            PathQualifier { ty, tr } => {
                let mut children = vec![ty.as_mut()];
                if let Some(trait_node) = tr.as_mut() {
                    children.push(trait_node.as_mut());
                }
                children
            }

            Block(statements) => statements.iter_mut().collect(),

            IfStatement {
                condition,
                then_branch,
                else_if_branches,
                else_branch,
            } => {
                let mut children = vec![];

                children.push(condition.as_mut());
                children.push(then_branch.as_mut());

                for (elif_cond, elif_branch) in else_if_branches.iter_mut() {
                    children.push(elif_cond.as_mut());
                    children.push(elif_branch.as_mut());
                }

                if let Some(else_node) = else_branch.as_mut() {
                    children.push(else_node.as_mut());
                }

                children
            }

            ForLoop {
                initializer,
                condition,
                increment,
                body,
            } => {
                let mut children = vec![];

                if let Some(init) = initializer.as_mut() {
                    children.push(init.as_mut());
                }

                if let Some(cond) = condition.as_mut() {
                    children.push(cond.as_mut());
                }

                if let Some(inc) = increment.as_mut() {
                    children.push(inc.as_mut());
                }

                children.push(body.as_mut());

                children
            }

            WhileLoop { condition, body } => vec![condition.as_mut(), body.as_mut()],

            Return(opt_expr) => {
                if let Some(expr) = opt_expr.as_mut() {
                    vec![expr.as_mut()]
                } else {
                    vec![]
                }
            }

            Break | Continue => vec![],

            Function {
                generic_parameters,
                parameters,
                return_type,
                body,
                ..
            } => {
                let mut children = vec![];

                children.extend(generic_parameters.iter_mut());
                children.extend(parameters.iter_mut());

                if let Some(rt) = return_type.as_mut() {
                    children.push(rt.as_mut());
                }

                if let Some(b) = body.as_mut() {
                    children.push(b.as_mut());
                }

                children
            }

            FunctionPointer { params, return_type } => {
                let mut children = vec![];

                for p in params.iter_mut() {
                    children.push(p);
                }

                if let Some(ret) = return_type.as_mut() {
                    children.push(ret.as_mut());
                }

                children
            }

            FunctionParameter {
                type_annotation, ..
            } => vec![type_annotation.as_mut()],

            StructDeclaration {
                generic_parameters,
                fields,
                ..
            } => {
                let mut children = vec![];

                for gp in generic_parameters.iter_mut() {
                    children.push(gp);
                }

                for field_node in fields.iter_mut() {
                    children.push(field_node);
                }

                children
            }

            StructField {
                type_annotation, ..
            } => vec![type_annotation.as_mut()],

            StructLiteral { fields, .. } => fields.values_mut().collect(),

            EnumDeclaration { variants, .. } => {
                let mut children = vec![];

                for (_, (variant_node, opt_payload)) in variants.iter_mut() {
                    children.push(variant_node);
                    if let Some(payload) = opt_payload.as_mut() {
                        children.push(payload);
                    }
                }

                children
            }

            ImplDeclaration {
                generic_parameters,
                trait_node,
                type_reference,
                associated_constants,
                associated_functions,
                associated_types,
            } => {
                let mut children = vec![];

                for gp in generic_parameters.iter_mut() {
                    children.push(gp);
                }

                if let Some(tn) = trait_node.as_mut() {
                    children.push(tn.as_mut());
                }

                children.push(type_reference.as_mut());

                for const_node in associated_constants.iter_mut() {
                    children.push(const_node);
                }

                for func_node in associated_functions.iter_mut() {
                    children.push(func_node);
                }

                for type_node in associated_types.iter_mut() {
                    children.push(type_node);
                }

                children
            }

            AssociatedConstant {
                type_annotation,
                initializer,
                ..
            } => {
                let mut children = vec![];

                if let Some(ta) = type_annotation.as_mut() {
                    children.push(ta.as_mut());
                }

                children.push(initializer.as_mut());
                children
            }

            AssociatedType { value, .. } => vec![value.as_mut()],

            TraitDeclaration {
                generic_parameters,
                types,
                constants,
                signatures,
                ..
            } => {
                let mut children = vec![];

                for gp in generic_parameters.iter_mut() {
                    children.push(gp);
                }

                for t in types.iter_mut() {
                    children.push(t);
                }

                for c in constants.iter_mut() {
                    children.push(c);
                }

                for s in signatures.iter_mut() {
                    children.push(s);
                }

                children
            }

            TraitConstant {
                type_annotation, ..
            } => vec![type_annotation.as_mut()],

            TraitType(_) => vec![],

            TypeReference { generic_types, .. } => generic_types.iter_mut().collect(),

            TypeDeclaration {
                generic_parameters,
                value,
                ..
            } => {
                let mut children = vec![];

                for gp in generic_parameters.iter_mut() {
                    children.push(gp);
                }

                children.push(value.as_mut());
                children
            }

            FieldAccess { left, right } => vec![left.as_mut(), right.as_mut()],

            FunctionCall {
                function,
                arguments,
            } => {
                let mut children = vec![];
                children.push(function.as_mut());

                for arg in arguments.iter_mut() {
                    children.push(arg);
                }

                children
            }

            GenericParameter { .. } => vec![],
            ExpressionStatement(expr) => vec![expr.as_mut()],
        }
    }

    pub fn children(&self) -> Vec<&AstNode> {
        use AstNodeKind::*;

        match &self.kind {
            IntegerLiteral(_)
            | FloatLiteral(_)
            | BooleanLiteral(_)
            | StringLiteral(_)
            | CharLiteral(_)
            | Identifier(_)
            | EnumVariant(_)
            | SelfExpr
            | SelfType(_) => vec![],

            Program(statements) => statements.iter().collect(),

            VariableDeclaration {
                type_annotation,
                initializer,
                ..
            } => {
                let mut children = vec![];

                if let Some(node) = type_annotation.as_ref() {
                    children.push(node.as_ref());
                }

                children.push(initializer);

                children
            }

            UnaryOperation { operand, .. } => vec![operand.as_ref()],

            BinaryOperation { left, right, .. } | ConditionalOperation { left, right, .. } => {
                vec![left.as_ref(), right.as_ref()]
            },
            HeapExpression(expr) => vec![expr.as_ref()],

            TypeCast { expr, target_type } => vec![expr.as_ref(), target_type.as_ref()],
            PathQualifier { ty, tr } => {
                let mut children = vec![ty.as_ref()];
                if let Some(trait_node) = tr.as_ref() {
                    children.push(trait_node.as_ref());
                }
                children
            }

            Block(statements) => statements.iter().collect(),

            IfStatement {
                condition,
                then_branch,
                else_if_branches,
                else_branch,
            } => {
                let mut children = vec![];

                children.push(condition.as_ref());
                children.push(then_branch.as_ref());

                for (elif_cond, elif_branch) in else_if_branches.iter() {
                    children.push(elif_cond.as_ref());
                    children.push(elif_branch.as_ref());
                }

                if let Some(else_node) = else_branch.as_ref() {
                    children.push(else_node.as_ref());
                }

                children
            }

            ForLoop {
                initializer,
                condition,
                increment,
                body,
            } => {
                let mut children = vec![];

                if let Some(init) = initializer.as_ref() {
                    children.push(init.as_ref());
                }

                if let Some(cond) = condition.as_ref() {
                    children.push(cond.as_ref());
                }

                if let Some(inc) = increment.as_ref() {
                    children.push(inc.as_ref());
                }

                children.push(body.as_ref());

                children
            }

            WhileLoop { condition, body } => vec![condition.as_ref(), body.as_ref()],

            Return(opt_expr) => {
                if let Some(expr) = opt_expr.as_ref() {
                    vec![expr.as_ref()]
                } else {
                    vec![]
                }
            }

            Break | Continue => vec![],

            Function {
                generic_parameters,
                parameters,
                return_type,
                body,
                ..
            } => {
                let mut children = vec![];

                children.extend(generic_parameters.iter());
                children.extend(parameters.iter());

                if let Some(rt) = return_type.as_ref() {
                    children.push(rt.as_ref());
                }

                if let Some(b) = body.as_ref() {
                    children.push(b.as_ref());
                }

                children
            }

            FunctionPointer { params, return_type } => {
                let mut children = vec![];

                for p in params.iter() {
                    children.push(p);
                }

                if let Some(ret) = return_type.as_ref() {
                    children.push(ret.as_ref());
                }

                children
            }

            FunctionParameter {
                type_annotation, ..
            } => vec![type_annotation.as_ref()],

            StructDeclaration {
                generic_parameters,
                fields,
                ..
            } => {
                let mut children = vec![];

                for gp in generic_parameters.iter() {
                    children.push(gp);
                }

                for field_node in fields.iter() {
                    children.push(field_node);
                }

                children
            }

            StructField {
                type_annotation, ..
            } => vec![type_annotation.as_ref()],

            StructLiteral { fields, .. } => fields.values().collect(),

            EnumDeclaration { variants, .. } => {
                let mut children = vec![];

                for (_, (variant_node, opt_payload)) in variants.iter() {
                    children.push(variant_node);
                    if let Some(payload) = opt_payload.as_ref() {
                        children.push(payload);
                    }
                }

                children
            }

            ImplDeclaration {
                generic_parameters,
                trait_node,
                type_reference,
                associated_constants,
                associated_functions,
                associated_types,
            } => {
                let mut children = vec![];

                for gp in generic_parameters.iter() {
                    children.push(gp);
                }

                if let Some(tn) = trait_node.as_ref() {
                    children.push(tn.as_ref());
                }

                children.push(type_reference.as_ref());

                for const_node in associated_constants.iter() {
                    children.push(const_node);
                }

                for func_node in associated_functions.iter() {
                    children.push(func_node);
                }

                for type_node in associated_types.iter() {
                    children.push(type_node);
                }

                children
            }

            AssociatedConstant {
                type_annotation,
                initializer,
                ..
            } => {
                let mut children = vec![];

                if let Some(ta) = type_annotation.as_ref() {
                    children.push(ta.as_ref());
                }

                children.push(initializer.as_ref());
                children
            }

            AssociatedType { value, .. } => vec![value.as_ref()],

            TraitDeclaration {
                generic_parameters,
                types,
                constants,
                signatures,
                ..
            } => {
                let mut children = vec![];

                for gp in generic_parameters.iter() {
                    children.push(gp);
                }

                for t in types.iter() {
                    children.push(t);
                }

                for c in constants.iter() {
                    children.push(c);
                }

                for s in signatures.iter() {
                    children.push(s);
                }

                children
            }

            TraitConstant {
                type_annotation, ..
            } => vec![type_annotation.as_ref()],

            TraitType(_) => vec![],

            TypeReference { generic_types, .. } => generic_types.iter().collect(),

            TypeDeclaration {
                generic_parameters,
                value,
                ..
            } => {
                let mut children = vec![];

                for gp in generic_parameters.iter() {
                    children.push(gp);
                }

                children.push(value.as_ref());
                children
            }

            FieldAccess { left, right } => vec![left.as_ref(), right.as_ref()],

            FunctionCall {
                function,
                arguments,
            } => {
                let mut children = vec![];
                children.push(function.as_ref());

                for arg in arguments.iter() {
                    children.push(arg);
                }

                children
            }

            GenericParameter { .. } => vec![],
            ExpressionStatement(expr) => vec![expr.as_ref()],
        }
    }
}