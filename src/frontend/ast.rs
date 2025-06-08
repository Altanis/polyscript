use colored::*;
use indexmap::IndexMap;
use crate::{backend::semantic_analyzer::{ValueSymbol, SymbolId, SymbolTable, TypeSymbol}, utils::kind::*};

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
        type_annotation: Option<BoxedAstNode>,
        initializer: Option<BoxedAstNode>,
    },
    
    // OPERATIONS //
    UnaryOperation {
        operator: Operation,
        operand: BoxedAstNode,
        prefix: bool
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
    
    // CONTROL FLOW //
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
    
    // FUNCTIONS //
    FunctionSignature {
        name: String,
        generic_parameters: Vec<AstNode>,
        parameters: Vec<AstNode>,
        return_type: Option<BoxedAstNode>,
        instance: Option<bool>
    },
    FunctionPointer {
        params: Vec<AstNode>,
        return_type: Option<BoxedAstNode>
    },
    FunctionDeclaration {
        signature: BoxedAstNode,
        body: BoxedAstNode,
    },
    FunctionParameter {
        name: String,
        type_annotation: BoxedAstNode,
        initializer: Option<BoxedAstNode>,
        mutable: bool
    },
    FunctionExpression {
        signature: BoxedAstNode,
        body: BoxedAstNode
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
        type_annotation: BoxedAstNode
    },
    StructLiteral {
        name: String,
        fields: IndexMap<String, AstNode>
    },

    // ENUMS //
    EnumDeclaration {
        name: String,
        variants: IndexMap<String, (AstNode, Option<AstNode>)>
    },
    EnumVariant(String),


    // IMPLEMENTATIONS //
    ImplDeclaration {
        generic_parameters: Vec<AstNode>,
        type_reference: BoxedAstNode,
        trait_node: Option<BoxedAstNode>,
        associated_constants: Vec<AstNode>,
        associated_functions: Vec<AstNode>,
        associated_types: Vec<AstNode>
    },
    AssociatedConstant {
        qualifier: QualifierKind,
        name: String,
        type_annotation: Option<BoxedAstNode>,
        initializer: BoxedAstNode
    },
    AssociatedFunction {
        qualifier: QualifierKind,
        signature: BoxedAstNode,
        body: BoxedAstNode,
    },
    AssociatedType {
        qualifier: QualifierKind,
        name: String,
        value: BoxedAstNode
    },

    SelfValue,
    SelfType(Option<Operation>),

    FieldAccess {
        left: BoxedAstNode,
        right: BoxedAstNode,
    },
    FunctionCall {
        function: BoxedAstNode,
        arguments: Vec<AstNode>
    },

    // TRAITS //
    TraitDeclaration {
        name: String,
        generic_parameters: Vec<AstNode>,
        types: Vec<AstNode>,
        constants: Vec<AstNode>,
        signatures: Vec<AstNode>
    },
    TraitConstant {
        name: String,
        type_annotation: BoxedAstNode
    },
    TraitType(String),

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
        value: BoxedAstNode,
    },

    // PROGRAM //
    Program(Vec<AstNode>)
}

#[derive(Debug, Clone)]
pub struct AstNode {
    pub kind: AstNodeKind,
    pub span: Span,
    pub value_id: Option<SymbolId>,
    pub type_id: Option<SymbolId>
}

pub type BoxedAstNode = Box<AstNode>;

impl AstNode {
    pub fn get_value_symbol<'a>(&self, symbol_table: &'a SymbolTable) -> Option<&'a ValueSymbol> {
        if let Some(id) = &self.value_id {
            return symbol_table.direct_value_symbol_lookup(id);
        }

        None
    }

    pub fn get_value_symbol_mut<'a>(&self, symbol_table: &'a mut SymbolTable) -> Option<&'a mut ValueSymbol> {
        if let Some(id) = &self.value_id {
            return symbol_table.direct_value_symbol_lookup_mut(id);
        }

        None
    }

    pub fn get_type_symbol<'a>(&self, symbol_table: &'a SymbolTable) -> Option<&'a TypeSymbol> {
        if let Some(id) = &self.value_id {
            return symbol_table.direct_type_symbol_lookup(id);
        }

        None
    }

    pub fn get_type_symbol_mut<'a>(&self, symbol_table: &'a mut SymbolTable) -> Option<&'a mut TypeSymbol> {
        if let Some(id) = &self.value_id {
            return symbol_table.direct_type_symbol_lookup_mut(id);
        }

        None
    }
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
                trait_node: trait_name,
                associated_constants,
                associated_functions,
                associated_types
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
                for type_node in associated_types {
                    writeln!(f, "    {}", type_node)?;
                }
                for constant in associated_constants {
                    writeln!(f, "    {}", constant)?;
                }
                for function in associated_functions {
                    writeln!(f, "    {}", function)?;
                }
                write!(f, "{}", "}".dimmed())?
            }

            AstNodeKind::AssociatedType { qualifier, name, value } => {
                write!(f, "{} ", match qualifier {
                    QualifierKind::Public => "public",
                    QualifierKind::Private => "private"
                }.purple())?;

                write!(f, "type ")?;
                write!(f, "{}", name.yellow())?;
                write!(f, " = {}", value)?;
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

            AstNodeKind::FunctionParameter {
                name,
                type_annotation,
                initializer,
                mutable
            } => {
                write!(f, "{}", indent_str)?;
                write!(f, "{}{}: {}", if *mutable { "mut ".purple() } else { "".white() }, name.yellow(), type_annotation)?;
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
                
                for (_, (variant, expr)) in variants {
                    write!(f, "{}", " ".repeat(child_indent + 4))?;
                    write!(f, "{}", variant)?;

                    if let Some(expr) = expr {
                        write!(f, " = {}", expr)?;
                    }
                    writeln!(f)?;
                }
                
                write!(f, "{}{}", indent_str, "}".dimmed())?
            },
            AstNodeKind::EnumVariant(name) => write!(f, "{}", name)?,
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
            AstNodeKind::TraitDeclaration { name, generic_parameters, signatures, types, constants } => {
                write!(f, "{}trait", indent_str)?;
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

                write!(f, " {}", name.yellow())?;

                writeln!(f, " {}", "{".dimmed())?;

                for type_node in types {
                    write!(f, "{}    ", indent_str)?;
                    type_node.fmt_with_indent(f, 0)?;
                    writeln!(f)?;
                }

                for constant in constants {
                    write!(f, "{}    ", indent_str)?;
                    constant.fmt_with_indent(f, 0)?;
                    writeln!(f)?;
                }
                
                for signature in signatures {
                    signature.fmt_with_indent(f, child_indent)?;
                    writeln!(f)?;
                }
                
                write!(f, "{}{}", indent_str, "}".dimmed())?
            }
            AstNodeKind::TraitConstant { name, type_annotation } => {
                write!(f, "{}const {}: {}", indent_str, name.yellow(), type_annotation)?;
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

        if let Some((scope, str)) = &self.type_id {
            write!(f, " {}",
                format_args!("[type: ({}, {})]", scope, str)
            )?;
        }

        if let Some((_, name)) = &self.value_id {
            write!(f, " [symbol: {}]", name.magenta().bold())?;
        }

        Ok(())
    }
}

impl AstNode {
    pub fn children_mut(&mut self) -> Vec<&mut AstNode> {
        use AstNodeKind::*;
        
        match &mut self.kind {
            IntegerLiteral(_) | FloatLiteral(_) | BooleanLiteral(_) | StringLiteral(_) | CharLiteral(_)
            | Identifier(_) | EnumVariant(_) | SelfValue | SelfType(_) => vec![],

            Program(statements) => statements.iter_mut().collect(),

            VariableDeclaration { type_annotation, initializer, .. } => {
                let mut children = vec![];

                if let Some(node) = type_annotation.as_mut() {
                    children.push(node.as_mut());
                }

                if let Some(node) = initializer.as_mut() {
                    children.push(node.as_mut());
                }

                children
            }

            UnaryOperation { operand, .. } => vec![operand.as_mut()],

            BinaryOperation { left, right, .. }
            | ConditionalOperation { left, right, .. } =>
                vec![left.as_mut(), right.as_mut()],

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

            FunctionSignature {
                generic_parameters,
                parameters,
                return_type,
                ..
            } => {
                let mut children = vec![];

                for gp in generic_parameters.iter_mut() {
                    children.push(gp);
                }

                for param in parameters.iter_mut() {
                    children.push(param);
                }

                if let Some(ret) = return_type.as_mut() {
                    children.push(ret.as_mut());
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

            FunctionDeclaration { signature, body } =>
                vec![signature.as_mut(), body.as_mut()],

            FunctionParameter {
                type_annotation,
                initializer,
                ..
            } => {
                let mut children = vec![];
                children.push(type_annotation.as_mut());

                if let Some(init) = initializer.as_mut() {
                    children.push(init.as_mut());
                }

                children
            }

            FunctionExpression { signature, body } =>
                vec![signature.as_mut(), body.as_mut()],

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

            StructField { type_annotation, .. } => vec![type_annotation.as_mut()],

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
                type_reference,
                associated_constants,
                associated_functions,
                associated_types,
                ..
            } => {
                let mut children = vec![];

                for gp in generic_parameters.iter_mut() {
                    children.push(gp);
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

            AssociatedFunction { signature, body, .. } =>
                vec![signature.as_mut(), body.as_mut()],

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

            TraitConstant { type_annotation, .. } => vec![type_annotation.as_mut()],

            TraitType(_) => vec![],

            TypeReference { generic_types, .. } =>
                generic_types.iter_mut().collect(),

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

            FunctionCall { function, arguments } => {
                let mut children = vec![];
                children.push(function.as_mut());

                for arg in arguments.iter_mut() {
                    children.push(arg);
                }

                children
            },

            GenericParameter { .. } => vec![]
        }
    }
}