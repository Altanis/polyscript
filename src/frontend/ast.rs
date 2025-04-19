use crate::utils::token::{Operation, Span};

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

#[derive(Debug, Clone)]
pub struct FunctionParameter {
    pub name: String,
    pub type_annotation: Node,
    pub default_value: Option<Node>,
}