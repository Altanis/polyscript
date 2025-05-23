use crate::{frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, utils::{error::*, kind::Span}};

use super::semantic_analyzer::{SemanticAnalyzer, Symbol, SymbolKind};

impl SemanticAnalyzer {
    pub fn symbol_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];

        let AstNodeKind::Program(statements) = &mut program.kind else { panic!("fed node that is not a Program"); };
        for statement in statements {
            match self.collect_node_symbol(statement) {
                Ok(symbol) => statement.symbol = symbol, 
                Err(err) => errors.push(*err)
            }
        }

        errors
    }

    fn collect_node_symbol(&mut self, statement: &mut AstNode) -> Result<Option<(usize, String)>, BoxedError> {
        match &mut statement.kind {
            AstNodeKind::VariableDeclaration { name, mutable, .. } => 
                self.collect_variable_symbol(name.clone(), *mutable, statement.span),
            AstNodeKind::UnaryOperation { operand, .. } 
                => self.collect_unary_operation_symbols(operand),
            AstNodeKind::BinaryOperation { left, right, .. } 
            | AstNodeKind::ConditionalOperation { left, right, .. }
                => self.collect_binary_operation_symbols(left, right),
            AstNodeKind::Block(statements) 
                => self.collect_block_symbols(statements),
            AstNodeKind::IfStatement { condition, then_branch, else_if_branches, else_branch }
                => self.collect_conditional_symbols(condition, then_branch, else_if_branches, else_branch),
            AstNodeKind::ForLoop { initializer, condition, increment, body }
                => self.collect_for_loop_symbols(initializer, condition, increment, body),
            AstNodeKind::WhileLoop { condition, body }
                => self.collect_while_loop_symbols(condition, body),
            AstNodeKind::Return(node) => {
                if let Some(node) = node.as_mut() {
                    self.collect_return_statement_symbols(node)
                } else {
                    Ok(None)
                }
            },
            AstNodeKind::Throw(node) => self.collect_throw_statement_symbols(node),
            AstNodeKind::FunctionDeclaration { signature, body } 
                => self.collect_signature_symbols(signature, body, statement.span),
            AstNodeKind::StructDeclaration { name, .. } 
                => self.collect_struct_symbols(name.clone(), statement.span),
            // AstNodeKind::EnumDeclaration { name, variants } 
                // => self.collect_enum_symbols(name.clone(), statement.span),
            AstNodeKind::TraitDeclaration { name, .. } 
                => self.collect_trait_symbols(name.clone(), statement.span),
            AstNodeKind::TypeDeclaration { name, .. } 
                => self.collect_type_symbols(name.clone(), statement.span),
            _ => Ok(None)
        }
    }

    fn collect_variable_symbol(&mut self, name: String, mutable: bool, span: Span) -> Result<Option<(usize, String)>, BoxedError> {
        Ok(Some((self.symbol_table.current_scope_mut().add_symbol(Symbol {
            name: name.clone(),
            kind: SymbolKind::Variable,
            type_info: None,
            mutable,
            span,
            public: None,
            generic_parameters: vec![],
            scope_id: 0
        })?, name.clone())))
    }

    fn collect_unary_operation_symbols(&mut self, operand: &mut AstNode) -> Result<Option<(usize, String)>, BoxedError> {
        self.collect_node_symbol(operand)?;
        Ok(None)
    }

    fn collect_binary_operation_symbols(&mut self, left: &mut AstNode, right: &mut AstNode) -> Result<Option<(usize, String)>, BoxedError> {
        self.collect_node_symbol(left)?;
        self.collect_node_symbol(right)?;
        Ok(None)
    }

    fn collect_signature_symbols(&mut self, signature: &mut BoxedAstNode, body: &mut BoxedAstNode, span: Span) -> Result<Option<(usize, String)>, BoxedError> {
        let AstNodeKind::FunctionSignature { name, generic_parameters, parameters, .. } 
            = &mut signature.kind else { panic!("FunctionDeclaration node is not holding a FunctionSignature"); };

        let ret = (self.symbol_table.current_scope_mut().add_symbol(Symbol {
            name: name.clone(),
            kind: SymbolKind::Function,
            type_info: None,
            mutable: false,
            span,
            public: None,
            generic_parameters: vec![],
            scope_id: 0
        })?, name.clone());

        self.symbol_table.enter_scope();

        for generic_parameter in generic_parameters.iter_mut() {
            let AstNodeKind::GenericParameter { name, .. } = &generic_parameter.kind else {
                panic!("FunctionDeclaration node has generic parameter not of kind GenericParameter");
            };

            generic_parameter.symbol = Some((self.symbol_table.current_scope_mut().add_symbol(Symbol {
                name: name.clone(),
                kind: SymbolKind::TypeAlias,
                type_info: None,
                generic_parameters: vec![],
                mutable: false,
                span: generic_parameter.span,
                public: None,
                scope_id: 0
            })?, name.clone()));
        }

        for parameter in parameters.iter_mut() {
            let AstNodeKind::FunctionParameter { name, .. } = &parameter.kind else {
                panic!("FunctionDeclaration node has generic parameter not of kind FunctionParameter");
            };

            parameter.symbol = Some((self.symbol_table.current_scope_mut().add_symbol(Symbol {
                name: name.clone(),
                kind: SymbolKind::Variable,
                type_info: None,
                generic_parameters: vec![],
                mutable: false,
                span: parameter.span,
                public: None,
                scope_id: 0
            })?, name.clone()));
        }

        self.collect_node_symbol(body)?;

        self.symbol_table.exit_scope();

        Ok(Some(ret))
    }

    fn collect_struct_symbols(&mut self, name: String, span: Span) -> Result<Option<(usize, String)>, BoxedError> {
        Ok(Some((self.symbol_table.current_scope_mut().add_symbol(Symbol {
            name: name.clone(),
            kind: SymbolKind::Struct,
            type_info: None,
            mutable: false,
            span,
            public: None,
            generic_parameters: vec![],
            scope_id: 0
        })?, name.clone())))
    }

    fn collect_enum_symbols(&mut self, name: String, span: Span) -> Result<Option<(usize, String)>, BoxedError> {
        Ok(Some((self.symbol_table.current_scope_mut().add_symbol(Symbol {
            name: name.clone(),
            kind: SymbolKind::Enum,
            type_info: None,
            mutable: false,
            span,
            public: None,
            generic_parameters: vec![],
            scope_id: 0
        })?, name.clone())))
    }

    fn collect_trait_symbols(&mut self, name: String, span: Span) -> Result<Option<(usize, String)>, BoxedError> {
        Ok(Some((self.symbol_table.current_scope_mut().add_symbol(Symbol {
            name: name.clone(),
            kind: SymbolKind::Trait,
            type_info: None,
            mutable: false,
            span,
            public: None,
            generic_parameters: vec![],
            scope_id: 0
        })?, name.clone())))
    }

    fn collect_type_symbols(&mut self, name: String, span: Span) -> Result<Option<(usize, String)>, BoxedError> {
        Ok(Some((self.symbol_table.current_scope_mut().add_symbol(Symbol {
            name: name.clone(),
            kind: SymbolKind::TypeAlias,
            type_info: None,
            mutable: false,
            span,
            public: None,
            generic_parameters: vec![],
            scope_id: 0
        })?, name.clone())))
    }

    fn collect_block_symbols(&mut self, statements: &mut [AstNode]) -> Result<Option<(usize, String)>, BoxedError> {
        self.symbol_table.enter_scope();
        
        for statement in statements.iter_mut() {
            statement.symbol = self.collect_node_symbol(statement)?;
        }

        self.symbol_table.exit_scope();

        Ok(None)
    }

    fn collect_conditional_symbols(&mut self, condition: &mut BoxedAstNode, then_branch: &mut BoxedAstNode, else_if_branches: &mut [(BoxedAstNode, BoxedAstNode)], else_branch: &mut Option<BoxedAstNode>) -> Result<Option<(usize, String)>, BoxedError> {
        self.collect_node_symbol(condition)?;
        self.collect_node_symbol(then_branch)?;

        for (condition, branch) in else_if_branches.iter_mut() {
            self.collect_node_symbol(condition)?;
            self.collect_node_symbol(branch)?;
        }

        if let Some(else_branch) = else_branch {
            self.collect_node_symbol(else_branch)?;
        }

        Ok(None)
    }

    fn collect_for_loop_symbols(&mut self, initializer: &mut Option<BoxedAstNode>, condition: &mut Option<BoxedAstNode>, increment: &mut Option<BoxedAstNode>, body: &mut BoxedAstNode) -> Result<Option<(usize, String)>, BoxedError> {
        self.symbol_table.enter_scope();

        if let Some(initializer) = initializer {
            self.collect_node_symbol(initializer)?;
        }

        if let Some(condition) = condition {
            self.collect_node_symbol(condition)?;
        }

        if let Some(increment) = increment {
            self.collect_node_symbol(increment)?;
        }

        self.collect_node_symbol(body)?;

        self.symbol_table.exit_scope();

        Ok(None)
    }

    fn collect_while_loop_symbols(&mut self, condition: &mut BoxedAstNode, body: &mut BoxedAstNode) -> Result<Option<(usize, String)>, BoxedError> {
        self.symbol_table.enter_scope();
        self.collect_node_symbol(condition)?;
        self.collect_node_symbol(body)?;
        self.symbol_table.exit_scope();

        Ok(None)
    }

    fn collect_return_statement_symbols(&mut self, node: &mut BoxedAstNode) -> Result<Option<(usize, String)>, BoxedError> {
        self.collect_node_symbol(node)?;
        Ok(None)
    }

    fn collect_throw_statement_symbols(&mut self, node: &mut BoxedAstNode) -> Result<Option<(usize, String)>, BoxedError> {
        self.collect_node_symbol(node)?;
        Ok(None)
    }
}