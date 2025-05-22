use crate::{frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, utils::{error::Error, kind::Span}};

use super::semantic_analyzer::{SemanticAnalyzer, Symbol, SymbolKind};

impl SemanticAnalyzer {
    pub fn symbol_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];

        let AstNodeKind::Program(statements) = &mut program.kind else { panic!("fed node that is not a Program"); };
        for statement in statements {
            match self.collect_statement_symbol(statement) {
                Ok(symbol) => statement.symbol = symbol, 
                Err(err) => errors.push(*err)
            }
        }

        errors
    }

    fn collect_statement_symbol(&mut self, statement: &mut AstNode) -> Result<Option<(usize, String)>, Box<Error>> {
            match &mut statement.kind {
                AstNodeKind::VariableDeclaration { name, mutable, .. } => 
                    self.collect_variable_symbol(name.clone(), *mutable, statement.span),
                AstNodeKind::FunctionDeclaration { signature, .. } => 
                    self.collect_signature_symbols(signature, statement.span),
                AstNodeKind::StructDeclaration { name, .. } 
                    => self.collect_struct_symbols(name.clone(), statement.span),
                AstNodeKind::EnumDeclaration { name, .. } 
                    => self.collect_enum_symbols(name.clone(), statement.span),
                AstNodeKind::TraitDeclaration { name, .. } 
                    => self.collect_trait_symbols(name.clone(), statement.span),
                AstNodeKind::TypeDeclaration { name, .. } 
                    => self.collect_type_symbols(name.clone(), statement.span),
                AstNodeKind::Block(statements)
                    => self.collect_block_symbols(statements),
                AstNodeKind::IfStatement { then_branch, else_if_branches, else_branch, .. }
                    => self.collect_conditional_symbols(then_branch, else_if_branches, else_branch),
                _ => Ok(None)
            }
    }

    fn collect_variable_symbol(&mut self, name: String, mutable: bool, span: Span) -> Result<Option<(usize, String)>, Box<Error>> {
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

    fn collect_signature_symbols(&mut self, signature: &mut BoxedAstNode, span: Span) -> Result<Option<(usize, String)>, Box<Error>> {
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

        self.symbol_table.exit_scope();

        Ok(Some(ret))
    }

    fn collect_struct_symbols(&mut self, name: String, span: Span) -> Result<Option<(usize, String)>, Box<Error>> {
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

    fn collect_enum_symbols(&mut self, name: String, span: Span) -> Result<Option<(usize, String)>, Box<Error>> {
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

    fn collect_trait_symbols(&mut self, name: String, span: Span) -> Result<Option<(usize, String)>, Box<Error>> {
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

    fn collect_type_symbols(&mut self, name: String, span: Span) -> Result<Option<(usize, String)>, Box<Error>> {
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

    fn collect_block_symbols(&mut self, statements: &mut [AstNode]) -> Result<Option<(usize, String)>, Box<Error>> {
        self.symbol_table.enter_scope();
        
        for statement in statements.iter_mut() {
            statement.symbol = self.collect_statement_symbol(statement)?;
        }

        self.symbol_table.exit_scope();

        Ok(None)
    }

    fn collect_conditional_symbols(&mut self, then_branch: &mut BoxedAstNode, else_if_branches: &mut [(BoxedAstNode, BoxedAstNode)], else_branch: &mut Option<BoxedAstNode>) -> Result<Option<(usize, String)>, Box<Error>> {
        let AstNodeKind::Block(statement) = &mut then_branch.kind else {
            panic!("then_branch is not a Block node");
        };
        self.collect_block_symbols(statement)?;

        for (_, else_branch) in else_if_branches.iter_mut() {
            let AstNodeKind::Block(statements) = &mut else_branch.kind else {
                panic!("else_if_branches do not comprise Block nodes");
            };

            self.collect_block_symbols(statements)?;
        }

        if let Some(branch) = else_branch {
            let AstNodeKind::Block(statement) = &mut branch.kind else {
                panic!("else_branch is not a Block node");
            };
            self.collect_block_symbols(statement)?;
        }

        Ok(None)
    }
}