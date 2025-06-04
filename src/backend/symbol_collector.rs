use indexmap::IndexMap;
use crate::{frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, utils::{error::*, kind::{QualifierKind, Span}}};
use super::semantic_analyzer::{ScopeKind, SemanticAnalyzer, Symbol, SymbolKind, TypeInfo};

impl SemanticAnalyzer {
    pub fn symbol_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];
        if let AstNodeKind::Program(statements) = &mut program.kind {
            for statement in statements {
                if let Err(err) = self.collect_node_symbol(statement) {
                    errors.push(*err);
                }
            }
        } else {
            panic!("Fed node that is not a Program");
        }
        errors
    }

    fn collect_node_symbol(&mut self, node: &mut AstNode) -> Result<Option<(usize, String)>, BoxedError> {
        let declared_symbol_opt = match &mut node.kind {
            AstNodeKind::VariableDeclaration { name, mutable, type_annotation, initializer } => 
                self.collect_variable_symbol(name.clone(), *mutable, type_annotation, initializer, node.span),
            AstNodeKind::UnaryOperation { operand, .. } => 
                self.collect_unary_operation_symbols(operand),
            AstNodeKind::BinaryOperation { left, right, .. } |
            AstNodeKind::ConditionalOperation { left, right, .. } =>
                self.collect_binary_operation_symbols(left, right),
            AstNodeKind::Block(statements) => 
                self.collect_block_symbols(statements),
            AstNodeKind::IfStatement { condition, then_branch, else_if_branches, else_branch } =>
                self.collect_conditional_symbols(condition, then_branch, else_if_branches, else_branch),
            AstNodeKind::ForLoop { initializer, condition, increment, body } =>
                self.collect_for_loop_symbols(initializer, condition, increment, body),
            AstNodeKind::WhileLoop { condition, body } =>
                self.collect_while_loop_symbols(condition, body),
            AstNodeKind::Return(opt_expr) => 
                self.collect_return_statement_symbols(opt_expr),
            AstNodeKind::FunctionDeclaration { signature, body } => 
                self.collect_function_declaration(signature, body, node.span),
            AstNodeKind::FunctionExpression { signature, body } => 
                self.collect_function_expression_symbols(signature, body),
            AstNodeKind::StructDeclaration { name, fields, generic_parameters } => 
                self.collect_struct_symbols(name.clone(), fields, generic_parameters, node.span),
            AstNodeKind::EnumDeclaration { name, variants } => 
                self.collect_enum_symbols(name.clone(), variants, node.span),
            AstNodeKind::ImplDeclaration { associated_constants, associated_functions, generic_parameters, .. } => 
                self.collect_impl_symbols(associated_constants, associated_functions, generic_parameters),
            AstNodeKind::TraitDeclaration { name, signatures } => 
                self.collect_trait_symbols(name.clone(), signatures, node.span),
            AstNodeKind::TypeDeclaration { name, generic_parameters, .. } => 
                self.collect_type_symbols(name.clone(), generic_parameters, node.span),
            _ => Ok(None)
        };

        if let Ok(Some(ref declared_symbol_info)) = declared_symbol_opt {
            node.symbol = Some(declared_symbol_info.clone());
        }

        declared_symbol_opt
    }

    fn collect_variable_symbol(
        &mut self, 
        name: String, 
        mutable: bool,
        type_annotation: &mut Option<BoxedAstNode>,
        initializer: &mut Option<BoxedAstNode>, 
        span: Span
    ) -> Result<Option<(usize, String)>, BoxedError> {
        self.collect_optional_node(type_annotation)?;
        self.collect_optional_node(initializer)?;

        let symbol_id = self.add_symbol(SymbolKind::Variable, &name, mutable, span, None, vec![])?;
        Ok(Some((symbol_id, name)))
    }

    fn collect_function_declaration(
        &mut self,
        signature: &mut BoxedAstNode,
        body: &mut BoxedAstNode,
        span: Span
    ) -> Result<Option<(usize, String)>, BoxedError> {
        let (name, generic_params, params) = match &mut signature.kind {
            AstNodeKind::FunctionSignature { name, generic_parameters, parameters, .. } => {
                (name.clone(), generic_parameters, parameters)
            }
            _ => panic!("FunctionDeclaration node is not holding a FunctionSignature"),
        };

        let symbol_id = self.add_symbol(SymbolKind::Function, &name, false, span, None, vec![])?;
        self.symbol_table.enter_scope(ScopeKind::Function);

        self.collect_generic_parameters(generic_params)?;
        self.collect_function_parameters(params)?;
        self.collect_node_symbol(body)?;

        self.symbol_table.exit_scope();
        Ok(Some((symbol_id, name)))
    }

    fn collect_function_expression_symbols(
        &mut self,
        signature: &mut BoxedAstNode,
        body: &mut BoxedAstNode
    ) -> Result<Option<(usize, String)>, BoxedError> {
        self.symbol_table.enter_scope(ScopeKind::Function);

        if let AstNodeKind::FunctionSignature { generic_parameters, parameters, return_type, .. } = &mut signature.kind {
            self.collect_generic_parameters(generic_parameters)?;
            self.collect_function_parameters(parameters)?;
            self.collect_optional_node(return_type)?;
        } else {
            panic!("FunctionExpression node is not holding a FunctionSignature");
        }

        self.collect_node_symbol(body)?;
        self.symbol_table.exit_scope();
        
        Ok(None)
    }

    fn collect_struct_symbols(
        &mut self,
        name: String,
        fields: &mut [AstNode],
        generic_parameters: &mut [AstNode],
        span: Span
    ) -> Result<Option<(usize, String)>, BoxedError> {
        let scope_id = self.symbol_table.enter_scope(ScopeKind::Struct);
        let symbol_id = self.add_symbol(SymbolKind::Struct(scope_id), &name, false, span, None, vec![])?;

        for field in fields {
            if let AstNodeKind::StructField { qualifier, name, .. } = &field.kind {
                field.symbol = Some((
                    self.add_symbol(SymbolKind::StructField, name, false, field.span, Some(*qualifier), vec![])?,
                    name.clone()
                ));
            }
        }

        self.collect_generic_parameters(generic_parameters)?;
        self.symbol_table.exit_scope();
        Ok(Some((symbol_id, name)))
    }

    fn collect_enum_symbols(
        &mut self,
        name: String,
        variants: &mut IndexMap<String, (AstNode, Option<AstNode>)>,
        span: Span
    ) -> Result<Option<(usize, String)>, BoxedError> {
        let scope_id = self.symbol_table.enter_scope(ScopeKind::Enum);
        let symbol_id = self.add_symbol(SymbolKind::Enum(scope_id), &name, false, span, None, vec![])?;

        for (variant_name, (variant_node, _)) in variants {
            variant_node.symbol = Some((
                self.add_symbol(SymbolKind::EnumVariant, variant_name, false, variant_node.span, None, vec![])?,
                variant_name.clone()
            ));
        }

        self.symbol_table.exit_scope();
        Ok(Some((symbol_id, name)))
    }

    fn collect_generic_parameters(&mut self, params: &mut [AstNode]) -> Result<(), BoxedError> {
        for param in params {
            if let AstNodeKind::GenericParameter { name, .. } = &param.kind {
                param.symbol = Some((
                    self.add_symbol(SymbolKind::TypeAlias, name, false, param.span, None, vec![])?,
                    name.clone()
                ));
            }
        }
        Ok(())
    }

    fn collect_function_parameters(&mut self, params: &mut [AstNode]) -> Result<(), BoxedError> {
        for param in params {
            if let AstNodeKind::FunctionParameter { name, mutable, .. } = &param.kind {
                param.symbol = Some((
                    self.add_symbol(SymbolKind::Variable, name, *mutable, param.span, None, vec![])?,
                    name.clone()
                ));
            }
        }
        Ok(())
    }

    fn collect_block_symbols(&mut self, statements: &mut [AstNode]) -> Result<Option<(usize, String)>, BoxedError> {
        self.symbol_table.enter_scope(ScopeKind::Block);
        for statement in statements {
            self.collect_node_symbol(statement)?;
        }
        self.symbol_table.exit_scope();
        Ok(None)
    }

    fn add_symbol(
        &mut self,
        kind: SymbolKind,
        name: &str,
        mutable: bool,
        span: Span,
        qualifier: Option<QualifierKind>,
        generic_parameters: Vec<TypeInfo>
    ) -> Result<usize, BoxedError> {
        self.symbol_table.current_scope_mut().add_symbol(Symbol {
            name: name.to_string(),
            kind,
            type_info: None,
            mutable,
            span,
            qualifier,
            generic_parameters,
            scope_id: 0
        })
    }

    fn collect_impl_symbols(
        &mut self,
        associated_constants: &mut [AstNode],
        associated_functions: &mut [AstNode],
        generic_parameters: &mut [AstNode]
    ) -> Result<Option<(usize, String)>, BoxedError> {
        self.symbol_table.enter_scope(ScopeKind::Impl);

        self.collect_generic_parameters(generic_parameters)?;

        for const_node in associated_constants {
            if let AstNodeKind::AssociatedConstant { qualifier, name, .. } = &const_node.kind {
                const_node.symbol = Some((
                    self.add_symbol(SymbolKind::Variable, name, false, const_node.span, Some(*qualifier), vec![])?,
                    name.clone()
                ));
            }
        }

        for func_node in associated_functions {
            if let AstNodeKind::AssociatedFunction { qualifier, signature, body } = &mut func_node.kind {
                let (name, generic_params, params) = match &mut signature.kind {
                    AstNodeKind::FunctionSignature { name, generic_parameters, parameters, .. } => 
                        (name.clone(), generic_parameters, parameters),
                    _ => panic!("AssociatedFunction doesn't contain FunctionSignature")
                };

                self.symbol_table.enter_scope(ScopeKind::Function);
                self.collect_generic_parameters(generic_params)?;
                self.collect_function_parameters(params)?;
                self.collect_node_symbol(body)?;
                self.symbol_table.exit_scope();

                func_node.symbol = Some((
                    self.add_symbol(SymbolKind::Function, &name, false, func_node.span, Some(*qualifier), vec![])?,
                    name.clone()
                ));
            }
        }

        self.symbol_table.exit_scope();
        Ok(None)
    }

    fn collect_trait_symbols(
        &mut self,
        name: String,
        signatures: &mut [AstNode],
        span: Span
    ) -> Result<Option<(usize, String)>, BoxedError> {
        let id = self.symbol_table.enter_scope(ScopeKind::Trait);

        for signature in signatures.iter_mut() {
            let (name, generic_params, params) = match &mut signature.kind {
                AstNodeKind::FunctionSignature { name, generic_parameters, parameters, .. } => 
                    (name.clone(), generic_parameters, parameters),
                _ => panic!("AssociatedFunction doesn't contain FunctionSignature")
            };

            self.symbol_table.enter_scope(ScopeKind::Function);
            self.collect_generic_parameters(generic_params)?;
            self.collect_function_parameters(params)?;
            self.symbol_table.exit_scope();

            signature.symbol = Some((
                self.add_symbol(SymbolKind::Function, &name, false, signature.span, None, vec![])?,
                name.clone()
            ));
        }

        self.symbol_table.exit_scope();

        let symbol_id = self.add_symbol(SymbolKind::Trait(id), &name, false, span, None, vec![])?;
        Ok(Some((symbol_id, name)))
    }

    fn collect_type_symbols(
        &mut self,
        name: String,
        generic_parameters: &mut [AstNode],
        span: Span
    ) -> Result<Option<(usize, String)>, BoxedError> {
        self.symbol_table.enter_scope(ScopeKind::Type);
        self.collect_generic_parameters(generic_parameters)?;
        self.symbol_table.exit_scope();

        let symbol_id = self.add_symbol(SymbolKind::TypeAlias, &name, false, span, None, vec![])?;
        Ok(Some((symbol_id, name)))
    }

    fn collect_conditional_symbols(
        &mut self,
        condition: &mut BoxedAstNode,
        then_branch: &mut BoxedAstNode,
        else_if_branches: &mut [(BoxedAstNode, BoxedAstNode)],
        else_branch: &mut Option<BoxedAstNode>
    ) -> Result<Option<(usize, String)>, BoxedError> {
        self.collect_node_symbol(condition)?;
        self.collect_node_symbol(then_branch)?;

        for (cond, branch) in else_if_branches {
            self.collect_node_symbol(cond)?;
            self.collect_node_symbol(branch)?;
        }

        self.collect_optional_node(else_branch)?;

        Ok(None)
    }

    fn collect_for_loop_symbols(
        &mut self,
        initializer: &mut Option<BoxedAstNode>,
        condition: &mut Option<BoxedAstNode>,
        increment: &mut Option<BoxedAstNode>,
        body: &mut BoxedAstNode
    ) -> Result<Option<(usize, String)>, BoxedError> {
        self.symbol_table.enter_scope(ScopeKind::Block);

        self.collect_optional_node(initializer)?;
        self.collect_optional_node(condition)?;
        self.collect_optional_node(increment)?;
        self.collect_node_symbol(body)?;

        self.symbol_table.exit_scope();
        Ok(None)
    }

    fn collect_while_loop_symbols(
        &mut self,
        condition: &mut BoxedAstNode,
        body: &mut BoxedAstNode
    ) -> Result<Option<(usize, String)>, BoxedError> {
        self.symbol_table.enter_scope(ScopeKind::Block);
        self.collect_node_symbol(condition)?;
        self.collect_node_symbol(body)?;
        self.symbol_table.exit_scope();
        Ok(None)
    }

    fn collect_return_statement_symbols(
        &mut self,
        opt_expr: &mut Option<BoxedAstNode>
    ) -> Result<Option<(usize, String)>, BoxedError> {
        self.collect_optional_node(opt_expr)?;
        Ok(None)
    }

    fn collect_optional_node(
        &mut self,
        node: &mut Option<BoxedAstNode>
    ) -> Result<(), BoxedError> {
        if let Some(n) = node {
            self.collect_node_symbol(n)?;
        }

        Ok(())
    }

    fn collect_unary_operation_symbols(
        &mut self,
        operand: &mut BoxedAstNode
    ) -> Result<Option<(usize, String)>, BoxedError> {
        self.collect_node_symbol(operand)?;
        Ok(None)
    }

    fn collect_binary_operation_symbols(
        &mut self,
        left: &mut BoxedAstNode,
        right: &mut BoxedAstNode
    ) -> Result<Option<(usize, String)>, BoxedError> {
        self.collect_node_symbol(left)?;
        self.collect_node_symbol(right)?;
        Ok(None)
    }
}