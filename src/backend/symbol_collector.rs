use indexmap::IndexMap;
use crate::{backend::semantic_analyzer::{FunctionData, SymbolId, TypeSymbol, TypeSymbolKind}, frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, utils::{error::*, kind::{QualifierKind, Span}}};
use super::semantic_analyzer::{ScopeKind, SemanticAnalyzer, ValueSymbol, ValueSymbolKind};

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
            unreachable!();
        }
        
        errors
    }

    fn collect_node_symbol(&mut self, node: &mut AstNode) -> Result<(Option<SymbolId>, Option<SymbolId>), BoxedError> {
        use AstNodeKind::*;

        let declared_symbol_opt = match &mut node.kind {
            VariableDeclaration { name, mutable, type_annotation, initializer } => 
                self.collect_variable_symbol(name.clone(), *mutable, type_annotation, initializer, node.span),
            FunctionDeclaration { signature, body } 
                => self.collect_function_declaration(signature, body, node.span),
            FunctionExpression { signature, body } => 
                self.collect_function_expression_symbols(signature, body),
            StructDeclaration { name, fields, generic_parameters } =>
                self.collect_struct_symbols(name.clone(), fields, generic_parameters, node.span),
            EnumDeclaration { name, variants } =>
                self.collect_enum_symbols(name.clone(), variants, node.span),
            ImplDeclaration { associated_constants, associated_functions, generic_parameters, .. } =>
                self.collect_impl_symbols(associated_constants, associated_functions, generic_parameters),
            TraitDeclaration { name, signatures, .. } =>
                self.collect_trait_symbols(name.clone(), signatures, node.span),
            TypeDeclaration { name, generic_parameters, .. } =>
                self.collect_type_symbols(name.clone(), generic_parameters, node.span),
            Block(statements) =>
                self.collect_block_symbols(statements),
            _ => {
                for child in node.children_mut() {
                    self.collect_node_symbol(child)?;
                }

                Ok((None, None))
            }
        };

        if let Ok((ref value_info, ref type_info)) = declared_symbol_opt {
            if let Some(value_info) = value_info {
                node.value_id = Some(value_info.clone());
            }

            if let Some(type_info) = type_info {
                node.type_id = Some(type_info.clone());
            }
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
    ) -> Result<(Option<SymbolId>, Option<SymbolId>), BoxedError> {
        self.collect_optional_node(type_annotation)?;
        self.collect_optional_node(initializer)?;

        let value_id = self.add_value_symbol(ValueSymbolKind::Variable, &name, mutable, span, QualifierKind::Public)?;
        Ok((Some((value_id, name)), None))
    }

    fn collect_function_declaration(
        &mut self,
        signature: &mut BoxedAstNode,
        body: &mut BoxedAstNode,
        span: Span
    ) -> Result<(Option<SymbolId>, Option<SymbolId>), BoxedError> {
        let (name, generic_params, params) = match &mut signature.kind {
            AstNodeKind::FunctionSignature { name, generic_parameters, parameters, .. } => {
                (name.clone(), generic_parameters, parameters)
            }
            _ => unreachable!(),
        };

        let value_id = self.add_value_symbol(ValueSymbolKind::Function, &name, false, span, QualifierKind::Public)?;
        self.symbol_table.enter_scope(ScopeKind::Function);

        self.collect_generic_parameters(generic_params)?;
        self.collect_function_parameters(params)?;
        self.collect_node_symbol(body)?;

        self.symbol_table.exit_scope();
        Ok((Some((value_id, name)), None))
    }

    fn collect_function_expression_symbols(
        &mut self,
        signature: &mut BoxedAstNode,
        body: &mut BoxedAstNode
    ) -> Result<(Option<SymbolId>, Option<SymbolId>), BoxedError> {
        self.symbol_table.enter_scope(ScopeKind::Function);

        if let AstNodeKind::FunctionSignature { generic_parameters, parameters, return_type, .. } = &mut signature.kind {
            self.collect_generic_parameters(generic_parameters)?;
            self.collect_function_parameters(parameters)?;
            self.collect_optional_node(return_type)?;
        } else {
            unreachable!();
        }

        self.collect_node_symbol(body)?;
        self.symbol_table.exit_scope();
        
        Ok((None, None))
    }

    fn collect_struct_symbols(
        &mut self,
        name: String,
        fields: &mut [AstNode],
        generic_parameters: &mut [AstNode],
        span: Span
    ) -> Result<(Option<SymbolId>, Option<SymbolId>), BoxedError> {
        let scope_id = self.symbol_table.enter_scope(ScopeKind::Struct);
        let generic_parameters = self.collect_generic_parameters(generic_parameters)?;

        for field in fields {
            if let AstNodeKind::StructField { qualifier, name, .. } = &field.kind {
                field.value_id = Some((
                    self.add_value_symbol(ValueSymbolKind::StructField, name, false, field.span, *qualifier)?,
                    name.clone()
                ));
            }
        }

        self.symbol_table.exit_scope();
        let type_id = self.add_type_symbol(&name, TypeSymbolKind::Struct(scope_id), generic_parameters, None, span)?;

        Ok((None, Some((type_id, name))))
    }

    fn collect_enum_symbols(
        &mut self,
        name: String,
        variants: &mut IndexMap<String, (AstNode, Option<AstNode>)>,
        span: Span
    ) -> Result<(Option<SymbolId>, Option<SymbolId>), BoxedError> {
        let scope_id = self.symbol_table.enter_scope(ScopeKind::Enum);

        for (variant_name, (variant_node, _)) in variants {
            variant_node.value_id = Some((
                self.add_value_symbol(ValueSymbolKind::EnumVariant, variant_name, false, variant_node.span, QualifierKind::Public)?,
                variant_name.clone()
            ));
        }

        self.symbol_table.exit_scope();
        let type_id = self.add_type_symbol(&name, TypeSymbolKind::Enum(scope_id), vec![], None, span)?;

        Ok((None, Some((type_id, name))))
    }

    fn collect_generic_parameters(&mut self, params: &mut [AstNode]) -> Result<Vec<SymbolId>, BoxedError> {
        let mut ids = vec![];

        for param in params {
            if let AstNodeKind::GenericParameter { name, .. } = &param.kind {
                let id = (
                    self.add_type_symbol(name, TypeSymbolKind::Generic, vec![], None, param.span)?,
                    name.clone()
                );

                param.type_id = Some(id.clone());
                ids.push(id);
            }
        }

        Ok(ids)
    }

    fn collect_function_parameters(&mut self, params: &mut [AstNode]) -> Result<(), BoxedError> {
        for param in params {
            if let AstNodeKind::FunctionParameter { name, mutable, .. } = &param.kind {
                param.value_id = Some((
                    self.add_value_symbol(ValueSymbolKind::Variable, name, *mutable, param.span, QualifierKind::Public)?,
                    name.clone()
                ));
            }
        }
        Ok(())
    }

    fn collect_block_symbols(&mut self, statements: &mut [AstNode]) -> Result<(Option<SymbolId>, Option<SymbolId>), BoxedError> {
        self.symbol_table.enter_scope(ScopeKind::Block);
        for statement in statements {
            self.collect_node_symbol(statement)?;
        }
        self.symbol_table.exit_scope();
        Ok((None, None))
    }

    fn collect_impl_symbols(
        &mut self,
        associated_constants: &mut [AstNode],
        associated_functions: &mut [AstNode],
        generic_parameters: &mut [AstNode]
    ) -> Result<(Option<SymbolId>, Option<SymbolId>), BoxedError> {
        self.symbol_table.enter_scope(ScopeKind::Impl);

        self.collect_generic_parameters(generic_parameters)?;

        for const_node in associated_constants {
            if let AstNodeKind::AssociatedConstant { qualifier, name, .. } = &const_node.kind {
                const_node.value_id = Some((
                    self.add_value_symbol(ValueSymbolKind::Variable, name, false, const_node.span, *qualifier)?,
                    name.clone()
                ));
            }
        }

        for func_node in associated_functions {
            if let AstNodeKind::AssociatedFunction { qualifier, signature, body } = &mut func_node.kind {
                let (name, generic_params, params) = match &mut signature.kind {
                    AstNodeKind::FunctionSignature { name, generic_parameters, parameters, .. } => 
                        (name.clone(), generic_parameters, parameters),
                    _ => unreachable!()
                };

                self.symbol_table.enter_scope(ScopeKind::Function);
                self.collect_generic_parameters(generic_params)?;
                self.collect_function_parameters(params)?;
                self.collect_node_symbol(body)?;
                self.symbol_table.exit_scope();

                func_node.value_id = Some((
                    self.add_value_symbol(ValueSymbolKind::Function, &name, false, func_node.span, *qualifier)?,
                    name.clone()
                ));
            }
        }

        self.symbol_table.exit_scope();
        Ok((None, None))
    }

    fn collect_trait_symbols(
        &mut self,
        name: String,
        signatures: &mut [AstNode],
        span: Span
    ) -> Result<(Option<SymbolId>, Option<SymbolId>), BoxedError> {
        let id = self.symbol_table.enter_scope(ScopeKind::Trait);

        for signature in signatures.iter_mut() {
            let (name, generic_params, params) = match &mut signature.kind {
                AstNodeKind::FunctionSignature { name, generic_parameters, parameters, .. } => 
                    (name.clone(), generic_parameters, parameters),
                _ => unreachable!()
            };

            self.symbol_table.enter_scope(ScopeKind::Function);
            self.collect_generic_parameters(generic_params)?;
            self.collect_function_parameters(params)?;
            self.symbol_table.exit_scope();

            signature.value_id = Some((
                self.add_value_symbol(ValueSymbolKind::Function, &name, false, signature.span, QualifierKind::Public)?,
                name.clone()
            ));
        }

        self.symbol_table.exit_scope();

        let type_id = self.add_type_symbol(&name, TypeSymbolKind::Trait(id), vec![], None, span)?;
        Ok((None, Some((type_id, name))))
    }

    fn collect_type_symbols(
        &mut self,
        name: String,
        generic_parameters: &mut [AstNode],
        span: Span
    ) -> Result<(Option<SymbolId>, Option<SymbolId>), BoxedError> {
        self.symbol_table.enter_scope(ScopeKind::Type);
        let generic_parameters = self.collect_generic_parameters(generic_parameters)?;
        self.symbol_table.exit_scope();

        let type_id = self.add_type_symbol(&name, TypeSymbolKind::Custom, generic_parameters, None, span)?;
        Ok((None, Some((type_id, name))))
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

    fn add_value_symbol(
        &mut self,
        kind: ValueSymbolKind,
        name: &str,
        mutable: bool,
        span: Span,
        qualifier: QualifierKind
    ) -> Result<usize, BoxedError> {
        self.symbol_table.current_scope_mut().add_value_symbol(ValueSymbol {
            name: name.to_string(),
            kind,
            mutable,
            span,
            qualifier,
            scope_id: 0,
            type_id: None
        })
    }

    fn add_type_symbol(
        &mut self,
        name: &str,
        kind: TypeSymbolKind,
        generic_parameters: Vec<SymbolId>,
        function_data: Option<FunctionData>,
        span: Span
    ) -> Result<usize, BoxedError> {
        self.symbol_table.current_scope_mut().add_type_symbol(TypeSymbol {
            name: name.to_string(),
            kind,
            generic_parameters,
            function_data,
            scope_id: 0,
            span: Some(span)
        })
    }
}