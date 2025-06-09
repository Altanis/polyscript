use indexmap::IndexMap;
use crate::{backend::semantic_analyzer::{PrimitiveKind, TypeSymbolKind, ValueSymbolId, TypeSymbolId}, frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, utils::{error::*, kind::{QualifierKind, Span}}};
use super::semantic_analyzer::{ScopeKind, SemanticAnalyzer, ValueSymbolKind};

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

    fn collect_node_symbol(&mut self, node: &mut AstNode) -> Result<(Option<ValueSymbolId>, Option<TypeSymbolId>), BoxedError> {
        use AstNodeKind::*;

        let declared_symbol_opt = match &mut node.kind {
            VariableDeclaration { name, mutable, type_annotation, initializer } => 
                self.collect_variable_symbol(name, *mutable, type_annotation, initializer, node.span),
            FunctionDeclaration { signature, body } 
                => self.collect_function_declaration(signature, body, node.span),
            FunctionExpression { signature, body } => 
                self.collect_function_expression_symbols(signature, body),
            StructDeclaration { name, fields, generic_parameters } =>
                self.collect_struct_symbols(name, fields, generic_parameters, node.span),
            EnumDeclaration { name, variants } =>
                self.collect_enum_symbols(name, variants, node.span),
            ImplDeclaration { associated_constants, associated_functions, associated_types, generic_parameters, .. } =>
                self.collect_impl_symbols(associated_constants, associated_functions, associated_types, generic_parameters),
            TraitDeclaration { name, signatures, constants, types, .. } =>
                self.collect_trait_symbols(name, signatures, constants, types, node.span),
            TypeDeclaration { name, generic_parameters, .. } =>
                self.collect_type_symbols(name, generic_parameters, node.span),
            Block(statements) =>
                self.collect_block_symbols(statements),
            _ => {
                for child in node.children_mut() {
                    self.collect_node_symbol(child)?;
                }

                Ok((None, None))
            }
        };

        if let Ok((value_id_opt, type_id_opt)) = declared_symbol_opt {
            node.value_id = value_id_opt;
            node.type_id = type_id_opt;
        }

        declared_symbol_opt
    }

    fn collect_variable_symbol(
        &mut self, 
        name: &str, 
        mutable: bool,
        type_annotation: &mut Option<BoxedAstNode>,
        initializer: &mut Option<BoxedAstNode>, 
        span: Span
    ) -> Result<(Option<ValueSymbolId>, Option<TypeSymbolId>), BoxedError> {
        self.collect_optional_node(type_annotation)?;
        self.collect_optional_node(initializer)?;

        let value_id = self.symbol_table.add_value_symbol(
            name,
            ValueSymbolKind::Variable,
            mutable,
            QualifierKind::Public,
            None,
            Some(span)
        )?;

        Ok((Some(value_id), None))
    }

    fn collect_function_declaration(
        &mut self,
        signature: &mut BoxedAstNode,
        body: &mut BoxedAstNode,
        span: Span
    ) -> Result<(Option<ValueSymbolId>, Option<TypeSymbolId>), BoxedError> {
        let (name, generic_params, params) = match &mut signature.kind {
            AstNodeKind::FunctionSignature { name, generic_parameters, parameters, .. } => {
                (name.clone(), generic_parameters, parameters)
            }
            _ => unreachable!(),
        };
        
        let value_id = self.symbol_table.add_value_symbol(
            &name,
            ValueSymbolKind::Function,
            false,
            QualifierKind::Public,
            None,
            Some(span)
        )?;
        
        self.symbol_table.enter_scope(ScopeKind::Function);
        self.collect_generic_parameters(generic_params)?;
        self.collect_function_parameters(params)?;
        self.collect_node_symbol(body)?;
        self.symbol_table.exit_scope();

        Ok((Some(value_id), None))
    }

    fn collect_function_expression_symbols(
        &mut self,
        signature: &mut BoxedAstNode,
        body: &mut BoxedAstNode
    ) -> Result<(Option<ValueSymbolId>, Option<TypeSymbolId>), BoxedError> {
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
        name: &str,
        fields: &mut [AstNode],
        generic_parameters: &mut [AstNode],
        span: Span
    ) -> Result<(Option<ValueSymbolId>, Option<TypeSymbolId>), BoxedError> {
        let scope_id = self.symbol_table.enter_scope(ScopeKind::Struct);
        let generic_param_ids = self.collect_generic_parameters(generic_parameters)?;

        for field in fields {
            if let AstNodeKind::StructField { qualifier, name, .. } = &field.kind {
                let field_id = self.symbol_table.add_value_symbol(
                    name,
                    ValueSymbolKind::StructField,
                    false,
                    *qualifier,
                    None,
                    Some(field.span)
                )?;
                field.value_id = Some(field_id);
            }
        }

        self.symbol_table.exit_scope();
        let type_id = self.symbol_table.add_type_symbol(
            name,
            TypeSymbolKind::Struct(scope_id),
            generic_param_ids,
            QualifierKind::Public,
            Some(span)
        )?;

        Ok((None, Some(type_id)))
    }

    fn collect_enum_symbols(
        &mut self,
        name: &str,
        variants: &mut IndexMap<String, (AstNode, Option<AstNode>)>,
        span: Span
    ) -> Result<(Option<ValueSymbolId>, Option<TypeSymbolId>), BoxedError> {
        let scope_id = self.symbol_table.enter_scope(ScopeKind::Enum);

        for (variant_name, (variant_node, _)) in variants {
            let variant_id = self.symbol_table.add_value_symbol(
                variant_name,
                ValueSymbolKind::EnumVariant,
                false,
                QualifierKind::Public,
                None,
                Some(variant_node.span)
            )?;
            variant_node.value_id = Some(variant_id);
        }

        self.symbol_table.exit_scope();
        let type_id = self.symbol_table.add_type_symbol(
            name,
            TypeSymbolKind::Enum(scope_id),
            vec![],
            QualifierKind::Public,
            Some(span)
        )?;

        Ok((None, Some(type_id)))
    }

    fn collect_generic_parameters(&mut self, params: &mut [AstNode]) -> Result<Vec<TypeSymbolId>, BoxedError> {
        let mut ids = vec![];
        for param in params {
            if let AstNodeKind::GenericParameter { name, .. } = &param.kind {
                let id = self.symbol_table.add_type_symbol(
                    name,
                    TypeSymbolKind::Generic,
                    vec![],
                    QualifierKind::Public,
                    Some(param.span)
                )?;
                param.type_id = Some(id);
                ids.push(id);
            }
        }
        Ok(ids)
    }

    fn collect_function_parameters(&mut self, params: &mut [AstNode]) -> Result<Vec<ValueSymbolId>, BoxedError> {
        let mut ids = vec![];
        for param in params {
            if let AstNodeKind::FunctionParameter { name, mutable, .. } = &param.kind {
                let id = self.symbol_table.add_value_symbol(
                    name,
                    ValueSymbolKind::Variable,
                    *mutable,
                    QualifierKind::Public,
                    None,
                    Some(param.span)
                )?;
                param.value_id = Some(id);
                ids.push(id);
            }
        }
        Ok(ids)
    }

    fn collect_block_symbols(&mut self, statements: &mut [AstNode]) -> Result<(Option<ValueSymbolId>, Option<TypeSymbolId>), BoxedError> {
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
        associated_types: &mut [AstNode],
        generic_parameters: &mut [AstNode]
    ) -> Result<(Option<ValueSymbolId>, Option<TypeSymbolId>), BoxedError> {
        self.symbol_table.enter_scope(ScopeKind::Impl);
        self.collect_generic_parameters(generic_parameters)?;
        
        self.symbol_table.add_type_symbol("Self", TypeSymbolKind::TypeAlias(None), vec![], QualifierKind::Public, None)?;

        for func_node in associated_functions {
            if let AstNodeKind::AssociatedFunction { qualifier, signature, body } = &mut func_node.kind {
                if let AstNodeKind::FunctionSignature { name, generic_parameters, parameters, .. } = &mut signature.kind {
                    let func_id = self.symbol_table.add_value_symbol(name, ValueSymbolKind::Function, false, *qualifier, None, Some(func_node.span))?;
                    func_node.value_id = Some(func_id);

                    self.symbol_table.enter_scope(ScopeKind::Function);
                    self.collect_generic_parameters(generic_parameters)?;
                    self.collect_function_parameters(parameters)?;
                    self.collect_node_symbol(body)?;
                    self.symbol_table.exit_scope();
                }
            }
        }

        for const_node in associated_constants {
            if let AstNodeKind::AssociatedConstant { qualifier, name, .. } = &const_node.kind {
                let const_id = self.symbol_table.add_value_symbol(name, ValueSymbolKind::Variable, false, *qualifier, None, Some(const_node.span))?;
                const_node.value_id = Some(const_id);
            }
        }

        for type_node in associated_types {
            if let AstNodeKind::AssociatedType { name, qualifier, .. } = &type_node.kind {
                let type_id = self.symbol_table.add_type_symbol(name, TypeSymbolKind::Custom, vec![], *qualifier, Some(type_node.span))?;
                type_node.type_id = Some(type_id);
            }
        }

        self.symbol_table.exit_scope();
        Ok((None, None))
    }

    fn collect_trait_symbols(
        &mut self,
        name: &str,
        signatures: &mut [AstNode],
        constants: &mut [AstNode],
        types: &mut [AstNode],
        span: Span
    ) -> Result<(Option<ValueSymbolId>, Option<TypeSymbolId>), BoxedError> {
        let trait_scope_id = self.symbol_table.enter_scope(ScopeKind::Trait);
        
        self.symbol_table.add_type_symbol("Self", TypeSymbolKind::TypeAlias(None), vec![], QualifierKind::Public, None)?;
        
        let null_type_id = self.builtins[PrimitiveKind::Null as usize];

        for signature in signatures.iter_mut() {
            if let AstNodeKind::FunctionSignature { name, generic_parameters, instance, .. } = &mut signature.kind {
                let generic_param_ids = self.collect_generic_parameters(generic_parameters)?;
                let param_ids: Vec<TypeSymbolId> = vec![];
                
                let sig_type_id = self.symbol_table.add_type_symbol(
                    name,
                    TypeSymbolKind::FunctionSignature {
                        params: param_ids,
                        return_type: null_type_id,
                        instance: *instance
                    },
                    generic_param_ids,
                    QualifierKind::Public,
                    Some(signature.span)
                )?;
                signature.type_id = Some(sig_type_id);
            }
        }

        for const_node in constants {
            if let AstNodeKind::TraitConstant { name, .. } = &const_node.kind {
                let const_id = self.symbol_table.add_value_symbol(name, ValueSymbolKind::Variable, false, QualifierKind::Public, None, Some(const_node.span))?;
                const_node.value_id = Some(const_id);
            }
        }

        for type_node in types {
            if let AstNodeKind::TraitType(name) = &type_node.kind {
                let type_id = self.symbol_table.add_type_symbol(name, TypeSymbolKind::Custom, vec![], QualifierKind::Public, Some(type_node.span))?;
                type_node.type_id = Some(type_id);
            }
        }

        self.symbol_table.exit_scope();

        let trait_type_id = self.symbol_table.add_type_symbol(name, TypeSymbolKind::Trait(trait_scope_id), vec![], QualifierKind::Public, Some(span))?;
        Ok((None, Some(trait_type_id)))
    }

    fn collect_type_symbols(
        &mut self,
        name: &str,
        generic_parameters: &mut [AstNode],
        span: Span
    ) -> Result<(Option<ValueSymbolId>, Option<TypeSymbolId>), BoxedError> {
        self.symbol_table.enter_scope(ScopeKind::Type);
        let generic_param_ids = self.collect_generic_parameters(generic_parameters)?;
        self.symbol_table.exit_scope();

        let type_id = self.symbol_table.add_type_symbol(
            name,
            TypeSymbolKind::TypeAlias(None),
            generic_param_ids,
            QualifierKind::Public,
            Some(span)
        )?;
        Ok((None, Some(type_id)))
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
}