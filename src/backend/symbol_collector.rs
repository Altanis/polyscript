use indexmap::IndexMap;
use crate::{backend::semantic_analyzer::{InherentImpl, PrimitiveKind, ScopeId, TypeSymbolId, TypeSymbolKind, ValueSymbolId}, frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, utils::{error::*, kind::{QualifierKind, Span}}};
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
            ImplDeclaration { .. } => Ok((None, None)),
            EnumDeclaration { name, variants } =>
                self.collect_enum_symbols(name, variants, node.span),
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
        
        let scope_id = self.symbol_table.enter_scope(ScopeKind::Function);
        self.collect_generic_parameters(generic_params)?;
        self.collect_function_parameters(params)?;
        self.collect_node_symbol(body)?;
        self.symbol_table.exit_scope();
        
        let value_id = self.symbol_table.add_value_symbol(
            &name,
            ValueSymbolKind::Function(scope_id),
            false,
            QualifierKind::Public,
            None,
            Some(span)
        )?;

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
            TypeSymbolKind::Struct((scope_id, vec![])),
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
            TypeSymbolKind::Enum((scope_id, vec![])),
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

    fn collect_trait_symbols(
        &mut self,
        name: &str,
        signatures: &mut [AstNode],
        constants: &mut [AstNode],
        types: &mut [AstNode],
        span: Span
    ) -> Result<(Option<ValueSymbolId>, Option<TypeSymbolId>), BoxedError> {
        let trait_scope_id = self.symbol_table.enter_scope(ScopeKind::Trait);
        
        self.symbol_table.add_type_symbol("Self", TypeSymbolKind::TypeAlias((None, None)), vec![], QualifierKind::Public, None)?;
        
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
        let (scope_id, generics) = if !generic_parameters.is_empty() {
            let scope_id = self.symbol_table.enter_scope(ScopeKind::Type);
            let generics = self.collect_generic_parameters(generic_parameters)?;
            self.symbol_table.exit_scope();

            (Some(scope_id), generics)
        } else {
            (None, vec![])
        };

        let type_id = self.symbol_table.add_type_symbol(
            name,
            TypeSymbolKind::TypeAlias((scope_id, None)),
            generics,
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

impl SemanticAnalyzer {
    pub fn impl_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];

        if let AstNodeKind::Program(statements) = &mut program.kind {
            for statement in statements {
                if let AstNodeKind::ImplDeclaration { .. } = &mut statement.kind {
                    if let Err(err) = self.collect_and_register_impl_block(statement) {
                        errors.push(*err);
                    }
                }
            }
        } else {
            unreachable!();
        }
        
        errors
    }

    fn find_type_by_name(&self, node: &AstNode) -> Result<TypeSymbolId, BoxedError> {
        let name = node.get_name().ok_or_else(|| self.create_error(
            ErrorKind::ExpectedType,
            node.span,
            &[node.span],
        ))?;
        
        let type_symbol = self.symbol_table.find_type_symbol(&name).ok_or_else(|| self.create_error(
            ErrorKind::UnknownIdentifier(name.clone()),
            node.span,
            &[node.span],
        ))?;

        Ok(type_symbol.id)
    }

    fn collect_and_register_impl_block(&mut self, node: &mut AstNode) -> Result<(), BoxedError> {
        let (
            associated_constants,
            associated_types,
            associated_functions,
            impl_generics,
            type_reference,
            trait_node
        ) = match &mut node.kind {
            AstNodeKind::ImplDeclaration {
                associated_constants, associated_types, associated_functions,
                generic_parameters, type_reference, trait_node
            } => (
                associated_constants, associated_types, associated_functions,
                generic_parameters, type_reference, trait_node
            ),
            _ => unreachable!()
        };

        match trait_node {
            Some(trait_node) => {
                Ok(())
            }
            None => {
                let impl_scope_id = self.symbol_table.enter_scope(ScopeKind::Impl);
                let impl_generic_param_ids = self.collect_generic_parameters(impl_generics)?;
                
                let (base_type_name, specialization_arg_nodes) = match &mut type_reference.kind {
                    AstNodeKind::TypeReference { type_name, generic_types, .. } => (type_name, generic_types),
                    _ => return Err(self.create_error(ErrorKind::InvalidImpl(None), type_reference.span, &[type_reference.span])),
                };

                let mut specialization_types = vec![];
                for arg_node in specialization_arg_nodes {
                    let type_id = self.find_type_by_name(arg_node)?;
                    specialization_types.push(type_id);
                }

                self.symbol_table.add_type_symbol("Self", TypeSymbolKind::TypeAlias((None, None)), vec![], QualifierKind::Public, None)?;
                
                for func_node in associated_functions {
                    if let AstNodeKind::AssociatedFunction { qualifier, signature, body } = &mut func_node.kind {
                        if let AstNodeKind::FunctionSignature { name, generic_parameters, parameters, .. } = &mut signature.kind {
                            let func_scope_id = self.symbol_table.enter_scope(ScopeKind::Function);
                            self.collect_generic_parameters(generic_parameters)?;
                            self.collect_function_parameters(parameters)?;
                            self.collect_node_symbol(body)?;
                            self.symbol_table.exit_scope();

                            func_node.value_id = Some(self.symbol_table.add_value_symbol(
                                name, ValueSymbolKind::Function(func_scope_id), false, *qualifier, None, Some(func_node.span)
                            )?);
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

                let impl_block = InherentImpl {
                    scope_id: impl_scope_id,
                    specialization: specialization_types,
                    generic_params: impl_generic_param_ids,
                };

                let unknown_identifier_error = self.create_error(
                    ErrorKind::UnknownIdentifier(base_type_name.clone()), 
                    type_reference.span, 
                    &[type_reference.span]
                );

                let base_type_symbol = self.symbol_table.find_type_symbol_mut(base_type_name).ok_or(unknown_identifier_error)?;

                match &mut base_type_symbol.kind {
                    TypeSymbolKind::Struct((_, impls)) | TypeSymbolKind::Enum((_, impls)) => {
                        impls.push(impl_block);
                    }
                    _ => return Err(self.create_error(ErrorKind::InvalidImpl(Some(base_type_name.clone())), type_reference.span, &[type_reference.span])),
                }

                Ok(())
            }
        }
    }

    fn collect_impl_symbols(
        &mut self, 
        associated_constants: &mut [AstNode],
        associated_types: &mut [AstNode],
        associated_functions: &mut [AstNode],
        generic_parameters: &mut [AstNode]
    ) -> Result<ScopeId, BoxedError> {
        let impl_scope_id = self.symbol_table.enter_scope(ScopeKind::Impl);
        
        self.collect_generic_parameters(generic_parameters)?;
        self.symbol_table.add_type_symbol("Self", TypeSymbolKind::TypeAlias((None, None)), vec![], QualifierKind::Public, None)?;

        for func_node in associated_functions {
            if let AstNodeKind::AssociatedFunction { qualifier, signature, body } = &mut func_node.kind {
                if let AstNodeKind::FunctionSignature { name, generic_parameters, parameters, .. } = &mut signature.kind {
                    let scope_id = self.symbol_table.enter_scope(ScopeKind::Function);
                    self.collect_generic_parameters(generic_parameters)?;
                    self.collect_function_parameters(parameters)?;
                    self.collect_node_symbol(body)?;
                    self.symbol_table.exit_scope();

                    func_node.value_id = Some(self.symbol_table.add_value_symbol(
                        name, 
                        ValueSymbolKind::Function(scope_id), 
                        false, 
                        *qualifier, 
                        None, 
                        Some(func_node.span))?
                    );
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

        Ok(impl_scope_id)
    }
}