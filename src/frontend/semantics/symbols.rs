use super::analyzer::{ScopeKind, SemanticAnalyzer, ValueSymbolKind};
use crate::{
    frontend::syntax::ast::{AstNode, AstNodeKind, BoxedAstNode},
    frontend::semantics::analyzer::{
        InherentImpl, PrimitiveKind, TraitImpl, Type, TypeSymbolId, TypeSymbolKind, ValueSymbolId,
    },
    utils::{
        error::*,
        kind::{QualifierKind, ReferenceKind, Span},
    },
};
use indexmap::IndexMap;

impl SemanticAnalyzer {
    pub fn symbol_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];

        program.scope_id = Some(self.symbol_table.get_current_scope_id());

        if let AstNodeKind::Program(statements) = &mut program.kind {
            for statement in statements {
                if let Err(err) = self.symbol_collector_check_node(statement) {
                    errors.push(*err);
                }
            }
        } else {
            unreachable!();
        }

        errors
    }

    fn symbol_collector_check_node(
        &mut self,
        node: &mut AstNode,
    ) -> Result<(Option<ValueSymbolId>, Option<Type>), BoxedError> {
        node.scope_id = Some(self.symbol_table.get_current_scope_id());

        use AstNodeKind::*;

        let declared_symbol_opt = match &mut node.kind {
            VariableDeclaration {
                name,
                mutable,
                type_annotation,
                initializer,
            } => self.collect_variable_symbol(name, *mutable, type_annotation, initializer, node.span),
            Function { .. } => self.collect_function_item_symbols(node),
            StructDeclaration {
                name,
                fields,
                generic_parameters,
            } => self.collect_struct_symbols(name, fields, generic_parameters, node.span),
            ImplDeclaration { .. } => Ok((None, None)),
            PathQualifier { ty, tr } => {
                self.symbol_collector_check_node(ty)?;
                self.collect_optional_node(tr)?;
                Ok((None, None))
            },
            EnumDeclaration { name, variants } => self.collect_enum_symbols(name, variants, node.span),
            TraitDeclaration {
                name,
                generic_parameters,
                constants,
                types,
                signatures,
            } => {
                self.collect_trait_symbols(name, generic_parameters, constants, types, signatures, node.span)
            }
            TypeDeclaration {
                name,
                generic_parameters,
                value
            } => self.collect_type_symbols(name, generic_parameters, value, node.span),
            Block(_) => self.collect_block_symbols(node),
            _ => {
                for child in node.children_mut() {
                    self.symbol_collector_check_node(child)?;
                }

                Ok((None, None))
            }
        };

        if let Ok((value_id_opt, ref type_id_opt)) = declared_symbol_opt {
            node.value_id = value_id_opt;
            node.type_id = type_id_opt.clone();
        }

        declared_symbol_opt
    }

    fn collect_variable_symbol(
        &mut self,
        name: &str,
        mutable: bool,
        type_annotation: &mut Option<BoxedAstNode>,
        initializer: &mut Option<BoxedAstNode>,
        span: Span,
    ) -> Result<(Option<ValueSymbolId>, Option<Type>), BoxedError> {
        self.collect_optional_node(type_annotation)?;
        self.collect_optional_node(initializer)?;

        let value_id = self.symbol_table.add_value_symbol(
            name,
            ValueSymbolKind::Variable,
            mutable,
            QualifierKind::Public,
            None,
            Some(span),
        )?;

        Ok((Some(value_id), None))
    }

    fn collect_function_item_symbols(
        &mut self,
        node: &mut AstNode,
    ) -> Result<(Option<ValueSymbolId>, Option<Type>), BoxedError> {
        let (is_declaration, qualifier, name, generic_parameters, parameters, return_type, body, instance) =
            if let AstNodeKind::Function {
                qualifier,
                name,
                generic_parameters,
                parameters,
                return_type,
                body,
                instance,
            } = &mut node.kind
            {
                (
                    !name.is_empty(),
                    *qualifier,
                    name.clone(),
                    generic_parameters,
                    parameters,
                    return_type,
                    body,
                    instance,
                )
            } else {
                unreachable!();
            };

        let scope_id = self.symbol_table.enter_scope(ScopeKind::Function);
        node.scope_id = Some(scope_id);

        let scope = self.symbol_table.get_scope_mut(scope_id).unwrap();
        scope.receiver_kind = *instance;

        self.collect_generic_parameters(generic_parameters)?;
        self.collect_function_parameters(parameters)?;
        self.collect_optional_node(return_type)?;

        if let Some(b) = body {
            self.symbol_collector_check_node(b)?;
        }

        self.symbol_table.exit_scope();

        if is_declaration {
            let value_id = self.symbol_table.add_value_symbol(
                &name,
                ValueSymbolKind::Function(scope_id),
                false,
                qualifier.unwrap_or(QualifierKind::Public),
                None,
                Some(node.span),
            )?;
            Ok((Some(value_id), None))
        } else {
            Ok((None, None))
        }
    }

    fn collect_struct_symbols(
        &mut self,
        name: &str,
        fields: &mut [AstNode],
        generic_parameters: &mut [AstNode],
        span: Span,
    ) -> Result<(Option<ValueSymbolId>, Option<Type>), BoxedError> {
        let scope_id = self.symbol_table.enter_scope(ScopeKind::Struct);

        let generic_param_ids = self.collect_generic_parameters(generic_parameters)?;
        for field in fields {
            self.symbol_collector_check_node(field)?;
            if let AstNodeKind::StructField { qualifier, name, .. } = &field.kind {
                let field_id = self.symbol_table.add_value_symbol(
                    name,
                    ValueSymbolKind::StructField,
                    false,
                    *qualifier,
                    None,
                    Some(field.span),
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
            Some(span),
        )?;

        Ok((None, Some(Type::new_base(type_id))))
    }

    fn collect_enum_symbols(
        &mut self,
        name: &str,
        variants: &mut IndexMap<String, (AstNode, Option<AstNode>)>,
        span: Span,
    ) -> Result<(Option<ValueSymbolId>, Option<Type>), BoxedError> {
        let scope_id = self.symbol_table.enter_scope(ScopeKind::Enum);

        for (variant_name, (variant_node, _)) in variants {
            self.symbol_collector_check_node(variant_node)?;
            let variant_id = self.symbol_table.add_value_symbol(
                variant_name,
                ValueSymbolKind::EnumVariant,
                false,
                QualifierKind::Public,
                None,
                Some(variant_node.span),
            )?;
            variant_node.value_id = Some(variant_id);
        }

        self.symbol_table.exit_scope();
        let type_id = self.symbol_table.add_type_symbol(
            name,
            TypeSymbolKind::Enum((scope_id, vec![])),
            vec![],
            QualifierKind::Public,
            Some(span),
        )?;

        Ok((None, Some(Type::new_base(type_id))))
    }

    fn collect_trait_symbols(
        &mut self,
        name: &mut str,
        generic_parameters: &mut [AstNode],
        constants: &mut [AstNode],
        types: &mut [AstNode],
        signatures: &mut [AstNode],
        span: Span,
    ) -> Result<(Option<ValueSymbolId>, Option<Type>), BoxedError> {
        let trait_scope_id = self.symbol_table.enter_scope(ScopeKind::Trait);

        let generic_param_ids = self.collect_generic_parameters(generic_parameters)?;
        self.symbol_table.add_type_symbol(
            "Self",
            TypeSymbolKind::TraitSelf,
            vec![],
            QualifierKind::Public,
            None,
        )?;

        for const_node in constants {
            self.symbol_collector_check_node(const_node)?;
            if let AstNodeKind::TraitConstant { name, .. } = &const_node.kind {
                let const_id = self.symbol_table.add_value_symbol(
                    name,
                    ValueSymbolKind::Variable,
                    false,
                    QualifierKind::Public,
                    None,
                    Some(const_node.span),
                )?;
                const_node.value_id = Some(const_id);
            }
        }

        for type_node in types {
            self.symbol_collector_check_node(type_node)?;
            if let AstNodeKind::TraitType(name) = &type_node.kind {
                let type_id = self.symbol_table.add_type_symbol(
                    name,
                    TypeSymbolKind::TypeAlias((None, None)),
                    vec![],
                    QualifierKind::Public,
                    Some(type_node.span),
                )?;
                type_node.type_id = Some(Type::new_base(type_id));
            }
        }

        for signature in signatures.iter_mut() {
            self.symbol_collector_check_node(signature)?;
            if let AstNodeKind::Function {
                name,
                generic_parameters,
                instance,
                ..
            } = &mut signature.kind
            {
                let sig_generic_param_ids = self.collect_generic_parameters(generic_parameters)?;

                let sig_type_id = self.symbol_table.add_type_symbol(
                    name,
                    TypeSymbolKind::FunctionSignature {
                        params: vec![],
                        return_type: Type::new_base(self.builtin_types[PrimitiveKind::Void as usize]),
                        instance: *instance,
                    },
                    sig_generic_param_ids,
                    QualifierKind::Public,
                    Some(signature.span),
                )?;

                signature.type_id = Some(Type::new_base(sig_type_id));
            }
        }

        self.symbol_table.exit_scope();

        let trait_type_id = self.symbol_table.add_type_symbol(
            name,
            TypeSymbolKind::Trait(trait_scope_id),
            generic_param_ids,
            QualifierKind::Public,
            Some(span),
        )?;
        Ok((None, Some(Type::new_base(trait_type_id))))
    }

    fn collect_generic_parameters(
        &mut self,
        params: &mut [AstNode],
    ) -> Result<Vec<TypeSymbolId>, BoxedError> {
        let mut ids = vec![];
        for param in params {
            self.symbol_collector_check_node(param)?;
            if let AstNodeKind::GenericParameter { name, .. } = &param.kind {
                let id = self.symbol_table.add_type_symbol(
                    name,
                    TypeSymbolKind::Generic(vec![]),
                    vec![],
                    QualifierKind::Public,
                    Some(param.span),
                )?;
                param.type_id = Some(Type::new_base(id));
                ids.push(id);
            }
        }
        Ok(ids)
    }

    fn collect_function_parameters(
        &mut self,
        params: &mut [AstNode],
    ) -> Result<Vec<ValueSymbolId>, BoxedError> {
        let mut ids = vec![];
        for param in params {
            self.symbol_collector_check_node(param)?;
            if let AstNodeKind::FunctionParameter { name, mutable, .. } = &param.kind {
                let id = self.symbol_table.add_value_symbol(
                    name,
                    ValueSymbolKind::Variable,
                    *mutable,
                    QualifierKind::Public,
                    None,
                    Some(param.span),
                )?;
                param.value_id = Some(id);
                ids.push(id);
            }
        }
        Ok(ids)
    }

    fn collect_block_symbols(
        &mut self,
        node: &mut AstNode,
    ) -> Result<(Option<ValueSymbolId>, Option<Type>), BoxedError> {
        let scope_id = self.symbol_table.enter_scope(ScopeKind::Block);
        node.scope_id = Some(scope_id);

        if let AstNodeKind::Block(statements) = &mut node.kind {
            for statement in statements {
                self.symbol_collector_check_node(statement)?;
            }
        }

        self.symbol_table.exit_scope();
        Ok((None, None))
    }

    fn collect_type_symbols(
        &mut self,
        name: &str,
        generic_parameters: &mut [AstNode],
        value: &mut BoxedAstNode,
        span: Span,
    ) -> Result<(Option<ValueSymbolId>, Option<Type>), BoxedError> {
        let (scope_id, generics) = if !generic_parameters.is_empty() {
            let scope_id = self.symbol_table.enter_scope(ScopeKind::Type);
            let generics = self.collect_generic_parameters(generic_parameters)?;
            self.symbol_table.exit_scope();

            (Some(scope_id), generics)
        } else {
            (None, vec![])
        };

        self.symbol_collector_check_node(value)?;

        let type_id = self.symbol_table.add_type_symbol(
            name,
            TypeSymbolKind::TypeAlias((scope_id, None)),
            generics,
            QualifierKind::Public,
            Some(span),
        )?;
        Ok((None, Some(Type::new_base(type_id))))
    }

    fn collect_optional_node(&mut self, node: &mut Option<BoxedAstNode>) -> Result<(), BoxedError> {
        if let Some(n) = node {
            self.symbol_collector_check_node(n)?;
        }
        Ok(())
    }
}

impl SemanticAnalyzer {
    pub fn generic_constraints_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];

        if let AstNodeKind::Program(statements) = &mut program.kind {
            for statement in statements {
                if let Err(err) = self.generic_constraints_check_node(statement) {
                    errors.push(*err);
                }
            }
        } else {
            unreachable!();
        }

        errors
    }

    fn generic_constraints_check_node(&mut self, statement: &mut AstNode) -> Result<(), BoxedError> {
        match &statement.kind {
            AstNodeKind::GenericParameter { .. } => self.collect_generic_constraint(statement),
            _ => {
                for node in statement.children_mut() {
                    self.generic_constraints_check_node(node)?;
                }

                Ok(())
            }
        }
    }

    fn collect_generic_constraint(&mut self, node: &mut AstNode) -> Result<(), BoxedError> {
        node.scope_id = Some(self.symbol_table.get_current_scope_id());

        if node.type_id.is_none() {
            return Ok(());
        }

        let AstNodeKind::GenericParameter { constraints, .. } = &mut node.kind else {
            unreachable!();
        };
        let mut trait_ids = vec![];

        for constraint in constraints.iter() {
            let type_symbol = self.symbol_table.find_type_symbol(constraint).ok_or_else(|| {
                self.create_error(
                    ErrorKind::UnknownIdentifier(constraint.clone()),
                    node.span,
                    &[node.span],
                )
            })?;

            if !matches!(type_symbol.kind, TypeSymbolKind::Trait(_)) {
                return Err(self.create_error(
                    ErrorKind::InvalidConstraint(constraint.clone()),
                    node.span,
                    &[node.span],
                ));
            }

            trait_ids.push(type_symbol.id);
        }

        let type_symbol = self
            .symbol_table
            .get_type_symbol_mut(node.type_id.as_ref().unwrap().get_base_symbol())
            .unwrap();
        if let TypeSymbolKind::Generic(constraints) = &mut type_symbol.kind {
            *constraints = trait_ids;
        }

        Ok(())
    }
}

impl SemanticAnalyzer {
    pub fn struct_field_type_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];

        if let AstNodeKind::Program(statements) = &mut program.kind {
            for statement in statements {
                if let Err(err) = self.struct_field_type_collector_check_node(statement) {
                    errors.push(*err);
                }
            }
        } else {
            unreachable!();
        }

        errors
    }

    fn struct_field_type_collector_check_node(&mut self, statement: &mut AstNode) -> Result<(), BoxedError> {
        match &mut statement.kind {
            AstNodeKind::StructDeclaration { fields, .. } => self.struct_field_type_collector_handle_fields(fields),
            _ => {
                for node in statement.children_mut() {
                    self.struct_field_type_collector_check_node(node)?;
                }

                Ok(())
            }
        }
    }

    fn struct_field_type_collector_handle_fields(&mut self, fields: &mut [AstNode]) -> Result<(), BoxedError> {
        for field_node in fields.iter_mut() {
            let AstNodeKind::StructField { type_annotation, .. } = &mut field_node.kind else {
                continue;
            };

            let resolved_type = self.get_type_from_ast(type_annotation)?;

            let field_symbol = self
                .symbol_table
                .get_value_symbol_mut(field_node.value_id.unwrap())
                .unwrap();

            field_symbol.type_id = Some(resolved_type.clone());
            field_node.type_id = Some(resolved_type);
        }

        Ok(())
    }

    fn get_type_from_ast(&mut self, node: &mut AstNode) -> Result<Type, BoxedError> {
        match &mut node.kind {
            AstNodeKind::TypeReference {
                type_name,
                generic_types,
                reference_kind,
            } => {
                let args = generic_types
                    .iter_mut()
                    .map(|arg_node| self.get_type_from_ast(arg_node))
                    .collect::<Result<Vec<_>, _>>()?;

                let base_symbol = self
                    .symbol_table
                    .find_type_symbol_from_scope(node.scope_id.unwrap(), type_name)
                    .ok_or_else(|| {
                        self.create_error(
                            ErrorKind::UnknownIdentifier(type_name.clone()),
                            node.span,
                            &[node.span],
                        )
                    })?;

                let base_type = Type::Base {
                    symbol: base_symbol.id,
                    args,
                };

                Ok(match reference_kind {
                    ReferenceKind::Value => base_type,
                    ReferenceKind::Reference => Type::Reference(Box::new(base_type)),
                    ReferenceKind::MutableReference => Type::MutableReference(Box::new(base_type)),
                })
            },
            AstNodeKind::FunctionPointer { params, return_type } => {
                let param_types = params
                    .iter_mut()
                    .map(|p| self.get_type_from_ast(p))
                    .collect::<Result<Vec<_>, _>>()?;

                let return_type_val = if let Some(rt_node) = return_type {
                    self.get_type_from_ast(rt_node)?
                } else {
                    Type::new_base(self.builtin_types[PrimitiveKind::Void as usize])
                };

                let fn_ptr_id = self.symbol_table.add_type_symbol(
                    &format!("#fn_ptr_{:?}", node.span.start),
                    TypeSymbolKind::FunctionSignature {
                        params: param_types,
                        return_type: return_type_val,
                        instance: None,
                    },
                    vec![],
                    QualifierKind::Private,
                    Some(node.span),
                )?;

                Ok(Type::new_base(fn_ptr_id))
            },
            _ => Err(self.create_error(ErrorKind::ExpectedType, node.span, &[node.span])),
        }
    }
}

impl SemanticAnalyzer {
    pub fn impl_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];

        if let AstNodeKind::Program(statements) = &mut program.kind {
            for statement in statements {
                if let Err(err) = self.impl_collector_check_node(statement) {
                    errors.push(*err);
                }
            }
        } else {
            unreachable!();
        }

        errors
    }

    fn impl_collector_check_node(&mut self, statement: &mut AstNode) -> Result<(), BoxedError> {
        match &statement.kind {
            AstNodeKind::ImplDeclaration { .. } => self.collect_and_register_impl_block(statement),
            _ => {
                for node in statement.children_mut() {
                    self.impl_collector_check_node(node)?;
                }

                Ok(())
            }
        }
    }

    fn collect_and_register_impl_block(&mut self, node: &mut AstNode) -> Result<(), BoxedError> {
        let (
            associated_constants,
            associated_types,
            associated_functions,
            impl_generics,
            type_reference,
            trait_node,
        ) = match &mut node.kind {
            AstNodeKind::ImplDeclaration {
                associated_constants,
                associated_types,
                associated_functions,
                generic_parameters,
                type_reference,
                trait_node,
            } => (
                associated_constants,
                associated_types,
                associated_functions,
                generic_parameters,
                type_reference,
                trait_node,
            ),
            _ => return Ok(()),
        };

        let impl_scope_id = self.symbol_table.enter_scope(ScopeKind::Impl);
        let impl_generic_param_ids = self.collect_generic_parameters(impl_generics)?;
        for generic in impl_generics.iter_mut() {
            self.collect_generic_constraint(generic)?;
        }

        node.scope_id = Some(impl_scope_id);
        type_reference.scope_id = Some(impl_scope_id);

        if let Some(trait_node) = trait_node {
            trait_node.scope_id = Some(impl_scope_id);

            let (trait_id, trait_generic_specialization) = self.resolve_type_ref_from_ast(trait_node)?;
            self.symbol_table.get_scope_mut(impl_scope_id).unwrap().trait_id = Some(trait_id);

            let (implementing_type_id, type_specialization) = self.resolve_type_ref_from_ast(type_reference)?;
            let self_type = Type::Base {
                symbol: implementing_type_id,
                args: type_specialization.iter().map(|id| Type::new_base(*id)).collect()
            };

            self.symbol_table.add_type_symbol(
                "Self",
                TypeSymbolKind::TypeAlias((None, Some(self_type))),
                vec![],
                QualifierKind::Public,
                None,
            )?;

            self.collect_impl_body_symbols(associated_constants, associated_types, associated_functions)?;

            let trait_impl = TraitImpl {
                impl_scope_id,
                impl_generic_params: impl_generic_param_ids,
                trait_generic_specialization,
                type_specialization,
            };

            self.trait_registry
                .register(trait_id, implementing_type_id, trait_impl);
        } else {
            let (base_type_id, specialization) = self.resolve_type_ref_from_ast(type_reference)?;

            let base_type_symbol = self.symbol_table.get_type_symbol(base_type_id).unwrap();
            let self_type = Type::Base {
                symbol: base_type_symbol.id,
                args: specialization.iter().map(|id| Type::new_base(*id)).collect()
            };

            self.symbol_table.add_type_symbol(
                "Self",
                TypeSymbolKind::TypeAlias((None, Some(self_type))),
                vec![],
                QualifierKind::Public,
                None,
            )?;

            self.collect_impl_body_symbols(associated_constants, associated_types, associated_functions)?;

            let impl_block = InherentImpl {
                scope_id: impl_scope_id,
                specialization,
                generic_params: impl_generic_param_ids,
                span: node.span,
            };

            let invalid_impl_error = self.create_error(
                ErrorKind::InvalidImpl(Some(
                    self.symbol_table
                        .get_type_name(self.symbol_table.get_type_symbol(base_type_id).unwrap().name_id)
                        .to_string(),
                )),
                type_reference.span,
                &[type_reference.span],
            );
            let base_type_symbol_mut = self.symbol_table.get_type_symbol_mut(base_type_id).unwrap();

            match &mut base_type_symbol_mut.kind {
                TypeSymbolKind::Struct((_, impls)) | TypeSymbolKind::Enum((_, impls)) => {
                    impls.push(impl_block);
                }
                _ => return Err(invalid_impl_error),
            }
        }

        self.symbol_table.exit_scope();
        Ok(())
    }

    fn collect_impl_body_symbols(
        &mut self,
        associated_constants: &mut [AstNode],
        associated_types: &mut [AstNode],
        associated_functions: &mut [AstNode],
    ) -> Result<(), BoxedError> {
        for func_node in associated_functions {
            if let AstNodeKind::Function {
                qualifier,
                name,
                generic_parameters,
                parameters,
                body,
                instance,
                return_type
            } = &mut func_node.kind
            {
                let func_scope_id = self.symbol_table.enter_scope(ScopeKind::Function);
                func_node.scope_id = Some(func_scope_id);

                let scope = self.symbol_table.get_scope_mut(func_scope_id).unwrap();
                scope.receiver_kind = *instance;

                self.collect_generic_parameters(generic_parameters)?;
                for generic in generic_parameters.iter_mut() {
                    self.collect_generic_constraint(generic)?;
                }

                self.collect_function_parameters(parameters)?;
                self.symbol_collector_check_node(body.as_mut().unwrap())?;
                self.collect_optional_node(return_type)?;
                self.symbol_table.exit_scope();

                func_node.value_id = Some(self.symbol_table.add_value_symbol(
                    name,
                    ValueSymbolKind::Function(func_scope_id),
                    false,
                    qualifier.unwrap(),
                    None,
                    Some(func_node.span),
                )?);
            }
        }

        for const_node in associated_constants {
            const_node.scope_id = Some(self.symbol_table.get_current_scope_id());

            if let AstNodeKind::AssociatedConstant { qualifier, name, type_annotation, initializer } = &mut const_node.kind {
                let const_id = self.symbol_table.add_value_symbol(
                    name,
                    ValueSymbolKind::Variable,
                    false,
                    *qualifier,
                    None,
                    Some(const_node.span),
                )?;
                const_node.value_id = Some(const_id);

                self.collect_optional_node(type_annotation)?;
                self.symbol_collector_check_node(initializer)?;
            }
        }

        for type_node in associated_types {
            type_node.scope_id = Some(self.symbol_table.get_current_scope_id());

            if let AstNodeKind::AssociatedType { name, qualifier, value } = &mut type_node.kind {
                let type_id = self.symbol_table.add_type_symbol(
                    name,
                    TypeSymbolKind::TypeAlias((None, None)),
                    vec![],
                    *qualifier,
                    Some(type_node.span),
                )?;
                type_node.type_id = Some(Type::new_base(type_id));

                self.symbol_collector_check_node(value)?;
            }
        }

        Ok(())
    }

    fn find_type_by_name(&self, node: &AstNode) -> Result<TypeSymbolId, BoxedError> {
        let name = node
            .get_name()
            .ok_or_else(|| self.create_error(ErrorKind::ExpectedType, node.span, &[node.span]))?;

        let type_symbol = self.symbol_table.find_type_symbol(&name).ok_or_else(|| {
            self.create_error(
                ErrorKind::UnknownIdentifier(name.clone()),
                node.span,
                &[node.span],
            )
        })?;

        Ok(type_symbol.id)
    }

    fn resolve_type_ref_from_ast(
        &self,
        node: &mut AstNode,
    ) -> Result<(TypeSymbolId, Vec<TypeSymbolId>), BoxedError> {
        node.scope_id = Some(self.symbol_table.get_current_scope_id());

        let (name, arg_nodes) = match &mut node.kind {
            AstNodeKind::TypeReference {
                type_name,
                generic_types,
                ..
            } => (type_name, generic_types),
            _ => return Err(self.create_error(ErrorKind::ExpectedType, node.span, &[node.span])),
        };

        let base_type_id = self
            .symbol_table
            .find_type_symbol(name)
            .ok_or_else(|| {
                self.create_error(
                    ErrorKind::UnknownIdentifier(name.clone()),
                    node.span,
                    &[node.span],
                )
            })?
            .id;

        let mut arg_ids = vec![];
        for arg_node in arg_nodes {
            let arg_id = self.resolve_type_ref_from_ast(arg_node)?.0;
            arg_ids.push(arg_id);
        }

        Ok((base_type_id, arg_ids))
    }
}
