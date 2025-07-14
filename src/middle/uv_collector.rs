// middle/uv_collector.rs
use crate::{
    boxed,
    frontend::ast::{AstNode, AstNodeKind, BoxedAstNode},
    middle::semantic_analyzer::{
        Constraint, ConstraintInfo, PrimitiveKind, ScopeId, ScopeKind, SemanticAnalyzer, Type, TypeSymbolId,
        TypeSymbolKind,
    },
    utils::{
        error::{BoxedError, Error, ErrorKind},
        kind::{Operation, QualifierKind, ReferenceKind, Span},
    },
};

impl SemanticAnalyzer {
    fn get_primitive_type(&self, primitive: PrimitiveKind) -> TypeSymbolId {
        self.builtin_types[primitive as usize]
    }

    fn get_type_of_identifier(&self, scope_id: ScopeId, name: &str, span: Span) -> Result<Type, BoxedError> {
        match self.symbol_table.find_value_symbol_from_scope(scope_id, name) {
            Some(value_symbol) => match value_symbol.type_id.clone() {
                Some(type_id) => Ok(type_id),
                None => Err(self.create_error(ErrorKind::UnresolvedType(name.to_string()), span, &[span])),
            },
            None => Err(self.create_error(ErrorKind::UnknownIdentifier(name.to_string()), span, &[span])),
        }
    }

    fn collect_uv_unary_operation(
        &mut self,
        uv_id: TypeSymbolId,
        operator: &mut Operation,
        operand: &mut BoxedAstNode,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let uv_type = self.collect_uvs(operand)?;
        let result_uv = Type::new_base(uv_id);

        match operator.to_trait_data() {
            Some((trait_name, _)) => {
                self.unification_context.register_constraint(
                    Constraint::Operation(
                        result_uv,
                        Type::new_base(self.trait_registry.get_default_trait(&trait_name)),
                        uv_type,
                        None,
                    ),
                    info,
                );
            }
            None => match operator {
                Operation::Dereference => self.unification_context.register_constraint(
                    Constraint::Equality(uv_type, Type::Reference(Box::new(result_uv))),
                    info,
                ),
                Operation::ImmutableAddressOf => self.unification_context.register_constraint(
                    Constraint::Equality(result_uv, Type::Reference(boxed!(uv_type))),
                    info,
                ),
                Operation::MutableAddressOf => self.unification_context.register_constraint(
                    Constraint::Equality(result_uv, Type::MutableReference(boxed!(uv_type))),
                    info,
                ),
                _ => unreachable!(),
            },
        }

        Ok(())
    }

    fn collect_uv_binary_operation(
        &mut self,
        uv_id: TypeSymbolId,
        left: &mut BoxedAstNode,
        right: &mut BoxedAstNode,
        operator: &mut Operation,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let left_type = self.collect_uvs(left)?;
        let right_type = self.collect_uvs(right)?;
        let result_uv = Type::new_base(uv_id);

        match operator.to_trait_data() {
            Some((trait_name, _)) => {
                self.unification_context.register_constraint(
                    Constraint::Operation(
                        result_uv,
                        Type::Base {
                            symbol: self.trait_registry.get_default_trait(&trait_name),
                            args: vec![right_type.clone()],
                        },
                        left_type,
                        Some(right_type),
                    ),
                    info,
                );
            }
            None => match operator {
                Operation::Assign => {
                    self.unification_context
                        .register_constraint(Constraint::Equality(left_type, right_type), info);

                    self.unification_context.register_constraint(
                        Constraint::Equality(
                            result_uv,
                            Type::new_base(self.get_primitive_type(PrimitiveKind::Void)),
                        ),
                        info,
                    );
                }
                _ => unreachable!(),
            },
        }

        Ok(())
    }

    fn collect_uv_conditional_operation(
        &mut self,
        uv_id: TypeSymbolId,
        left: &mut BoxedAstNode,
        right: &mut BoxedAstNode,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let left_type = self.collect_uvs(left)?;
        let right_type = self.collect_uvs(right)?;
        let bool_type = Type::new_base(self.get_primitive_type(PrimitiveKind::Bool));

        self.unification_context
            .register_constraint(Constraint::Equality(left_type, bool_type.clone()), info);
        self.unification_context
            .register_constraint(Constraint::Equality(right_type, bool_type.clone()), info);
        self.unification_context.register_constraint(
            Constraint::Equality(Type::new_base(uv_id), bool_type),
            info,
        );

        Ok(())
    }

    fn collect_uv_variable_declaration(
        &mut self,
        uv_id: TypeSymbolId,
        node: &mut AstNode,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let AstNodeKind::VariableDeclaration {
            type_annotation,
            initializer,
            ..
        } = &mut node.kind
        else {
            unreachable!();
        };

        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::new_base(uv_id),
                Type::new_base(self.get_primitive_type(PrimitiveKind::Void)),
            ),
            info,
        );

        let init_type = if let Some(init) = initializer {
            Some(self.collect_uvs(init)?)
        } else {
            None
        };

        let symbol_uv = self
            .unification_context
            .generate_uv_type(&mut self.symbol_table, span);

        if let Some(annot) = type_annotation {
            let annot_type = self.collect_uvs(annot)?;

            if let Some(init_type) = init_type {
                self.unification_context
                    .register_constraint(Constraint::Equality(annot_type.clone(), init_type), info);
            }

            self.unification_context
                .register_constraint(Constraint::Equality(symbol_uv.clone(), annot_type), info);
        } else if let Some(init_type) = init_type {
            self.unification_context
                .register_constraint(Constraint::Equality(symbol_uv.clone(), init_type), info);
        } else {
            return Err(self.create_error(ErrorKind::BadVariableDeclaration, span, &[span]));
        }

        self.symbol_table
            .get_value_symbol_mut(node.value_id.unwrap())
            .unwrap()
            .type_id = Some(symbol_uv.clone());

        Ok(())
    }

    fn collect_uv_block(
        &mut self,
        uv_id: TypeSymbolId,
        statements: &mut [AstNode],
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let mut last_type = None;

        for stmt in statements.iter_mut() {
            last_type = Some(self.collect_uvs(stmt)?);
        }

        if let Some(last_type) = last_type {
            self.unification_context.register_constraint(
                Constraint::Equality(Type::new_base(uv_id), last_type),
                info,
            );
        }

        Ok(())
    }

    fn collect_uv_if_statement(
        &mut self,
        uv_id: TypeSymbolId,
        condition: &mut BoxedAstNode,
        then_branch: &mut BoxedAstNode,
        else_if_branches: &mut [(BoxedAstNode, BoxedAstNode)],
        else_branch: &mut Option<BoxedAstNode>,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let cond_type = self.collect_uvs(condition)?;
        let bool_type = Type::new_base(self.get_primitive_type(PrimitiveKind::Bool));
        self.unification_context
            .register_constraint(Constraint::Equality(cond_type, bool_type.clone()), info);

        let then_type = self.collect_uvs(then_branch)?;
        let mut branch_types = vec![then_type.clone()];

        for (elif_cond, elif_branch) in else_if_branches.iter_mut() {
            let elif_cond_type = self.collect_uvs(elif_cond)?;
            self.unification_context
                .register_constraint(Constraint::Equality(elif_cond_type, bool_type.clone()), info);
            let elif_type = self.collect_uvs(elif_branch)?;
            branch_types.push(elif_type);
        }

        if let Some(else_node) = else_branch {
            let else_type = self.collect_uvs(else_node)?;
            branch_types.push(else_type);
        }

        for branch_type in &branch_types {
            self.unification_context.register_constraint(
                Constraint::Equality(Type::new_base(uv_id), branch_type.clone()),
                info,
            );
        }

        Ok(())
    }

    fn collect_uv_while_loop(
        &mut self,
        uv_id: TypeSymbolId,
        condition: &mut BoxedAstNode,
        body: &mut BoxedAstNode,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let cond_type = self.collect_uvs(condition)?;
        let bool_type = Type::new_base(self.get_primitive_type(PrimitiveKind::Bool));
        self.unification_context
            .register_constraint(Constraint::Equality(cond_type, bool_type), info);

        self.collect_uvs(body)?;

        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::new_base(uv_id),
                Type::new_base(self.get_primitive_type(PrimitiveKind::Void)),
            ),
            info,
        );

        Ok(())
    }

    fn collect_uv_for_loop(
        &mut self,
        uv_id: TypeSymbolId,
        initializer: &mut Option<BoxedAstNode>,
        condition: &mut Option<BoxedAstNode>,
        increment: &mut Option<BoxedAstNode>,
        body: &mut BoxedAstNode,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        if let Some(init) = initializer {
            self.collect_uvs(init)?;
        }

        if let Some(cond) = condition {
            let cond_type = self.collect_uvs(cond)?;
            let bool_type = Type::new_base(self.get_primitive_type(PrimitiveKind::Bool));
            self.unification_context
                .register_constraint(Constraint::Equality(cond_type, bool_type), info);
        }

        if let Some(inc) = increment {
            self.collect_uvs(inc)?;
        }

        self.collect_uvs(body)?;

        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::new_base(uv_id),
                Type::new_base(self.get_primitive_type(PrimitiveKind::Void)),
            ),
            info,
        );

        Ok(())
    }

    fn collect_uv_return(
        &mut self,
        uv_id: TypeSymbolId,
        opt_expr: &mut Option<BoxedAstNode>,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::new_base(uv_id),
                Type::new_base(self.get_primitive_type(PrimitiveKind::Never)),
            ),
            info,
        );

        let Some(expected_return_type) = self.current_return_type.clone() else {
             return Err(self.create_error(ErrorKind::InvalidReturn, info.span, &[info.span]));
        };

        let value_type = if let Some(expr) = opt_expr {
            self.collect_uvs(expr)?
        } else {
            Type::new_base(self.get_primitive_type(PrimitiveKind::Void))
        };
        
        self.unification_context.register_constraint(
            Constraint::Equality(expected_return_type, value_type),
            info,
        );

        Ok(())
    }

    fn collect_uv_function(
        &mut self,
        uv_id: TypeSymbolId,
        node: &mut AstNode,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let AstNodeKind::Function {
            name,
            generic_parameters,
            parameters,
            return_type,
            instance,
            body,
            ..
        } = &mut node.kind
        else {
            unreachable!();
        };

        let is_declaration = !name.is_empty();

        let symbol_uv_opt = if is_declaration {
            let uv = self
                .unification_context
                .generate_uv_type(&mut self.symbol_table, span);

            self.symbol_table
                .get_value_symbol_mut(node.value_id.unwrap())
                .unwrap()
                .type_id = Some(uv.clone());

            Some(uv)
        } else {
            None
        };

        let generic_types: Vec<TypeSymbolId> = generic_parameters
            .iter_mut()
            .map(|p| self.collect_uvs(p).map(|t| t.get_base_symbol()))
            .collect::<Result<_, _>>()?;

        for param_node in parameters.iter_mut() {
            self.collect_uvs(param_node)?;
        }

        let param_types: Vec<Type> = parameters
            .iter()
            .map(|p| {
                self.symbol_table
                    .get_value_symbol(p.value_id.unwrap())
                    .unwrap()
                    .type_id
                    .clone()
                    .unwrap()
            })
            .collect();

        let return_type_val = if let Some(rt_node) = return_type {
            self.collect_uvs(rt_node)?
        } else {
            Type::new_base(self.get_primitive_type(PrimitiveKind::Void))
        };

        let old_return_type = self.current_return_type.clone();
        self.current_return_type = Some(return_type_val.clone());

        if let Some(body_node) = body {
            self.collect_uvs(body_node)?;
        }

        self.current_return_type = old_return_type;

        let fn_sig_type_id = self.symbol_table.add_type_symbol(
            &format!("#fn_sig_{}", uv_id),
            TypeSymbolKind::FunctionSignature {
                params: param_types,
                return_type: return_type_val,
                instance: *instance,
            },
            generic_types,
            QualifierKind::Private,
            Some(span),
        )?;

        let fn_sig_type = Type::new_base(fn_sig_type_id);

        if is_declaration {
            self.unification_context.register_constraint(
                Constraint::Equality(
                    Type::new_base(uv_id),
                    Type::new_base(self.get_primitive_type(PrimitiveKind::Void)),
                ),
                info,
            );

            self.unification_context
                .register_constraint(Constraint::Equality(symbol_uv_opt.unwrap(), fn_sig_type), info);
        } else {
            self.unification_context
                .register_constraint(Constraint::Equality(Type::new_base(uv_id), fn_sig_type), info);
        }

        Ok(())
    }

    fn collect_uv_function_parameter(
        &mut self,
        uv_id: TypeSymbolId,
        node: &mut AstNode,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let AstNodeKind::FunctionParameter {
            type_annotation,
            initializer,
            ..
        } = &mut node.kind
        else {
            unreachable!();
        };

        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::new_base(uv_id),
                Type::new_base(self.get_primitive_type(PrimitiveKind::Void)),
            ),
            info,
        );

        let annotation_type = self.collect_uvs(type_annotation)?;

        if let Some(init_node) = initializer {
            let init_type = self.collect_uvs(init_node)?;
            self.unification_context
                .register_constraint(Constraint::Equality(init_type, annotation_type.clone()), info);
        }

        let symbol_uv = self
            .unification_context
            .generate_uv_type(&mut self.symbol_table, span);

        self.unification_context
            .register_constraint(Constraint::Equality(symbol_uv.clone(), annotation_type), info);

        self.symbol_table
            .get_value_symbol_mut(node.value_id.unwrap())
            .unwrap()
            .type_id = Some(symbol_uv);

        Ok(())
    }

    fn collect_uv_function_pointer(
        &mut self,
        uv_id: TypeSymbolId,
        params: &mut [AstNode],
        return_type_node: &mut Option<BoxedAstNode>,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let param_types: Vec<Type> = params
            .iter_mut()
            .map(|p| self.collect_uvs(p))
            .collect::<Result<_, _>>()?;

        let return_type = if let Some(rt_node) = return_type_node {
            self.collect_uvs(rt_node)?
        } else {
            Type::new_base(self.get_primitive_type(PrimitiveKind::Void))
        };

        let fn_ptr_sig_id = self.symbol_table.add_type_symbol(
            &format!("#fn_ptr_sig_{}", uv_id),
            TypeSymbolKind::FunctionSignature {
                params: param_types,
                return_type,
                instance: None,
            },
            vec![],
            QualifierKind::Private,
            Some(span),
        )?;

        self.unification_context.register_constraint(
            Constraint::Equality(Type::new_base(uv_id), Type::new_base(fn_ptr_sig_id)),
            info,
        );

        Ok(())
    }

    fn collect_uv_struct_literal(
        &mut self,
        uv_id: TypeSymbolId,
        scope_id: ScopeId,
        name: &str,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let Some(symbol) = self.symbol_table.find_type_symbol_from_scope(scope_id, name) else {
            return Err(self.create_error(ErrorKind::UnknownIdentifier(name.to_owned()), span, &[span]));
        };

        self.unification_context.register_constraint(
            Constraint::Equality(Type::new_base(uv_id), Type::new_base(symbol.id)),
            info,
        );

        Ok(())
    }

    fn collect_uv_associated_const(
        &mut self,
        uv_id: TypeSymbolId,
        node: &mut AstNode,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::new_base(uv_id),
                Type::new_base(self.get_primitive_type(PrimitiveKind::Void)),
            ),
            info,
        );

        let AstNodeKind::AssociatedConstant {
            type_annotation,
            initializer,
            ..
        } = &mut node.kind
        else {
            unreachable!();
        };

        let init_type = self.collect_uvs(initializer)?;

        if let Some(annot) = type_annotation {
            let annot_type = self.collect_uvs(annot)?;

            self.unification_context
                .register_constraint(Constraint::Equality(annot_type, init_type.clone()), info);
        }

        let symbol_uv = self
            .unification_context
            .generate_uv_type(&mut self.symbol_table, span);

        self.unification_context
            .register_constraint(Constraint::Equality(symbol_uv.clone(), init_type), info);

        self.symbol_table
            .get_value_symbol_mut(node.value_id.unwrap())
            .unwrap()
            .type_id = Some(symbol_uv.clone());

        Ok(())
    }

    fn collect_uv_type_reference(
        &mut self,
        uv_id: TypeSymbolId,
        scope_id: ScopeId,
        type_name: &str,
        generic_types: &mut [AstNode],
        reference_kind: &mut ReferenceKind,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let symbol = self
            .symbol_table
            .find_type_symbol_from_scope(scope_id, type_name)
            .ok_or_else(|| {
                self.create_error(ErrorKind::UnknownIdentifier(type_name.to_owned()), span, &[span])
            })?
            .id;

        let args: Vec<Type> = generic_types
            .iter_mut()
            .map(|generic_type| self.collect_uvs(generic_type))
            .collect::<Result<Vec<_>, _>>()?;

        let base_symbol = Type::Base { symbol, args };

        let constraint = match reference_kind {
            ReferenceKind::Value => base_symbol,
            ReferenceKind::Reference => Type::Reference(boxed!(base_symbol)),
            ReferenceKind::MutableReference => Type::MutableReference(boxed!(base_symbol)),
        };

        self.unification_context.register_constraint(
            Constraint::Equality(Type::new_base(uv_id), constraint),
            info,
        );

        Ok(())
    }

    fn collect_uv_type_declaration(
        &mut self,
        uv_id: TypeSymbolId,
        node: &mut AstNode,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::new_base(uv_id),
                Type::new_base(self.get_primitive_type(PrimitiveKind::Void)),
            ),
            info,
        );

        let initializer_type = if let AstNodeKind::AssociatedType { value, .. } = &mut node.kind {
            self.collect_uvs(value)?
        } else if let AstNodeKind::TypeDeclaration { value, .. } = &mut node.kind {
            self.collect_uvs(value)?
        } else {
            unreachable!();
        };

        let symbol_uv = self
            .unification_context
            .generate_uv_type(&mut self.symbol_table, span);

        self.unification_context
            .register_constraint(Constraint::Equality(symbol_uv.clone(), initializer_type), info);

        let type_symbol = self
            .symbol_table
            .get_type_symbol_mut(node.type_id.as_mut().unwrap().get_base_symbol())
            .unwrap();
        let TypeSymbolKind::TypeAlias((_, alias)) = &mut type_symbol.kind else {
            unreachable!();
        };
        *alias = Some(symbol_uv);

        Ok(())
    }

    fn collect_uv_self_value(
        &mut self,
        uv_id: TypeSymbolId,
        scope_id: ScopeId,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let mut function_scope = self.symbol_table.get_scope(scope_id).unwrap();
        while function_scope.kind != ScopeKind::Function {
            match function_scope.parent {
                Some(parent_id) => function_scope = self.symbol_table.get_scope(parent_id).unwrap(),
                None => {
                    return Err(self.create_error(
                        ErrorKind::InvalidThis("outside of a function"),
                        span,
                        &[span],
                    ))
                }
            }
        }

        let receiver_kind = match function_scope.receiver_kind {
            Some(kind) => kind,
            None => {
                return Err(self.create_error(
                    ErrorKind::InvalidThis("in a static method without a 'this' parameter"),
                    span,
                    &[span],
                ))
            }
        };

        let impl_scope = match function_scope.parent {
            Some(parent_id) => self.symbol_table.get_scope(parent_id).unwrap(),
            None => {
                return Err(self.create_error(
                    ErrorKind::InvalidThis("outside of an impl block"),
                    span,
                    &[span],
                ))
            }
        };

        if impl_scope.kind != ScopeKind::Impl {
            return Err(self.create_error(ErrorKind::InvalidThis("outside of an impl block"), span, &[span]));
        }

        let TypeSymbolKind::TypeAlias((_, Some(self_type))) = &self
            .symbol_table
            .find_type_symbol_from_scope(impl_scope.id, "Self")
            .ok_or_else(|| self.create_error(ErrorKind::SelfOutsideImpl, span, &[span]))?
            .kind
        else {
            unreachable!();
        };

        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::new_base(uv_id),
                match receiver_kind {
                    ReferenceKind::Value => self_type.clone(),
                    ReferenceKind::Reference => Type::Reference(Box::new(self_type.clone())),
                    ReferenceKind::MutableReference => Type::MutableReference(Box::new(self_type.clone())),
                },
            ),
            info,
        );

        Ok(())
    }

    fn collect_uv_self_type(
        &mut self,
        uv_id: TypeSymbolId,
        scope_id: ScopeId,
        reference_kind: ReferenceKind,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let self_symbol = self
            .symbol_table
            .find_type_symbol_from_scope(scope_id, "Self")
            .ok_or_else(|| self.create_error(ErrorKind::SelfOutsideImpl, span, &[span]))?;

        if let TypeSymbolKind::TypeAlias((_, Some(concrete_type))) = &self_symbol.kind {
            self.unification_context.register_constraint(
                Constraint::Equality(
                    Type::new_base(uv_id),
                    match reference_kind {
                        ReferenceKind::Value => concrete_type.clone(),
                        ReferenceKind::Reference => Type::Reference(boxed!(concrete_type.clone())),
                        ReferenceKind::MutableReference => {
                            Type::MutableReference(boxed!(concrete_type.clone()))
                        }
                    },
                ),
                info,
            );
        }

        Ok(())
    }

    fn collect_uv_field_access(
        &mut self,
        uv_id: TypeSymbolId,
        left: &mut BoxedAstNode,
        right: &mut BoxedAstNode,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let right_name = right
            .get_name()
            .ok_or_else(|| self.create_error(ErrorKind::ExpectedIdentifier, right.span, &[right.span]))?;

        if let AstNodeKind::Identifier(left_name) = &left.kind {
            if let Some(type_symbol) = self
                .symbol_table
                .find_type_symbol_from_scope(left.scope_id.unwrap(), left_name)
            {
                let static_type = Type::new_base(type_symbol.id);
                left.type_id = Some(static_type.clone());

                self.unification_context.register_constraint(
                    Constraint::StaticMemberAccess(Type::new_base(uv_id), static_type, right_name),
                    info,
                );

                return Ok(());
            }
        }

        let left_type = self.collect_uvs(left)?;

        self.unification_context.register_constraint(
            Constraint::InstanceMemberAccess(Type::new_base(uv_id), left_type, right_name),
            info,
        );

        Ok(())
    }

    fn collect_uv_function_call(
        &mut self,
        uv_id: TypeSymbolId,
        function_node: &mut BoxedAstNode,
        arguments: &mut [AstNode],
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let function_type = self.collect_uvs(function_node)?;

        let argument_types: Vec<Type> = arguments
            .iter_mut()
            .map(|arg| self.collect_uvs(arg))
            .collect::<Result<_, _>>()?;

        let return_uv_type = self
            .unification_context
            .generate_uv_type(&mut self.symbol_table, span);

        self.unification_context.register_constraint(
            Constraint::FunctionSignature(function_type, argument_types, return_uv_type.clone()),
            info,
        );

        self.unification_context.register_constraint(
            Constraint::Equality(Type::new_base(uv_id), return_uv_type),
            info,
        );

        Ok(())
    }

    fn collect_uv_struct_field(
        &mut self,
        uv_id: TypeSymbolId,
        name: &str,
        type_annotation: &mut BoxedAstNode,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::new_base(uv_id),
                Type::new_base(self.get_primitive_type(PrimitiveKind::Void)),
            ),
            info,
        );

        let annotation_type = self.collect_uvs(type_annotation)?;
        self.symbol_table
            .find_value_symbol_in_scope_mut(name, info.scope_id)
            .unwrap()
            .type_id = Some(annotation_type);

        Ok(())
    }

    fn collect_uv_enum_variant(
        &mut self,
        uv_id: TypeSymbolId,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let enum_scope = self.symbol_table.get_scope(info.scope_id).unwrap();
        let enum_parent_scope = self
            .symbol_table
            .get_scope(enum_scope.parent.unwrap())
            .unwrap();

        let enum_type_symbol = enum_parent_scope
            .types
            .values()
            .find_map(|type_id| {
                let symbol = self.symbol_table.get_type_symbol(*type_id).unwrap();
                if let TypeSymbolKind::Enum((scope, _)) = symbol.kind {
                    if scope == info.scope_id {
                        return Some(symbol);
                    }
                }
                None
            })
            .unwrap();

        let enum_type = Type::new_base(enum_type_symbol.id);

        self.unification_context.register_constraint(
            Constraint::Equality(Type::new_base(uv_id), enum_type.clone()),
            info,
        );

        Ok(())
    }
}

impl SemanticAnalyzer {
    pub fn uv_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let mut errors = vec![];

        if let AstNodeKind::Program(statements) = &mut program.kind {
            for statement in statements {
                if let Err(err) = self.collect_uvs(statement) {
                    errors.push(*err);
                }
            }
        } else {
            unreachable!();
        }

        errors
    }

    fn collect_uvs(&mut self, expr: &mut AstNode) -> Result<Type, BoxedError> {
        use AstNodeKind::*;

        let uv = self
            .unification_context
            .generate_uv_type(&mut self.symbol_table, expr.span);
        let uv_id = uv.get_base_symbol();

        let info = ConstraintInfo {
            span: expr.span,
            scope_id: expr.scope_id.unwrap_or_else(|| panic!("scope_id should exist on node, especially this one: {} \n{:?}", expr, expr)),
        };

        match &mut expr.kind {
            IntegerLiteral(_) => self.unification_context.register_constraint(
                Constraint::Equality(
                    uv.clone(),
                    Type::new_base(self.get_primitive_type(PrimitiveKind::Int)),
                ),
                info,
            ),
            FloatLiteral(_) => self.unification_context.register_constraint(
                Constraint::Equality(
                    uv.clone(),
                    Type::new_base(self.get_primitive_type(PrimitiveKind::Float)),
                ),
                info,
            ),
            BooleanLiteral(_) => self.unification_context.register_constraint(
                Constraint::Equality(
                    uv.clone(),
                    Type::new_base(self.get_primitive_type(PrimitiveKind::Bool)),
                ),
                info,
            ),
            StringLiteral(_) => self.unification_context.register_constraint(
                Constraint::Equality(
                    uv.clone(),
                    Type::new_base(self.get_primitive_type(PrimitiveKind::String)),
                ),
                info,
            ),
            CharLiteral(_) => self.unification_context.register_constraint(
                Constraint::Equality(
                    uv.clone(),
                    Type::new_base(self.get_primitive_type(PrimitiveKind::Char)),
                ),
                info,
            ),
            Identifier(string) => self.unification_context.register_constraint(
                Constraint::Equality(
                    uv.clone(),
                    self.get_type_of_identifier(expr.scope_id.unwrap(), string, expr.span)?,
                ),
                info,
            ),

            UnaryOperation { operator, operand } => {
                self.collect_uv_unary_operation(uv_id, operator, operand, info)?
            }
            BinaryOperation {
                left,
                right,
                operator,
            } => self.collect_uv_binary_operation(uv_id, left, right, operator, info)?,
            ConditionalOperation { left, right, .. } => {
                self.collect_uv_conditional_operation(uv_id, left, right, info)?
            }
            VariableDeclaration { .. } => {
                self.collect_uv_variable_declaration(uv_id, expr, expr.span, info)?
            }
            Block(statements) => self.collect_uv_block(uv_id, statements, info)?,
            IfStatement {
                condition,
                then_branch,
                else_if_branches,
                else_branch,
            } => self.collect_uv_if_statement(
                uv_id,
                condition,
                then_branch,
                else_if_branches,
                else_branch,
                info,
            )?,
            WhileLoop { condition, body } => self.collect_uv_while_loop(uv_id, condition, body, info)?,
            ForLoop {
                initializer,
                condition,
                increment,
                body,
            } => self.collect_uv_for_loop(uv_id, initializer, condition, increment, body, info)?,
            Return(opt_expr) => self.collect_uv_return(uv_id, opt_expr, info)?,
            Function { .. } => self.collect_uv_function(uv_id, expr, expr.span, info)?,
            FunctionPointer { params, return_type } => {
                self.collect_uv_function_pointer(uv_id, params, return_type, expr.span, info)?
            }
            FunctionParameter { .. } => self.collect_uv_function_parameter(uv_id, expr, expr.span, info)?,
            StructLiteral { name, .. } => {
                self.collect_uv_struct_literal(uv_id, expr.scope_id.unwrap(), name, expr.span, info)?
            }
            AssociatedConstant { .. } => self.collect_uv_associated_const(uv_id, expr, expr.span, info)?,
            SelfValue => self.collect_uv_self_value(uv_id, expr.scope_id.unwrap(), expr.span, info)?,
            SelfType(reference_kind) => {
                self.collect_uv_self_type(uv_id, expr.scope_id.unwrap(), *reference_kind, expr.span, info)?
            }
            FieldAccess { left, right } => self.collect_uv_field_access(uv_id, left, right, info)?,
            FunctionCall { function, arguments } => {
                self.collect_uv_function_call(uv_id, function, arguments, expr.span, info)?
            }
            TypeReference {
                type_name,
                generic_types,
                reference_kind,
            } => self.collect_uv_type_reference(
                uv_id,
                expr.scope_id.unwrap(),
                type_name,
                generic_types,
                reference_kind,
                expr.span,
                info,
            )?,
            StructField { name, type_annotation, .. } => {
                self.collect_uv_struct_field(uv_id, name, type_annotation, info)?
            }
            EnumVariant(_) => self.collect_uv_enum_variant(uv_id, info)?,
            Break | Continue => self.unification_context.register_constraint(
                Constraint::Equality(
                    uv.clone(), 
                    Type::new_base(self.get_primitive_type(PrimitiveKind::Never))
                ),
                info
            ),
            StructDeclaration { .. }
            | EnumDeclaration { .. }
            | TraitDeclaration { .. }
            | ImplDeclaration { .. } => {
                self.unification_context.register_constraint(
                    Constraint::Equality(
                        uv.clone(),
                        Type::new_base(self.get_primitive_type(PrimitiveKind::Void)),
                    ),
                    info,
                );

                for child in expr.children_mut() {
                    self.collect_uvs(child)?;
                }
            }
            _ => {
                for child in expr.children_mut() {
                    self.collect_uvs(child)?;
                }
            }
        }

        expr.type_id = Some(uv.clone());

        Ok(uv)
    }
}