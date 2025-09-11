use std::collections::HashSet;

use indexmap::IndexMap;

use crate::{
    frontend::{semantics::analyzer::{Constraint, ConstraintInfo, PrimitiveKind, ScopeId, ScopeKind, SemanticAnalyzer, Type, TypeSymbolId, TypeSymbolKind, ValueSymbolId, ValueSymbolKind}, syntax::ast::{AstNode, AstNodeKind, BoxedAstNode}},
    utils::{
        error::{BoxedError, Error, ErrorKind},
        kind::{DirectiveKind, Operation, QualifierKind, Span},
    },
};

impl SemanticAnalyzer {
    fn get_type_and_value_tuple(&self, scope_id: ScopeId, name: &str, span: Span) -> Result<(ValueSymbolId, Type), BoxedError> {
        match self.symbol_table.find_value_symbol_from_scope(scope_id, name) {
            Some(value_symbol) => match value_symbol.type_id.clone() {
                Some(type_id) => Ok((value_symbol.id, type_id)),
                None => Err(self.create_error(ErrorKind::UnresolvedType(name.to_string()), span, &[span])),
            },
            None => Err(self.create_error(ErrorKind::UnknownIdentifier(name.to_string()), span, &[span])),
        }
    }

    fn get_type_from_type_name(&self, scope_id: ScopeId, name: &str, span: Span) -> Result<Type, BoxedError> {
        let type_symbol = self
            .symbol_table
            .find_type_symbol_from_scope(scope_id, name)
            .ok_or_else(|| self.create_error(ErrorKind::UnknownIdentifier(name.to_string()), span, &[span]))?;

        if let TypeSymbolKind::TypeAlias((_, Some(ty))) = &type_symbol.kind {
            return Ok(ty.clone());
        }

        Ok(Type::from_no_args(type_symbol.id))
    }

    fn collect_uv_unary_operation(
        &mut self,
        uv_id: TypeSymbolId,
        operator: &mut Operation,
        operand: &mut BoxedAstNode,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let uv_type = self.collect_uvs(operand)?;
        let result_uv = Type::from_no_args(uv_id);

        if let Some((trait_name, _)) = operator.to_trait_data() {
            self.unification_context.register_constraint(
                Constraint::Operation(
                    result_uv,
                    Type::from_no_args(self.trait_registry.get_default_trait(&trait_name)),
                    uv_type,
                    None,
                    *operator
                ),
                info,
            );
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
        let result_uv = Type::from_no_args(uv_id);

        match operator.to_trait_data() {
            Some((trait_name, _)) => {
                self.unification_context.register_constraint(
                    Constraint::Operation(
                        result_uv,
                        Type {
                            symbol: self.trait_registry.get_default_trait(&trait_name),
                            args: vec![right_type.clone()],
                        },
                        left_type,
                        Some(right_type),
                        *operator
                    ),
                    info,
                );
            }
            None => match operator {
                Operation::Assign => {
                    self.unification_context.register_constraint(Constraint::Equality(left_type, right_type), info);
                    self.unification_context.register_constraint(
                        Constraint::Equality(
                            result_uv,
                            Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void)),
                        ),
                        info,
                    );
                }
                _ => unreachable!(),
            },
        }

        Ok(())
    }

    fn collect_uv_type_cast(
        &mut self,
        uv_id: TypeSymbolId,
        expression: &mut BoxedAstNode,
        target_type_node: &mut BoxedAstNode,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let source_type = self.collect_uvs(expression)?;
        let target_type = self.collect_uvs(target_type_node)?;

        self.unification_context.register_constraint(
            Constraint::Equality(Type::from_no_args(uv_id), target_type.clone()),
            info,
        );

        self.unification_context.register_constraint(
            Constraint::Cast(source_type, target_type),
            info,
        );

        Ok(())
    }

    fn collect_uv_conditional_operation(
        &mut self,
        uv_id: TypeSymbolId,
        left: &mut BoxedAstNode,
        right: &mut BoxedAstNode,
        operator: &mut Operation,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let left_type = self.collect_uvs(left)?;
        let right_type = self.collect_uvs(right)?;
        let result_uv = Type::from_no_args(uv_id);

        match *operator {
            Operation::And | Operation::Or => {
                let bool_type = Type::from_no_args(self.get_primitive_type(PrimitiveKind::Bool));

                self.unification_context.register_constraint(Constraint::Equality(left_type, bool_type.clone()), info);
                self.unification_context.register_constraint(Constraint::Equality(right_type, bool_type.clone()), info);

                self.unification_context.register_constraint(Constraint::Equality(result_uv, bool_type), info);
            }
            _ => {
                let (trait_name, _) = operator.to_trait_data().unwrap();

                self.unification_context.register_constraint(
                    Constraint::Operation(
                        result_uv,
                        Type {
                            symbol: self.trait_registry.get_default_trait(&trait_name),
                            args: vec![right_type.clone()],
                        },
                        left_type,
                        Some(right_type),
                        *operator,
                    ),
                    info,
                );
            }
        }

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
                Type::from_no_args(uv_id),
                Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void)),
            ),
            info,
        );

        let init_type = self.collect_uvs(initializer)?;

        let symbol_uv = self
            .unification_context
            .generate_uv_type(&mut self.symbol_table, span);

        if let Some(annot) = type_annotation {
            let annot_type = self.collect_uvs(annot)?;

            self.unification_context.register_constraint(Constraint::Equality(init_type, annot_type.clone()), info);
            self.unification_context.register_constraint(Constraint::NonVoidEquality(symbol_uv.clone(), annot_type), info);
        } else {
            self.unification_context.register_constraint(Constraint::NonVoidEquality(symbol_uv.clone(), init_type), info);
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
        expr: &mut AstNode,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let AstNodeKind::Block(statements) = &mut expr.kind else { unreachable!(); };

        let mut last_type = None;

        for stmt in statements.iter_mut() {
            last_type = Some(self.collect_uvs(stmt)?);
        }

        if let Some(last_stmt) = statements.last() && !matches!(last_stmt.kind, AstNodeKind::ExpressionStatement(_)) {
            expr.value_id = last_stmt.value_id;
        }

        if let Some(last_type) = last_type {
            self.unification_context.register_constraint(
                Constraint::Equality(Type::from_no_args(uv_id), last_type),
                info,
            );
        } else {
            self.unification_context.register_constraint(
                Constraint::Equality(
                    Type::from_no_args(uv_id),
                    Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void)),
                ),
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
        let bool_type = Type::from_no_args(self.get_primitive_type(PrimitiveKind::Bool));
        self.unification_context
            .register_constraint(Constraint::Equality(cond_type, bool_type.clone()), info);

        let result_uv = Type::from_no_args(uv_id);

        let then_type = self.collect_uvs(then_branch)?;

        for (elif_cond, elif_branch) in else_if_branches.iter_mut() {
            let elif_cond_type = self.collect_uvs(elif_cond)?;
            self.unification_context
                .register_constraint(Constraint::Equality(elif_cond_type, bool_type.clone()), info);

            let elif_type = self.collect_uvs(elif_branch)?;
            self.unification_context.register_constraint(
                Constraint::Equality(then_type.clone(), elif_type),
                info,
            );
        }

        if let Some(else_node) = else_branch {
            let else_type = self.collect_uvs(else_node)?;
            self.unification_context.register_constraint(
                Constraint::Equality(then_type.clone(), else_type),
                info,
            );

            self.unification_context.register_constraint(
                Constraint::Equality(result_uv, then_type),
                info,
            );
        } else {
            let void_type = Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void));
            
            self.unification_context.register_constraint(
                Constraint::Equality(then_type, void_type.clone()),
                info,
            );

            self.unification_context.register_constraint(
                Constraint::Equality(result_uv, void_type),
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
        self.uv_collection_ctx.in_loop = true;

        let cond_type = self.collect_uvs(condition)?;
        let bool_type = Type::from_no_args(self.get_primitive_type(PrimitiveKind::Bool));
        self.unification_context
            .register_constraint(Constraint::Equality(cond_type, bool_type), info);

        self.collect_uvs(body)?;

        let return_type = if condition.kind == AstNodeKind::BooleanLiteral(true) {
            Type::from_no_args(self.get_primitive_type(PrimitiveKind::Never))
        } else {
            Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void))
        };

        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::from_no_args(uv_id),
                return_type,
            ),
            info,
        );

        self.uv_collection_ctx.in_loop = false;

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
        self.uv_collection_ctx.in_loop = true;

        if let Some(init) = initializer {
            self.collect_uvs(init)?;
        }

        let is_infinite = if let Some(cond) = condition {
            let cond_type = self.collect_uvs(cond)?;
            let bool_type = Type::from_no_args(self.get_primitive_type(PrimitiveKind::Bool));
            self.unification_context
                .register_constraint(Constraint::Equality(cond_type, bool_type), info);
            false
        } else {
            true
        };

        if let Some(inc) = increment {
            self.collect_uvs(inc)?;
        }

        self.collect_uvs(body)?;

        let return_type = if is_infinite {
            Type::from_no_args(self.get_primitive_type(PrimitiveKind::Never))
        } else {
            Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void))
        };

        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::from_no_args(uv_id),
                return_type,
            ),
            info,
        );

        self.uv_collection_ctx.in_loop = false;

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
                Type::from_no_args(uv_id),
                Type::from_no_args(self.get_primitive_type(PrimitiveKind::Never)),
            ),
            info,
        );

        let Some(expected_return_type) = self.uv_collection_ctx.current_return_type.clone() else {
             return Err(self.create_error(ErrorKind::InvalidReturn, info.span, &[info.span]));
        };

        let value_type = if let Some(expr) = opt_expr {
            self.collect_uvs(expr)?
        } else {
            Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void))
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
        if let Some(value_id) = node.value_id {
            self.uv_collection_ctx.current_function_stack.push((value_id, vec![]));
        }

        let AstNodeKind::Function {
            name,
            generic_parameters,
            parameters,
            return_type,
            body,
            instance,
            ..
        } = &mut node.kind
        else {
            unreachable!();
        };

        let is_declaration = !name.is_empty();

        let symbol_uv = if node.value_id.is_some() {
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
            .map(|p| self.collect_uvs(p).map(|t| t.symbol))
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
            Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void))
        };

        let old_return_type = self.uv_collection_ctx.current_return_type.clone();
        self.uv_collection_ctx.current_return_type = Some(return_type_val.clone());

        if let Some(body_node) = body {
            let body_type = self.collect_uvs(body_node)?;

            if let Some(returned_val_id) = body_node.value_id && let Some(fn_val_id) = node.value_id {
                let fn_symbol = self.symbol_table.get_value_symbol_mut(fn_val_id).unwrap();
                fn_symbol.statically_known_return_value_id = Some(returned_val_id);
            }

            let span = if let AstNodeKind::Block(stmts) = &body_node.kind {
                stmts.last().map_or(body_node.span, |s| s.span)
            } else {
                body_node.span
            };

            self.unification_context.register_constraint(
                Constraint::Equality(body_type, return_type_val.clone()),
                ConstraintInfo {
                    span,
                    scope_id: body_node.scope_id.unwrap(),
                },
            );
        }

        self.uv_collection_ctx.current_return_type = old_return_type;
        if let Some(value_id) = node.value_id {
            let (_, spans) = self.uv_collection_ctx.current_function_stack.pop().unwrap();
            let ValueSymbolKind::Function(_, captured_items) = &self.symbol_table.get_value_symbol(value_id).as_ref().unwrap().kind else {
                unreachable!();
            };

            if !captured_items.is_empty() && !generic_parameters.is_empty() {
                return Err(self.create_error(
                    ErrorKind::ClosureWithGenerics(name.clone()),
                    span,
                    &{
                        let mut all_spans = generic_parameters.iter().map(|param| param.span).collect::<Vec<_>>();
                        all_spans.extend(spans);
                        all_spans
                    },
                ));
            }

        }

        let fn_sig_type_name = if is_declaration {
            format!("#fn_sig_{}_{}", name, node.id)
        } else {
            format!("#fn_sig_{}", uv_id)
        };

        let fn_sig_type_id = self.symbol_table.add_type_symbol(
            &fn_sig_type_name,
            TypeSymbolKind::FunctionSignature {
                params: param_types,
                return_type: return_type_val,
                instance: *instance
            },
            generic_types,
            QualifierKind::Private,
            Some(span),
        )?;

        let fn_sig_type = Type::from_no_args(fn_sig_type_id);

        if is_declaration {
            self.unification_context.register_constraint(
                Constraint::Equality(
                    Type::from_no_args(uv_id),
                    Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void)),
                ),
                info,
            );

            self.unification_context
                .register_constraint(Constraint::Equality(symbol_uv.unwrap(), fn_sig_type), info);
        } else {
            self.unification_context
                .register_constraint(Constraint::Equality(Type::from_no_args(uv_id), fn_sig_type.clone()), info);
            
            if let Some(uv) = symbol_uv {
                self.unification_context.register_constraint(Constraint::Equality(uv, fn_sig_type), info);
            }
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
            ..
        } = &mut node.kind
        else {
            unreachable!();
        };

        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::from_no_args(uv_id),
                Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void)),
            ),
            info,
        );

        let annotation_type = self.collect_uvs(type_annotation)?;

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
            Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void))
        };

        let fn_ptr_sig_id = self.symbol_table.add_type_symbol(
            &format!("#fn_ptr_sig_{}", uv_id),
            TypeSymbolKind::FunctionSignature {
                params: param_types,
                return_type,
                instance: false
            },
            vec![],
            QualifierKind::Private,
            Some(span),
        )?;

        self.unification_context.register_constraint(
            Constraint::Equality(Type::from_no_args(uv_id), Type::from_no_args(fn_ptr_sig_id)),
            info,
        );

        Ok(())
    }

    fn collect_uv_struct_literal(
        &mut self,
        uv_id: TypeSymbolId,
        scope_id: ScopeId,
        name: &str,
        fields: &mut IndexMap<String, AstNode>,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let symbol = self.symbol_table.find_type_symbol_from_scope(scope_id, name)
            .ok_or_else(|| self.create_error(ErrorKind::UnknownIdentifier(name.to_owned()), span, &[span]))?
            .clone();

        let (struct_symbol, struct_scope_id) = match &symbol.kind {
            TypeSymbolKind::Struct((id, _)) => (symbol.clone(), *id),
            TypeSymbolKind::TypeAlias((_, Some(ty))) => {
                let base_symbol_id = ty.symbol;
                let base_symbol_ref = self.symbol_table.get_type_symbol(base_symbol_id).unwrap();
                if let TypeSymbolKind::Struct((id, _)) = &base_symbol_ref.kind {
                    (base_symbol_ref.clone(), *id)
                } else {
                    return Err(self.create_error(ErrorKind::InvalidStructLiteral(name.to_string()), span, &[span]));
                }
            },
            _ => return Err(self.create_error(ErrorKind::InvalidStructLiteral(name.to_string()), span, &[span]))
        };
        
        let literal_field_names: HashSet<String> = fields.keys().cloned().collect();
        let declared_field_names: HashSet<String> = self.symbol_table.get_scope(struct_scope_id).unwrap()
            .values.values()
            .map(|id| self.symbol_table.get_value_name(self.symbol_table.get_value_symbol(*id).unwrap().name_id).to_string())
            .collect();
        
        let missing_fields: Vec<String> = declared_field_names
            .difference(&literal_field_names)
            .cloned().collect();

        let extra_fields: Vec<String> = literal_field_names
            .difference(&declared_field_names)
            .cloned().collect();

        if !missing_fields.is_empty() || !extra_fields.is_empty() {
            return Err(self.create_error(
                ErrorKind::MismatchedStructFields {
                    struct_name: name.to_string(),
                    missing_fields,
                    extra_fields,
                },
                span,
                &[span],
            ));
        }

        let generic_params = struct_symbol.generic_parameters.clone();

        let generic_uvs: IndexMap<TypeSymbolId, Type> = generic_params
            .iter()
            .map(|&param_id| {
                let uv_type = self.unification_context.generate_uv_type(&mut self.symbol_table, span);
                (param_id, uv_type)
            })
            .collect();

        let struct_type = Type {
            symbol: struct_symbol.id,
            args: generic_uvs.values().cloned().collect()
        };

        self.unification_context.register_constraint(
            Constraint::Equality(Type::from_no_args(uv_id), struct_type),
            info,
        );

        for (field_name, field_expr) in fields.iter_mut() {
            let expr_uv = self.collect_uvs(field_expr)?;

            let field_type = self.symbol_table
                .find_value_symbol_in_scope(field_name, struct_scope_id)
                .ok_or_else(|| self.create_error(
                    ErrorKind::InvalidField(name.to_string(), field_name.to_string()), 
                    field_expr.span,
                    &[field_expr.span, span]
                ))?
                .type_id.clone().unwrap();
            
            if let Some(ty) = generic_uvs.get(&field_type.symbol) {
                self.unification_context.register_constraint(
                    Constraint::Equality(expr_uv, ty.clone()),
                    info
                );
            } else {
                self.unification_context.register_constraint(
                    Constraint::Equality(expr_uv, field_type),
                    info
                );
            }
        }

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
                Type::from_no_args(uv_id),
                Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void)),
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

    fn collect_uv_trait_const(
        &mut self,
        uv_id: TypeSymbolId,
        node: &mut AstNode,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::from_no_args(uv_id),
                Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void)),
            ),
            info,
        );
        
        let AstNodeKind::TraitConstant {
            type_annotation,
            ..
        } = &mut node.kind
        else {
            unreachable!();
        };

        let annot_type = self.collect_uvs(type_annotation)?;

        let symbol_uv = self.unification_context.generate_uv_type(&mut self.symbol_table, span);
        self.unification_context.register_constraint(Constraint::Equality(symbol_uv.clone(), annot_type), info);
        self.symbol_table.get_value_symbol_mut(node.value_id.unwrap()).unwrap().type_id = Some(symbol_uv.clone());

        Ok(())
    }

    fn collect_uv_type_reference(
        &mut self,
        uv_id: TypeSymbolId,
        scope_id: ScopeId,
        type_name: &str,
        generic_types: &mut [AstNode],
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let symbol = self.symbol_table.find_type_symbol_from_scope(scope_id, type_name)
            .ok_or_else(|| {
                self.create_error(ErrorKind::UnknownIdentifier(type_name.to_owned()), span, &[span])
            })?.id;

        let symbol_params = &self.symbol_table.get_type_symbol(symbol).unwrap().generic_parameters;
        
        if symbol_params.len() != generic_types.len() {
            return Err(self.create_error(
                ErrorKind::InvalidTypeReference(type_name.to_string(), generic_types.len(), symbol_params.len()),
                span,
                &[span]
            ))
        }

        let args: Vec<Type> = generic_types
            .iter_mut()
            .map(|generic_type| self.collect_uvs(generic_type))
            .collect::<Result<Vec<_>, _>>()?;

        let base_symbol = Type { symbol, args };

        self.unification_context.register_constraint(
            Constraint::Equality(Type::from_no_args(uv_id), base_symbol),
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
                Type::from_no_args(uv_id),
                Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void)),
            ),
            info,
        );

        let value_node = if let AstNodeKind::AssociatedType { value, .. } = &mut node.kind {
            value
        } else if let AstNodeKind::TypeDeclaration { value, .. } = &mut node.kind {
            value
        } else {
            unreachable!();
        };
 
        // Ensure RHS is not an enum variant.
        if let AstNodeKind::FieldAccess { left, right } = &value_node.kind
            && let Some(left_name) = left.get_name()
            && let Some(symbol) = self.symbol_table.find_type_symbol_from_scope(node.scope_id.unwrap(), &left_name)
            && let TypeSymbolKind::Enum((scope_id, _)) = symbol.kind
            && let Some(right_name) = right.get_name()
            && let Some(variant_symbol) = self.symbol_table.find_value_symbol_in_scope(&right_name, scope_id)
            && matches!(variant_symbol.kind, ValueSymbolKind::EnumVariant)
        {
            return Err(self.create_error(ErrorKind::ExpectedType, value_node.span, &[value_node.span]));
        }
         
        let initializer_type = self.collect_uvs(value_node)?;

        let symbol_uv = self
            .unification_context
            .generate_uv_type(&mut self.symbol_table, span);

        self.unification_context
            .register_constraint(Constraint::Equality(symbol_uv.clone(), initializer_type), info);

        let type_symbol = self
            .symbol_table
            .get_type_symbol_mut(node.type_id.as_mut().unwrap().symbol)
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
                        ErrorKind::InvalidSelf("outside of a function"),
                        span,
                        &[span],
                    ))
                }
            }
        }

        let impl_scope = match function_scope.parent {
            Some(parent_id) => self.symbol_table.get_scope(parent_id).unwrap(),
            None => {
                return Err(self.create_error(
                    ErrorKind::InvalidSelf("outside of an impl block"),
                    span,
                    &[span],
                ))
            }
        };

        if impl_scope.kind != ScopeKind::Impl {
            return Err(self.create_error(ErrorKind::InvalidSelf("outside of an impl block"), span, &[span]));
        }

        let TypeSymbolKind::TypeAlias((_, Some(self_type))) = &self
            .symbol_table
            .find_type_symbol_in_scope("Self", impl_scope.id)
            .ok_or_else(|| self.create_error(ErrorKind::SelfOutsideImpl, span, &[span]))?
            .kind
        else {
            unreachable!();
        };

        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::from_no_args(uv_id),
                self_type.clone()
            ),
            info,
        );

        Ok(())
    }

    fn collect_uv_self_type(
        &mut self,
        uv_id: TypeSymbolId,
        scope_id: ScopeId,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let self_symbol = self
            .symbol_table
            .find_type_symbol_from_scope(scope_id, "Self")
            .ok_or_else(|| self.create_error(ErrorKind::SelfOutsideImpl, span, &[span]))?;

        self.unification_context.register_constraint(
            Constraint::Equality(Type::from_no_args(uv_id), Type::from_no_args(self_symbol.id)),
            info,
        );

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

        match &mut left.kind {
            AstNodeKind::PathQualifier { ty, tr } => {
                let type_val = self.collect_uvs(ty)?;
                left.type_id = Some(type_val.clone());

                let trait_val = if let Some(trait_node) = tr {
                    Some(self.collect_uvs(trait_node)?)
                } else {
                    None
                };
                
                self.unification_context.register_constraint(Constraint::FullyQualifiedAccess(
                    Type::from_no_args(uv_id),
                    type_val,
                    trait_val,
                    right_name,
                ), info);
                
                return Ok(());
            },
            AstNodeKind::Identifier(left_name) => {
                if left_name == "Self" {
                    let mut scope_id = Some(info.scope_id);

                    while let Some(id) = scope_id {
                        let scope = self.symbol_table.get_scope(id).unwrap();
                        if scope.kind == ScopeKind::Impl {
                            if let Some(trait_id) = scope.trait_id {
                                let self_type = self.get_type_from_type_name(info.scope_id, "Self", left.span)?;
                                let trait_type = Type::from_no_args(trait_id);

                                left.type_id = Some(self_type.clone());

                                self.unification_context.register_constraint(
                                    Constraint::FullyQualifiedAccess(
                                        Type::from_no_args(uv_id),
                                        self_type,
                                        Some(trait_type),
                                        right_name,
                                    ),
                                    info,
                                );

                                return Ok(());
                            }

                            break;
                        }

                        scope_id = scope.parent;
                    }
                }

                if self.symbol_table.find_value_symbol_from_scope(left.scope_id.unwrap(), left_name).is_some() {
                    let left_type = self.collect_uvs(left)?;
                    
                    self.unification_context.register_constraint(
                        Constraint::InstanceMemberAccess(Type::from_no_args(uv_id), left_type, right_name),
                        info,
                    );

                    return Ok(());
                }

                if let Some(type_symbol) = self.symbol_table.find_type_symbol_from_scope(left.scope_id.unwrap(), left_name) {
                    let static_type = Type::from_no_args(type_symbol.id);
                    left.type_id = Some(static_type.clone());

                    self.unification_context.register_constraint(
                        Constraint::StaticMemberAccess(Type::from_no_args(uv_id), static_type, right_name),
                        info,
                    );

                    return Ok(());
                }
            },
            _ => {}
        }

        let left_type = self.collect_uvs(left)?;

        self.unification_context.register_constraint(
            Constraint::InstanceMemberAccess(Type::from_no_args(uv_id), left_type, right_name),
            info,
        );

        Ok(())
    }

    fn collect_uv_function_call(
        &mut self,
        uv_id: TypeSymbolId,
        node: &mut AstNode,
        span: Span,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        let AstNodeKind::FunctionCall { function: function_node, arguments, .. } = &mut node.kind else { unreachable!(); };

        let function_type = self.collect_uvs(function_node)?;

        let argument_types: Vec<Type> = arguments
            .iter_mut()
            .map(|arg| self.collect_uvs(arg))
            .collect::<Result<_, _>>()?;

        let return_uv_type = self
            .unification_context
            .generate_uv_type(&mut self.symbol_table, span);

        let mut is_method_call = false;
        if let AstNodeKind::FieldAccess { left, .. } = &mut function_node.kind {
            let is_static_path = match &left.kind {
                AstNodeKind::Identifier(name) => self
                    .symbol_table
                    .find_type_symbol_from_scope(left.scope_id.unwrap(), name)
                    .is_some(),
                AstNodeKind::PathQualifier { .. } => true,
                _ => false,
            };

            if !is_static_path {
                is_method_call = true;

                let instance_type = left
                    .type_id
                    .clone()
                    .expect("instance in method call should have a type");

                self.unification_context.register_constraint(
                    Constraint::MethodCall(
                        instance_type,
                        function_type.clone(),
                        argument_types.clone(),
                        return_uv_type.clone(),
                    ),
                    info,
                );
            }
        }
        
        if !is_method_call {
            self.unification_context.register_constraint(
                Constraint::FunctionSignature(function_type, argument_types, return_uv_type.clone()),
                info,
            );
        }

        self.unification_context.register_constraint(
            Constraint::Equality(Type::from_no_args(uv_id), return_uv_type),
            info,
        );

        if let Some(callee_id) = function_node.value_id {
            let callee_sym = self.symbol_table.get_value_symbol(callee_id).unwrap();
            if let Some(returned_id) = callee_sym.statically_known_return_value_id {
                node.value_id = Some(returned_id);
            }
        }

        Ok(())
    }

    fn collect_uv_struct_field(
        &mut self,
        uv_id: TypeSymbolId,
        info: ConstraintInfo,
    ) -> Result<(), BoxedError> {
        self.unification_context.register_constraint(
            Constraint::Equality(
                Type::from_no_args(uv_id),
                Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void)),
            ),
            info,
        );

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
                if let TypeSymbolKind::Enum((scope, _)) = symbol.kind && scope == info.scope_id {
                    return Some(symbol);
                }
                
                None
            })
            .unwrap();

        let enum_type = Type::from_no_args(enum_type_symbol.id);

        self.unification_context.register_constraint(
            Constraint::Equality(Type::from_no_args(uv_id), enum_type.clone()),
            info,
        );

        Ok(())
    }

    fn collect_uv_compiler_directive(&mut self, uv_id: TypeSymbolId, directive: DirectiveKind, nodes: &mut [AstNode], info: ConstraintInfo) -> Result<(), BoxedError> {
        let ty = match directive {
            DirectiveKind::IsRefcounted => {
                self.collect_uvs(&mut nodes[0])?;
                Type::from_no_args(self.get_primitive_type(PrimitiveKind::Bool))
            },
        };

        self.unification_context.register_constraint(Constraint::Equality(Type::from_no_args(uv_id), ty), info);

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

        if matches!(expr.kind, AstNodeKind::ImportStatement { .. } | AstNodeKind::ExportStatement { .. }) {
            return Ok(Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void)));
        }

        let uv = self.unification_context.generate_uv_type(&mut self.symbol_table, expr.span);
        let uv_id = uv.symbol;

        let info = ConstraintInfo {
            span: expr.span,
            scope_id: expr.scope_id.unwrap_or_else(|| panic!("scope_id should exist on node, especially this one: {} \n{:?}", expr, expr)),
        };

        match &mut expr.kind {
            IntegerLiteral(_) => self.unification_context.register_constraint(
                Constraint::Equality(
                    uv.clone(),
                    Type::from_no_args(self.get_primitive_type(PrimitiveKind::Int)),
                ),
                info,
            ),
            FloatLiteral(_) => self.unification_context.register_constraint(
                Constraint::Equality(
                    uv.clone(),
                    Type::from_no_args(self.get_primitive_type(PrimitiveKind::Float)),
                ),
                info,
            ),
            BooleanLiteral(_) => self.unification_context.register_constraint(
                Constraint::Equality(
                    uv.clone(),
                    Type::from_no_args(self.get_primitive_type(PrimitiveKind::Bool)),
                ),
                info,
            ),
            StringLiteral(_) => self.unification_context.register_constraint(
                Constraint::Equality(
                    uv.clone(),
                    Type::from_no_args(self.get_primitive_type(PrimitiveKind::StaticString)),
                ),
                info,
            ),
            CharLiteral(_) => self.unification_context.register_constraint(
                Constraint::Equality(
                    uv.clone(),
                    Type::from_no_args(self.get_primitive_type(PrimitiveKind::Char)),
                ),
                info,
            ),
            Identifier(name) => {
                let (value_id, ty) = self.get_type_and_value_tuple(expr.scope_id.unwrap(), name, expr.span)?;
                
                let mut captured = false;
                if let Some(&(current_fn_id, _)) = self.uv_collection_ctx.current_function_stack.last() {
                    let accessed_symbol = self.symbol_table.get_value_symbol(value_id).unwrap();
                    let function_symbol = self.symbol_table.get_value_symbol(current_fn_id).unwrap();
                
                    if let ValueSymbolKind::Function(function_scope_id, _) = function_symbol.kind
                        && !self.is_ancestor_of(function_scope_id, accessed_symbol.scope_id)
                        && accessed_symbol.kind == ValueSymbolKind::Variable
                        && accessed_symbol.mutable
                    {
                        let function_symbol_mut = self.symbol_table.get_value_symbol_mut(current_fn_id).unwrap();
                        if let ValueSymbolKind::Function(_, captured_items) = &mut function_symbol_mut.kind {
                            captured_items.insert(value_id);
                            captured = true;
                        }
                    }
                }

                if captured {
                    let Some((_, spans)) = self.uv_collection_ctx.current_function_stack.last_mut() else { unreachable!(); };
                    spans.push(expr.span);
                }

                expr.value_id = Some(value_id);
                self.unification_context.register_constraint(Constraint::Equality(uv.clone(), ty), info)
            },

            UnaryOperation { operator, operand } => {
                self.collect_uv_unary_operation(uv_id, operator, operand, info)?
            }
            BinaryOperation {
                left,
                right,
                operator,
            } => self.collect_uv_binary_operation(uv_id, left, right, operator, info)?,
            TypeCast {
                expr,
                target_type,
            } => self.collect_uv_type_cast(uv_id, expr, target_type, info)?,
            ConditionalOperation { left, right, operator, .. } => {
                self.collect_uv_conditional_operation(uv_id, left, right, operator, info)?
            }
            VariableDeclaration { .. } => {
                self.collect_uv_variable_declaration(uv_id, expr, expr.span, info)?
            }
            Block(_) => self.collect_uv_block(uv_id, expr, info)?,
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
            StructLiteral { name, fields, .. } => {
                self.collect_uv_struct_literal(uv_id, expr.scope_id.unwrap(), name, fields, expr.span, info)?
            }
            AssociatedConstant { .. } => self.collect_uv_associated_const(uv_id, expr, expr.span, info)?,
            TraitConstant { .. } => self.collect_uv_trait_const(uv_id, expr, expr.span, info)?,
            SelfExpr => {
                if let Some(symbol) = self.symbol_table.find_value_symbol_from_scope(info.scope_id, "self") {
                    expr.value_id = Some(symbol.id);
                }
                
                self.collect_uv_self_value(uv_id, expr.scope_id.unwrap(), expr.span, info)?
            },
            SelfType => self.collect_uv_self_type(uv_id, expr.scope_id.unwrap(), expr.span, info)?,
            FieldAccess { left, right } => self.collect_uv_field_access(uv_id, left, right, info)?,
            FunctionCall { .. } => self.collect_uv_function_call(uv_id, expr, expr.span, info)?,
            PathQualifier { .. } => {
                return Err(self.create_error(ErrorKind::InvalidPathQualifier, expr.span, &[expr.span]))
            },
            TypeReference {
                type_name,
                generic_types,
                ..
            } => self.collect_uv_type_reference(
                uv_id,
                expr.scope_id.unwrap(),
                type_name,
                generic_types,
                expr.span,
                info,
            )?,
            AssociatedType { .. } | TypeDeclaration { .. } => self.collect_uv_type_declaration(uv_id, expr, expr.span, info)?,
            StructField { .. } => {
                self.collect_uv_struct_field(uv_id, info)?
            }
            EnumVariant(_) => self.collect_uv_enum_variant(uv_id, info)?,
            Break | Continue => {
                if self.uv_collection_ctx.in_loop {
                    self.unification_context.register_constraint(
                        Constraint::Equality(
                            uv.clone(), 
                            Type::from_no_args(self.get_primitive_type(PrimitiveKind::Never))
                        ),
                        info
                    )
                } else {
                    return Err(self.create_error(ErrorKind::OutsideOfLoop, expr.span, &[expr.span]));
                }
            },
            StructDeclaration { .. }
            | EnumDeclaration { .. }
            | TraitDeclaration { .. }
            | ImplDeclaration { .. }
            | TraitType(_)
            | GenericParameter { .. } => {
                self.unification_context.register_constraint(
                    Constraint::Equality(
                        uv.clone(),
                        Type::from_no_args(self.get_primitive_type(PrimitiveKind::Void)),
                    ),
                    info,
                );

                for child in expr.children_mut() {
                    self.collect_uvs(child)?;
                }
            },
            ExpressionStatement(inner_expr) => {
                let inner_type = self.collect_uvs(inner_expr)?;
                let result_type = uv.clone();

                self.unification_context.register_constraint(
                    Constraint::ExpressionStatement(inner_type, result_type),
                    info,
                );
            },
            SizeofExpression(ty_node) => {
                self.collect_uvs(ty_node)?;
                self.unification_context.register_constraint(
                    Constraint::Equality(
                        uv.clone(),
                        Type::from_no_args(self.get_primitive_type(PrimitiveKind::Int)),
                    ),
                    info,
                );
            },
            CompilerDirective { directive, nodes } => self.collect_uv_compiler_directive(uv_id, *directive, nodes, info)?,
            ImportStatement { .. } | ExportStatement { .. } | Program(_) => unreachable!()
        }

        expr.type_id = Some(uv.clone());

        Ok(uv)
    }
}