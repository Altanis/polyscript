use crate::{frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, middle::semantic_analyzer::{Constraint, PrimitiveKind, SemanticAnalyzer, Type, TypeSymbol, TypeSymbolId, TypeSymbolKind, ValueSymbolKind}, utils::{error::{BoxedError, Error, ErrorKind}, kind::{Operation, QualifierKind, Span}}};

impl SemanticAnalyzer {
    fn get_primitive_type(&self, primitive: PrimitiveKind) -> TypeSymbolId {
        self.builtin_types[primitive as usize]
    }

    fn get_type_from_identifier(&self, name: &str, span: Span) -> Result<Type, BoxedError> {
        match self.symbol_table.find_value_symbol(name) {
            Some(value_symbol) => {
                match value_symbol.type_id.clone() {
                    Some(type_id) => Ok(type_id),
                    None => Err(self.create_error(ErrorKind::UnresolvedType(name.to_string()), span, &[span]))
                }
            },
            None => Err(self.create_error(ErrorKind::UnknownIdentifier(name.to_string()), span, &[span]))
        }
    }

    // fn find_impl_member_type(&mut self, name: String) -> Result<Type, BoxedError> {

    // }

    // fn resolve_static_member_access(&mut self, type_symbol: &TypeSymbol, right: &mut BoxedAstNode) -> Result<Type, BoxedError> {
    //     match type_symbol.kind {
    //         TypeSymbolKind::Enum((scope, impls)) => {

    //         }
    //     }
    // }

    // fn resolve_instance_member_access(&mut self, lhs_type: &Type, right: &mut BoxedAstNode) -> Result<Type, BoxedError> {
        
    // }
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

        let unification_variable = self.unification_context.generate_uv_type(&mut self.symbol_table, expr.span);
        let uv_id = unification_variable.get_base_symbol();

        match &mut expr.kind {
            IntegerLiteral(_) => self.unification_context.register_constraint(Constraint::Equality(
                uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Int))
            )),
            FloatLiteral(_) => self.unification_context.register_constraint(Constraint::Equality(
                uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Float))
            )),
            BooleanLiteral(_) => self.unification_context.register_constraint(Constraint::Equality(
                uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Bool))
            )),
            StringLiteral(_) => self.unification_context.register_constraint(Constraint::Equality(
                uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::String))
            )),
            CharLiteral(_) => self.unification_context.register_constraint(Constraint::Equality(
                uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Char))
            )),
            Identifier(string) => self.unification_context.register_constraint(Constraint::Equality(
                uv_id, Type::new_base(self.get_type_from_identifier(string, expr.span)?.get_base_symbol())
            )),
            UnaryOperation { operator, operand } => {
                let uv_type = self.collect_uvs(operand)?;
                match operator.to_trait_data() {
                    Some((trait_name, _)) => {
                        self.unification_context.register_constraint(Constraint::Trait(
                            uv_type.get_base_symbol(), Type::new_base(self.trait_registry.get_default_trait(&trait_name))
                        ));
                    },
                    None => match operator {
                        Operation::Dereference => self.unification_context.register_constraint(Constraint::Equality(
                            uv_type.get_base_symbol(), unification_variable.clone()
                        )),
                        Operation::ImmutableAddressOf => self.unification_context.register_constraint(Constraint::Equality(
                            uv_id, Type::Reference(Box::new(uv_type))
                        )),
                        Operation::MutableAddressOf => self.unification_context.register_constraint(Constraint::Equality(
                            uv_id, Type::MutableReference(Box::new(uv_type))
                        )),
                        _ => unreachable!()
                    }
                }
            },
            BinaryOperation { left, right, operator } => {
                let left_type = self.collect_uvs(left)?;
                let right_type = self.collect_uvs(right)?;

                match operator.to_trait_data() {
                    Some((trait_name, _)) => {
                        self.unification_context.register_constraint(Constraint::Trait(
                            left_type.get_base_symbol(), Type::Base {
                                symbol: self.trait_registry.get_default_trait(&trait_name),
                                args: vec![right_type.clone()]
                            }
                        ));
                    },
                    None => match operator {
                        Operation::Assign => {
                            self.unification_context.register_constraint(Constraint::Equality(
                                left_type.get_base_symbol(), right_type.clone()
                            ));

                            self.unification_context.register_constraint(Constraint::Equality(
                                uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Null))
                            ));
                        },
                        // `FunctionCall` and `FieldAcces` never appear in a BinaryOperation node
                        _ => unreachable!()
                    }
                }
            },
            ConditionalOperation { left, right, .. } => {
                let left_type = self.collect_uvs(left)?;
                let right_type = self.collect_uvs(right)?;

                let bool_type = Type::new_base(self.get_primitive_type(PrimitiveKind::Bool));

                self.unification_context.register_constraint(Constraint::Equality(left_type.get_base_symbol(), bool_type.clone()));
                self.unification_context.register_constraint(Constraint::Equality(right_type.get_base_symbol(), bool_type.clone()));
                self.unification_context.register_constraint(Constraint::Equality(uv_id, bool_type));
            },
            VariableDeclaration { name: _, mutable: _, type_annotation, initializer } => {
                let init_type = if let Some(init) = initializer {
                    Some(self.collect_uvs(init)?)
                } else {
                    None
                };

                if let Some(annot) = type_annotation {
                    let annot_type = self.collect_uvs(annot)?;
                    if let Some(init_type) = init_type {
                        self.unification_context.register_constraint(Constraint::Equality(
                            annot_type.get_base_symbol(), init_type
                        ));
                    }

                    self.unification_context.register_constraint(Constraint::Equality(
                        uv_id, annot_type
                    ));
                } else if let Some(init_type) = init_type {
                    self.unification_context.register_constraint(Constraint::Equality(
                        uv_id, init_type
                    ));
                } else {
                    return Err(self.create_error(ErrorKind::BadVariableDeclaration, expr.span, &[expr.span]));
                }
            },
            Block(statements) => {
                let mut last_type = None;
                for stmt in statements.iter_mut() {
                    last_type = Some(self.collect_uvs(stmt)?);
                }

                if let Some(last_type) = last_type {
                    self.unification_context.register_constraint(Constraint::Equality(
                        uv_id, last_type
                    ));
                }
            },
            IfStatement { condition, then_branch, else_if_branches, else_branch } => {
                let cond_type = self.collect_uvs(condition)?;
                let bool_type = Type::new_base(self.get_primitive_type(PrimitiveKind::Bool));
                self.unification_context.register_constraint(Constraint::Equality(cond_type.get_base_symbol(), bool_type.clone()));
                
                let then_type = self.collect_uvs(then_branch)?;
                let mut branch_types = vec![then_type.clone()];

                for (elif_cond, elif_branch) in else_if_branches.iter_mut() {
                    let elif_cond_type = self.collect_uvs(elif_cond)?;
                    self.unification_context.register_constraint(Constraint::Equality(elif_cond_type.get_base_symbol(), bool_type.clone()));
                    let elif_type = self.collect_uvs(elif_branch)?;
                    branch_types.push(elif_type);
                }

                if let Some(else_node) = else_branch {
                    let else_type = self.collect_uvs(else_node)?;
                    branch_types.push(else_type);
                }

                for branch_type in &branch_types {
                    self.unification_context.register_constraint(Constraint::Equality(
                        uv_id, branch_type.clone()
                    ));
                }
            },
            WhileLoop { condition, body } => {
                let cond_type = self.collect_uvs(condition)?;
                let bool_type = Type::new_base(self.get_primitive_type(PrimitiveKind::Bool));
                self.unification_context.register_constraint(Constraint::Equality(cond_type.get_base_symbol(), bool_type));

                self.collect_uvs(body)?;
                self.unification_context.register_constraint(Constraint::Equality(
                    uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Null))
                ));
            },
            ForLoop { initializer, condition, increment, body } => {
                if let Some(init) = initializer {
                    self.collect_uvs(init)?;
                }

                if let Some(cond) = condition {
                    let cond_type = self.collect_uvs(cond)?;
                    let bool_type = Type::new_base(self.get_primitive_type(PrimitiveKind::Bool));
                    self.unification_context.register_constraint(Constraint::Equality(cond_type.get_base_symbol(), bool_type));
                }

                if let Some(inc) = increment {
                    self.collect_uvs(inc)?;
                }

                self.collect_uvs(body)?;

                self.unification_context.register_constraint(Constraint::Equality(
                    uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Null))
                ));
            },
            Return(opt_expr) => {
                if let Some(expr) = opt_expr {
                    self.collect_uvs(expr)?;
                }

                self.unification_context.register_constraint(Constraint::Equality(
                    uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Null))
                ));
            },
            
            // function stuff

            StructLiteral { name, .. } => {
                let Some(symbol) = self.symbol_table.find_type_symbol(name) else {
                    return Err(self.create_error(ErrorKind::UnknownIdentifier(name.clone()), expr.span, &[expr.span]));
                };

                self.unification_context.register_constraint(Constraint::Equality(
                    uv_id, Type::new_base(symbol.id)
                ));
            },

            
            _ => {
                for child in expr.children_mut() {
                    self.collect_uvs(child)?;
                }
            }
        }

        expr.type_id = Some(unification_variable.clone());
        Ok(unification_variable)
    }
}