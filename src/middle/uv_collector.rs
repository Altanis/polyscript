use crate::{frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, middle::semantic_analyzer::{Constraint, PrimitiveKind, ScopeId, SemanticAnalyzer, Type, TypeSymbolId}, utils::{error::{BoxedError, Error, ErrorKind}, kind::{Operation, ReferenceKind, Span}}};

impl SemanticAnalyzer {
    fn get_primitive_type(&self, primitive: PrimitiveKind) -> TypeSymbolId {
        self.builtin_types[primitive as usize]
    }

    fn get_type_of_identifier(&self, scope_id: ScopeId, name: &str, span: Span) -> Result<Type, BoxedError> {
        match self.symbol_table.find_value_symbol_from_scope(scope_id, name) {
            Some(value_symbol) => {
                match value_symbol.type_id.clone() {
                    Some(type_id) => Ok(type_id),
                    None => Err(self.create_error(ErrorKind::UnresolvedType(name.to_string()), span, &[span]))
                }
            },
            None => Err(self.create_error(ErrorKind::UnknownIdentifier(name.to_string()), span, &[span]))
        }
    }    

    fn collect_uv_unary_operation(&mut self, uv_id: TypeSymbolId, operator: &mut Operation, operand: &mut BoxedAstNode) -> Result<(), BoxedError> {
        let uv_type = self.collect_uvs(operand)?;
        match operator.to_trait_data() {
            Some((trait_name, _)) => {
                self.unification_context.register_constraint(Constraint::Trait(
                    uv_type.get_base_symbol(), Type::new_base(self.trait_registry.get_default_trait(&trait_name))
                ));
            },
            None => match operator {
                Operation::Dereference => self.unification_context.register_constraint(Constraint::DereferenceEquality(
                    uv_id, uv_type
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

        Ok(())
    }

    fn collect_uv_binary_operation(&mut self, uv_id: TypeSymbolId, left: &mut BoxedAstNode, right: &mut BoxedAstNode, operator: &mut Operation) -> Result<(), BoxedError> {
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
                _ => unreachable!()
            }
        }

        Ok(())
    }

    fn collect_uv_conditional_operation(&mut self, uv_id: TypeSymbolId, left: &mut BoxedAstNode, right: &mut BoxedAstNode) -> Result<(), BoxedError> {
        let left_type = self.collect_uvs(left)?;
        let right_type = self.collect_uvs(right)?;
        let bool_type = Type::new_base(self.get_primitive_type(PrimitiveKind::Bool));

        self.unification_context.register_constraint(Constraint::Equality(left_type.get_base_symbol(), bool_type.clone()));
        self.unification_context.register_constraint(Constraint::Equality(right_type.get_base_symbol(), bool_type.clone()));
        self.unification_context.register_constraint(Constraint::Equality(uv_id, bool_type));

        Ok(())
    }

    fn collect_uv_variable_declaration(&mut self, uv_id: TypeSymbolId, type_annotation: &mut Option<BoxedAstNode>, initializer: &mut Option<BoxedAstNode>, span: Span) -> Result<(), BoxedError> {
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
            return Err(self.create_error(ErrorKind::BadVariableDeclaration, span, &[span]));
        }

        Ok(())
    }

    fn collect_uv_block(&mut self, uv_id: TypeSymbolId, statements: &mut [AstNode]) -> Result<(), BoxedError> {
        let mut last_type = None;
        
        for stmt in statements.iter_mut() {
            last_type = Some(self.collect_uvs(stmt)?);
        }

        if let Some(last_type) = last_type {
            self.unification_context.register_constraint(Constraint::Equality(
                uv_id, last_type
            ));
        }
        Ok(())
    }

    fn collect_uv_if_statement(&mut self, uv_id: TypeSymbolId, condition: &mut BoxedAstNode, then_branch: &mut BoxedAstNode, else_if_branches: &mut [(BoxedAstNode, BoxedAstNode)], else_branch: &mut Option<BoxedAstNode>) -> Result<(), BoxedError> {
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
        
        Ok(())
    }

    fn collect_uv_while_loop(&mut self, uv_id: TypeSymbolId, condition: &mut BoxedAstNode, body: &mut BoxedAstNode) -> Result<(), BoxedError> {
        let cond_type = self.collect_uvs(condition)?;
        let bool_type = Type::new_base(self.get_primitive_type(PrimitiveKind::Bool));
        self.unification_context.register_constraint(Constraint::Equality(cond_type.get_base_symbol(), bool_type));

        self.collect_uvs(body)?;

        self.unification_context.register_constraint(Constraint::Equality(
            uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Null))
        ));

        Ok(())
    }

    fn collect_uv_for_loop(&mut self, uv_id: TypeSymbolId, initializer: &mut Option<BoxedAstNode>, condition: &mut Option<BoxedAstNode>, increment: &mut Option<BoxedAstNode>, body: &mut BoxedAstNode) -> Result<(), BoxedError> {
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

        Ok(())
    }

    fn collect_uv_return(&mut self, uv_id: TypeSymbolId, opt_expr: &mut Option<BoxedAstNode>) -> Result<(), BoxedError> {
        if let Some(expr) = opt_expr {
            self.collect_uvs(expr)?;
        }

        self.unification_context.register_constraint(Constraint::Equality(
            uv_id, Type::new_base(self.get_primitive_type(PrimitiveKind::Null))
        ));

        Ok(())
    }

    fn collect_uv_struct_literal(&mut self, uv_id: TypeSymbolId, name: &str, span: Span) -> Result<(), BoxedError> {
        let Some(symbol) = self.symbol_table.find_type_symbol(name) else {
            return Err(self.create_error(ErrorKind::UnknownIdentifier(name.to_owned()), span, &[span]));
        };

        self.unification_context.register_constraint(Constraint::Equality(
            uv_id, Type::new_base(symbol.id)
        ));

        Ok(())
    }

    fn collect_uv_associated_const(&mut self, uv_id: TypeSymbolId, type_annotation: &mut Option<BoxedAstNode>, initializer: &mut BoxedAstNode) -> Result<(), BoxedError> {
        let init_type = self.collect_uvs(initializer)?;

        if let Some(annot) = type_annotation {
            let annot_type = self.collect_uvs(annot)?;

            self.unification_context.register_constraint(Constraint::Equality(
                annot_type.get_base_symbol(), init_type.clone()
            ));
        } 

        self.unification_context.register_constraint(Constraint::Equality(
            uv_id, init_type
        ));

        Ok(())
    }

    fn collect_uv_type_reference(&mut self, uv_id: TypeSymbolId, type_name: &str, generic_types: &mut [AstNode], reference_kind: &mut ReferenceKind, span: Span) -> Result<(), BoxedError> {
        let symbol = self.symbol_table.find_type_symbol(type_name)
            .ok_or_else(|| self.create_error(ErrorKind::UnknownIdentifier(type_name.to_owned()), span, &[span]))?
            .id;

        let args: Vec<Type> = generic_types.iter_mut()
            .map(|generic_type| self.collect_uvs(generic_type))
            .collect::<Result<Vec<_>, _>>()?;

        let base_symbol = Type::Base {
            symbol,
            args
        };

        let constraint = match reference_kind {
            ReferenceKind::Value => base_symbol,
            ReferenceKind::Reference => Type::Reference(Box::new(base_symbol)),
            ReferenceKind::MutableReference => Type::MutableReference(Box::new(base_symbol))
        };

        self.unification_context.register_constraint(Constraint::Equality(uv_id, constraint));

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

        let uv = self.unification_context.generate_uv_type(&mut self.symbol_table, expr.span);
        let uv_id = uv.get_base_symbol();

        // note: find_symbol doesnt work unless scopes are correct 

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
                uv_id, Type::new_base(self.get_type_of_identifier(expr.scope_id.expect("scope_id should exist on ident node"), string, expr.span)?.get_base_symbol())
            )),
            UnaryOperation { operator, operand } => 
                self.collect_uv_unary_operation(uv_id, operator, operand)?,
            BinaryOperation { left, right, operator } =>
                self.collect_uv_binary_operation(uv_id, left, right, operator)?,
            ConditionalOperation { left, right, .. } =>
                self.collect_uv_conditional_operation(uv_id, left, right)?,
            VariableDeclaration { type_annotation, initializer, .. } =>
                self.collect_uv_variable_declaration(uv_id, type_annotation, initializer, expr.span)?,
            Block(statements) =>
                self.collect_uv_block(uv_id, statements)?,
            IfStatement { condition, then_branch, else_if_branches, else_branch } =>
                self.collect_uv_if_statement(uv_id, condition, then_branch, else_if_branches, else_branch)?,
            WhileLoop { condition, body } =>
                self.collect_uv_while_loop(uv_id, condition, body)?,
            ForLoop { initializer, condition, increment, body } =>
                self.collect_uv_for_loop(uv_id, initializer, condition, increment, body)?,
            Return(opt_expr) =>
                self.collect_uv_return(uv_id, opt_expr)?,
            // Function garbage
            StructLiteral { name, .. } =>
                self.collect_uv_struct_literal(uv_id, name, expr.span)?,
            AssociatedConstant { type_annotation, initializer, .. } =>
                self.collect_uv_associated_const(uv_id, type_annotation, initializer)?,
            // AssociatedFunction
            // AssociatedType
            // SelfValue/SelfType
            // FieldAccess
            // FunctionCall
            TypeReference { type_name, generic_types, reference_kind } =>
                self.collect_uv_type_reference(uv_id, type_name, generic_types, reference_kind, expr.span)?,
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