use std::collections::{HashMap, HashSet};

use colored::Colorize;

use crate::{
    frontend::{
        semantics::analyzer::{SemanticAnalyzer, Type, TypeSymbolId, TypeSymbolKind, ValueSymbolKind},
        syntax::ast::{AstNode, AstNodeKind},
    },
    mir::ir_node::{IRNode, IRNodeKind},
};

#[derive(Default)]
pub struct MonomorphizationContext {
    substitutions: HashMap<TypeSymbolId, HashSet<(Vec<Type>, Vec<Type>)>>
}

pub struct IRBuilder<'a> {
    analyzer: &'a mut SemanticAnalyzer,
    monomorphization_ctx: MonomorphizationContext
}

impl<'a> IRBuilder<'a> {
    pub fn new(analyzer: &'a mut SemanticAnalyzer) -> Self {
        Self {
            analyzer,
            monomorphization_ctx: MonomorphizationContext::default()
        }
    }
}

impl<'a> IRBuilder<'a> {
    pub fn type_is_fully_concrete(&self, ty: &Type) -> bool {
        match ty {
            Type::Base { symbol, args } => {
                let type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
                if matches!(type_symbol.kind, TypeSymbolKind::Generic(_)) {
                    return false;
                }

                args.iter().all(|arg| self.type_is_fully_concrete(arg))
            },
            Type::Reference(inner) | Type::MutableReference(inner) => {
                self.type_is_fully_concrete(inner)
            }
        }
    }

    pub fn monomorphize(&mut self, program: &AstNode) {
        let AstNodeKind::Program(stmts) = &program.kind else { unreachable!(); };
        for stmt in stmts.iter() {
            self.collect_monomorphization_sites(stmt);
        }
    }

    fn collect_generic_mappings(
        &self,
        concrete_ty: &Type,
        template_ty: &Type,
        substitutions: &mut HashMap<TypeSymbolId, Type>,
    ) {
        match (concrete_ty, template_ty) {
            (
                Type::Base {
                    symbol: concrete_symbol,
                    args: concrete_args,
                },
                Type::Base {
                    symbol: template_symbol,
                    args: template_args,
                },
            ) => {
                let template_type_symbol = self
                    .analyzer
                    .symbol_table
                    .get_type_symbol(*template_symbol)
                    .unwrap();

                if let TypeSymbolKind::Generic(_) = template_type_symbol.kind {
                    substitutions.insert(*template_symbol, concrete_ty.clone());
                    return;
                }

                if concrete_symbol == template_symbol && concrete_args.len() == template_args.len() {
                    for (c_arg, t_arg) in concrete_args.iter().zip(template_args.iter()) {
                        self.collect_generic_mappings(c_arg, t_arg, substitutions);
                    }
                }
            },
            (Type::Reference(c_inner), Type::Reference(t_inner))
                | (Type::MutableReference(c_inner), Type::MutableReference(t_inner))
            => {
                self.collect_generic_mappings(c_inner, t_inner, substitutions);
            },
            _ => {}
        }
    }

    fn collect_monomorphization_sites(&mut self, node: &AstNode) {
        match &node.kind {
            AstNodeKind::FunctionCall { function, arguments } => {
                let Some(fn_value_symbol) = function.value_id.and_then(|id| self.analyzer.symbol_table.get_value_symbol(id)) else { return; };
                let Some(template_fn_type) = fn_value_symbol.type_id.as_ref() else { return; };

                let Type::Base { symbol: fn_symbol_id, .. } = template_fn_type else { return; };
                let fn_symbol = self.analyzer.symbol_table.get_type_symbol(*fn_symbol_id).unwrap();
                let TypeSymbolKind::FunctionSignature { params: template_params, return_type: template_return, .. } = &fn_symbol.kind else { return; };

                let mut generic_id_to_concrete_type = HashMap::new();
                
                let has_receiver = fn_symbol.generic_parameters.iter().any(|p| {
                    let sym = self.analyzer.symbol_table.get_type_symbol(*p).unwrap();
                    let name = self.analyzer.symbol_table.get_type_name(sym.name_id);
                    name == "Self"
                }) || (!template_params.is_empty() && arguments.len() < template_params.len());


                if has_receiver
                    && let AstNodeKind::FieldAccess { left, .. } = &function.kind
                    && let Some(instance_type) = &left.type_id
                {
                    let mut concrete_receiver_ty = instance_type;
                    while let Type::Reference(inner) | Type::MutableReference(inner) = concrete_receiver_ty {
                        concrete_receiver_ty = inner;
                    }
                
                    let template_receiver_ty = &template_params[0];
                    let mut base_template_receiver_ty = template_receiver_ty;
                    while let Type::Reference(inner) | Type::MutableReference(inner) = base_template_receiver_ty {
                        base_template_receiver_ty = inner;
                    }
                
                    self.collect_generic_mappings(
                        concrete_receiver_ty,
                        base_template_receiver_ty,
                        &mut generic_id_to_concrete_type,
                    );
                }

                let params_to_zip = if has_receiver {
                    &template_params[1..]
                } else {
                    template_params
                };

                for (arg_node, template_param) in arguments.iter().zip(params_to_zip.iter()) {
                    if let Some(concrete_type) = &arg_node.type_id {
                        self.collect_generic_mappings(concrete_type, template_param, &mut generic_id_to_concrete_type);
                    }
                }
                
                if let Some(call_site_return_type) = &node.type_id {
                    self.collect_generic_mappings(
                        call_site_return_type,
                        template_return,
                        &mut generic_id_to_concrete_type,
                    );
                }

                let ValueSymbolKind::Function(fn_scope_id) = fn_value_symbol.kind else { return };

                let mut parent_generic_ids = Vec::new();
                let mut local_generic_ids = Vec::new();

                for &generic_param_id in generic_id_to_concrete_type.keys() {
                    let generic_param_symbol = self.analyzer.symbol_table.get_type_symbol(generic_param_id).unwrap();
                    if generic_param_symbol.scope_id == fn_scope_id {
                        local_generic_ids.push(generic_param_id);
                    } else {
                        parent_generic_ids.push(generic_param_id);
                    }
                }

                parent_generic_ids.sort();
                local_generic_ids.sort();

                let parent_args: Vec<Type> = parent_generic_ids.iter().map(|id| generic_id_to_concrete_type[id].clone()).collect();
                let local_args: Vec<Type> = local_generic_ids.iter().map(|id| generic_id_to_concrete_type[id].clone()).collect();


                if (!local_args.is_empty() || !parent_args.is_empty()) &&
                   local_args.iter().all(|t| self.type_is_fully_concrete(t)) &&
                   parent_args.iter().all(|t| self.type_is_fully_concrete(t))
                {
                    self.monomorphization_ctx
                        .substitutions
                        .entry(*fn_symbol_id)
                        .or_default()
                        .insert((parent_args, local_args));
                }
            },
            AstNodeKind::StructLiteral { .. } | AstNodeKind::TypeReference { .. } => {
                if let Some(Type::Base { symbol, args, .. }) = &node.type_id {
                    let type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
                    
                    if type_symbol.generic_parameters.is_empty() || args.is_empty() {
                        return;
                    }

                    if args.iter().all(|arg| self.type_is_fully_concrete(arg)) {
                        self.monomorphization_ctx
                            .substitutions
                            .entry(*symbol)
                            .or_default()
                            .insert((vec![], args.clone()));
                    }
                }
            },
            _ => {}
        }

        for child in node.children().iter() {
            self.collect_monomorphization_sites(child);
        }
    }
}

impl<'a> IRBuilder<'a> {
    pub fn build(&mut self, program: &AstNode) -> Option<IRNode> {
        self.lower_node(program)
    }

    fn lower_node(&mut self, node: &AstNode) -> Option<IRNode> {
        let kind = match &node.kind {
            AstNodeKind::IntegerLiteral(v) => IRNodeKind::IntegerLiteral(*v),
            AstNodeKind::FloatLiteral(v) => IRNodeKind::FloatLiteral(*v),
            AstNodeKind::BooleanLiteral(v) => IRNodeKind::BooleanLiteral(*v),
            AstNodeKind::StringLiteral(v) => IRNodeKind::StringLiteral(v.clone()),
            AstNodeKind::CharLiteral(v) => IRNodeKind::CharLiteral(*v),

            AstNodeKind::Identifier(name) => IRNodeKind::Identifier(name.clone()),
            AstNodeKind::SelfExpr => IRNodeKind::SelfExpr,
            AstNodeKind::HeapExpression(expr) => IRNodeKind::HeapExpression(Box::new(self.lower_node(expr)?)),
            AstNodeKind::ExpressionStatement(expr) => {
                IRNodeKind::ExpressionStatement(Box::new(self.lower_node(expr)?))
            }

            AstNodeKind::VariableDeclaration { name, mutable, initializer, .. } => {
                IRNodeKind::VariableDeclaration {
                    name: name.clone(),
                    mutable: *mutable,
                    initializer: Box::new(self.lower_node(initializer)?),
                }
            }

            AstNodeKind::UnaryOperation { operator, operand } => IRNodeKind::UnaryOperation {
                operator: *operator,
                operand: Box::new(self.lower_node(operand)?),
            },
            AstNodeKind::BinaryOperation { operator, left, right } => IRNodeKind::BinaryOperation {
                operator: *operator,
                left: Box::new(self.lower_node(left)?),
                right: Box::new(self.lower_node(right)?),
            },
            AstNodeKind::ConditionalOperation { operator, left, right } => {
                IRNodeKind::ConditionalOperation {
                    operator: *operator,
                    left: Box::new(self.lower_node(left)?),
                    right: Box::new(self.lower_node(right)?),
                }
            }

            AstNodeKind::TypeCast { expr, .. } => IRNodeKind::TypeCast {
                expr: Box::new(self.lower_node(expr)?),
                target_type: node.type_id.clone()?,
            },

            AstNodeKind::Block(stmts) => {
                IRNodeKind::Block(stmts.iter().filter_map(|s| self.lower_node(s)).collect())
            }
            AstNodeKind::IfStatement { condition, then_branch, else_if_branches, else_branch } => {
                IRNodeKind::IfStatement {
                    condition: Box::new(self.lower_node(condition)?),
                    then_branch: Box::new(self.lower_node(then_branch)?),
                    else_if_branches: else_if_branches
                        .iter()
                        .filter_map(|(c, b)| {
                            Some((Box::new(self.lower_node(c)?), Box::new(self.lower_node(b)?)))
                        })
                        .collect(),
                    else_branch: else_branch.as_ref().map(|b| Box::new(self.lower_node(b).unwrap())),
                }
            }
            AstNodeKind::WhileLoop { condition, body } => IRNodeKind::WhileLoop {
                condition: Box::new(self.lower_node(condition)?),
                body: Box::new(self.lower_node(body)?),
            },
            AstNodeKind::ForLoop { initializer, condition, increment, body } => {
                IRNodeKind::ForLoop {
                    initializer: initializer.as_ref().map(|n| Box::new(self.lower_node(n).unwrap())),
                    condition: condition.as_ref().map(|n| Box::new(self.lower_node(n).unwrap())),
                    increment: increment.as_ref().map(|n| Box::new(self.lower_node(n).unwrap())),
                    body: Box::new(self.lower_node(body)?),
                }
            }
            AstNodeKind::Return(expr) => {
                IRNodeKind::Return(expr.as_ref().map(|e| Box::new(self.lower_node(e).unwrap())))
            }
            AstNodeKind::Break => IRNodeKind::Break,
            AstNodeKind::Continue => IRNodeKind::Continue,

            AstNodeKind::Function { name, parameters, instance, body, generic_parameters, .. } => {
                if !generic_parameters.is_empty() {
                    return None;
                }

                IRNodeKind::Function {
                    name: name.clone(),
                    parameters: parameters.iter().filter_map(|p| self.lower_node(p)).collect(),
                    instance: *instance,
                    body: body.as_ref().map(|b| Box::new(self.lower_node(b).unwrap())),
                }
            }
            AstNodeKind::FunctionParameter { name, mutable, .. } => IRNodeKind::FunctionParameter {
                name: name.clone(),
                mutable: *mutable,
            },
            AstNodeKind::FunctionCall { function, arguments } => IRNodeKind::FunctionCall {
                function: Box::new(self.lower_node(function)?),
                arguments: arguments.iter().filter_map(|a| self.lower_node(a)).collect(),
            },
            AstNodeKind::FieldAccess { left, right } => IRNodeKind::FieldAccess {
                left: Box::new(self.lower_node(left)?),
                right: Box::new(self.lower_node(right)?),
            },

            AstNodeKind::StructDeclaration { name, fields, generic_parameters } => {
                if !generic_parameters.is_empty() {
                    return None;
                }

                IRNodeKind::StructDeclaration {
                    name: name.clone(),
                    fields: fields.iter().filter_map(|f| self.lower_node(f)).collect(),
                }
            }
            AstNodeKind::StructField { name, .. } => IRNodeKind::StructField { name: name.clone() },
            AstNodeKind::StructLiteral { fields, .. } => {
                let concrete_struct_type = node.type_id.as_ref().unwrap();
                let mangled_name = self.analyzer.symbol_table.display_type(concrete_struct_type);

                IRNodeKind::StructLiteral {
                    name: mangled_name,
                    fields: fields
                        .iter()
                        .map(|(k, v)| (k.clone(), self.lower_node(v).unwrap()))
                        .collect(),
                }
            }

            AstNodeKind::EnumDeclaration { name, variants } => IRNodeKind::EnumDeclaration {
                name: name.clone(),
                variants: variants
                    .iter()
                    .map(|(k, (v, e))| {
                        (
                            k.clone(),
                            (self.lower_node(v).unwrap(), e.as_ref().map(|expr| self.lower_node(expr).unwrap())),
                        )
                    })
                    .collect(),
            },
            AstNodeKind::EnumVariant(name) => IRNodeKind::EnumVariant(name.clone()),

            AstNodeKind::Program(stmts) => {
                IRNodeKind::Program(stmts.iter().filter_map(|s| self.lower_node(s)).collect())
            }

            AstNodeKind::ImplDeclaration { .. }
            | AstNodeKind::TraitDeclaration { .. }
            | AstNodeKind::TypeDeclaration { .. }
            | AstNodeKind::AssociatedConstant { .. }
            | AstNodeKind::AssociatedType { .. }
            | AstNodeKind::TraitConstant { .. }
            | AstNodeKind::TraitType(_)
            | AstNodeKind::PathQualifier { .. }
            | AstNodeKind::TypeReference { .. }
            | AstNodeKind::FunctionPointer { .. }
            | AstNodeKind::SelfType(_)
            | AstNodeKind::GenericParameter { .. } => return None,
        };

        Some(IRNode {
            kind,
            span: node.span,
            value_id: node.value_id,
            type_id: node.type_id.clone(),
        })
    }
}

impl std::fmt::Display for IRBuilder<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "\n{}", "Monomorphization Sites:".bold().underline())?;
        if self.monomorphization_ctx.substitutions.is_empty() {
            return writeln!(f, "  {}", "(no monomorphization sites found)".dimmed());
        }

        let mut keys: Vec<_> = self.monomorphization_ctx.substitutions.keys().cloned().collect();
        keys.sort();

        for symbol_id in keys {
            let instantiations = &self.monomorphization_ctx.substitutions[&symbol_id];
            let symbol = self.analyzer.symbol_table.get_type_symbol(symbol_id).unwrap();
            let name = self.analyzer.symbol_table.get_type_name(symbol.name_id);
            
            let generic_params_str = symbol.generic_parameters
                .iter()
                .map(|&p_id| {
                    let param_symbol = self.analyzer.symbol_table.get_type_symbol(p_id).unwrap();
                    self.analyzer.symbol_table.get_type_name(param_symbol.name_id).yellow().to_string()
                })
                .collect::<Vec<_>>()
                .join(", ");

            if generic_params_str.is_empty() {
                 writeln!(f, "  {}", name.cyan())?;
            } else {
                 writeln!(f, "  {} <{}>", name.cyan(), generic_params_str)?;
            }
            
            let mut sorted_instantiations: Vec<_> = instantiations.iter().collect();
            sorted_instantiations.sort_by_key(|(parent_args, local_args)| {
                let p_str: String = parent_args.iter().map(|t| self.analyzer.symbol_table.display_type(t)).collect();
                let l_str: String = local_args.iter().map(|t| self.analyzer.symbol_table.display_type(t)).collect();
                (p_str, l_str)
            });
            
            for (parent_args, local_args) in sorted_instantiations {
                write!(f, "    - ")?;

                if parent_args.is_empty() {
                    write!(f, "Parent: {} ", "[]".dimmed())?;
                } else {
                    let parent_args_str = parent_args
                        .iter()
                        .map(|ty| self.analyzer.symbol_table.display_type(ty).bright_blue().to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "Parent: <{}> ", parent_args_str)?;
                }
                
                write!(f, "{}", "/".dimmed())?;

                if local_args.is_empty() {
                    writeln!(f, " Local: {}", "[]".dimmed())?;
                } else {
                    let local_args_str = local_args
                        .iter()
                        .map(|ty| self.analyzer.symbol_table.display_type(ty).bright_green().to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    writeln!(f, " Local: <{}>", local_args_str)?;
                }
            }
        }

        Ok(())
    }
}