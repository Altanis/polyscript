use std::{collections::{BTreeMap, HashMap, HashSet}, rc::Rc};

use colored::Colorize;

use crate::{
    frontend::{
        semantics::analyzer::{ScopeKind, SemanticAnalyzer, Type, TypeSymbolId, TypeSymbolKind, ValueSymbolKind},
        syntax::ast::{AstNode, AstNodeKind},
    },
    mir::ir_node::{IRNode, IRNodeKind}
};

#[derive(Default)]
pub struct MonomorphizationContext {
    instantiations: HashMap<TypeSymbolId, HashSet<BTreeMap<TypeSymbolId, Type>>>,
    substitution_ctx: Option<Rc<BTreeMap<TypeSymbolId, Type>>>
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

    fn discover_monomorphic_sites(&mut self, program: &mut AstNode) {
        let AstNodeKind::Program(stmts) = &mut program.kind else { unreachable!(); };
        for stmt in stmts.iter_mut() {
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

    fn collect_generic_ids(&self, ty: &Type, out: &mut Vec<TypeSymbolId>) {
        match ty {
            Type::Base { symbol, args } => {
                match self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap().kind {
                    TypeSymbolKind::Generic(_) => {
                        if !out.contains(symbol) {
                            out.push(*symbol);
                        }
                    },
                    _ => {
                        for a in args {
                            self.collect_generic_ids(a, out);
                        }
                    }
                }
            },
            Type::Reference(inner) | Type::MutableReference(inner) => self.collect_generic_ids(inner, out)
        }
    }

    fn collect_monomorphization_sites(&mut self, node: &mut AstNode) {
        match &mut node.kind {
            AstNodeKind::FunctionCall { function, arguments, generic_arguments } => {
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

                let mut ordered_generic_ids: Vec<TypeSymbolId> = vec![];

                if has_receiver {
                    let template_receiver_ty = &template_params[0];
                    let mut base_template_receiver_ty = template_receiver_ty;
                    while let Type::Reference(inner) | Type::MutableReference(inner) = base_template_receiver_ty {
                        base_template_receiver_ty = inner;
                    }
                    self.collect_generic_ids(base_template_receiver_ty, &mut ordered_generic_ids);
                }

                for template_param in params_to_zip.iter() {
                    self.collect_generic_ids(template_param, &mut ordered_generic_ids);
                }

                self.collect_generic_ids(template_return, &mut ordered_generic_ids);

                ordered_generic_ids.retain(|&gid| {
                    let sym = self.analyzer.symbol_table.get_type_symbol(gid).unwrap();
                    let name = self.analyzer.symbol_table.get_type_name(sym.name_id);
                    name != "Self"
                });

                let ordered_args_option: Option<Vec<Type>> = ordered_generic_ids
                    .iter()
                    .map(|gid| {
                        let ty = generic_id_to_concrete_type.get(gid)?;
                        if !self.type_is_fully_concrete(ty) { return None; }

                        Some(ty.clone())
                    })
                    .collect();

                let Some(ordered_args) = ordered_args_option else { return };

                if !ordered_args.is_empty() {
                    let instantiation_map: BTreeMap<TypeSymbolId, Type> = ordered_generic_ids
                        .iter()
                        .cloned()
                        .zip(ordered_args.iter().cloned())
                        .collect();

                    *generic_arguments = ordered_args;

                    self.monomorphization_ctx
                        .instantiations
                        .entry(*fn_symbol_id)
                        .or_default()
                        .insert(instantiation_map);
                }
            },
            AstNodeKind::StructLiteral { generic_arguments, .. } | AstNodeKind::TypeReference { generic_arguments, .. } => {
                if let Some(Type::Base { symbol, args, .. }) = &node.type_id {
                    let type_symbol = self.analyzer.symbol_table.get_type_symbol(*symbol).unwrap();
                    
                    if type_symbol.generic_parameters.is_empty() || args.is_empty() {
                        return;
                    }

                    if args.iter().all(|arg| self.type_is_fully_concrete(arg)) {
                        *generic_arguments = args.clone();

                        let instantiation_map: BTreeMap<TypeSymbolId, Type> = type_symbol
                            .generic_parameters
                            .iter()
                            .zip(args.iter())
                            .map(|(&gid, ty)| (gid, ty.clone()))
                            .collect();
                        
                        if !instantiation_map.is_empty() {
                            self.monomorphization_ctx
                                .instantiations
                                .entry(*symbol)
                                .or_default()
                                .insert(instantiation_map);
                        }
                    }
                }
            },
            _ => {}
        }

        for child in node.children_mut() {
            self.collect_monomorphization_sites(child);
        }
    }
}

impl<'a> IRBuilder<'a> {
    fn monomorphize(&mut self, program: &mut AstNode) -> IRNode {
        let mut mir_stmts = vec![];

        let AstNodeKind::Program(stmts) = &mut program.kind else { unreachable!(); };
        for stmt in stmts.iter_mut() {
            mir_stmts.extend(self.build_concrete_stmt(stmt));
        }

        IRNode {
            kind: IRNodeKind::Program(mir_stmts),
            span: program.span,
            value_id: None,
            type_id: None
        }
    }

    fn mangle_name(&self, name: &String, concrete_types: &BTreeMap<TypeSymbolId, Type>) -> String {
        format!("#{}{}", name, if concrete_types.is_empty() { "" } else { "_" })
            + concrete_types.values()
                .map(|ty| self.analyzer.symbol_table.display_type(ty))
                .collect::<Vec<String>>()
                .join("_")
                .as_str()
    }

    fn substitute_type(generic_type: &Type, substitutions: &BTreeMap<TypeSymbolId, Type>) -> Type {
        match generic_type {
            Type::Base { symbol, args } => {
                if let Some(concrete_type) = substitutions.get(symbol) {
                    return concrete_type.clone();
                }

                let new_args = args
                    .iter()
                    .map(|arg| Self::substitute_type(arg, substitutions))
                    .collect();

                Type::Base {
                    symbol: *symbol,
                    args: new_args,
                }
            },
            Type::Reference(inner) => Type::Reference(Box::new(Self::substitute_type(inner, substitutions))),
            Type::MutableReference(inner) => Type::MutableReference(Box::new(Self::substitute_type(inner, substitutions)))
        }
    }

    fn build_concrete_stmt(&mut self, node: &mut AstNode) -> Vec<IRNode> {
        for child in node.children_mut() {
            self.build_concrete_stmt(child);
        }

        let template_symbol_id = match &node.kind {
            AstNodeKind::StructDeclaration { name, .. }
                => self.analyzer.symbol_table.find_type_symbol_in_scope(name, node.scope_id.unwrap()).unwrap().id,
            _ => return vec![]
        };
        let Some(concrete_types_set) = self.monomorphization_ctx.instantiations.get(&template_symbol_id).cloned() else { return vec![]; };

        let mut concrete_ir_nodes = vec![];

        match &node.kind {
            AstNodeKind::StructDeclaration { .. } | AstNodeKind::Function { .. } => {
                for concrete_types in concrete_types_set {
                    self.monomorphization_ctx.substitution_ctx = Some(Rc::new(concrete_types));
                    concrete_ir_nodes.push(self.lower_node(node).unwrap());
                    self.monomorphization_ctx.substitution_ctx = None;
                }
            },
            _ => {}
        }

        concrete_ir_nodes
    }
}

impl<'a> IRBuilder<'a> {
    pub fn build(&mut self, program: &mut AstNode) -> IRNode {
        self.discover_monomorphic_sites(program);
        let mut mir_program = self.monomorphize(program);

        let IRNodeKind::Program(hoisted_stmts) = &mut mir_program.kind else { unreachable!(); };
        let IRNodeKind::Program(other_stmts) = self.lower_node(program).unwrap().kind else { unreachable!(); };
        hoisted_stmts.extend(other_stmts);

        mir_program
    }

    fn lower_node(&mut self, node: &mut AstNode) -> Option<IRNode> {
        let kind = match &mut node.kind {
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
                IRNodeKind::Block(stmts.iter_mut().filter_map(|s| self.lower_node(s)).collect())
            },
            AstNodeKind::IfStatement { condition, then_branch, else_if_branches, else_branch } => {
                IRNodeKind::IfStatement {
                    condition: Box::new(self.lower_node(condition)?),
                    then_branch: Box::new(self.lower_node(then_branch)?),
                    else_if_branches: else_if_branches
                        .iter_mut()
                        .filter_map(|(c, b)| {
                            Some((Box::new(self.lower_node(c)?), Box::new(self.lower_node(b)?)))
                        })
                        .collect(),
                    else_branch: else_branch.as_mut().map(|b| Box::new(self.lower_node(b).unwrap())),
                }
            },
            AstNodeKind::WhileLoop { condition, body } => IRNodeKind::WhileLoop {
                condition: Box::new(self.lower_node(condition)?),
                body: Box::new(self.lower_node(body)?),
            },
            AstNodeKind::ForLoop { initializer, condition, increment, body } => {
                IRNodeKind::ForLoop {
                    initializer: initializer.as_mut().map(|n| Box::new(self.lower_node(n).unwrap())),
                    condition: condition.as_mut().map(|n| Box::new(self.lower_node(n).unwrap())),
                    increment: increment.as_mut().map(|n| Box::new(self.lower_node(n).unwrap())),
                    body: Box::new(self.lower_node(body)?),
                }
            }
            AstNodeKind::Return(expr) => {
                IRNodeKind::Return(expr.as_mut().map(|e| Box::new(self.lower_node(e).unwrap())))
            }
            AstNodeKind::Break => IRNodeKind::Break,
            AstNodeKind::Continue => IRNodeKind::Continue,

            AstNodeKind::Function { name, parameters, instance, body, generic_parameters, .. } => {
                if !generic_parameters.is_empty() {
                    return None;
                }

                IRNodeKind::Function {
                    name: name.clone(),
                    parameters: parameters.iter_mut().filter_map(|p| self.lower_node(p)).collect(),
                    instance: *instance,
                    body: body.as_mut().map(|b| Box::new(self.lower_node(b).unwrap())),
                }
            }
            AstNodeKind::FunctionParameter { name, mutable, .. } => IRNodeKind::FunctionParameter {
                name: name.clone(),
                mutable: *mutable,
            },
            AstNodeKind::FunctionCall { function, arguments, .. } => IRNodeKind::FunctionCall {
                function: Box::new(self.lower_node(function)?),
                arguments: arguments.iter_mut().filter_map(|a| self.lower_node(a)).collect(),
            },
            AstNodeKind::FieldAccess { left, right } => IRNodeKind::FieldAccess {
                left: Box::new(self.lower_node(left)?),
                right: Box::new(self.lower_node(right)?),
            },

            AstNodeKind::StructDeclaration { name, fields, generic_parameters } => {
                if let Some(substitutions) = &self.monomorphization_ctx.substitution_ctx {
                    let template_symbol = self.analyzer.symbol_table.find_type_symbol_in_scope(name, node.scope_id.unwrap()).unwrap().clone();
                    let parent_scope_id = self.analyzer.symbol_table.get_scope(template_symbol.scope_id).unwrap().parent.unwrap();

                    let mangled_name = self.mangle_name(name, substitutions);

                    let original_scope = self.analyzer.symbol_table.get_current_scope_id();
                    self.analyzer.symbol_table.current_scope_id = parent_scope_id;
                    let new_scope_id = self.analyzer.symbol_table.enter_scope(ScopeKind::Struct);
                    
                    let ir_fields = fields.iter_mut()
                        .map(|field| self.lower_node(field).unwrap())
                        .collect();

                    self.analyzer.symbol_table.exit_scope();
                    
                    let new_type_symbol_id = self.analyzer.symbol_table.add_type_symbol(
                        &mangled_name,
                        TypeSymbolKind::Struct((new_scope_id, vec![])),
                        vec![],
                        template_symbol.qualifier,
                        Some(node.span),
                    ).unwrap();

                    self.analyzer.symbol_table.current_scope_id = original_scope;

                    return Some(IRNode {
                        kind: IRNodeKind::StructDeclaration { name: mangled_name, fields: ir_fields },
                        span: node.span,
                        value_id: node.value_id,
                        type_id: Some(Type::new_base(new_type_symbol_id))
                    });
                } else if generic_parameters.is_empty() {
                    IRNodeKind::StructDeclaration {
                        name: name.clone(),
                        fields: fields.iter_mut().filter_map(|f| self.lower_node(f)).collect(),
                    }
                } else {
                    return None;
                }
            }
            AstNodeKind::StructField { name, qualifier, .. } => {
                let kind = IRNodeKind::StructField { name: name.clone() };

                if let Some(substitutions) = &self.monomorphization_ctx.substitution_ctx {
                    let generic_field_type = self.analyzer.symbol_table
                        .find_value_symbol_in_scope(name, node.scope_id.unwrap())
                        .unwrap()
                        .type_id
                        .as_ref()
                        .unwrap();
                    let concrete_field_type = Self::substitute_type(generic_field_type, substitutions);

                    let new_value_symbol_id = self.analyzer.symbol_table.add_value_symbol(
                        name,
                        ValueSymbolKind::StructField,
                        false,
                        *qualifier,
                        Some(concrete_field_type.clone()),
                        Some(node.span),
                    ).unwrap();

                    return Some(IRNode {
                        kind,
                        span: node.span,
                        value_id: Some(new_value_symbol_id),
                        type_id: Some(concrete_field_type.clone())
                    });
                } else {
                    kind
                }
            },
            AstNodeKind::StructLiteral { fields, .. } => {
                let concrete_struct_type = node.type_id.as_ref().unwrap();
                let mangled_name = self.analyzer.symbol_table.display_type(concrete_struct_type);

                IRNodeKind::StructLiteral {
                    name: mangled_name,
                    fields: fields
                        .iter_mut()
                        .map(|(k, v)| (k.clone(), self.lower_node(v).unwrap()))
                        .collect(),
                }
            }

            AstNodeKind::EnumDeclaration { name, variants } => IRNodeKind::EnumDeclaration {
                name: name.clone(),
                variants: variants
                    .iter_mut()
                    .map(|(k, (v, e))| {
                        (
                            k.clone(),
                            (self.lower_node(v).unwrap(), e.as_mut().map(|expr| self.lower_node(expr).unwrap())),
                        )
                    })
                    .collect(),
            },
            AstNodeKind::EnumVariant(name) => IRNodeKind::EnumVariant(name.clone()),

            AstNodeKind::Program(stmts) => {
                let mut ir_nodes = vec![];
                for stmt in stmts {
                    match &mut stmt.kind {
                        AstNodeKind::ImplDeclaration { associated_functions, generic_parameters, .. } => {
                            if generic_parameters.is_empty() {
                                for func in associated_functions {
                                    if let Some(ir_func) = self.lower_node(func) {
                                        ir_nodes.push(ir_func);
                                    }
                                }
                            }
                        },
                        _ => {
                            if let Some(ir_node) = self.lower_node(stmt) {
                                ir_nodes.push(ir_node);
                            }
                        }
                    }
                }
                IRNodeKind::Program(ir_nodes)
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
        if self.monomorphization_ctx.instantiations.is_empty() {
            return writeln!(f, "  {}", "(no monomorphization sites found)".dimmed());
        }

        let mut keys: Vec<_> = self.monomorphization_ctx.instantiations.keys().cloned().collect();
        keys.sort();

        for symbol_id in keys {
            let instantiations = &self.monomorphization_ctx.instantiations[&symbol_id];
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
            sorted_instantiations.sort_by_key(|map| {
                let mut content = map.iter().collect::<Vec<_>>();
                content.sort_by_key(|(k, _)| *k);
                content.iter().map(|(_, t)| self.analyzer.symbol_table.display_type(t)).collect::<String>()
            });

            for instantiation_map in sorted_instantiations {
                write!(f, "    - ")?;
                if instantiation_map.is_empty() {
                    writeln!(f, "{}", "<>".dimmed())?;
                } else {
                    let mut items: Vec<_> = instantiation_map.iter().collect();
                    items.sort_by_key(|(k, _)| *k);

                    let args_str = items
                        .iter()
                        .map(|(gid, ty)| {
                            let g_sym = self.analyzer.symbol_table.get_type_symbol(**gid).unwrap();
                            let g_name = self.analyzer.symbol_table.get_type_name(g_sym.name_id);
                            format!("{}: {}", g_name.yellow(), self.analyzer.symbol_table.display_type(ty).bright_blue())
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    writeln!(f, "<{}>", args_str)?;
                }
            }
        }

        Ok(())
    }
}


/*
when handling a function, give state to monomorphization_ctx. let it know that its handling the function.
the thing itself needs to be lowered (function and body). lower it properly using state from monomorphization ctx.
you should do it for struct monomorphization too.
consider making dsa HashSet<HashMap<TypeSymbolId, Type>>
*/