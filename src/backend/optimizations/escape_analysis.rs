use crate::{
    frontend::semantics::analyzer::{PrimitiveKind, ScopeKind, SemanticAnalyzer, Type, TypeSymbolKind, ValueSymbolId, ValueSymbolKind}, mir::ir_node::{MIRNode, MIRNodeKind}, utils::{error::{BoxedError, Error, ErrorKind}, kind::Operation}
};

fn is_primitive(analyzer: &SemanticAnalyzer, ty: &Type) -> bool {
    if let Type::Base { symbol, .. } = ty && let Some(type_symbol) = analyzer.symbol_table.get_type_symbol(*symbol) {
        return matches!(type_symbol.kind, TypeSymbolKind::Primitive(_));
    }

    false
}

fn is_fn_ptr(analyzer: &SemanticAnalyzer, ty: &Type) -> bool {
    if let Type::Base { symbol, .. } = ty && let Some(type_symbol) = analyzer.symbol_table.get_type_symbol(*symbol) {
        return matches!(type_symbol.kind, TypeSymbolKind::FunctionSignature { .. });
    }

    false
}

fn is_str_primitive(analyzer: &SemanticAnalyzer, ty: &Type) -> bool {
    if let Type::Base { symbol, .. } = ty && let Some(type_symbol) = analyzer.symbol_table.get_type_symbol(*symbol) {
        return matches!(type_symbol.kind, TypeSymbolKind::Primitive(PrimitiveKind::StaticString));
    }

    false
}

pub fn init(program: &mut MIRNode, analyzer: &mut SemanticAnalyzer) -> Vec<Error> {
    let mut errors = vec![];

    loop {
        match analysis_pass(analyzer, program) {
            Ok(changed) => {
                if !changed {
                    break;
                }
            },
            Err(e) => {
                errors.push(*e);
            }
        }
    }

    errors
}

fn analysis_pass(analyzer: &mut SemanticAnalyzer, node: &mut MIRNode) -> Result<bool, BoxedError> {
    let mut changed = false;

    for child in node.children_mut() {
        changed |= analysis_pass(analyzer, child)?;
    }

    match &mut node.kind {
        MIRNodeKind::Return(Some(expr)) => {
            if let Some(function_scope) = get_function_scope(analyzer, node.scope_id) {
                let expr_type = expr.type_id.as_ref().unwrap();
                if matches!(expr_type, Type::Reference { .. } | Type::MutableReference { .. }) {
                    match check_for_escape(analyzer, expr, function_scope, true) {
                        Ok(c) => changed |= c,
                        Err(e) => return Err(e),
                    }
                }
            }
        }

        MIRNodeKind::Function { body: Some(body_node), .. } => {
            if let MIRNodeKind::Block(statements) = &mut body_node.kind
                && let Some(last_expr) = statements.last_mut()
                && !matches!(last_expr.kind, MIRNodeKind::ExpressionStatement(_))
                && let Some(function_scope) = get_function_scope(analyzer, node.scope_id)
            {
                let expr_type = last_expr.type_id.as_ref().unwrap();
                if matches!(expr_type, Type::Reference { .. } | Type::MutableReference { .. }) {
                    match check_for_escape(analyzer, last_expr, function_scope, true) {
                        Ok(c) => changed |= c,
                        Err(e) => return Err(e),
                    }
                }
            }
        }

        MIRNodeKind::VariableDeclaration { initializer, .. } => {
            let destination_scope = node.scope_id;
            match check_for_escape(analyzer, initializer, destination_scope, false) {
                Ok(c) => changed |= c,
                Err(e) => return Err(e),
            }

            if let MIRNodeKind::HeapExpression(_) = &initializer.kind {
                 match move_to_heap(analyzer, node.value_id.unwrap()) {
                    Ok(c) => changed |= c,
                    Err(e) => return Err(e),
                 }
            }
        }
        _ => {}
    }

    Ok(changed)
}

fn check_for_escape(
    analyzer: &mut SemanticAnalyzer,
    expr: &mut MIRNode,
    destination_scope: usize,
    is_escaping_context: bool,
) -> Result<bool, BoxedError> {
    let mut changed = false;
    match &mut expr.kind {
        MIRNodeKind::Identifier(_) => {
            if let Some(var_id) = expr.value_id {
                let symbol = analyzer.symbol_table.get_value_symbol(var_id).unwrap();
                let should_heapify = if is_escaping_context {
                    is_scope_or_descendant(analyzer, symbol.scope_id, destination_scope)
                } else {
                    is_child_scope_of(analyzer, symbol.scope_id, destination_scope)
                };

                if matches!(symbol.kind, ValueSymbolKind::Variable) && should_heapify {
                    let symbol_type = symbol.type_id.as_ref().unwrap();
                    if !is_primitive(analyzer, symbol_type) && !is_fn_ptr(analyzer, symbol_type) {
                        match move_to_heap(analyzer, var_id) {
                            Ok(c) => changed |= c,
                            Err(e) => return Err(e),
                        }
                    }
                }
            }
        },
        MIRNodeKind::UnaryOperation { operator, operand }
            if *operator == Operation::ImmutableAddressOf
                || *operator == Operation::MutableAddressOf =>
        {
            if let Some(var_id) = get_base_variable(operand) {
                let symbol = analyzer.symbol_table.get_value_symbol(var_id).unwrap();
                let should_heapify = if is_escaping_context {
                    is_scope_or_descendant(analyzer, symbol.scope_id, destination_scope)
                } else {
                    is_child_scope_of(analyzer, symbol.scope_id, destination_scope)
                };

                if matches!(symbol.kind, ValueSymbolKind::Variable) && should_heapify {
                    let symbol_type = symbol.type_id.as_ref().unwrap();
                    if !is_fn_ptr(analyzer, symbol_type) {
                        match move_to_heap(analyzer, var_id) {
                            Ok(c) => changed |= c,
                            Err(e) => return Err(e),
                        }
                    }
                }
            }
        },
        MIRNodeKind::Block(statements) => {
            if let Some(last_expr) = statements.last_mut()
                && !matches!(last_expr.kind, MIRNodeKind::ExpressionStatement(_))
            {
                changed |= check_for_escape(
                    analyzer,
                    last_expr,
                    destination_scope,
                    is_escaping_context,
                )?;
            }
        },
        MIRNodeKind::IfStatement {
            then_branch,
            else_if_branches,
            else_branch,
            ..
        } => {
            changed |= check_for_escape(
                analyzer,
                then_branch,
                destination_scope,
                is_escaping_context,
            )?;
            for (_, branch) in else_if_branches {
                changed |= check_for_escape(
                    analyzer,
                    branch,
                    destination_scope,
                    is_escaping_context,
                )?;
            }
            if let Some(branch) = else_branch {
                changed |= check_for_escape(
                    analyzer,
                    branch,
                    destination_scope,
                    is_escaping_context,
                )?;
            }
        },
        _ => {}
    }
    Ok(changed)
}

fn get_base_variable(place: &MIRNode) -> Option<ValueSymbolId> {
    match &place.kind {
        MIRNodeKind::Identifier(_) => place.value_id,
        MIRNodeKind::FieldAccess { left, .. } => get_base_variable(left),
        MIRNodeKind::UnaryOperation { operator, .. } if *operator == Operation::Dereference => None,
        _ => None,
    }
}

fn move_to_heap(analyzer: &mut SemanticAnalyzer, var_id: ValueSymbolId) -> Result<bool, BoxedError> {
    let heap_type = analyzer.get_heap_type();
    let is_heap_type = {
        let symbol = analyzer.symbol_table.get_value_symbol(var_id).unwrap();
        analyzer.is_heap_type(symbol.type_id.as_ref().unwrap())
    };

    let (kind, ty, name_id, span) = {
        let symbol = analyzer.symbol_table.get_value_symbol_mut(var_id).unwrap();
        (
            symbol.kind.clone(),
            symbol.type_id.as_mut().unwrap(),
            symbol.name_id,
            symbol.span,
        )
    };

    if kind == ValueSymbolKind::Variable && !is_heap_type {
        *ty = Type::Base { symbol: heap_type, args: vec![] };

        let name = analyzer.symbol_table.get_value_name(name_id).to_string();
        let span = span.unwrap_or_default();
        return Err(analyzer.create_error(ErrorKind::NeedsHeapAllocation(name), span, &[span]));
    }

    Ok(false)
}

fn get_function_scope(analyzer: &SemanticAnalyzer, scope_id: usize) -> Option<usize> {
    let mut current_id = Some(scope_id);
    while let Some(id) = current_id {
        let scope = analyzer.symbol_table.get_scope(id).unwrap();
        if scope.kind == ScopeKind::Function {
            return Some(id);
        }

        current_id = scope.parent;
    }

    None
}

fn is_scope_or_descendant(
    analyzer: &SemanticAnalyzer,
    child_candidate: usize,
    parent_candidate: usize,
) -> bool {
    if child_candidate == parent_candidate {
        return true;
    }

    is_child_scope_of(analyzer, child_candidate, parent_candidate)
}

fn is_child_scope_of(
    analyzer: &SemanticAnalyzer,
    child_candidate: usize,
    parent_candidate: usize,
) -> bool {
    let mut current_id = analyzer.symbol_table.get_scope(child_candidate).unwrap().parent;
    while let Some(id) = current_id {
        if id == parent_candidate {
            return true;
        }

        current_id = analyzer.symbol_table.get_scope(id).unwrap().parent;
    }
    
    false
}