use crate::{
    frontend::semantics::analyzer::{
            AllocationKind, ScopeKind, SemanticAnalyzer, ValueSymbolId, ValueSymbolKind,
        },
    mir::ir_node::{MIRNode, MIRNodeKind},
    utils::kind::Operation
};

pub fn init(program: &mut MIRNode, analyzer: &mut SemanticAnalyzer) {
    loop {
        if !analysis_pass(analyzer, program) {
            break;
        }
    }

    for symbol in analyzer.symbol_table.registry.value_symbols.values_mut() {
        if symbol.kind == ValueSymbolKind::Variable && symbol.allocation_kind == AllocationKind::Unresolved {
            symbol.allocation_kind = AllocationKind::Stack;
        }
    }
}

fn analysis_pass(analyzer: &mut SemanticAnalyzer, node: &mut MIRNode) -> bool {
    let mut changed = false;

    for child in node.children_mut() {
        if analysis_pass(analyzer, child) {
            changed = true;
        }
    }

    match &mut node.kind {
        MIRNodeKind::Return(Some(expr)) => {
            if let Some(function_scope) = get_function_scope(analyzer, node.scope_id) {
                check_for_escape(analyzer, expr, function_scope, true, &mut changed);
            }
        }

        MIRNodeKind::Function { body: Some(body_node), .. } => {
            if let MIRNodeKind::Block(statements) = &mut body_node.kind
                && let Some(last_expr) = statements.last_mut()
                && !matches!(last_expr.kind, MIRNodeKind::ExpressionStatement(_))
                && let Some(function_scope) = get_function_scope(analyzer, node.scope_id)
            {
                check_for_escape(analyzer, last_expr, function_scope, true, &mut changed);
            }
        }

        MIRNodeKind::VariableDeclaration { initializer, .. } => {
            let destination_scope = node.scope_id;
            check_for_escape(analyzer, initializer, destination_scope, false, &mut changed);

            if let MIRNodeKind::HeapExpression(_) = &initializer.kind
                && move_to_heap(analyzer, node.value_id.unwrap())
            {
                changed = true;
            }
        }
        _ => {}
    }

    changed
}

fn check_for_escape(
    analyzer: &mut SemanticAnalyzer,
    expr: &mut MIRNode,
    destination_scope: usize,
    is_return_or_heap_assign: bool,
    changed: &mut bool,
) {
    match &mut expr.kind {
        MIRNodeKind::Identifier(_) => {
            if let Some(var_id) = expr.value_id {
                let symbol = analyzer.symbol_table.get_value_symbol(var_id).unwrap();
                let should_heapify = if is_return_or_heap_assign {
                    is_scope_or_descendant(analyzer, symbol.scope_id, destination_scope)
                } else {
                    is_child_scope_of(analyzer, symbol.scope_id, destination_scope)
                };

                if matches!(symbol.kind, ValueSymbolKind::Variable) && should_heapify
                    && move_to_heap(analyzer, var_id)
                {
                    *changed = true;
                }
            }
        },
        MIRNodeKind::UnaryOperation { operator, operand }
            if *operator == Operation::ImmutableAddressOf
                || *operator == Operation::MutableAddressOf =>
        {
            if let Some(var_id) = get_base_variable(operand) {
                let symbol = analyzer.symbol_table.get_value_symbol(var_id).unwrap();
                let should_heapify = if is_return_or_heap_assign {
                    is_scope_or_descendant(analyzer, symbol.scope_id, destination_scope)
                } else {
                    is_child_scope_of(analyzer, symbol.scope_id, destination_scope)
                };

                if matches!(symbol.kind, ValueSymbolKind::Variable) && should_heapify
                    && move_to_heap(analyzer, var_id)
                {
                    *changed = true;
                }
            }
        },
        MIRNodeKind::Block(statements) => {
            if let Some(last_expr) = statements.last_mut()
                && !matches!(last_expr.kind, MIRNodeKind::ExpressionStatement(_))
            {
                check_for_escape(
                    analyzer,
                    last_expr,
                    destination_scope,
                    is_return_or_heap_assign,
                    changed,
                );
            }
        },
        MIRNodeKind::IfStatement {
            then_branch,
            else_if_branches,
            else_branch,
            ..
        } => {
            check_for_escape(
                analyzer,
                then_branch,
                destination_scope,
                is_return_or_heap_assign,
                changed,
            );
            for (_, branch) in else_if_branches {
                check_for_escape(
                    analyzer,
                    branch,
                    destination_scope,
                    is_return_or_heap_assign,
                    changed,
                );
            }
            if let Some(branch) = else_branch {
                check_for_escape(
                    analyzer,
                    branch,
                    destination_scope,
                    is_return_or_heap_assign,
                    changed,
                );
            }
        },
        MIRNodeKind::FunctionCall { function: _, arguments } => {
            for arg in arguments {
                check_for_escape(
                    analyzer,
                    arg,
                    destination_scope,
                    is_return_or_heap_assign,
                    changed,
                );
            }
        },
        _ => {}
    }
}

fn get_base_variable(place: &MIRNode) -> Option<ValueSymbolId> {
    match &place.kind {
        MIRNodeKind::Identifier(_) => place.value_id,
        MIRNodeKind::FieldAccess { left, .. } => get_base_variable(left),
        MIRNodeKind::UnaryOperation { operator, .. } if *operator == Operation::Dereference => None,
        _ => None,
    }
}

fn move_to_heap(analyzer: &mut SemanticAnalyzer, var_id: ValueSymbolId) -> bool {
    let symbol = analyzer.symbol_table.get_value_symbol_mut(var_id).unwrap();
    if symbol.allocation_kind != AllocationKind::Heap {
        symbol.allocation_kind = AllocationKind::Heap;
        return true;
    }

    false
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