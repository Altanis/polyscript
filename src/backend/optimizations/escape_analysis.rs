use crate::{frontend::{
    semantics::analyzer::{AllocationKind, ScopeKind, SemanticAnalyzer, Type, ValueSymbolId, ValueSymbolKind},
    syntax::ast::{AstNode, AstNodeKind},
}, utils::kind::Operation};

pub fn init(program: &mut AstNode, analyzer: &mut SemanticAnalyzer) {
    loop {
        if !analysis_pass(analyzer, program) {
            break;
        }
    }
    
    for symbol in analyzer.symbol_table.value_symbols.values_mut() {
        if let ValueSymbolKind::Variable = symbol.kind
            && symbol.allocation_kind == AllocationKind::Unresolved
        {
            symbol.allocation_kind = AllocationKind::Stack;
        }
    }
}

fn scan_and_heapify_locals(
    analyzer: &mut SemanticAnalyzer,
    expr: &mut AstNode,
    scope_context: usize,
    changed: &mut bool,
) {
    let mut worklist = vec![expr];

    while let Some(current) = worklist.pop() {
        if let Some(id) = get_id_of_referenced_local(analyzer, current, scope_context)
            && move_to_heap(analyzer, id)
        {
            *changed = true;
        }

        for child in current.children_mut() {
            worklist.push(child);
        }
    }
}

fn analysis_pass(analyzer: &mut SemanticAnalyzer, node: &mut AstNode) -> bool {
    let mut changed = false;
    
    for child in node.children_mut() {
        if analysis_pass(analyzer, child) {
            changed = true;
        }
    }
    
    let scope_context = node.scope_id.unwrap();
    
    match &mut node.kind {
        AstNodeKind::Return(Some(expr)) => scan_and_heapify_locals(analyzer, expr, scope_context, &mut changed),
        AstNodeKind::Function { body: Some(body_node), .. } => {
            if let AstNodeKind::Block(statements) = &mut body_node.kind
                && let Some(last_expr) = statements.last_mut()
                && !matches!(last_expr.kind, AstNodeKind::ExpressionStatement(_))
            {
                let last_expr_scope = last_expr.scope_id.unwrap();
                scan_and_heapify_locals(analyzer, last_expr, last_expr_scope, &mut changed);
            }
        },
        AstNodeKind::BinaryOperation { operator, left, right } if operator.is_assignment() => {
            if is_escaping_place(analyzer, left) {
                scan_and_heapify_locals(analyzer, right, scope_context, &mut changed);
            }
        },
        AstNodeKind::FunctionCall { arguments, .. } => {
            for arg in arguments {
                scan_and_heapify_locals(analyzer, arg, scope_context, &mut changed);
            }
        },
        AstNodeKind::VariableDeclaration { initializer, .. } => {
            let var_id = node.value_id.unwrap();
            let var_scope = analyzer.symbol_table.get_value_symbol(var_id).unwrap().scope_id;
            
            let mut worklist = vec![initializer.as_mut()];
            while let Some(current) = worklist.pop() {
                if let Some(init_id) = get_id_of_referenced_local(analyzer, current, scope_context) {
                    let init_var_scope = analyzer.symbol_table.get_value_symbol(init_id).unwrap().scope_id;
                    if is_scope_outlived_by(analyzer, init_var_scope, var_scope)
                        && move_to_heap(analyzer, init_id)
                    {
                        changed = true;
                    }
                }

                worklist.extend(current.children_mut());
            }
        },
        AstNodeKind::HeapExpression(expr) => {
            scan_and_heapify_locals(analyzer, expr, scope_context, &mut changed);
        },
        _ => {}
    }
    
    changed
}


fn get_id_of_referenced_local(analyzer: &SemanticAnalyzer, expr: &AstNode, current_scope: usize) -> Option<ValueSymbolId> {
    let operand = if let AstNodeKind::UnaryOperation { operator, operand } = &expr.kind {
        if *operator == Operation::ImmutableAddressOf || *operator == Operation::MutableAddressOf {
            operand
        } else {
            return None;
        }
    } else {
        return None;
    };
    
    if let Some(var_id) = operand.value_id {
        let symbol = analyzer.symbol_table.get_value_symbol(var_id).unwrap();
        
        if !matches!(symbol.kind, ValueSymbolKind::Variable) {
            return None;
        }
        
        let fn_scope = get_function_scope(analyzer, current_scope)?;
        if is_in_scope(analyzer, symbol.scope_id, fn_scope) {
            return Some(var_id);
        }
    }
    None
}

fn is_escaping_place(analyzer: &SemanticAnalyzer, place: &AstNode) -> bool {
    match &place.kind {
        AstNodeKind::Identifier(_) => {
            let place_id = place.value_id.unwrap();
            let place_symbol = analyzer.symbol_table.get_value_symbol(place_id).unwrap();
            place_symbol.allocation_kind == AllocationKind::Heap
        }
        AstNodeKind::FieldAccess { left, .. } => {
            if let Some(ty) = &left.type_id
                && matches!(ty, Type::Reference(_) | Type::MutableReference(_))
            {
                return true;
            }

            is_escaping_place(analyzer, left)
        }
        _ => false,
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

fn is_in_scope(analyzer: &SemanticAnalyzer, descendant_candidate: usize, ancestor_candidate: usize) -> bool {
    let mut current_id = Some(descendant_candidate);
    while let Some(id) = current_id {
        if id == ancestor_candidate {
            return true;
        }

        current_id = analyzer.symbol_table.get_scope(id).unwrap().parent;
    }
    false
}

fn is_scope_outlived_by(analyzer: &SemanticAnalyzer, inner_scope: usize, outer_scope: usize) -> bool {
    is_in_scope(analyzer, inner_scope, outer_scope) && inner_scope != outer_scope
}