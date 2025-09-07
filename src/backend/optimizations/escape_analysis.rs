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
            Err(e) => errors.push(*e)
        }
    }

    errors
}

fn heapify_if_local(
    analyzer: &mut SemanticAnalyzer,
    value_node: &mut MIRNode,
    current_function_scope_id: usize,
) -> Result<bool, BoxedError> {
    let mut changed = false;

    if let MIRNodeKind::StructLiteral { fields, .. } = &mut value_node.kind {
        for field_expr in fields.values_mut() {
            changed |= heapify_if_local(analyzer, field_expr, current_function_scope_id)?;
        }
        return Ok(changed);
    }

    if let Some(var_id) = get_base_variable(value_node) {
        let symbol = analyzer.symbol_table.get_value_symbol(var_id).unwrap();
        
        if matches!(symbol.kind, ValueSymbolKind::Variable) && is_scope_or_descendant(analyzer, symbol.scope_id, current_function_scope_id) {
            let symbol_type = symbol.type_id.as_ref().unwrap();
            
            if !is_primitive(analyzer, symbol_type) && !is_fn_ptr(analyzer, symbol_type) && !is_str_primitive(analyzer, symbol_type) {
                return move_to_heap(analyzer, var_id);
            }
        }
    }
    Ok(changed)
}

fn analysis_pass(analyzer: &mut SemanticAnalyzer, node: &mut MIRNode) -> Result<bool, BoxedError> {
    let mut changed = false;

    for child in node.children_mut() {
        changed |= analysis_pass(analyzer, child)?;
    }

    match &mut node.kind {
        MIRNodeKind::Return(Some(expr)) => {
            if let Some(function_scope) = get_function_scope(analyzer, node.scope_id) {
                changed |= heapify_if_local(analyzer, expr, function_scope)?;
            }
        }

        MIRNodeKind::Function { body: Some(body_node), .. } => {
            if let MIRNodeKind::Block(statements) = &mut body_node.kind
                && let Some(last_expr) = statements.last_mut()
                && !matches!(last_expr.kind, MIRNodeKind::ExpressionStatement(_))
                && let Some(function_scope) = get_function_scope(analyzer, node.scope_id)
            {
                changed |= heapify_if_local(analyzer, last_expr, function_scope)?;
            }
        },

        MIRNodeKind::BinaryOperation { operator: Operation::Assign, left, right } => {
            if let Some(base_var_id) = get_base_variable(left)
                && let Some(func_scope) = get_function_scope(analyzer, node.scope_id)
            {
                let symbol = analyzer.symbol_table.get_value_symbol(base_var_id).unwrap();
                if !is_scope_or_descendant(analyzer, symbol.scope_id, func_scope) {
                    changed |= heapify_if_local(analyzer, right, func_scope)?;
                }
            }
        },

        MIRNodeKind::FunctionCall { arguments, .. } => {
            if let Some(func_scope) = get_function_scope(analyzer, node.scope_id) {
                for arg in arguments.iter_mut() {
                    if let MIRNodeKind::UnaryOperation { operator, operand } = &mut arg.kind
                        && (*operator == Operation::ImmutableAddressOf || *operator == Operation::MutableAddressOf)
                    {
                        changed |= heapify_if_local(analyzer, operand, func_scope)?;
                    }
                }
            }
        }

        MIRNodeKind::VariableDeclaration { initializer, .. } => {
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

fn get_base_variable(place: &MIRNode) -> Option<ValueSymbolId> {
    match &place.kind {
        MIRNodeKind::Identifier(_) => place.value_id,
        MIRNodeKind::FieldAccess { left, .. } => get_base_variable(left),
        MIRNodeKind::UnaryOperation { operator, .. } if *operator == Operation::Dereference => None,
        _ => None,
    }
}

fn move_to_heap(analyzer: &mut SemanticAnalyzer, var_id: ValueSymbolId) -> Result<bool, BoxedError> {
    let heap_type_id = analyzer.get_heap_type();
    
    let symbol = analyzer.symbol_table.get_value_symbol(var_id).unwrap();
    let is_already_heap = analyzer.is_heap_type(symbol.type_id.as_ref().unwrap());

    if matches!(symbol.kind, ValueSymbolKind::Variable) && !is_already_heap {
        let (name_id, span) = {
            let symbol = analyzer.symbol_table.get_value_symbol_mut(var_id).unwrap();
            let original_type = symbol.type_id.as_ref().unwrap().clone();
            symbol.type_id = Some(Type::Base { symbol: heap_type_id, args: vec![original_type] });
            (symbol.name_id, symbol.span)
        };
        
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