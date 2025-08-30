use crate::{
    frontend::semantics::analyzer::{SemanticAnalyzer, Type, TypeSymbolKind},
    mir::ir_node::{CaptureStrategy, MIRNode, MIRNodeKind}, utils::kind::Operation
};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum UsageKind {
    NoUsage,
    ByValue,
    ByReference,
    ByMutableReference,
}

pub fn init(program: &mut MIRNode, analyzer: &SemanticAnalyzer) {
    analyze_node_for_closures(program, analyzer);
}

fn analyze_node_for_closures(node: &mut MIRNode, analyzer: &SemanticAnalyzer) {
    if let MIRNodeKind::Function { captures, body: Some(body), .. } = &mut node.kind && !captures.is_empty() {
        let capture_usages: HashMap<usize, UsageKind> = captures
            .iter()
            .map(|capture| {
                let capture_id = capture.value_id.unwrap();
                (capture_id, find_variable_usage(body, capture_id, analyzer))
            })
            .collect();

        for capture in captures.iter_mut() {
            if let MIRNodeKind::EnvironmentCapture { strategy, .. } = &mut capture.kind {
                let capture_id = capture.value_id.unwrap();
                let usage = capture_usages.get(&capture_id).copied().unwrap_or(UsageKind::NoUsage);
                *strategy = match usage {
                    UsageKind::ByMutableReference => CaptureStrategy::MutableReference,
                    UsageKind::ByReference => CaptureStrategy::Reference,
                    UsageKind::ByValue | UsageKind::NoUsage => CaptureStrategy::Copy
                }
            }
        }
    }

    for child in node.children_mut() {
        analyze_node_for_closures(child, analyzer);
    }
}

fn find_variable_usage(node: &MIRNode, target_id: usize, analyzer: &SemanticAnalyzer) -> UsageKind {
    let mut max_usage = UsageKind::NoUsage;

    for child in node.children() {
        max_usage = max_usage.max(find_variable_usage(child, target_id, analyzer));
    }

    let current_node_usage = match &node.kind {
        MIRNodeKind::BinaryOperation { operator, left, .. } if operator.is_assignment() => {
            if get_base_variable(left) == Some(target_id) { UsageKind::ByMutableReference } else { UsageKind::NoUsage }
        },
        MIRNodeKind::UnaryOperation { operator, operand } => {
            if get_base_variable(operand) == Some(target_id) {
                match operator {
                    Operation::MutableAddressOf => UsageKind::ByMutableReference,
                    Operation::ImmutableAddressOf => UsageKind::ByReference,
                    _ => UsageKind::ByValue
                }
            } else {
                UsageKind::NoUsage
            }
        }
        MIRNodeKind::Identifier(_) if node.value_id == Some(target_id) => UsageKind::ByValue,
        MIRNodeKind::FunctionCall { function, arguments } => {
            let mut call_site_usage = UsageKind::NoUsage;

            if let Some(fn_type) = &function.type_id {
                let fn_type_symbol = analyzer.symbol_table.get_type_symbol(fn_type.get_base_symbol()).unwrap();
                if let TypeSymbolKind::FunctionSignature { params, .. } = &fn_type_symbol.kind {
                    for (i, arg_node) in arguments.iter().enumerate() {
                        if get_base_variable(arg_node) == Some(target_id) && let Some(param_type) = params.get(i) {
                            let usage_from_param = match param_type {
                                Type::MutableReference { .. } => UsageKind::ByMutableReference,
                                Type::Reference { .. } => UsageKind::ByReference,
                                _ => UsageKind::ByValue
                            };

                            call_site_usage = call_site_usage.max(usage_from_param);
                        }
                    }
                }
            }
            call_site_usage
        },
        _ => UsageKind::NoUsage,
    };

    max_usage.max(current_node_usage)
}

fn is_copy_type(analyzer: &SemanticAnalyzer, ty: &Type) -> bool {
    match ty {
        Type::Base { symbol, .. } => {
            if let Some(type_symbol) = analyzer.symbol_table.get_type_symbol(*symbol) {
                matches!(type_symbol.kind, TypeSymbolKind::Primitive(_) | TypeSymbolKind::FunctionSignature { .. } | TypeSymbolKind::Enum(_))
            } else { false }
        },
        Type::Reference { .. } | Type::MutableReference { .. } => true
    }
}

fn get_base_variable(node: &MIRNode) -> Option<usize> {
    match &node.kind {
        MIRNodeKind::Identifier(_) => node.value_id,
        MIRNodeKind::FieldAccess { left, .. } => get_base_variable(left),
        MIRNodeKind::UnaryOperation { operator: Operation::Dereference, .. } => None,
        _ => None,
    }
}