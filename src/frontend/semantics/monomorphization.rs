use crate::{frontend::{semantics::analyzer::SemanticAnalyzer, syntax::ast::{AstNode, AstNodeKind}}, utils::{error::Error, kind::Span}};

fn find_node_by_span_mut(node: &mut AstNode, target_span: Span) -> Option<&mut AstNode> {
    if node.span == target_span {
        return Some(node);
    }

    for child in node.children_mut() {
        if let Some(found) = find_node_by_span_mut(child, target_span) {
            return Some(found);
        }
    }

    None
}

impl SemanticAnalyzer {
    pub fn monomorphization_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
        let requests = std::mem::take(&mut self.unification_context.monomorphization_requests);
        for (span, types) in requests {
            if let Some(node) = find_node_by_span_mut(program, span) 
                && let AstNodeKind::FunctionCall { ref mut generic_arguments, .. } = node.kind
            {
                *generic_arguments = Some(types);
            }
        }

        vec![]
    }
}