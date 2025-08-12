use std::collections::HashMap;

use crate::frontend::{semantics::analyzer::{SemanticAnalyzer, Type, TypeSymbolId}, syntax::ast::{AstNode, AstNodeKind}};

pub fn init(program: &mut AstNode, analyzer: &mut SemanticAnalyzer) {
    dbg!(&analyzer.unification_context.monomorphization_requests);
}