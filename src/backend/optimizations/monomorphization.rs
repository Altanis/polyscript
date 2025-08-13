use crate::frontend::{semantics::analyzer::SemanticAnalyzer, syntax::ast::{AstNode, AstNodeKind}};

pub fn init(program: &mut AstNode, analyzer: &mut SemanticAnalyzer) {
    let AstNodeKind::Program(stmts) = &mut program.kind else { unreachable!(); };

    let mut nodes = vec![];
    for stmt in stmts {
        collect_monomorphs(stmt, analyzer, &mut nodes);
    }
}

fn collect_monomorphs(stmt: &mut AstNode, analyzer: &mut SemanticAnalyzer, nodes: &mut Vec<AstNode>) {
    

    for child in stmt.children_mut().iter_mut() {
        collect_monomorphs(child, analyzer, nodes);
    }
}
