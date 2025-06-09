// use crate::{backend::semantic_analyzer::{PrimitiveKind, SymbolId}, frontend::ast::{AstNode, AstNodeKind, BoxedAstNode}, utils::{error::*, kind::{Operation, Span}}};
// use super::semantic_analyzer::SemanticAnalyzer;

// impl SemanticAnalyzer {
//     fn get_builtin_type(&self, builtin: PrimitiveKind) -> SymbolId {
//         self.builtins[builtin as usize].clone()
//     }

//     fn get_type_from_identifier(&self, name: &String, span: Span) -> Result<SymbolId, BoxedError> {
//         match self.symbol_table.current_scope().find_value_symbol(name, &self.symbol_table) {
//             Some(value_symbol) => {
//                 match value_symbol.type_id.clone() {
//                     Some(type_id) => Ok(type_id),
//                     None => Err(self.create_error(ErrorKind::UnresolvedType(name.to_string()), span, &[span]))
//                 }
//             },
//             None => Err(self.create_error(ErrorKind::UnknownVariable(name.to_string()), span, &[span]))
//         }
//     }

//     // fn get_type_from_unary_operation(&self, operator: Operation, operand: &mut BoxedAstNode) -> Result<SymbolId, BoxedError> {
//     //     let operand_type_id = self.associate_node_with_type(operand)?;
        
//     // }

//     fn associate_node_with_type(&self, node: &mut AstNode) -> Result<SymbolId, BoxedError> {
//         use AstNodeKind::*;

//         if let Some(id) = &node.type_id {
//             return Ok(id.clone());
//         }

//         let id = (match &mut node.kind {
//             IntegerLiteral(_) => Ok(self.get_builtin_type(PrimitiveKind::Int)),
//             FloatLiteral(_) => Ok(self.get_builtin_type(PrimitiveKind::Float)),
//             BooleanLiteral(_) => Ok(self.get_builtin_type(PrimitiveKind::Bool)),
//             StringLiteral(_) => Ok(self.get_builtin_type(PrimitiveKind::String)),
//             CharLiteral(_) => Ok(self.get_builtin_type(PrimitiveKind::Char)),
//             Identifier(name) => self.get_type_from_identifier(name, node.span),
//             // UnaryOperation { operator, operand, .. } 
//                 // => Ok(self.get_builtin_type(self.get_type_from_unary_operation(*operator, operand)?)),
//             _ => Err(self.create_error(ErrorKind::UnknownType, node.span, &[node.span])),
//         })?;

//         node.type_id = Some(id.clone());

//         Ok(id)
//     }
// }

// impl SemanticAnalyzer {
//     pub fn type_collector_pass(&mut self, program: &mut AstNode) -> Vec<Error> {
//         let mut errors = vec![];

//         if let AstNodeKind::Program(statements) = &mut program.kind {
//             for statement in statements {
//                 if let Err(err) = self.collect_type_symbol(statement) {
//                     errors.push(*err);
//                 }
//             }
//         } else {
//             unreachable!();
//         }

//         errors
//     }

//     fn collect_type_symbol(&mut self, node: &mut AstNode) -> Result<Option<SymbolId>, BoxedError> {
//         use AstNodeKind::*;

//         let declared_type_opt: Result<Option<TypeInfo>, BoxedError> = match &mut node.kind {
//             VariableDeclaration { name, mutable, type_annotation, initializer } => 
//                 self.collect_variable_type(name.clone(), *mutable, type_annotation, initializer, node.span),
//             // FunctionDeclaration { signature, body } 
//             //     => self.collect_function_declaration(signature, body, node.span),
//             // FunctionExpression { signature, body } => 
//             //     self.collect_function_expression_symbols(signature, body),
//             // StructDeclaration { name, fields, generic_parameters } =>
//             //     self.collect_struct_symbols(name.clone(), fields, generic_parameters, node.span),
//             // EnumDeclaration { name, variants } =>
//             //     self.collect_enum_symbols(name.clone(), variants, node.span),
//             // ImplDeclaration { associated_constants, associated_functions, generic_parameters, .. } =>
//             //     self.collect_impl_symbols(associated_constants, associated_functions, generic_parameters),
//             // TraitDeclaration { name, signatures } =>
//             //     self.collect_trait_symbols(name.clone(), signatures, node.span),
//             // TypeDeclaration { name, generic_parameters, .. } =>
//             //     self.collect_type_symbols(name.clone(), generic_parameters, node.span),
//             // Block(statements) =>
//             //     self.collect_block_symbols(statements),
//             _ => {
//                 for child in node.children_mut() {
//                     self.collect_type_symbol(child)?;
//                 }

//                 Ok(None)
//             }
//         };

//         if let Ok(Some(ref info)) = declared_type_opt {
//             self.associate_node_with_type(node, info);
//         }

//         declared_type_opt
//     }

//     fn collect_variable_type(
//         &mut self,
//         name: &mut String, 
//         mutable: bool, 
//         type_annotation: &mut Option<BoxedAstNode>,
//         initializer: &mut Option<BoxedAstNode>
//     ) -> Result<Option<TypeInfo>, BoxedError> {
        
//     }
// }