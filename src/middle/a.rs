fn get_type_from_unary_operation(&mut self, operator: Operation, operand: &mut BoxedAstNode, span: Span) -> Result<Type, BoxedError> {
    let operand_type = self.associate_node_with_type(operand)?;

    match operator {
        Operation::Dereference => {
            match operand_type {
                Type::Base { .. } => Err(self.create_error(
                    ErrorKind::InvalidDereference,
                    span,
                    &[span]
                )),
                Type::Reference(ty) => Ok(*ty.clone()),
                Type::MutableReference(ty) => Ok(*ty.clone())
            }
        },
        Operation::ImmutableAddressOf => Ok(Type::Reference(Box::new(operand_type.clone()))),
        Operation::MutableAddressOf => Ok(Type::MutableReference(Box::new(operand_type.clone()))),
        _ => {
            let (trait_name, _) = operator.to_trait_data().unwrap();
            let trait_id = self.symbol_table.find_type_symbol(&trait_name).map(|symbol| symbol.id).unwrap();

            let applicable_impl = self.trait_registry.find_applicable_impl(
                trait_id, 
                &operand_type,
                &[], 
                self,
                span
            )?;

            let output_type = self.symbol_table
                .find_type_symbol_in_scope("Output", applicable_impl.impl_scope_id)
                .ok_or(self.create_error(
                    ErrorKind::InvalidTraitImpl("Output".to_string()),
                    span,
                    &[span]
                ))?;

            let TypeSymbolKind::TypeAlias((_, inner_id)) = &output_type.kind else { unreachable!(); };
            let inner_type = inner_id.clone().ok_or(self.create_error(
                    ErrorKind::InvalidTraitImpl("Output".to_string()),
                    span,
                    &[span]
                ))?;

            Ok(inner_type)
        }
    }
}