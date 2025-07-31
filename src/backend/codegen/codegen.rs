use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::BasicTypeEnum;
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue};
use std::collections::HashMap;

use crate::frontend::semantics::analyzer::{NameInterner, SemanticAnalyzer, TypeSymbolId, ValueSymbolId};
use crate::frontend::syntax::ast::{AstNode, AstNodeKind};

pub type StringLiteralId = usize;

pub struct CodeGen<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    
    analyzer: &'a SemanticAnalyzer,

    variables: HashMap<ValueSymbolId, PointerValue<'ctx>>,
    functions: HashMap<ValueSymbolId, FunctionValue<'ctx>>,

    string_interner: NameInterner,
    string_literals: HashMap<StringLiteralId, PointerValue<'ctx>>,
    
    current_function: Option<FunctionValue<'ctx>>,
    
    type_map: HashMap<TypeSymbolId, BasicTypeEnum<'ctx>>,
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    fn compile_integer_literal(&mut self, value: i64) -> BasicValueEnum<'ctx> {
        self.context.i64_type()
            .const_int(value as u64, true)
            .as_basic_value_enum()
    }

    fn compile_float_literal(&mut self, value: f64) -> BasicValueEnum<'ctx> {
        self.context.f64_type()
            .const_float(value)
            .as_basic_value_enum()
    }

    fn compile_bool_literal(&mut self, value: bool) -> BasicValueEnum<'ctx> {
        self.context.bool_type()
            .const_int(value as u64, false)
            .as_basic_value_enum()
    }

    fn compile_string_literal(&mut self, value: &String) -> BasicValueEnum<'ctx> {
        let key = self.string_interner.intern(value);
        if let Some(ptr) = self.string_literals.get(&key) {
            return ptr.as_basic_value_enum();
        }

        let string_const = self.context.const_string(value.as_bytes(), true);

        let global = self.module.add_global(string_const.get_type(), None, "");
        global.set_initializer(&string_const);
        global.set_constant(true);
        global.set_linkage(Linkage::Private);

        let ptr_type = string_const.get_type();
        let zero = self.context.i32_type().const_int(0, false);

        let ptr = unsafe {
            self.builder.build_gep(
                ptr_type, 
                global.as_pointer_value(), 
                &[zero, zero], 
                ""
            ).unwrap()
        };

        self.string_literals.insert(key, ptr);
        ptr.as_basic_value_enum()
    }

    fn compile_char_literal(&mut self, value: char) -> BasicValueEnum<'ctx> {
        self.context.i8_type()
            .const_int(value as u8 as u64, false)
            .as_basic_value_enum()
    }
}

impl<'a, 'ctx> CodeGen<'a, 'ctx> {
    pub fn new(context: &'ctx Context, builder: &'a Builder<'ctx>, module: &'a Module<'ctx>, analyzer: &'a SemanticAnalyzer) -> Self {
        CodeGen {
            context,
            builder,
            module,
            analyzer,
            variables: HashMap::new(),
            functions: HashMap::new(),
            string_interner: NameInterner::new(),
            string_literals: HashMap::new(),
            current_function: None,
            type_map: HashMap::new(),
        }
    }

    pub fn compile_program(&mut self, program: &AstNode) {
        let AstNodeKind::Program(stmts) = &program.kind else { unreachable!(); };
        for stmt in stmts.iter() {
            self.compile_node(stmt);
        }
    }

    fn compile_node(&mut self, stmt: &AstNode) -> BasicValueEnum<'ctx> {
        match &stmt.kind {
            AstNodeKind::IntegerLiteral(value) => self.compile_integer_literal(*value),
            AstNodeKind::FloatLiteral(value) => self.compile_float_literal(*value),
            AstNodeKind::BooleanLiteral(value) => self.compile_bool_literal(*value),
            AstNodeKind::StringLiteral(value) => self.compile_string_literal(value),
            AstNodeKind::CharLiteral(value) => self.compile_char_literal(*value),
            _ => unimplemented!()
        }
    }
}