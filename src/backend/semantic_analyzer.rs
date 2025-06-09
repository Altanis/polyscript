use std::{collections::{HashMap, HashSet}, rc::Rc};
use colored::*;
use strum::IntoEnumIterator;
use crate::{frontend::ast::AstNode, utils::{error::*, kind::*}};

pub type ScopeId = usize;
pub type SymbolId = (usize, String);

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ValueSymbolKind {
    Variable,
    Function,
    StructField,
    EnumVariant
}

#[derive(Debug, Clone, Copy, PartialEq, strum_macros::EnumIter, strum_macros::Display)]
pub enum PrimitiveKind {
    Int,
    Float,
    Bool,
    String,
    Char,
    Null
}

impl PrimitiveKind {
    pub fn to_symbol(&self) -> String {
        (match self {
            PrimitiveKind::Int => INT_TYPE,
            PrimitiveKind::Float => FLOAT_TYPE,
            PrimitiveKind::Bool => BOOL_TYPE,
            PrimitiveKind::String => STRING_TYPE,
            PrimitiveKind::Char => CHAR_TYPE,
            PrimitiveKind::Null => NULL_TYPE
        }).to_string()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeSymbolKind {
    Primitive(PrimitiveKind),
    Enum(ScopeId),
    Struct(ScopeId),
    Trait(ScopeId),
    TypeAlias(Option<SymbolId>),
    FunctionSignature {
        params: Vec<SymbolId>,
        return_type: SymbolId,
        instance: Option<ReferenceKind>
    },
    UnfulfilledObligation(usize),
    Generic,
    Custom
}


#[derive(Debug, Clone)]
pub enum ScopeKind {
    Root,
    Function,
    Block,
    Enum,
    Struct,
    Impl,
    Trait,
    Type
}

#[derive(Debug, Clone)]
pub struct ValueSymbol {
    pub name: String,
    pub kind: ValueSymbolKind,
    pub mutable: bool,
    pub span: Option<Span>,
    pub qualifier: QualifierKind,
    pub scope_id: ScopeId,
    pub type_id: Option<SymbolId>
}

#[derive(Debug, Clone)]
pub struct TypeSymbol {
    pub name: String,
    pub kind: TypeSymbolKind,
    pub generic_parameters: Vec<SymbolId>,
    pub qualifier: QualifierKind,
    pub scope_id: ScopeId,
    pub span: Option<Span>
}

impl TypeSymbol {
    pub fn can_assign(&self, other: TypeSymbol) -> bool {
        self.scope_id == other.scope_id && self.name == other.name // lol
    }
}

#[derive(Debug)]
pub struct Scope {
    values: HashMap<String, ValueSymbol>,
    types: HashMap<String, TypeSymbol>,
    parent: Option<ScopeId>,
    lines: Rc<Vec<String>>,
    id: ScopeId,
    kind: ScopeKind
}

impl Scope {
    pub fn find_value_symbol<'a>(&'a self, name: &str, symbol_table: &'a SymbolTable) -> Option<&'a ValueSymbol> {
        if let Some(symbol) = self.values.get(name) {
            Some(symbol)
        } else if let Some(parent_id) = self.parent {
            symbol_table.scopes.get(&parent_id)?.find_value_symbol(name, symbol_table)
        } else {
            None
        }
    }

    pub fn find_value_symbol_mut<'a>(&self, name: &str, symbol_table: &'a mut SymbolTable) -> Option<&'a mut ValueSymbol> {
        let owner_id = symbol_table.find_value_symbol_owner(name, self.id)?;

        symbol_table
            .scopes
            .get_mut(&owner_id)
            .and_then(|scope| scope.values.get_mut(name))
    }

    pub fn add_value_symbol(&mut self, mut symbol: ValueSymbol) -> Result<ScopeId, BoxedError> {
        symbol.scope_id = self.id;

        if let Some(existing) = self.values.get(&symbol.name) {
            let (existing_span, symbol_span) = (existing.span, symbol.span);

            match (existing_span, symbol_span) {
                (None, None) => return Err(Error::new(ErrorKind::AlreadyDeclared(symbol.name))),
                (Some(span), None) => return Err(Error::from_one_error(
                    ErrorKind::AlreadyDeclared(symbol.name),
                    span,
                    (self.lines[span.start_pos.line - 1].clone(), span.start_pos.line)
                )),
                (None, Some(span)) => return Err(Error::from_one_error(
                    ErrorKind::AlreadyDeclared(symbol.name),
                    span,
                    (self.lines[span.start_pos.line - 1].clone(), span.start_pos.line)
                )),
                (Some(existing_span), Some(symbol_span)) => {
                    return Err(Error::from_multiple_errors(
                        ErrorKind::AlreadyDeclared(symbol.name),
                        symbol_span,
                        Span::get_all_lines(self.lines.clone(), &[existing_span, symbol_span]),
                    ));
                }
            }

            // return Err(Error::from_multiple_errors(
            //     ErrorKind::AlreadyDeclared(symbol.name),
            //     symbol.span,
            //     Span::get_all_lines(self.lines.clone(), &[existing.span, symbol.span]),
            // ));
        }

        self.values.insert(symbol.name.clone(), symbol);
        Ok(self.id)
    }

    pub fn find_type_symbol<'a>(&'a self, name: &str, symbol_table: &'a SymbolTable) -> Option<&'a TypeSymbol> {
        if let Some(symbol) = self.types.get(name) {
            Some(symbol)
        } else if let Some(parent_id) = self.parent {
            symbol_table.scopes.get(&parent_id)?.find_type_symbol(name, symbol_table)
        } else {
            None
        }
    }

    pub fn find_type_symbol_mut<'a>(&self, name: &str, symbol_table: &'a mut SymbolTable) -> Option<&'a mut TypeSymbol> {
        let owner_id = symbol_table.find_type_symbol_owner(name, self.id)?;

        symbol_table
            .scopes
            .get_mut(&owner_id)
            .and_then(|scope| scope.types.get_mut(name))
    }

    pub fn add_type_symbol(&mut self, mut symbol: TypeSymbol) -> Result<ScopeId, BoxedError> {
        symbol.scope_id = self.id;

        if let Some(existing) = self.types.get(&symbol.name) {
            let (existing_span, symbol_span) = (existing.span, symbol.span);

            match (existing_span, symbol_span) {
                (None, None) => return Err(Error::new(ErrorKind::AlreadyDeclared(symbol.name))),
                (Some(span), None) => return Err(Error::from_one_error(
                    ErrorKind::AlreadyDeclared(symbol.name),
                    span,
                    (self.lines[span.start_pos.line - 1].clone(), span.start_pos.line)
                )),
                (None, Some(span)) => return Err(Error::from_one_error(
                    ErrorKind::AlreadyDeclared(symbol.name),
                    span,
                    (self.lines[span.start_pos.line - 1].clone(), span.start_pos.line)
                )),
                (Some(existing_span), Some(symbol_span)) => {
                    return Err(Error::from_multiple_errors(
                        ErrorKind::AlreadyDeclared(symbol.name),
                        symbol_span,
                        Span::get_all_lines(self.lines.clone(), &[existing_span, symbol_span]),
                    ));
                }
            }
        }

        self.types.insert(symbol.name.clone(), symbol);
        Ok(self.id)
    }
}

pub struct SymbolTable {
    pub scopes: HashMap<ScopeId, Scope>,
    lines: Rc<Vec<String>>,
    current_scope_id: ScopeId,
    next_scope_id: ScopeId,
}

impl SymbolTable {
    pub fn new(lines: Rc<Vec<String>>) -> Self {
        let mut table = SymbolTable {
            scopes: HashMap::new(),
            lines: lines.clone(),
            current_scope_id: 0,
            next_scope_id: 0
        };

        let mut root = Scope {
            values: HashMap::new(),
            types: HashMap::new(),
            parent: None,
            lines: lines.clone(),
            id: table.get_next_scope_id(),
            kind: ScopeKind::Root
        };

        SymbolTable::populate_with_defaults(&mut root, &mut table);

        let init = Scope {
            values: HashMap::new(),
            types: HashMap::new(),
            parent: Some(0),
            lines,
            id: table.get_next_scope_id(),
            kind: ScopeKind::Block
        };

        table.scopes.insert(root.id, root);
        table.scopes.insert(init.id, init);

        table
    }

    fn populate_with_defaults(scope: &mut Scope, symbol_table: &mut SymbolTable) {
        // PRIMITIVE TYPES //
        for ty in PrimitiveKind::iter() {
            scope.add_type_symbol(TypeSymbol {
                name: ty.to_symbol(),
                kind: TypeSymbolKind::Primitive(ty),
                generic_parameters: vec![],
                qualifier: QualifierKind::Public,
                scope_id: 0,
                span: None
            }).unwrap();
        }

        // for op in Operation::iter() {
        //     let (trait_name, is_binary) = op.to_trait_data();

        //     let scope_id = symbol_table.enter_scope(ScopeKind::Trait);

        //     symbol_table.current_scope_mut().add_type_symbol(TypeSymbol {
        //         name: "Output".to_string(),
        //         kind: TypeSymbolKind::Custom,
        //         generic_parameters: vec![],
        //         qualifier: QualifierKind::Public,
        //         scope_id: 0,
        //         span: None
        //     }).unwrap_or_else(|_| panic!("[output_type] couldn't add builtin trait {}", trait_name));

        //     // let self_type = symbol_table.current_scope_mut().add_type_symbol(TypeSymbol {
        //     //     name: "Self".to_uppercase(),
        //     //     kind: TypeSymbolKind::TypeAlias,
        //     //     span: None,
        //     //     qualifier: QualifierKind::Public,
        //     //     scope_id: 0,
        //     //     generic_parameters: vec![]
        //     // }).unwrap_or_else(|_| panic!("[self_type] couldn't add builtin trait {}", trait_name));

        //     symbol_table.current_scope_mut().add_type_symbol(TypeSymbol {
        //         name: trait_name.clone().to_lowercase(),
        //         kind: TypeSymbolKind::FunctionSignature {
        //             params: if is_binary {
        //                 vec![TypeSymbol {

        //                 }]
        //             } else {
        //                 vec![]
        //             },
        //             // return_type: 
        //         },
        //         span: None,
        //         qualifier: QualifierKind::Public,
        //         scope_id: 0,
        //         generic_parameters: vec![]
        //     }).unwrap_or_else(|_| panic!("[fn_signature] couldn't add builtin trait {}", trait_name));

        //     symbol_table.exit_scope();

        //     symbol_table.current_scope_mut().add_type_symbol(TypeSymbol {
        //         name: trait_name.clone(),
        //         kind: TypeSymbolKind::Trait(scope_id),
        //         generic_parameters: vec![],
        //         qualifier: QualifierKind::Public,
        //         scope_id: 0,
        //         span: None
        //     }).unwrap_or_else(|_| panic!("[trait] couldn't add builtin trait {}", trait_name));
        // }
    }

    fn find_value_symbol_owner(&self, name: &str, start_scope_id: ScopeId) -> Option<ScopeId> {
        let mut scope_id = start_scope_id;
        loop {
            let scope = &self.scopes[&scope_id];

            if scope.values.contains_key(name) {
                return Some(scope_id);
            }

            match scope.parent {
                Some(parent_id) => scope_id = parent_id,
                None => return None,
            }
        }
    }

    fn find_type_symbol_owner(&self, name: &str, start_scope_id: ScopeId) -> Option<ScopeId> {
        let mut scope_id = start_scope_id;
        loop {
            let scope = &self.scopes[&scope_id];

            if scope.types.contains_key(name) {
                return Some(scope_id);
            }

            match scope.parent {
                Some(parent_id) => scope_id = parent_id,
                None => return None,
            }
        }
    }

    pub fn direct_value_symbol_lookup(&self, (scope_id, name): &SymbolId) -> Option<&ValueSymbol> {
        self.scopes.get(scope_id).and_then(|scope| scope.values.get(name))
    }

    pub fn direct_value_symbol_lookup_mut(&mut self, (scope_id, name): &SymbolId) -> Option<&mut ValueSymbol> {
        self.scopes.get_mut(scope_id).and_then(|scope| scope.values.get_mut(name))
    }
    
    pub fn direct_type_symbol_lookup(&self, (scope_id, name): &SymbolId) -> Option<&TypeSymbol> {
        self.scopes.get(scope_id).and_then(|scope| scope.types.get(name))
    }

    pub fn direct_type_symbol_lookup_mut(&mut self, (scope_id, name): &SymbolId) -> Option<&mut TypeSymbol> {
        self.scopes.get_mut(scope_id).and_then(|scope| scope.types.get_mut(name))
    }
    
    pub fn get_next_scope_id(&mut self) -> ScopeId {
        let new_id = self.next_scope_id;
        self.current_scope_id = new_id;
        self.next_scope_id += 1;
        new_id
    }

    pub fn enter_scope(&mut self, kind: ScopeKind) -> ScopeId {
        let parent_id = self.current_scope_id;
        let new_id = self.get_next_scope_id();

        let new_scope = Scope {
            values: HashMap::new(),
            types: HashMap::new(),
            parent: Some(parent_id),
            lines: self.lines.clone(),
            id: new_id,
            kind
        };

        self.scopes.insert(new_id, new_scope);
        new_id
    }

    pub fn exit_scope(&mut self) {
        if let Some(parent_id) = self.current_scope().parent {
            self.current_scope_id = parent_id;
        } else {
            panic!("Tried to exit global scope");
        }
    }

    pub fn current_scope_mut(&mut self) -> &mut Scope {
        self.scopes.get_mut(&self.current_scope_id).expect("Scope should exist")
    }

    pub fn current_scope(&self) -> &Scope {
        self.scopes.get(&self.current_scope_id).expect("Scope should exist")
    }
}

impl std::fmt::Display for ValueSymbolKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let colored = match self {
            ValueSymbolKind::Variable => "Variable".green(),
            ValueSymbolKind::Function => "Function".blue(),
            ValueSymbolKind::StructField => "StructField".yellow(),
            ValueSymbolKind::EnumVariant => "EnumVariant".yellow(),
        };
        write!(f, "{}", colored)
    }
}

impl std::fmt::Display for ValueSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name.cyan().bold())?;
        write!(f, " ({})", self.kind)?;

        if self.mutable {
            write!(f, " {}", "mut".red())?;
        }

        write!(f, " {}", self.qualifier)?;
        
        Ok(())
    }
}

impl std::fmt::Display for TypeSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let type_variant = match &self.kind {
            TypeSymbolKind::Struct(scope_id) => format!("Struct({})", scope_id).blue(),
            TypeSymbolKind::Trait(scope_id) => format!("Trait({})", scope_id).cyan(),
            TypeSymbolKind::Enum(scope_id) => format!("Enum({})", scope_id).blue(),
            TypeSymbolKind::TypeAlias(scope_id) => format!("TypeAlias({:?})", scope_id).white(),
            TypeSymbolKind::Primitive(name) => format!("Builtin({})", name).green(),
            TypeSymbolKind::FunctionSignature { params, return_type, instance } => {
                let instance_str = match instance {
                    Some(ReferenceKind::Value) => "self",
                    Some(ReferenceKind::Reference) => "&self",
                    Some(ReferenceKind::MutableReference) => "&mut self",
                    None => ""
                };

                let params_str = params.iter()
                    .map(|(scope_id, name)| format!("{}:{}", scope_id, name))
                    .collect::<Vec<_>>()
                    .join(", ");
                
                let return_type_str = format!(": {}", return_type.1);

                format!("FunctionSignature({}({}), {})", instance_str, params_str, return_type_str).blue()
            },
            TypeSymbolKind::UnfulfilledObligation(id) => format!("UnfulfilledObligation({})", id).red(),
            TypeSymbolKind::Custom => "Custom".white(),
            TypeSymbolKind::Generic => "Generic".white()
        };

        write!(f, "[{}] {}", type_variant, self.name.cyan().bold())?;

        if !self.generic_parameters.is_empty() {
            write!(f, "<{}>", self.generic_parameters.iter().map(|(id, name)| format!("{}:{}", id, name)).collect::<Vec<_>>().join(", "))?;
        }

        Ok(())
    }
}

impl SymbolTable {
    fn display_scope(&self, scope_id: ScopeId, indent: usize, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let scope = match self.scopes.get(&scope_id) {
            Some(s) => s,
            None => return Ok(())
        };

        for symbol in scope.values.values() {
            writeln!(f, "{:indent$}[val] {}", "", symbol, indent = indent)?;
        }

        for symbol in scope.types.values() {
            writeln!(f, "{:indent$}[type] {}", "", symbol, indent = indent)?;
        }

        let mut child_scope_ids: Vec<ScopeId> = self.scopes.values()
            .filter(|s| s.parent == Some(scope_id))
            .map(|s| s.id)
            .collect();
        child_scope_ids.sort();

        for child_id in child_scope_ids {
            println!();

            writeln!(f, "{:indent$}{{", "", indent = indent)?;
            self.display_scope(child_id, indent + 4, f)?;
            writeln!(f, "{:indent$}}}", "", indent = indent)?;

            println!();
        }
        
        Ok(())
    }
}

impl std::fmt::Display for SymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.display_scope(0, 0, f)
    }
}

pub struct TraitRegistry {
    pub register: HashMap<SymbolId, HashSet<SymbolId>>
}

impl TraitRegistry {
    pub fn new() -> Self {
        TraitRegistry { register: HashMap::new() }
    }

    pub fn register(&mut self, trait_id: SymbolId, type_id: SymbolId) {
        self.register.entry(trait_id)
            .or_default()
            .insert(type_id);
    }

    pub fn implements(&self, trait_id: &SymbolId, type_id: &SymbolId) -> bool {
        self.register
            .get(trait_id)
            .map_or(false, |types| types.contains(type_id))
    }

    pub fn types_for_trait(&self, trait_id: &SymbolId) -> Option<&HashSet<SymbolId>> {
        self.register.get(trait_id)
    }

    pub fn traits_for_type(&self, type_id: &SymbolId) -> Vec<SymbolId> {
        self.register.iter()
            .filter_map(|(trait_id, types)| {
                if types.contains(type_id) {
                    Some(trait_id.clone())
                } else {
                    None
                }
            })
            .collect()
    }
}

impl std::fmt::Display for TraitRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for ((trait_scope, trait_name), types) in &self.register {
            writeln!(f, "{}({})", trait_name, trait_scope)?;
            for (type_scope, type_name) in types {
                writeln!(f, "  - {}({})", type_name, type_scope)?;
            }
        }
        Ok(())
    }
}

pub enum Obligations {
    TraitObligation {
        trait_kind: SymbolId,
        type_kind: SymbolId,
        result_type: Option<SymbolId>,
        span: Span
    }
}

pub struct SemanticAnalyzer {
    pub symbol_table: SymbolTable,
    pub builtins: Vec<SymbolId>,
    pub trait_registry: TraitRegistry,
    pub obligations: Vec<Obligations>,
    errors: Vec<Error>,
    lines: Rc<Vec<String>>
}

impl SemanticAnalyzer {
    pub fn new(lines: Rc<Vec<String>>) -> SemanticAnalyzer {
        SemanticAnalyzer {
            symbol_table: SymbolTable::new(lines.clone()),
            builtins: PrimitiveKind::iter().map(|k| (0, k.to_symbol())).collect(),
            trait_registry: TraitRegistry::new(),
            obligations: vec![],
            errors: vec![],
            lines
        }
    }

    pub fn create_error(&self, kind: ErrorKind, primary_span: Span, spans: &[Span]) -> BoxedError {
        let lines = Span::get_all_lines(self.lines.clone(), spans);
        Error::from_multiple_errors(kind, primary_span, lines)
    }

    pub fn analyze(&mut self, mut program: AstNode) -> Result<AstNode, Vec<Error>> {
        /* PASS STRUCTURE
            * 0: Collect all symbols and place into symbol table. Tag AST nodes with symbol references.
            * 1: Collect type information for symbols.
            * 2: Trait linking.
            * 3: Obligation resolution.
         */

        macro_rules! pass {
            ($self:ident, $method:ident, $program:expr) => {{
                let errors = $self.$method(&mut $program);
                if !errors.is_empty() {
                    return Err(errors);
                }
            }};
        }


        pass!(self, symbol_collector_pass, &mut program);
        // pass!(self, type_collector_pass, &mut program);

        Ok(program)
    }
}

impl std::fmt::Display for SemanticAnalyzer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Symbol Table:")?;
        writeln!(f, "{}", self.symbol_table)?;
        writeln!(f, "\nTrait Registry:")?;
        writeln!(f, "{}", self.trait_registry)?;
        Ok(())
    }
}