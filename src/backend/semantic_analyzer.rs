use std::{collections::{HashMap, HashSet}, rc::Rc};
use colored::*;
use strum::IntoEnumIterator;
use crate::{frontend::ast::AstNode, utils::{error::*, kind::*}};

pub type ScopeId = usize;
pub type ValueNameId = usize;
pub type TypeNameId = usize;
pub type ValueSymbolId = usize;
pub type TypeSymbolId = usize;

#[derive(Default, Debug)]
pub struct NameInterner {
    map: HashMap<String, usize>,
    vec: Vec<String>,
}

impl NameInterner {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, s: &str) -> usize {
        if let Some(&id) = self.map.get(s) {
            return id;
        }

        let id = self.vec.len();
        self.map.insert(s.to_string(), id);
        self.vec.push(s.to_string());

        id
    }

    pub fn lookup(&self, id: usize) -> &str {
        &self.vec[id]
    }

    pub fn get_id(&self, s: &str) -> Option<usize> {
        self.map.get(s).copied()
    }
}

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
    pub fn to_symbol_str(&self) -> &'static str {
        match self {
            PrimitiveKind::Int => INT_TYPE,
            PrimitiveKind::Float => FLOAT_TYPE,
            PrimitiveKind::Bool => BOOL_TYPE,
            PrimitiveKind::String => STRING_TYPE,
            PrimitiveKind::Char => CHAR_TYPE,
            PrimitiveKind::Null => NULL_TYPE
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeSymbolKind {
    Primitive(PrimitiveKind),
    Enum(ScopeId),
    Struct(ScopeId),
    Trait(ScopeId),
    TypeAlias(Option<TypeSymbolId>),
    FunctionSignature {
        params: Vec<TypeSymbolId>,
        return_type: TypeSymbolId,
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
    pub id: ValueSymbolId,
    pub name_id: ValueNameId,
    pub kind: ValueSymbolKind,
    pub mutable: bool,
    pub span: Option<Span>,
    pub qualifier: QualifierKind,
    pub scope_id: ScopeId,
    pub type_id: Option<TypeSymbolId>
}

#[derive(Debug, Clone)]
pub struct TypeSymbol {
    pub id: TypeSymbolId,
    pub name_id: TypeNameId,
    pub kind: TypeSymbolKind,
    pub generic_parameters: Vec<TypeSymbolId>,
    pub qualifier: QualifierKind,
    pub scope_id: ScopeId,
    pub span: Option<Span>
}

impl TypeSymbol {
    pub fn can_assign(&self, other: &TypeSymbol) -> bool {
        self.id == other.id
    }
}

#[derive(Debug)]
pub struct Scope {
    values: HashMap<ValueNameId, ValueSymbolId>,
    types: HashMap<TypeNameId, TypeSymbolId>,
    parent: Option<ScopeId>,
    id: ScopeId,
    kind: ScopeKind
}

pub struct SymbolTable {
    pub value_symbols: HashMap<ValueSymbolId, ValueSymbol>,
    pub type_symbols: HashMap<TypeSymbolId, TypeSymbol>,
    value_names: NameInterner,
    type_names: NameInterner,

    pub scopes: HashMap<ScopeId, Scope>,
    
    lines: Rc<Vec<String>>,
    current_scope_id: ScopeId,
    next_scope_id: ScopeId,
    next_value_symbol_id: ValueSymbolId,
    next_type_symbol_id: TypeSymbolId,
}

impl SymbolTable {
    pub fn new(lines: Rc<Vec<String>>) -> Self {
        let mut table = SymbolTable {
            value_symbols: HashMap::new(),
            type_symbols: HashMap::new(),
            scopes: HashMap::new(),
            value_names: NameInterner::new(),
            type_names: NameInterner::new(),
            lines: lines.clone(),
            current_scope_id: 0,
            next_scope_id: 0,
            next_value_symbol_id: 0,
            next_type_symbol_id: 0,
        };

        let root_scope_id = table.get_next_scope_id();
        let root_scope = Scope {
            values: HashMap::new(),
            types: HashMap::new(),
            parent: None,
            id: root_scope_id,
            kind: ScopeKind::Root,
        };
        table.scopes.insert(root_scope_id, root_scope);
        table.populate_with_defaults();

        let init_scope_id = table.get_next_scope_id();
        let init_scope = Scope {
            values: HashMap::new(),
            types: HashMap::new(),
            parent: Some(root_scope_id),
            id: init_scope_id,
            kind: ScopeKind::Block,
        };
        table.scopes.insert(init_scope_id, init_scope);

        table.current_scope_id = init_scope_id;

        table
    }

    fn populate_with_defaults(&mut self) {
        // PRIMITIVE TYPES //
        for ty in PrimitiveKind::iter() {
            self.add_type_symbol(
                ty.to_symbol_str(),
                TypeSymbolKind::Primitive(ty),
                vec![],
                QualifierKind::Public,
                None
            ).unwrap();
        }

        // TRAITS //
        for op in Operation::iter() {
            let (trait_name, is_binary) = op.to_trait_data();

            let fn_name = trait_name.chars().enumerate().map(|(i, c)| {
                if i != 0 && c.is_uppercase() {
                    format!("_{}", c.to_lowercase())
                } else {
                    c.to_lowercase().to_string()
                }
            }).collect::<String>();

            let scope_id = self.enter_scope(ScopeKind::Trait);

            let self_type = self.add_type_symbol(
                "Self",
                TypeSymbolKind::TypeAlias(None), 
                vec![], 
                QualifierKind::Public, 
                None
            ).unwrap_or_else(|_| panic!("[self_type] couldn't add default trait {}", trait_name));

            let output_type = self.add_type_symbol(
                "Output",
                TypeSymbolKind::TypeAlias(None), 
                vec![], 
                QualifierKind::Public, 
                None
            ).unwrap_or_else(|_| panic!("[output_type] couldn't add default trait {}", trait_name));

            self.add_type_symbol(
                &fn_name,
                TypeSymbolKind::FunctionSignature {
                    params: if is_binary {
                        vec![self_type, self_type]
                    } else {
                        vec![self_type]
                    },
                    return_type: output_type,
                    instance: Some(ReferenceKind::Value)
                }, 
                vec![], 
                QualifierKind::Public, 
                None
            ).unwrap_or_else(|_| panic!("[fn_signature] couldn't add default trait {}", trait_name));

            self.exit_scope();

            self.add_type_symbol(
                &trait_name, 
                TypeSymbolKind::Trait(scope_id), 
                vec![], 
                QualifierKind::Public, 
                None
            ).unwrap_or_else(|_| panic!("[trait] couldn't add default trait {}", trait_name));
        }
    }
    
    pub fn add_value_symbol(
        &mut self,
        name: &str,
        kind: ValueSymbolKind,
        mutable: bool,
        qualifier: QualifierKind,
        type_id: Option<TypeSymbolId>,
        span: Option<Span>,
    ) -> Result<ValueSymbolId, BoxedError> {
        let name_id = self.value_names.intern(name);
        let scope_id = self.current_scope_id;

        if let Some(existing_id) = self.scopes[&scope_id].values.get(&name_id) {
            let existing_symbol = &self.value_symbols[existing_id];
            let err = self.create_redeclaration_error(
                name.to_string(),
                existing_symbol.span,
                span
            );
            return Err(err);
        }

        let id = self.next_value_symbol_id;
        self.next_value_symbol_id += 1;

        let symbol = ValueSymbol {
            id, name_id, kind, mutable, qualifier, type_id, span, scope_id,
        };

        self.value_symbols.insert(id, symbol);
        self.current_scope_mut().values.insert(name_id, id);

        Ok(id)
    }

    pub fn add_type_symbol(
        &mut self,
        name: &str,
        kind: TypeSymbolKind,
        generic_parameters: Vec<TypeSymbolId>,
        qualifier: QualifierKind,
        span: Option<Span>,
    ) -> Result<TypeSymbolId, BoxedError> {
        let name_id = self.type_names.intern(name);
        let scope_id = self.current_scope_id;

        if let Some(existing_id) = self.scopes[&scope_id].types.get(&name_id) {
            let existing_symbol = &self.type_symbols[existing_id];
            let err = self.create_redeclaration_error(
                name.to_string(),
                existing_symbol.span,
                span
            );
            return Err(err);
        }

        let id = self.next_type_symbol_id;
        self.next_type_symbol_id += 1;

        let symbol = TypeSymbol {
            id, name_id, kind, generic_parameters, qualifier, span, scope_id,
        };

        self.type_symbols.insert(id, symbol);
        self.current_scope_mut().types.insert(name_id, id);

        Ok(id)
    }

    pub fn find_value_symbol(&self, name: &str) -> Option<&ValueSymbol> {
        let name_id = self.value_names.get_id(name)?;
        let mut scope_id = Some(self.current_scope_id);

        while let Some(id) = scope_id {
            let scope = &self.scopes[&id];
            if let Some(symbol_id) = scope.values.get(&name_id) {
                return self.value_symbols.get(symbol_id);
            }

            scope_id = scope.parent;
        }
        None
    }
    
    pub fn find_value_symbol_mut(&mut self, name: &str) -> Option<&mut ValueSymbol> {
        let name_id = self.value_names.get_id(name)?;
        let mut scope_id = Some(self.current_scope_id);

        while let Some(id) = scope_id {
            let scope = &self.scopes[&id];
            if let Some(symbol_id) = scope.values.get(&name_id) {
                return self.value_symbols.get_mut(symbol_id);
            }

            scope_id = scope.parent;
        }
        None
    }
    
    pub fn find_type_symbol(&self, name: &str) -> Option<&TypeSymbol> {
        let name_id = self.type_names.get_id(name)?;
        let mut scope_id = Some(self.current_scope_id);

        while let Some(id) = scope_id {
            let scope = &self.scopes[&id];
            if let Some(symbol_id) = scope.types.get(&name_id) {
                return self.type_symbols.get(symbol_id);
            }

            scope_id = scope.parent;
        }
        None
    }

    pub fn find_type_symbol_mut(&mut self, name: &str) -> Option<&mut TypeSymbol> {
        let name_id = self.type_names.get_id(name)?;
        let mut scope_id = Some(self.current_scope_id);

        while let Some(id) = scope_id {
            let scope = &self.scopes[&id];
            if let Some(symbol_id) = scope.types.get(&name_id) {
                return self.type_symbols.get_mut(symbol_id);
            }

            scope_id = scope.parent;
        }
        None
    }

    pub fn get_value_symbol(&self, id: ValueSymbolId) -> Option<&ValueSymbol> {
        self.value_symbols.get(&id)
    }

    pub fn get_value_symbol_mut(&mut self, id: ValueSymbolId) -> Option<&mut ValueSymbol> {
        self.value_symbols.get_mut(&id)
    }
    
    pub fn get_type_symbol(&self, id: TypeSymbolId) -> Option<&TypeSymbol> {
        self.type_symbols.get(&id)
    }

    pub fn get_type_symbol_mut(&mut self, id: TypeSymbolId) -> Option<&mut TypeSymbol> {
        self.type_symbols.get_mut(&id)
    }

    pub fn get_value_name(&self, id: ValueNameId) -> &str {
        self.value_names.lookup(id)
    }
    
    pub fn get_type_name(&self, id: TypeNameId) -> &str {
        self.type_names.lookup(id)
    }

    pub fn get_next_scope_id(&mut self) -> ScopeId {
        let new_id = self.next_scope_id;
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
            id: new_id,
            kind
        };

        self.scopes.insert(new_id, new_scope);
        self.current_scope_id = new_id;
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

    fn create_redeclaration_error(&self, name: String, span1: Option<Span>, span2: Option<Span>) -> BoxedError {
        match (span1, span2) {
            (Some(s1), Some(s2)) => Error::from_multiple_errors(
                ErrorKind::AlreadyDeclared(name),
                s2,
                Span::get_all_lines(self.lines.clone(), &[s1, s2]),
            ),
            (Some(s), None) | (None, Some(s)) => Error::from_one_error(
                ErrorKind::AlreadyDeclared(name),
                s,
                (self.lines[s.start_pos.line - 1].clone(), s.start_pos.line)
            ),
            (None, None) => Error::new(ErrorKind::AlreadyDeclared(name)),
        }
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

impl SymbolTable {
    pub fn display_value_symbol<'a>(&'a self, symbol: &'a ValueSymbol) -> impl std::fmt::Display + 'a {
        struct Displayer<'a> {
            symbol: &'a ValueSymbol,
            table: &'a SymbolTable,
        }

        impl std::fmt::Display for Displayer<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let name = self.table.get_value_name(self.symbol.name_id);
                write!(f, "{}", name.cyan().bold())?;
                write!(f, " ({})", self.symbol.kind)?;
                if self.symbol.mutable { write!(f, " {}", "mut".red())?; }
                write!(f, " {}", self.symbol.qualifier)?;
                Ok(())
            }
        }

        Displayer { symbol, table: self }
    }

    pub fn display_type_symbol<'a>(&'a self, symbol: &'a TypeSymbol) -> impl std::fmt::Display + 'a {
        struct Displayer<'a> {
            symbol: &'a TypeSymbol,
            table: &'a SymbolTable,
        }

        impl std::fmt::Display for Displayer<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let name = self.table.get_type_name(self.symbol.name_id);
                let type_variant = match &self.symbol.kind {
                    TypeSymbolKind::Struct(id) => format!("Struct({})", id).blue(),
                    TypeSymbolKind::Trait(id) => format!("Trait({})", id).cyan(),
                    TypeSymbolKind::Enum(id) => format!("Enum({})", id).blue(),
                    TypeSymbolKind::TypeAlias(id) => format!("TypeAlias({:?})", id).white(),
                    TypeSymbolKind::Primitive(k) => format!("Builtin({})", k).green(),
                    TypeSymbolKind::FunctionSignature { params, return_type, instance } => {
                        let instance_str = match instance {
                            Some(ReferenceKind::Value) => "self",
                            Some(ReferenceKind::Reference) => "&self",
                            Some(ReferenceKind::MutableReference) => "&mut self",
                            None => ""
                        };
                        let params_str = params.iter()
                            .map(|id| self.table.get_type_name(self.table.type_symbols[id].name_id))
                            .collect::<Vec<_>>()
                            .join(", ");
                        let return_type_str = self.table.get_type_name(self.table.type_symbols[return_type].name_id);
                        format!("fn({}({}), {})", instance_str, params_str, return_type_str).blue()
                    },
                    TypeSymbolKind::UnfulfilledObligation(id) => format!("UnfulfilledObligation({})", id).red(),
                    TypeSymbolKind::Custom => "Custom".white(),
                    TypeSymbolKind::Generic => "Generic".white()
                };

                write!(f, "[{}] {}", type_variant, name.cyan().bold())?;

                if !self.symbol.generic_parameters.is_empty() {
                    let params = self.symbol.generic_parameters.iter()
                        .map(|id| self.table.get_type_name(self.table.type_symbols[id].name_id))
                        .collect::<Vec<_>>().join(", ");
                    write!(f, "<{}>", params)?;
                }
                Ok(())
            }
        }
        Displayer { symbol, table: self }
    }

    fn display_scope(&self, scope_id: ScopeId, indent: usize, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let scope = self.scopes.get(&scope_id).unwrap();

        for symbol_id in scope.values.values() {
            let symbol = &self.value_symbols[symbol_id];
            writeln!(f, "{:indent$}[val] {}", "", self.display_value_symbol(symbol), indent = indent)?;
        }

        for symbol_id in scope.types.values() {
            let symbol = &self.type_symbols[symbol_id];
            writeln!(f, "{:indent$}[type] {}", "", self.display_type_symbol(symbol), indent = indent)?;
        }

        let mut child_scope_ids: Vec<ScopeId> = self.scopes.values()
            .filter(|s| s.parent == Some(scope_id))
            .map(|s| s.id)
            .collect();
        child_scope_ids.sort();

        for child_id in child_scope_ids {
            writeln!(f, "{:indent$}{{", "", indent = indent)?;
            self.display_scope(child_id, indent + 4, f)?;
            writeln!(f, "{:indent$}}}", "", indent = indent)?;
        }
        
        Ok(())
    }
}

impl std::fmt::Display for SymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Start displaying from the root scope (ID 0)
        self.display_scope(0, 0, f)
    }
}

pub struct TraitRegistry {
    pub register: HashMap<TypeSymbolId, HashSet<TypeSymbolId>>
}

impl TraitRegistry {
    pub fn new() -> Self {
        TraitRegistry { register: HashMap::new() }
    }

    pub fn register(&mut self, trait_id: TypeSymbolId, type_id: TypeSymbolId) {
        self.register.entry(trait_id)
            .or_default()
            .insert(type_id);
    }

    pub fn implements(&self, trait_id: TypeSymbolId, type_id: TypeSymbolId) -> bool {
        self.register
            .get(&trait_id)
            .map_or(false, |types| types.contains(&type_id))
    }

    pub fn types_for_trait(&self, trait_id: TypeSymbolId) -> Option<&HashSet<TypeSymbolId>> {
        self.register.get(&trait_id)
    }

    pub fn traits_for_type(&self, type_id: TypeSymbolId) -> Vec<TypeSymbolId> {
        self.register.iter()
            .filter_map(|(trait_id, types)| {
                if types.contains(&type_id) { Some(*trait_id) } else { None }
            })
            .collect()
    }
}

impl TraitRegistry {
    pub fn display<'a>(&'a self, symbol_table: &'a SymbolTable) -> impl std::fmt::Display + 'a {
        struct Displayer<'a> {
            registry: &'a TraitRegistry,
            table: &'a SymbolTable,
        }

        impl std::fmt::Display for Displayer<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                for (trait_id, types) in &self.registry.register {
                    let trait_name = self.table.get_type_name(self.table.type_symbols[trait_id].name_id);
                    writeln!(f, "{}({})", trait_name, trait_id)?;
                    for type_id in types {
                        let type_name = self.table.get_type_name(self.table.type_symbols[type_id].name_id);
                        writeln!(f, "  - {}({})", type_name, type_id)?;
                    }
                }
                Ok(())
            }
        }

        Displayer { registry: self, table: symbol_table }
    }
}

pub enum Obligations {
    TraitObligation {
        trait_kind: TypeSymbolId,
        type_kind: TypeSymbolId,
        result_type: Option<TypeSymbolId>,
        span: Span
    }
}

pub struct SemanticAnalyzer {
    pub symbol_table: SymbolTable,
    pub builtins: Vec<TypeSymbolId>,
    pub trait_registry: TraitRegistry,
    pub obligations: Vec<Obligations>,
    errors: Vec<Error>,
    lines: Rc<Vec<String>>
}

impl SemanticAnalyzer {
    pub fn new(lines: Rc<Vec<String>>) -> SemanticAnalyzer {
        let symbol_table = SymbolTable::new(lines.clone());
        
        let builtins = PrimitiveKind::iter()
            .map(|k| symbol_table.find_type_symbol(k.to_symbol_str()).unwrap().id)
            .collect();

        SemanticAnalyzer {
            symbol_table,
            builtins,
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
        writeln!(f, "{}", self.trait_registry.display(&self.symbol_table))?;
        Ok(())
    }
}