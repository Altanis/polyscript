use std::{collections::HashMap, rc::Rc};
use colored::*;
use crate::{frontend::ast::AstNode, utils::{error::*, kind::*}};

pub type ScopeId = usize;

#[derive(Debug, Clone)]
pub enum SymbolKind {
    Variable,
    Function,
    Struct(ScopeId),
    Enum(ScopeId),
    Trait(ScopeId),
    TypeAlias,
    StructField,
    EnumVariant
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
pub struct Symbol {
    pub name: String,
    pub kind: SymbolKind,
    pub type_info: Option<TypeInfo>,
    pub mutable: bool,
    pub span: Span,
    pub qualifier: Option<QualifierKind>,
    pub generic_parameters: Vec<TypeInfo>,
    pub scope_id: ScopeId
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeInfo {
    pub base_type: String,
    pub generic_parameters: Vec<TypeInfo>,
    pub function_data: Option<FunctionTypeData>,
    pub reference_kind: ReferenceKind,
    pub scope_reference: Option<ScopeId>
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionTypeData {
    pub params: Vec<TypeInfo>,
    pub return_type: Option<Box<TypeInfo>>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ReferenceKind {
    Value,
    Reference,
    MutableReference,
}

impl TypeInfo {
    pub fn new(base_type: impl Into<String>, generic_parameters: Vec<TypeInfo>, reference_kind: ReferenceKind) -> Self {
        Self {
            base_type: base_type.into(),
            generic_parameters,
            function_data: None,
            reference_kind,
            scope_reference: None
        }
    }

    pub fn from_scope_reference(
        base_type: impl Into<String>, 
        generic_parameters: Vec<TypeInfo>, 
        reference_kind: ReferenceKind, 
        scope_reference: ScopeId
    ) -> Self {
        Self {
            base_type: base_type.into(),
            generic_parameters,
            function_data: None,
            reference_kind,
            scope_reference: Some(scope_reference)
        }
    }

    pub fn from_function_expression(generic_parameters: Vec<TypeInfo>, function_data: FunctionTypeData) -> Self {
        Self {
            base_type: String::new(),
            generic_parameters,
            function_data: Some(function_data),
            reference_kind: ReferenceKind::Value,
            scope_reference: None
        }
    }
}

#[derive(Debug)]
pub struct Scope {
    variables: HashMap<String, Symbol>,
    parent: Option<ScopeId>,
    lines: Rc<Vec<String>>,
    id: ScopeId,
    kind: ScopeKind
}

impl Scope {
    pub fn find_symbol<'a>(&'a self, name: &str, symbol_table: &'a SymbolTable) -> Option<&'a Symbol> {
        if let Some(symbol) = self.variables.get(name) {
            Some(symbol)
        } else if let Some(parent_id) = self.parent {
            symbol_table.scopes.get(&parent_id)?.find_symbol(name, symbol_table)
        } else {
            None
        }
    }

    pub fn find_symbol_mut<'a>(&self, name: &str, symbol_table: &'a mut SymbolTable) -> Option<&'a mut Symbol> {
        let owner_id = symbol_table.find_symbol_owner(name, self.id)?;

        symbol_table
            .scopes
            .get_mut(&owner_id)
            .and_then(|scope| scope.variables.get_mut(name))
    }

    pub fn add_symbol(&mut self, mut symbol: Symbol) -> Result<ScopeId, BoxedError> {
        symbol.scope_id = self.id;

        if let Some(existing) = self.variables.get(&symbol.name) {
            return Err(Error::from_multiple_errors(
                ErrorKind::AlreadyDeclared(symbol.name),
                symbol.span,
                Span::get_all_lines(self.lines.clone(), &[existing.span, symbol.span]),
            ));
        }

        self.variables.insert(symbol.name.clone(), symbol);
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
        let mut root_scope = Scope {
            variables: HashMap::new(),
            parent: None,
            lines: lines.clone(),
            id: 0,
            kind: ScopeKind::Root
        };

        SymbolTable::populate_with_defaults(&mut root_scope);

        let mut scopes = HashMap::new();
        scopes.insert(0, root_scope);

        SymbolTable {
            scopes,
            lines,
            current_scope_id: 0,
            next_scope_id: 1,
        }
    }

    fn populate_with_defaults(scope: &mut Scope) {
        for ty in [INT_TYPE, FLOAT_TYPE, BOOL_TYPE, STRING_TYPE, CHAR_TYPE, NULL_TYPE] {
            scope.add_symbol(Symbol {
                name: ty.clone(),
                kind: SymbolKind::TypeAlias,
                type_info
            })
        }
    }

    fn find_symbol_owner(&self, name: &str, start_scope_id: ScopeId) -> Option<ScopeId> {
        let mut scope_id = start_scope_id;
        loop {
            let scope = &self.scopes[&scope_id];
            if scope.variables.contains_key(name) {
                return Some(scope_id);
            }
            match scope.parent {
                Some(parent_id) => scope_id = parent_id,
                None => return None,
            }
        }
    }

    pub fn direct_symbol_lookup(&mut self, scope_id: ScopeId, name: &str) -> Option<&mut Symbol> {
        self.scopes.get_mut(&scope_id).and_then(|scope| scope.variables.get_mut(name))
    }
    
    pub fn enter_scope(&mut self, kind: ScopeKind) -> ScopeId {
        let new_id = self.next_scope_id;
        let parent_id = self.current_scope_id;

        let new_scope = Scope {
            variables: HashMap::new(),
            parent: Some(parent_id),
            lines: self.lines.clone(),
            id: new_id,
            kind
        };

        self.scopes.insert(new_id, new_scope);
        self.current_scope_id = new_id;
        self.next_scope_id += 1;

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

impl std::fmt::Display for SymbolKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let colored = match self {
            SymbolKind::Variable => "Variable".green(),
            SymbolKind::Function => "Function".blue(),
            SymbolKind::Struct(scope_id) => format!("Struct({})", scope_id).blue(),
            SymbolKind::Trait(scope_id) => format!("Trait({})", scope_id).cyan(),
            SymbolKind::Enum(scope_id) => format!("Enum({})", scope_id).blue(),
            SymbolKind::TypeAlias => "TypeAlias".white(),
            SymbolKind::StructField => "StructField".yellow(),
            SymbolKind::EnumVariant => "EnumVariant".yellow(),
        };
        write!(f, "{}", colored)
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name.cyan().bold())?;
        write!(f, " ({})", self.kind)?;

        if let Some(type_info) = &self.type_info {
            write!(f, " : {}", type_info)?;
        } else {
            write!(f, " : undetermined_type")?;
        }
        
        if self.mutable {
            write!(f, " {}", "mut".red())?;
        }

        if let Some(qualifier) = self.qualifier {
            write!(f, " {}", qualifier)?;
        }
        
        if !self.generic_parameters.is_empty() {
            let generics = self.generic_parameters.iter()
                .map(|g| g.to_string().dimmed().to_string())
                .collect::<Vec<_>>()
                .join(", ");
            write!(f, " <{}>", generics)?;
        }
        
        Ok(())
    }
}

impl std::fmt::Display for TypeInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let reference = match self.reference_kind {
            ReferenceKind::Value => "".normal(),
            ReferenceKind::Reference => "&".red(),
            ReferenceKind::MutableReference => "&mut ".red().bold(),
        };

        if let Some(func_data) = &self.function_data {
            return write!(f, "{}{}", reference, func_data);
        }

        let base = self.base_type.yellow().bold();
        let generics = if !self.generic_parameters.is_empty() {
            format!("<{}>", 
                self.generic_parameters.iter()
                    .map(|g| g.to_string().blue().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        } else {
            String::new()
        };

        write!(f, "{}{}{}", reference, base, generics)
    }
}

impl std::fmt::Display for FunctionTypeData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let params = self.params.iter()
            .map(|p| p.to_string().green().to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "({})", params)?;

        if let Some(return_type) = &self.return_type {
            let return_type = return_type.to_string().magenta();
            write!(f, ": {}", return_type)?;
        }

        Ok(())
    }
}

impl std::fmt::Display for SymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.display_scope(0, 0, f)
    }
}

impl SymbolTable {
    fn display_scope(&self, scope_id: ScopeId, indent: usize, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let scope = match self.scopes.get(&scope_id) {
            Some(s) => s,
            None => return Ok(())
        };

        for symbol in scope.variables.values() {
            writeln!(f, "{:indent$}{}", "", symbol, indent = indent)?;
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

pub struct SemanticAnalyzer {
    pub symbol_table: SymbolTable,
    errors: Vec<Error>,
    lines: Rc<Vec<String>>
}

impl SemanticAnalyzer {
    pub fn new(lines: Rc<Vec<String>>) -> SemanticAnalyzer {
        SemanticAnalyzer {
            symbol_table: SymbolTable::new(lines.clone()),
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


            * 2: Verify type information is correct.
                * Verify operator is valid on certain types (Unary/BinaryOp).
                * Verify lhs and rhs resolve to `bool` (ConditionalOp).
                * Verify return type of function matches with explicit return type.
                * 
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