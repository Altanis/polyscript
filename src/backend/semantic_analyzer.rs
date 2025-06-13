use std::{collections::HashMap, rc::Rc};
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
    Function(ScopeId),
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

#[derive(Debug, Clone)]
pub struct InherentImpl {
    pub scope_id: ScopeId,
    pub specialization: Vec<TypeSymbolId>,
    pub generic_params: Vec<TypeSymbolId>
}

#[derive(Debug, Clone)]
pub struct TraitImpl {
    pub impl_scope_id: ScopeId,
    pub impl_generic_params: Vec<TypeSymbolId>,
    pub trait_generic_specialization: Vec<TypeSymbolId>,
    pub type_specialization: Vec<TypeSymbolId>
}


#[derive(Debug, Clone)]
pub enum TypeSymbolKind {
    Primitive(PrimitiveKind),
    Enum((ScopeId, Vec<InherentImpl>)),
    Struct((ScopeId, Vec<InherentImpl>)),
    Trait(ScopeId),
    TypeAlias((Option<ScopeId>, Option<TypeSymbolId>)),
    FunctionSignature {
        params: Vec<Type>,
        return_type: Type,
        instance: Option<ReferenceKind>
    },
    UnfulfilledObligation(usize),
    Generic(Vec<TypeSymbolId>),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Base {
        symbol: TypeSymbolId,
        args: Vec<Type>,
    },
    Reference(Box<Type>),
    MutableReference(Box<Type>),
}

impl Type {
    pub fn new_base(symbol: TypeSymbolId) -> Self {
        Type::Base { symbol, args: vec![] }
    }

    pub fn is_base(&self) -> bool {
        matches!(self, Type::Base { .. })
    }

    pub fn is_equivalent(&self, other: &Type) -> bool {
        // unification algorithm soon
        self == other
    }

    pub fn get_base_symbol(&self) -> TypeSymbolId {
        match self {
            Type::Base { symbol, .. } => *symbol,
            Type::Reference(inner) | Type::MutableReference(inner) => inner.get_base_symbol(),
        }
    }
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
    pub type_id: Option<Type>
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
    pub values: HashMap<ValueNameId, ValueSymbolId>,
    pub types: HashMap<TypeNameId, TypeSymbolId>,
    parent: Option<ScopeId>,
    id: ScopeId,
    kind: ScopeKind
}

pub struct SymbolTable {
    pub value_symbols: HashMap<ValueSymbolId, ValueSymbol>,
    pub type_symbols: HashMap<TypeSymbolId, TypeSymbol>,
    value_names: NameInterner,
    type_names: NameInterner,
    
    pub default_trait_impl_scopes: HashMap<(TypeSymbolId, TypeSymbolId), ScopeId>,

    pub scopes: HashMap<ScopeId, Scope>,
    
    lines: Rc<Vec<String>>,
    current_scope_id: ScopeId,
    next_scope_id: ScopeId,
    next_value_symbol_id: ValueSymbolId,
    next_type_symbol_id: TypeSymbolId,

    real_starting_scope: ScopeId
}

impl SymbolTable {
    pub fn new(lines: Rc<Vec<String>>) -> Self {
        let mut table = SymbolTable {
            value_symbols: HashMap::new(),
            type_symbols: HashMap::new(),
            value_names: NameInterner::new(),
            type_names: NameInterner::new(),
            default_trait_impl_scopes: HashMap::new(),
            scopes: HashMap::new(),
            lines: lines.clone(),
            current_scope_id: 0,
            next_scope_id: 0,
            next_value_symbol_id: 0,
            next_type_symbol_id: 0,
            real_starting_scope: 0
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
        
        for ty in PrimitiveKind::iter() {
            table.add_type_symbol(
                ty.to_symbol_str(),
                TypeSymbolKind::Primitive(ty),
                vec![],
                QualifierKind::Public,
                None
            ).unwrap();
        }

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
        table.real_starting_scope = init_scope_id;

        table
    }

    pub fn populate_with_defaults(&mut self, trait_registry: &mut TraitRegistry) {
        let old_scope = self.current_scope_id;
        self.current_scope_id = 0;

        // TRAITS //
        for op in Operation::iter() {
            let Some((trait_name, is_binary)) = op.to_trait_data() else { continue; };
            let is_unary = !is_binary;

            let fn_name = trait_name.chars().enumerate().map(|(i, c)| {
                if i != 0 && c.is_uppercase() { format!("_{}", c.to_lowercase()) }
                else { c.to_lowercase().to_string() }
            }).collect::<String>();

            let trait_scope_id = self.enter_scope(ScopeKind::Trait);

            let self_type_id = self.add_type_symbol("Self", TypeSymbolKind::TypeAlias((None, None)), vec![], QualifierKind::Public, None).unwrap();
            let output_type_id = self.add_type_symbol("Output", TypeSymbolKind::TypeAlias((None, None)), vec![], QualifierKind::Public, None).unwrap();
            
            let trait_generics = if is_unary { vec![] } else { vec!["Rhs"] };
            let trait_generic_ids: Vec<TypeSymbolId> = trait_generics
                .iter()
                .map(|&name| self.add_type_symbol(name, TypeSymbolKind::Generic(vec![]), vec![], QualifierKind::Public, None).unwrap())
                .collect();

            let mut params = vec![Type::new_base(self_type_id)];
            if !is_unary {
                params.push(Type::new_base(trait_generic_ids[0]));
            }
            
            self.add_type_symbol(
                &fn_name,
                TypeSymbolKind::FunctionSignature {
                    params,
                    return_type: Type::new_base(output_type_id),
                    instance: Some(ReferenceKind::Value)
                },
                vec![], QualifierKind::Public, None
            ).unwrap();

            self.exit_scope();

            let trait_id = self.add_type_symbol(
                &trait_name, 
                TypeSymbolKind::Trait(trait_scope_id), 
                trait_generic_ids.clone(),
                QualifierKind::Public, None
            ).unwrap();

            // DEFAULT IMPLS //
            for primitive in PrimitiveKind::iter() {
                let Some(return_type) = op.to_default_trait_return_type(primitive) else { continue; };
                let output_id = self.find_type_symbol(return_type.to_symbol_str()).unwrap().id;
                let self_id = self.find_type_symbol(primitive.to_symbol_str()).unwrap().id;

                let impl_scope_id = self.enter_scope(ScopeKind::Impl);
                
                let trait_specialization = if is_unary { vec![] } else { vec![self_id] };
                trait_registry.register(trait_id, self_id, TraitImpl {
                    impl_scope_id,
                    impl_generic_params: vec![],
                    trait_generic_specialization: trait_specialization,
                    type_specialization: vec![],
                });
                
                self.add_type_symbol("Self", TypeSymbolKind::TypeAlias((None, Some(self_id))), vec![], QualifierKind::Public, None).unwrap();
                self.add_type_symbol("Output", TypeSymbolKind::TypeAlias((None, Some(output_id))), vec![], QualifierKind::Public, None).unwrap();
                if !is_unary {
                    self.add_type_symbol(trait_generics[0], TypeSymbolKind::TypeAlias((None, Some(self_id))), vec![], QualifierKind::Public, None).unwrap();
                }

                let func_scope_id = self.enter_scope(ScopeKind::Function);
                self.add_value_symbol("this", ValueSymbolKind::Variable, false, QualifierKind::Public, Some(Type::new_base(self_id)), None).unwrap();
                if !is_unary {
                    self.add_value_symbol("other", ValueSymbolKind::Variable, false, QualifierKind::Public, Some(Type::new_base(self_id)), None).unwrap();
                }

                let concrete_sig_params = if is_unary { vec![Type::new_base(self_id)] } else { vec![Type::new_base(self_id), Type::new_base(self_id)] };
                let concrete_sig_id = self.add_type_symbol(
                    &fn_name,
                    TypeSymbolKind::FunctionSignature {
                        params: concrete_sig_params,
                        return_type: Type::new_base(output_id),
                        instance: Some(ReferenceKind::Value)
                    },
                    vec![], QualifierKind::Public, None
                ).unwrap();
                
                self.add_value_symbol(&fn_name, ValueSymbolKind::Function(func_scope_id), false, QualifierKind::Public, Some(Type::new_base(concrete_sig_id)), None).unwrap();
                
                self.exit_scope(); // function scope
                self.exit_scope(); // impl scope
            }
        }

        self.current_scope_id = old_scope;
    }

    pub fn add_value_symbol(
        &mut self,
        name: &str,
        kind: ValueSymbolKind,
        mutable: bool,
        qualifier: QualifierKind,
        type_id: Option<Type>,
        span: Option<Span>
    ) -> Result<ValueSymbolId, BoxedError> {
        let name_id = self.value_names.intern(name);
        let scope_id = self.current_scope_id;

        if let Some(existing_id) = self.scopes[&scope_id].values.get(&name_id) {
            let existing_symbol = &self.value_symbols[existing_id];
            let err = self.create_redeclaration_error(name.to_string(), existing_symbol.span, span);
            return Err(err);
        }

        let id = self.next_value_symbol_id;
        self.next_value_symbol_id += 1;
        let symbol = ValueSymbol { id, name_id, kind, mutable, qualifier, type_id, span, scope_id };
        self.value_symbols.insert(id, symbol);
        self.scopes.get_mut(&scope_id).unwrap().values.insert(name_id, id);

        Ok(id)
    }

    pub fn add_type_symbol(
        &mut self,
        name: &str,
        kind: TypeSymbolKind,
        generic_parameters: Vec<TypeSymbolId>,
        qualifier: QualifierKind,
        span: Option<Span>
    ) -> Result<TypeSymbolId, BoxedError> {
        let name_id = self.type_names.intern(name);
        let scope_id = self.current_scope_id;

        if let Some(existing_id) = self.scopes[&scope_id].types.get(&name_id) {
            let existing_symbol = &self.type_symbols[existing_id];
            let err = self.create_redeclaration_error(name.to_string(), existing_symbol.span, span);
            return Err(err);
        }

        let id = self.next_type_symbol_id;
        self.next_type_symbol_id += 1;
        let symbol = TypeSymbol { id, name_id, kind, generic_parameters, qualifier, span, scope_id };
        self.type_symbols.insert(id, symbol);
        self.scopes.get_mut(&scope_id).unwrap().types.insert(name_id, id);

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

    pub fn get_value_symbol(&self, id: ValueSymbolId) -> Option<&ValueSymbol> { self.value_symbols.get(&id) }
    pub fn get_value_symbol_mut(&mut self, id: ValueSymbolId) -> Option<&mut ValueSymbol> { self.value_symbols.get_mut(&id) }
    pub fn get_type_symbol(&self, id: TypeSymbolId) -> Option<&TypeSymbol> { self.type_symbols.get(&id) }
    pub fn get_type_symbol_mut(&mut self, id: TypeSymbolId) -> Option<&mut TypeSymbol> { self.type_symbols.get_mut(&id) }
    pub fn get_value_name(&self, id: ValueNameId) -> &str { self.value_names.lookup(id) }
    pub fn get_type_name(&self, id: TypeNameId) -> &str { self.type_names.lookup(id) }

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

    pub fn current_scope_mut(&mut self) -> &mut Scope { self.scopes.get_mut(&self.current_scope_id).expect("Scope should exist") }
    pub fn current_scope(&self) -> &Scope { self.scopes.get(&self.current_scope_id).expect("Scope should exist") }
    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> Option<&mut Scope> { self.scopes.get_mut(&scope_id) }
    pub fn get_scope(&self, scope_id: ScopeId) -> Option<&Scope> { self.scopes.get(&scope_id) }

    fn create_redeclaration_error(&self, name: String, span1: Option<Span>, span2: Option<Span>) -> BoxedError {
        match (span1, span2) {
            (Some(s1), Some(s2)) => Error::from_multiple_errors(ErrorKind::AlreadyDeclared(name), s2, Span::get_all_lines(self.lines.clone(), &[s1, s2])),
            (Some(s), None) | (None, Some(s)) => Error::from_one_error(ErrorKind::AlreadyDeclared(name), s, (self.lines[s.start_pos.line - 1].clone(), s.start_pos.line)),
            (None, None) => Error::new(ErrorKind::AlreadyDeclared(name)),
        }
    }
}

#[derive(Default)]
pub struct TraitRegistry {
    pub register: HashMap<TypeSymbolId, HashMap<TypeSymbolId, Vec<TraitImpl>>>,
}

impl TraitRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register(&mut self, trait_id: TypeSymbolId, type_id: TypeSymbolId, implementation: TraitImpl) {
        self.register
            .entry(trait_id)
            .or_default()
            .entry(type_id)
            .or_default()
            .push(implementation);
    }

    pub fn get_implementations(&self, trait_id: TypeSymbolId, type_id: TypeSymbolId) -> Option<&Vec<TraitImpl>> {
        self.register
            .get(&trait_id)
            .and_then(|impls| impls.get(&type_id))
    }

    pub fn find_applicable_impl<'a>(
        &'a self,
        trait_id: TypeSymbolId,
        self_type: &Type,
        trait_args: &[Type],
        semantic_analyzer: &'a SemanticAnalyzer, 
        span: Span
    ) -> Result<&'a TraitImpl, BoxedError> {
        let trait_name = semantic_analyzer.symbol_table.get_type_name(trait_id).to_string();
        let self_base_symbol = self_type.get_base_symbol();
        let type_name = semantic_analyzer.symbol_table.get_type_name(self_base_symbol).to_string();

        let entries = self.get_implementations(trait_id, self_base_symbol)
            .ok_or_else(|| semantic_analyzer.create_error(
                ErrorKind::UnimplementedTrait(trait_name.clone(), type_name.clone()),
                span, 
                &[span]
            ))?;
        
        let mut applicable_impls = vec![];
        for entry in entries.iter() {
            // TODO: unification
            let self_type_args: Vec<TypeSymbolId> = if let Type::Base { args, .. } = self_type {
                args.iter().map(|t| t.get_base_symbol()).collect()
            } else { vec![] };

            let trait_type_args: Vec<TypeSymbolId> = trait_args.iter().map(|t| t.get_base_symbol()).collect();
            
            if entry.type_specialization == self_type_args && entry.trait_generic_specialization == trait_type_args {
                applicable_impls.push(entry);
            }
        }

        match applicable_impls.len() {
            0 => Err(semantic_analyzer.create_error(
                ErrorKind::UnimplementedTrait(trait_name.clone(), type_name.clone()),
                span, 
                &[span]
            )),
            1 => Ok(applicable_impls[0]),
            _ => Err(semantic_analyzer.create_error(
                ErrorKind::ConflictingTraitImpl(trait_name, type_name),
                span,
                &[span]
            ))
        }
    }
}

#[derive(Debug)]
pub struct TraitObligation {
    pub trait_id: TypeSymbolId,
    pub self_type: Type,
    pub trait_args: Vec<Type>,
}

#[derive(Debug)]
pub enum ObligationCause {
    UnaryOperation(Operation),
    BinaryOperation(Operation)
}

#[derive(Debug)]
pub struct Obligation {
    pub id: usize,
    pub kind: TraitObligation,
    pub cause: ObligationCause,
    pub cause_span: Span,
    pub resolved_type: Option<Type>
}

pub struct SemanticAnalyzer {
    pub symbol_table: SymbolTable,
    pub primitives: Vec<TypeSymbolId>,
    pub trait_registry: TraitRegistry,
    pub obligations: Vec<Obligation>,
    errors: Vec<Error>,
    lines: Rc<Vec<String>>
}

impl SemanticAnalyzer {
    pub fn new(lines: Rc<Vec<String>>) -> SemanticAnalyzer {
        let mut symbol_table = SymbolTable::new(lines.clone());
        let mut trait_registry = TraitRegistry::new();

        symbol_table.populate_with_defaults(&mut trait_registry);
        
        let primitives: Vec<TypeSymbolId> = PrimitiveKind::iter()
            .map(|k| symbol_table.find_type_symbol(k.to_symbol_str()).unwrap().id)
            .collect();

        SemanticAnalyzer {
            trait_registry,
            symbol_table,
            primitives,
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
        macro_rules! pass {
            ($self:ident, $method:ident, $program:expr) => {{
                let errors = $self.$method(&mut $program);
                if !errors.is_empty() {
                    return Err(errors);
                }
            }};
        }
        
        pass!(self, symbol_collector_pass, &mut program);
        pass!(self, generic_constraints_pass, &mut program);
        pass!(self, impl_collector_pass, &mut program);
        // pass!(self, type_collector_pass, &mut program);

        Ok(program)
    }
}

impl std::fmt::Display for InherentImpl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "InherentImpl(scope_id: {}, specialization: {:?}, generic_params: {:?})", 
            self.scope_id, self.specialization, self.generic_params)
    }
}

impl std::fmt::Display for TraitImpl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TraitImpl(impl_scope_id: {:?}, impl_generic_params: {:?}, trait_generic_specialization: {:?}, type_specialization: {:?})", 
            self.impl_scope_id, self.impl_generic_params, self.trait_generic_specialization, self.type_specialization)
    }
}

impl std::fmt::Display for ValueSymbolKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let colored = match self {
            ValueSymbolKind::Variable => "Variable".green(),
            ValueSymbolKind::Function(scope_id) => format!("Function({})", scope_id).blue(),
            ValueSymbolKind::StructField => "StructField".yellow(),
            ValueSymbolKind::EnumVariant => "EnumVariant".yellow(),
        };
        write!(f, "{}", colored)
    }
}

impl SymbolTable {
    pub fn display_value_symbol<'a>(&'a self, symbol: &'a ValueSymbol) -> impl std::fmt::Display + 'a {
        struct Displayer<'a> { symbol: &'a ValueSymbol, table: &'a SymbolTable }
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
        struct Displayer<'a> { symbol: &'a TypeSymbol, table: &'a SymbolTable }
        impl std::fmt::Display for Displayer<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let name = self.table.get_type_name(self.symbol.name_id);
                let type_variant = match &self.symbol.kind {
                    TypeSymbolKind::Struct((id, scopes)) => format!("Struct({}, {:?})", id, scopes).blue(),
                    TypeSymbolKind::Trait(id) => format!("Trait({})", id).cyan(),
                    TypeSymbolKind::Enum((id, scopes)) => format!("Enum({}, {:?})", id, scopes).blue(),
                    TypeSymbolKind::TypeAlias(id) => format!("TypeAlias({:?})", id).white(),
                    TypeSymbolKind::Primitive(k) => format!("Builtin({})", k).green(),
                    TypeSymbolKind::FunctionSignature { params, return_type, .. } => {
                        let params_str = params.iter()
                            .map(|p_ty| self.table.display_type(p_ty))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("fn({}): {}", params_str, self.table.display_type(return_type)).blue()
                    },
                    TypeSymbolKind::UnfulfilledObligation(id) => format!("UnfulfilledObligation({})", id).red(),
                    TypeSymbolKind::Custom => "Custom".white(),
                    TypeSymbolKind::Generic(constraints) => format!("Generic({:?})", constraints).white()
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

    pub fn display_type<'a>(&'a self, ty: &'a Type) -> String {
        match ty {
            Type::Base { symbol, args } => {
                let base_name = self.get_type_name(self.type_symbols[symbol].name_id);
                if args.is_empty() {
                    base_name.to_string()
                } else {
                    let arg_str = args
                        .iter()
                        .map(|arg| self.display_type(arg))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{}>", base_name, arg_str)
                }
            }
            Type::Reference(inner) => format!("&{}", self.display_type(inner)),
            Type::MutableReference(inner) => format!("&mut {}", self.display_type(inner)),
        }
    }

    fn display_scope(&self, scope_id: ScopeId, indent: usize, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let scope = self.scopes.get(&scope_id).unwrap();
        for symbol_id in scope.values.values() {
            let symbol = &self.value_symbols[symbol_id];
            writeln!(f, "{:indent$}[Value({})] {}", "", symbol_id, self.display_value_symbol(symbol), indent = indent)?;
        }
        for symbol_id in scope.types.values() {
            let symbol = &self.type_symbols[symbol_id];
            writeln!(f, "{:indent$}[Type({})] {}", "", symbol_id, self.display_type_symbol(symbol), indent = indent)?;
        }
        let mut child_scope_ids: Vec<ScopeId> = self.scopes.values()
            .filter(|s| s.parent == Some(scope_id))
            .map(|s| s.id)
            .collect();
        child_scope_ids.sort();
        for child_id in child_scope_ids {
            writeln!(f, "{:indent$}{{ (Scope({}))", "", child_id, indent = indent)?;
            self.display_scope(child_id, indent + 4, f)?;
            writeln!(f, "{:indent$}}}", "", indent = indent)?;
        }
        Ok(())
    }
}

impl std::fmt::Display for SymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "--- Root Scope (0) ---")?;
        self.display_scope(0, 0, f)?;
        writeln!(f, "--- User Scope ({}) ---", self.real_starting_scope)?;
        self.display_scope(self.real_starting_scope, 0, f)
    }
}

impl TraitRegistry {
    pub fn display<'a>(&'a self, symbol_table: &'a SymbolTable) -> impl std::fmt::Display + 'a {
        struct Displayer<'a> { registry: &'a TraitRegistry, table: &'a SymbolTable }
        impl std::fmt::Display for Displayer<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                for (trait_id, impls) in &self.registry.register {
                    let trait_symbol = &self.table.type_symbols[trait_id];
                    let trait_name = self.table.get_type_name(trait_symbol.name_id);
                    writeln!(f, "{}", format!("[Trait({})] {}", trait_id, trait_name).underline())?;
                    for (type_id, impl_details) in impls {
                        let type_symbol = &self.table.type_symbols[type_id];
                        let type_name = self.table.get_type_name(type_symbol.name_id);
                        write!(f, "  for [Type({})] {}: ", type_id, type_name)?;
                        for (i, impl_detail) in impl_details.iter().enumerate() {
                            if i > 0 { write!(f, ", ")?; }
                            write!(f, "{:?}", impl_detail)?;
                        }
                        writeln!(f)?;
                    }
                }
                Ok(())
            }
        }
        Displayer { registry: self, table: symbol_table }
    }
}

impl std::fmt::Display for SemanticAnalyzer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}", "Symbol Table:".bold().underline())?;
        writeln!(f, "{}", self.symbol_table)?;
        writeln!(f, "\n{}", "Trait Registry:".bold().underline())?;
        writeln!(f, "{}", self.trait_registry.display(&self.symbol_table))?;
        Ok(())
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Base { symbol, args } => {
                let base_name = format!("TypeSymbol({})", symbol);
                if args.is_empty() {
                    write!(f, "{}", base_name)
                } else {
                    let arg_str = args
                        .iter()
                        .map(|arg| format!("{}", arg))
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "{}<{}>", base_name, arg_str)
                }
            }
            Type::Reference(inner) => write!(f, "&{}", inner),
            Type::MutableReference(inner) => write!(f, "&mut {}", inner),
        }
    }
}