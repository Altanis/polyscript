use crate::{frontend::syntax::ast::AstNode, utils::{error::*, kind::*}};
use colored::*;
use std::{collections::{BTreeMap, HashMap, HashSet, VecDeque}, rc::Rc};
use strum::IntoEnumIterator;
use rustc_hash::FxHashMap;

pub type ScopeId = usize;
pub type ValueNameId = usize;
pub type TypeNameId = usize;
pub type ValueSymbolId = usize;
pub type TypeSymbolId = usize;

/// A lookup table that maps Strings to numbers.
#[derive(Default, Debug)]
pub struct NameInterner {
    map: FxHashMap<Rc<str>, usize>,
    vec: Vec<Rc<str>>,
}

impl NameInterner {
    pub fn new() -> Self {
        Self::default()
    }

    /// Generates a unique ID for a string.
    pub fn intern(&mut self, s: &str) -> usize {
        if let Some(&id) = self.map.get(s) {
            return id;
        }

        let id = self.vec.len();
        let rc: Rc<str> = Rc::from(s);
        self.vec.push(rc.clone());
        self.map.insert(rc, id);

        id
    }

    /// Finds a string given an id.
    pub fn lookup(&self, id: usize) -> &str {
        &self.vec[id]
    }

    pub fn get_id(&self, s: &str) -> Option<usize> {
        self.map.get(s).copied()
    }

    pub fn purge_names(&mut self, names: &[usize]) {
        for &name in names.iter() {
            if name < self.vec.len() {
                let name_to_remove = self.vec[name].clone();
                self.map.remove(name_to_remove.as_ref());
                self.vec[name] = Rc::from("[deleted_type]");
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ValueSymbolKind {
    Variable,
    Function(ScopeId, HashSet<ValueSymbolId>),
    StructField,
    EnumVariant,
}

#[derive(Debug, Clone, Copy, PartialEq, strum_macros::EnumIter, strum_macros::Display)]
pub enum PrimitiveKind {
    Int,
    Float,
    Bool,
    StaticString,
    Char,
    Void,
    Never
}

impl PrimitiveKind {
    pub fn to_symbol_str(&self) -> &'static str {
        match self {
            PrimitiveKind::Int => INT_TYPE,
            PrimitiveKind::Float => FLOAT_TYPE,
            PrimitiveKind::Bool => BOOL_TYPE,
            PrimitiveKind::StaticString => STATIC_STRING_TYPE,
            PrimitiveKind::Char => CHAR_TYPE,
            PrimitiveKind::Void => VOID_TYPE,
            PrimitiveKind::Never => NEVER_TYPE
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct InherentImpl {
    pub scope_id: ScopeId,
    pub specialization: Vec<TypeSymbolId>,
    pub generic_params: Vec<TypeSymbolId>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct TraitImpl {
    pub impl_scope_id: ScopeId,
    pub impl_generic_params: Vec<TypeSymbolId>,
    pub trait_generic_specialization: Vec<TypeSymbolId>,
    pub type_specialization: Vec<TypeSymbolId>,
    pub span: Span
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeSymbolKind {
    Primitive(PrimitiveKind),
    Enum((ScopeId, Vec<InherentImpl>)),
    Struct((ScopeId, Vec<InherentImpl>)),
    Trait(ScopeId),
    TraitSelf(ScopeId),
    TypeAlias((Option<ScopeId>, Option<Type>)),
    FunctionSignature {
        params: Vec<Type>,
        return_type: Type,
        instance: bool
    },
    Generic(Vec<TypeSymbolId>),
    UnificationVariable(TypeSymbolId),
    OpaqueTypeProjection {
        ty: Type,
        tr: Type,
        member: String
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ScopeKind {
    Root,
    Function,
    Block,
    Enum,
    Struct,
    Impl,
    Trait,
    Type,
    ForLoop,
    WhileLoop
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Type {
    pub symbol: TypeSymbolId,
    pub args: Vec<Type>
}

impl Type {
    pub fn from_no_args(symbol: TypeSymbolId) -> Self {
        Type {
            symbol,
            args: vec![]
        }
    }

    /// Recursively traverses a type to check if it contains any generic type variables from a given set.
    pub fn contains_generics(&self, generics: &HashSet<TypeSymbolId>) -> bool {
        if generics.contains(&self.symbol) {
            return true;
        }

        self.args.iter().any(|arg| arg.contains_generics(generics))
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
    pub type_id: Option<Type>,
    pub statically_known_return_value_id: Option<ValueSymbolId>,
    pub is_intrinsic: bool
}

#[derive(Debug, Clone)]
pub struct TypeSymbol {
    pub id: TypeSymbolId,
    pub name_id: TypeNameId,
    pub kind: TypeSymbolKind,
    pub generic_parameters: Vec<TypeSymbolId>,
    pub qualifier: QualifierKind,
    pub scope_id: ScopeId,
    pub span: Option<Span>,
}

impl TypeSymbol {
    pub fn unify(&self, other: &TypeSymbol) -> Option<TypeSymbolId> {
        if self.id == other.id {
            return Some(self.id);
        }

        match (&self.kind, &other.kind) {
            (_, TypeSymbolKind::Primitive(PrimitiveKind::Never)) | (TypeSymbolKind::Primitive(PrimitiveKind::Never), _) => Some(self.id),
            (_, TypeSymbolKind::TraitSelf(_)) | (TypeSymbolKind::TraitSelf(_), _) => Some(self.id),

            _ => None
        }
    }

    pub fn is_valid_cast(&self, other: &TypeSymbol) -> bool {
        matches!((&self.kind, &other.kind), 
            (TypeSymbolKind::Primitive(PrimitiveKind::Int), TypeSymbolKind::Primitive(PrimitiveKind::Float))
            | (TypeSymbolKind::Primitive(PrimitiveKind::Float), TypeSymbolKind::Primitive(PrimitiveKind::Int))
            | (TypeSymbolKind::Primitive(PrimitiveKind::Int), TypeSymbolKind::Primitive(PrimitiveKind::Int))
            | (TypeSymbolKind::Primitive(PrimitiveKind::Float), TypeSymbolKind::Primitive(PrimitiveKind::Float))
            | (TypeSymbolKind::Primitive(PrimitiveKind::Char), TypeSymbolKind::Primitive(PrimitiveKind::Int))
            | (TypeSymbolKind::Primitive(PrimitiveKind::Int), TypeSymbolKind::Primitive(PrimitiveKind::Char)) 
            | (TypeSymbolKind::Enum(_), TypeSymbolKind::Primitive(PrimitiveKind::Int))
        )
    }
}

#[derive(Debug)]
pub struct Scope {
    pub values: HashMap<ValueNameId, ValueSymbolId>,
    pub types: HashMap<TypeNameId, TypeSymbolId>,
    pub kind: ScopeKind,
    pub parent: Option<ScopeId>,
    pub id: ScopeId,
    pub trait_id: Option<TypeSymbolId>,
}

#[derive(Default, Debug, Clone)]
pub struct SymbolRegistry {
    pub value_symbols: HashMap<ValueSymbolId, ValueSymbol>,
    pub type_symbols: HashMap<TypeSymbolId, TypeSymbol>,
    pub struct_template_map: HashMap<TypeSymbolId, (TypeSymbolId, Rc<BTreeMap<TypeSymbolId, Type>>)>
}

pub struct SymbolTable {
    pub registry: SymbolRegistry,
    pub value_names: NameInterner,
    pub type_names: NameInterner,

    pub default_trait_impl_scopes: HashMap<(TypeSymbolId, TypeSymbolId), ScopeId>,

    pub scopes: HashMap<ScopeId, Scope>,

    lines: Rc<Vec<String>>,
    pub current_scope_id: ScopeId,
    next_scope_id: ScopeId,
    next_value_symbol_id: ValueSymbolId,
    next_type_symbol_id: TypeSymbolId,

    file_path: Option<String>,

    pub real_starting_scope: ScopeId,
    pub intrinsics_scope_id: ScopeId,
}

impl SymbolTable {
    pub fn new(lines: Rc<Vec<String>>, file_path: Option<String>) -> Self {
        let mut table = SymbolTable {
            registry: SymbolRegistry::default(),
            value_names: NameInterner::new(),
            type_names: NameInterner::new(),
            default_trait_impl_scopes: HashMap::new(),
            scopes: HashMap::new(),
            lines: lines.clone(),
            current_scope_id: 0,
            next_scope_id: 0,
            next_value_symbol_id: 0,
            next_type_symbol_id: 0,
            file_path,
            real_starting_scope: 0,
            intrinsics_scope_id: 0,
        };

        let root_scope_id = table.get_next_scope_id();
        let root_scope = Scope {
            values: HashMap::new(),
            types: HashMap::new(),
            parent: None,
            id: root_scope_id,
            kind: ScopeKind::Root,
            trait_id: None,
        };
        table.scopes.insert(root_scope_id, root_scope);

        for ty in PrimitiveKind::iter() {
            table
                .add_type_symbol(
                    ty.to_symbol_str(),
                    TypeSymbolKind::Primitive(ty),
                    vec![],
                    QualifierKind::Public,
                    None,
                )
                .unwrap();
        }

        let intrinsics_scope_id = table.get_next_scope_id();
        let intrinsics_scope = Scope {
            values: HashMap::new(),
            types: HashMap::new(),
            parent: Some(root_scope_id),
            id: intrinsics_scope_id,
            kind: ScopeKind::Block,
            trait_id: None,
        };
        table.scopes.insert(intrinsics_scope_id, intrinsics_scope);
        table.intrinsics_scope_id = intrinsics_scope_id;

        table.populate_intrinsics();

        let init_scope_id = table.get_next_scope_id();
        let init_scope = Scope {
            values: HashMap::new(),
            types: HashMap::new(),
            parent: Some(root_scope_id),
            id: init_scope_id,
            kind: ScopeKind::Block,
            trait_id: None,
        };

        table.scopes.insert(init_scope_id, init_scope);

        table.current_scope_id = init_scope_id;
        table.real_starting_scope = init_scope_id;

        table
    }

    pub fn populate_intrinsics(&mut self) {
        let old_scope = self.current_scope_id;
        self.current_scope_id = self.intrinsics_scope_id;

        let int_type = Type::from_no_args(self.find_type_symbol("int").unwrap().id);
        let float_type = Type::from_no_args(self.find_type_symbol("float").unwrap().id);
        let char_type = Type::from_no_args(self.find_type_symbol("char").unwrap().id);
        let str_type = Type::from_no_args(self.find_type_symbol("str").unwrap().id);
        let void_type = Type::from_no_args(self.find_type_symbol("void").unwrap().id);
        let never_type = Type::from_no_args(self.find_type_symbol("never").unwrap().id);

        let mut add_intrinsic = |name: &str, params: Vec<Type>, ret: Type| {
            let fn_scope_id = self.enter_scope(ScopeKind::Function);
            self.exit_scope();

            let fn_sig_type_id = self
                .add_type_symbol(
                    &format!("#intrinsic_{}_sig", name),
                    TypeSymbolKind::FunctionSignature {
                        params,
                        return_type: ret.clone(),
                        instance: false
                    },
                    vec![],
                    QualifierKind::Public,
                    None,
                )
                .unwrap();

            let value_id = self
                .add_value_symbol(
                    name,
                    ValueSymbolKind::Function(fn_scope_id, HashSet::new()),
                    false,
                    QualifierKind::Public,
                    Some(Type::from_no_args(fn_sig_type_id)),
                    None,
                )
                .unwrap();

            self.get_value_symbol_mut(value_id).unwrap().is_intrinsic = true;
        };

        add_intrinsic("calloc", vec![int_type.clone(), int_type.clone()], int_type.clone());
        add_intrinsic("realloc", vec![int_type.clone(), int_type.clone()], int_type.clone());
        add_intrinsic("memcpy", vec![int_type.clone(), int_type.clone(), int_type.clone()], void_type.clone());
        add_intrinsic("memmove", vec![int_type.clone(), int_type.clone(), int_type.clone()], void_type.clone());
        add_intrinsic("free", vec![int_type.clone()], void_type.clone());
        add_intrinsic("incref", vec![int_type.clone()], void_type.clone());
        add_intrinsic("decref", vec![int_type.clone()], void_type.clone());
        add_intrinsic("print", vec![str_type.clone()], void_type.clone());
        add_intrinsic("eprint", vec![str_type.clone()], void_type.clone());
        add_intrinsic("print_int", vec![int_type.clone()], void_type.clone());
        add_intrinsic("print_char", vec![char_type.clone()], void_type.clone());
        add_intrinsic("eprint_char", vec![char_type.clone()], void_type.clone());
        add_intrinsic("endproc", vec![int_type.clone()], never_type.clone());
        add_intrinsic("strlen", vec![str_type.clone()], int_type.clone());
        add_intrinsic("strget", vec![str_type.clone(), int_type.clone()], char_type.clone());
        add_intrinsic("getchar", vec![], char_type.clone());

        let unary_float_fns = [
            "ln_", "log2_", "log10_", "sin_", "cos_", "tan_", "asin_", "acos_", "atan_",
            "sinh_", "cosh_", "tanh_", "asinh_", "acosh_", "atanh_"
        ];

        for &name in unary_float_fns.iter() {
            add_intrinsic(name, vec![float_type.clone()], float_type.clone());
        }

        add_intrinsic("atan2_", vec![float_type.clone(), float_type.clone()], float_type.clone());
        add_intrinsic("random_", vec![], float_type.clone());

        let t_generic_id = self.add_type_symbol("#T_intrinsic_drop", TypeSymbolKind::Generic(vec![]), vec![], QualifierKind::Public, None).unwrap();
        let t_type = Type::from_no_args(t_generic_id);

        let fn_scope_id = self.enter_scope(ScopeKind::Function);
        self.exit_scope();

        let fn_sig_type_id = self
            .add_type_symbol(
                "#intrinsic_drop_sig",
                TypeSymbolKind::FunctionSignature {
                    params: vec![t_type],
                    return_type: void_type.clone(),
                    instance: false
                },
                vec![t_generic_id],
                QualifierKind::Public,
                None,
            )
            .unwrap();

        let value_id = self
            .add_value_symbol(
                "drop",
                ValueSymbolKind::Function(fn_scope_id, HashSet::new()),
                false,
                QualifierKind::Public,
                Some(Type::from_no_args(fn_sig_type_id)),
                None,
            )
            .unwrap();
        self.get_value_symbol_mut(value_id).unwrap().is_intrinsic = true;

        let t_generic_ref_id = self.add_type_symbol("#T_intrinsic_ref", TypeSymbolKind::Generic(vec![]), vec![], QualifierKind::Public, None).unwrap();
        let t_type_ref = Type::from_no_args(t_generic_ref_id);
        let fn_scope_id_ref = self.enter_scope(ScopeKind::Function);
        self.exit_scope();
        let fn_sig_type_id_ref = self.add_type_symbol(
            "#intrinsic_ref_sig",
            TypeSymbolKind::FunctionSignature {
                params: vec![t_type_ref],
                return_type: int_type.clone(),
                instance: false
            },
            vec![t_generic_ref_id],
            QualifierKind::Public,
            None,
        ).unwrap();
        let value_id_ref = self.add_value_symbol(
            "ref",
            ValueSymbolKind::Function(fn_scope_id_ref, HashSet::new()),
            false,
            QualifierKind::Public,
            Some(Type::from_no_args(fn_sig_type_id_ref)),
            None,
        ).unwrap();
        self.get_value_symbol_mut(value_id_ref).unwrap().is_intrinsic = true;

        let t_generic_deref_id = self.add_type_symbol("#T_intrinsic_deref", TypeSymbolKind::Generic(vec![]), vec![], QualifierKind::Public, None).unwrap();
        let t_type_deref = Type::from_no_args(t_generic_deref_id);
        let fn_scope_id_deref = self.enter_scope(ScopeKind::Function);
        self.exit_scope();
        let fn_sig_type_id_deref = self.add_type_symbol(
            "#intrinsic_deref_sig",
            TypeSymbolKind::FunctionSignature {
                params: vec![t_type_deref.clone()],
                return_type: t_type_deref,
                instance: false
            },
            vec![t_generic_deref_id],
            QualifierKind::Public,
            None,
        ).unwrap();
        let value_id_deref = self.add_value_symbol(
            "deref",
            ValueSymbolKind::Function(fn_scope_id_deref, HashSet::new()),
            false,
            QualifierKind::Public,
            Some(Type::from_no_args(fn_sig_type_id_deref)),
            None,
        ).unwrap();
        self.get_value_symbol_mut(value_id_deref).unwrap().is_intrinsic = true;

        self.current_scope_id = old_scope;
    }

    pub fn populate_with_defaults(&mut self, trait_registry: &mut TraitRegistry) {
        let old_scope = self.current_scope_id;
        self.current_scope_id = 0;

        // TRAITS //
        for op in Operation::iter() {
            let Some((trait_name, is_binary)) = op.to_trait_data() else {
                continue;
            };
            let is_unary = !is_binary;

            let fn_name = trait_name
                .chars()
                .enumerate()
                .map(|(i, c)| {
                    if i != 0 && c.is_uppercase() {
                        format!("_{}", c.to_lowercase())
                    } else {
                        c.to_lowercase().to_string()
                    }
                })
                .collect::<String>();

            let trait_scope_id = self.enter_scope(ScopeKind::Trait);

            let self_type_id = self
                .add_type_symbol(
                    "Self",
                    TypeSymbolKind::TypeAlias((None, None)),
                    vec![],
                    QualifierKind::Public,
                    None,
                )
                .unwrap();
            let output_type_id = if op.is_assignment() {
                self.find_type_symbol("void").unwrap().id
            } else {
                self.add_type_symbol("Output", TypeSymbolKind::TypeAlias((None, None)), vec![], QualifierKind::Public, None).unwrap()
            };

            let trait_generics = if is_unary { vec![] } else { vec!["Rhs"] };
            let trait_generic_ids: Vec<TypeSymbolId> = trait_generics
                .iter()
                .map(|&name| {
                    self.add_type_symbol(
                        name,
                        TypeSymbolKind::Generic(vec![]),
                        vec![],
                        QualifierKind::Public,
                        None,
                    )
                    .unwrap()
                })
                .collect();

            let func_scope_id = self.enter_scope(ScopeKind::Function);
            self.exit_scope();

            let receiver_ty = Type::from_no_args(self_type_id);
            
            let mut params = vec![receiver_ty];
            if !is_unary {
                params.push(Type::from_no_args(trait_generic_ids[0]));
            }

            let fn_sig_type_id = self.add_type_symbol(
                &fn_name,
                TypeSymbolKind::FunctionSignature {
                    params,
                    return_type: Type::from_no_args(output_type_id),
                    instance: true
                },
                vec![],
                QualifierKind::Private,
                None,
            )
            .unwrap();

            self.add_value_symbol(
                &fn_name,
                ValueSymbolKind::Function(func_scope_id, HashSet::new()),
                false,
                QualifierKind::Public,
                Some(Type::from_no_args(fn_sig_type_id)),
                None,
            )
            .unwrap();

            self.exit_scope();

            let trait_id = self
                .add_type_symbol(
                    &trait_name,
                    TypeSymbolKind::Trait(trait_scope_id),
                    trait_generic_ids.clone(),
                    QualifierKind::Public,
                    None,
                )
                .unwrap();

            trait_registry.default_traits.insert(trait_name.clone(), trait_id);

            // DEFAULT IMPLS //
            for primitive in PrimitiveKind::iter() {
                let Some(return_type) = op.to_default_trait_return_type(primitive) else {
                    continue;
                };
                let output_id = self.find_type_symbol(return_type.to_symbol_str()).unwrap().id;
                let self_id = self.find_type_symbol(primitive.to_symbol_str()).unwrap().id;

                let impl_scope_id = self.enter_scope(ScopeKind::Impl);

                let trait_specialization = if is_unary { vec![] } else { vec![self_id] };
                trait_registry.register(
                    trait_id,
                    self_id,
                    TraitImpl {
                        impl_scope_id,
                        impl_generic_params: vec![],
                        trait_generic_specialization: trait_specialization,
                        type_specialization: vec![],
                        span: Span::default()
                    },
                );

                self.add_type_symbol(
                    "Self",
                    TypeSymbolKind::TypeAlias((None, Some(Type::from_no_args(self_id)))),
                    vec![],
                    QualifierKind::Public,
                    None,
                )
                .unwrap();
                self.add_type_symbol(
                    "Output",
                    TypeSymbolKind::TypeAlias((None, if op.is_assignment() {
                        Some(Type::from_no_args(self.find_type_symbol("void").unwrap().id))
                    } else {
                        Some(Type::from_no_args(output_id))
                    })),
                    vec![],
                    QualifierKind::Public,
                    None,
                )
                .unwrap();
                if !is_unary {
                    self.add_type_symbol(
                        trait_generics[0],
                        TypeSymbolKind::TypeAlias((None, Some(Type::from_no_args(self_id)))),
                        vec![],
                        QualifierKind::Public,
                        None,
                    )
                    .unwrap();
                }

                let func_scope_id = self.enter_scope(ScopeKind::Function);
                self.add_value_symbol(
                    "self",
                    ValueSymbolKind::Variable,
                    false,
                    QualifierKind::Public,
                    Some(Type::from_no_args(self_id)),
                    None,
                )
                .unwrap();
                if !is_unary {
                    self.add_value_symbol(
                        "other",
                        ValueSymbolKind::Variable,
                        false,
                        QualifierKind::Public,
                        Some(Type::from_no_args(self_id)),
                        None,
                    )
                    .unwrap();
                }

                let concrete_sig_params = if is_unary {
                    vec![Type::from_no_args(self_id)]
                } else {
                    vec![Type::from_no_args(self_id), Type::from_no_args(self_id)]
                };
                let concrete_sig_id = self
                    .add_type_symbol(
                        &fn_name,
                        TypeSymbolKind::FunctionSignature {
                            params: concrete_sig_params,
                            return_type: Type::from_no_args(output_id),
                            instance: true
                        },
                        vec![],
                        QualifierKind::Public,
                        None,
                    )
                    .unwrap();

                self.add_value_symbol(
                    &fn_name,
                    ValueSymbolKind::Function(func_scope_id, HashSet::new()),
                    false,
                    QualifierKind::Public,
                    Some(Type::from_no_args(concrete_sig_id)),
                    None,
                )
                .unwrap();

                self.exit_scope(); // function scope
                self.exit_scope(); // impl scope
            }
        }

        // -- Drop Trait -- //
        let trait_scope_id = self.enter_scope(ScopeKind::Trait);
        let self_type_id = self.add_type_symbol(
            "Self",
            TypeSymbolKind::TypeAlias((None, None)),
            vec![],
            QualifierKind::Public,
            None,
        ).unwrap();

        let func_scope_id = self.enter_scope(ScopeKind::Function);
        self.exit_scope();

        let params = vec![Type::from_no_args(self_type_id)];

        let fn_sig_type_id = self.add_type_symbol(
            "drop",
            TypeSymbolKind::FunctionSignature {
                params,
                return_type: Type::from_no_args(self.find_type_symbol("void").unwrap().id),
                instance: true
            },
            vec![],
            QualifierKind::Private,
            None,
        ).unwrap();

        self.add_value_symbol(
            "drop",
            ValueSymbolKind::Function(func_scope_id, HashSet::new()),
            false,
            QualifierKind::Public,
            Some(Type::from_no_args(fn_sig_type_id)),
            None,
        ).unwrap();

        self.exit_scope();

        let trait_id = self.add_type_symbol(
            "Drop",
            TypeSymbolKind::Trait(trait_scope_id),
            vec![],
            QualifierKind::Public,
            None,
        ).unwrap();

        trait_registry.default_traits.insert("Drop".to_string(), trait_id);

        self.current_scope_id = old_scope;
    }

    pub fn add_value_symbol(
        &mut self,
        name: &str,
        kind: ValueSymbolKind,
        mutable: bool,
        qualifier: QualifierKind,
        type_id: Option<Type>,
        span: Option<Span>,
    ) -> Result<ValueSymbolId, BoxedError> {
        let name_id = self.value_names.intern(name);
        let scope_id = self.current_scope_id;

        if let Some(existing_id) = self.scopes[&scope_id].values.get(&name_id) {
            let existing_symbol = &self.registry.value_symbols[existing_id];
            let err = self.create_redeclaration_error(name.to_string(), existing_symbol.span, span);
            return Err(err);
        }

        let id = self.next_value_symbol_id;
        self.next_value_symbol_id += 1;
        let symbol = ValueSymbol {
            id,
            name_id,
            kind,
            mutable,
            qualifier,
            type_id,
            span,
            scope_id,
            statically_known_return_value_id: None,
            is_intrinsic: false
        };
        self.registry.value_symbols.insert(id, symbol);
        self.scopes.get_mut(&scope_id).unwrap().values.insert(name_id, id);

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
            let existing_symbol = &self.registry.type_symbols[existing_id];
            let err = self.create_redeclaration_error(name.to_string(), existing_symbol.span, span);
            return Err(err);
        }

        let id = self.next_type_symbol_id;
        self.next_type_symbol_id += 1;
        let symbol = TypeSymbol {
            id,
            name_id,
            kind,
            generic_parameters,
            qualifier,
            span,
            scope_id,
        };
        self.registry.type_symbols.insert(id, symbol);
        self.scopes.get_mut(&scope_id).unwrap().types.insert(name_id, id);

        Ok(id)
    }

    pub fn find_value_symbol(&self, name: &str) -> Option<&ValueSymbol> {
        let name_id = self.value_names.get_id(name)?;
        let mut scope_id = Some(self.current_scope_id);

        while let Some(id) = scope_id {
            let scope = &self.scopes[&id];
            if let Some(symbol_id) = scope.values.get(&name_id) {
                return self.registry.value_symbols.get(symbol_id);
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
                return self.registry.value_symbols.get_mut(symbol_id);
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
                return self.registry.type_symbols.get(symbol_id);
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
                return self.registry.type_symbols.get_mut(symbol_id);
            }

            scope_id = scope.parent;
        }

        None
    }

    pub fn find_value_symbol_from_scope(&self, scope_id: ScopeId, name: &str) -> Option<&ValueSymbol> {
        let name_id = self.value_names.get_id(name)?;
        let mut scope_id = Some(scope_id);

        while let Some(id) = scope_id {
            let scope = &self.scopes[&id];
            if let Some(symbol_id) = scope.values.get(&name_id) {
                return self.registry.value_symbols.get(symbol_id);
            }

            scope_id = scope.parent;
        }

        None
    }

    pub fn find_value_symbol_from_scope_mut(
        &mut self,
        scope_id: ScopeId,
        name: &str,
    ) -> Option<&mut ValueSymbol> {
        let name_id = self.value_names.get_id(name)?;
        let mut scope_id = Some(scope_id);

        while let Some(id) = scope_id {
            let scope = &self.scopes[&id];
            if let Some(symbol_id) = scope.values.get(&name_id) {
                return self.registry.value_symbols.get_mut(symbol_id);
            }

            scope_id = scope.parent;
        }

        None
    }

    pub fn find_type_symbol_from_scope(&self, scope_id: ScopeId, name: &str) -> Option<&TypeSymbol> {
        let name_id = self.type_names.get_id(name)?;
        let mut scope_id = Some(scope_id);

        while let Some(id) = scope_id {
            let scope = &self.scopes[&id];
            if let Some(symbol_id) = scope.types.get(&name_id) {
                return self.registry.type_symbols.get(symbol_id);
            }

            scope_id = scope.parent;
        }

        None
    }

    pub fn find_type_symbol_from_scope_mut(
        &mut self,
        scope_id: ScopeId,
        name: &str,
    ) -> Option<&mut TypeSymbol> {
        let name_id = self.type_names.get_id(name)?;
        let mut scope_id = Some(scope_id);

        while let Some(id) = scope_id {
            let scope = &self.scopes[&id];
            if let Some(symbol_id) = scope.types.get(&name_id) {
                return self.registry.type_symbols.get_mut(symbol_id);
            }

            scope_id = scope.parent;
        }

        None
    }

    pub fn find_value_symbol_in_scope(&self, name: &str, scope_id: ScopeId) -> Option<&ValueSymbol> {
        let name_id = self.value_names.get_id(name)?;
        let symbol_id = self.scopes.get(&scope_id)?.values.get(&name_id)?;

        self.registry.value_symbols.get(symbol_id)
    }

    pub fn find_type_symbol_in_scope(&self, name: &str, scope_id: ScopeId) -> Option<&TypeSymbol> {
        let name_id = self.type_names.get_id(name)?;
        let symbol_id = self.scopes.get(&scope_id)?.types.get(&name_id)?;

        self.registry.type_symbols.get(symbol_id)
    }

    pub fn find_value_symbol_in_scope_mut(
        &mut self,
        name: &str,
        scope_id: ScopeId,
    ) -> Option<&mut ValueSymbol> {
        let name_id = self.value_names.get_id(name)?;
        let symbol_id = self.scopes.get(&scope_id)?.values.get(&name_id)?;
        self.registry.value_symbols.get_mut(symbol_id)
    }

    pub fn find_type_symbol_in_scope_mut(
        &mut self,
        name: &str,
        scope_id: ScopeId,
    ) -> Option<&mut TypeSymbol> {
        let name_id = self.type_names.get_id(name)?;
        let symbol_id = self.scopes.get(&scope_id)?.types.get(&name_id)?;
        self.registry.type_symbols.get_mut(symbol_id)
    }

    pub fn get_value_symbol(&self, id: ValueSymbolId) -> Option<&ValueSymbol> {
        self.registry.value_symbols.get(&id)
    }
    pub fn get_value_symbol_mut(&mut self, id: ValueSymbolId) -> Option<&mut ValueSymbol> {
        self.registry.value_symbols.get_mut(&id)
    }
    pub fn get_type_symbol(&self, id: TypeSymbolId) -> Option<&TypeSymbol> {
        self.registry.type_symbols.get(&id)
    }
    pub fn get_type_symbol_mut(&mut self, id: TypeSymbolId) -> Option<&mut TypeSymbol> {
        self.registry.type_symbols.get_mut(&id)
    }
    pub fn get_value_name(&self, id: ValueNameId) -> &str {
        self.value_names.lookup(id)
    }
    pub fn get_type_name(&self, id: TypeNameId) -> &str {
        self.type_names.lookup(id)
    }

    pub fn get_current_scope_id(&self) -> ScopeId {
        self.current_scope_id
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
            kind,
            trait_id: None,
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
        self.scopes
            .get_mut(&self.current_scope_id)
            .expect("Scope should exist")
    }
    pub fn current_scope(&self) -> &Scope {
        self.scopes
            .get(&self.current_scope_id)
            .expect("Scope should exist")
    }
    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> Option<&mut Scope> {
        self.scopes.get_mut(&scope_id)
    }
    pub fn get_scope(&self, scope_id: ScopeId) -> Option<&Scope> {
        self.scopes.get(&scope_id)
    }

    fn create_redeclaration_error(
        &self,
        name: String,
        span1: Option<Span>,
        span2: Option<Span>,
    ) -> BoxedError {
        match (span1, span2) {
            (Some(s1), Some(s2)) => Error::from_multiple_errors(
                ErrorKind::AlreadyDeclared(name),
                s2,
                Span::get_all_lines(self.lines.clone(), &[s1, s2]),
                self.file_path.clone()
            ),
            (Some(s), None) | (None, Some(s)) => Error::from_one_error(
                ErrorKind::AlreadyDeclared(name),
                s,
                (self.lines[s.start_pos.line - 1].clone(), s.start_pos.line),
                self.file_path.clone()
            ),
            (None, None) => Error::new(ErrorKind::AlreadyDeclared(name), self.file_path.clone()),
        }
    }
}

#[derive(Default)]
pub struct TraitRegistry {
    pub register: HashMap<TypeSymbolId, HashMap<TypeSymbolId, Vec<TraitImpl>>>,
    pub default_traits: HashMap<String, TypeSymbolId>,
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

    pub fn get_default_trait(&self, name: &String) -> TypeSymbolId {
        *self.default_traits.get(name).unwrap()
    }
}

/// A constraint imposed onto a metavariable.
#[derive(Debug, Clone)]
pub enum Constraint {
    /// Two types are equal.
    Equality(Type, Type),
    /// Two types are equal, but they cannot be equal to void.
    NonVoidEquality(Type, Type),
    /// A type denotes a function call on an instance.
    MethodCall(Type, Type, Vec<Type>, Type),
    /// A type denotes a function pointer.
    FunctionSignature(Type, Vec<Type>, Type),
    /// A type denotes the result of an operation that
    /// is trait overloadable.
    Operation(Type, Type, Type, Option<Type>, Operation),
    /// A type denotes the value of a member on an instance variable.
    InstanceMemberAccess(Type, Type, String),
    /// A type denotes a static member of a type, like an enum variant.
    StaticMemberAccess(Type, Type, String),
    /// A type denotes a fully qualified path access.
    FullyQualifiedAccess(Type, Type, Option<Type>, String),
    /// The initial type must be validly castable to the other.
    Cast(Type, Type),
    /// The type of an expression statement, conditional on its inner expression.
    ExpressionStatement(Type, Type)
}

/// Additional information about a constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConstraintInfo {
    pub span: Span,
    pub scope_id: ScopeId,
}

#[derive(Default)]
pub struct UnificationContext {
    next_id: TypeSymbolId,
    pub substitutions: HashMap<TypeSymbolId, Type>,
    pub constraints: VecDeque<(Constraint, ConstraintInfo)>
}

impl UnificationContext {
    fn get_next_uv_id(&mut self) -> TypeSymbolId {
        let old = self.next_id;
        self.next_id += 1;
        old
    }

    pub fn generate_uv_type(&mut self, symbol_table: &mut SymbolTable, span: Span) -> Type {
        let id = self.get_next_uv_id();

        let symbol = symbol_table
            .add_type_symbol(
                &format!("#uv_{}", id),
                TypeSymbolKind::UnificationVariable(id),
                vec![],
                QualifierKind::Private,
                Some(span),
            )
            .unwrap();

        Type::from_no_args(symbol)
    }

    pub fn register_constraint(&mut self, constraint: Constraint, info: ConstraintInfo) {
        self.constraints.push_back((constraint, info));
    }
}

pub struct UVCollectionContext {
    pub current_return_type: Option<Type>,
    pub current_function_stack: Vec<(ValueSymbolId, Vec<Span>)>,
    pub in_loop: bool
}

pub struct BuiltinTypes {
    primitives: Vec<TypeSymbolId>
}

pub struct SemanticAnalyzer {
    pub symbol_table: SymbolTable,
    pub trait_registry: TraitRegistry,
    pub unification_context: UnificationContext,
    pub uv_collection_ctx: UVCollectionContext,
    pub trusted: bool,
    builtin_types: BuiltinTypes,
    errors: Vec<Error>,
    lines: Rc<Vec<String>>,
    file_path: Option<String>
}

impl SemanticAnalyzer {
    pub fn new(lines: Rc<Vec<String>>, file_path: Option<String>) -> SemanticAnalyzer {
        let mut symbol_table = SymbolTable::new(lines.clone(), file_path.clone());
        let mut trait_registry = TraitRegistry::new();

        symbol_table.populate_with_defaults(&mut trait_registry);

        let builtin_types = BuiltinTypes {
            primitives: PrimitiveKind::iter()
                .map(|k| symbol_table.find_type_symbol(k.to_symbol_str()).unwrap().id)
                .collect()
        };

        SemanticAnalyzer {
            trait_registry,
            symbol_table,
            builtin_types,
            unification_context: UnificationContext::default(),
            uv_collection_ctx: UVCollectionContext { current_return_type: None, in_loop: false, current_function_stack: vec![] },
            trusted: false,
            errors: vec![],
            lines,
            file_path
        }
    }

    pub fn is_copy_type(&self, ty: &Type) -> bool {
        matches!(self.symbol_table.get_type_symbol(ty.symbol).unwrap().kind, TypeSymbolKind::Primitive(_) | TypeSymbolKind::FunctionSignature { .. } | TypeSymbolKind::Enum(_))
    }

    pub fn is_ancestor_of(&self, ancestor_id: ScopeId, child_id: ScopeId) -> bool {
        let mut current_id = Some(child_id);
        while let Some(id) = current_id {
            if id == ancestor_id { return true; }

            if let Some(scope) = self.symbol_table.get_scope(id) {
                current_id = scope.parent;
            } else {
                break;
            }
        }

        false
    }

    pub fn delete_uvs(&mut self) {
        let uvs_to_remove = self.symbol_table.registry.type_symbols
            .values()
            .filter_map(|symbol| {
                if let TypeSymbolKind::UnificationVariable(_) = symbol.kind {
                    Some((symbol.id, symbol.name_id))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
    
        if uvs_to_remove.is_empty() {
            return;
        }

        let uv_symbol_ids_set: HashSet<TypeSymbolId> = uvs_to_remove.iter().map(|(id, _)| *id).collect();

        self.symbol_table.registry.type_symbols.retain(|id, _| !uv_symbol_ids_set.contains(id));
        for scope in self.symbol_table.scopes.values_mut() {
            scope.types.retain(|_name_id, symbol_id| !uv_symbol_ids_set.contains(symbol_id));
        }

        let type_names_interner = &mut self.symbol_table.type_names;
        for (_, name_id) in uvs_to_remove {
            let name_to_remove = type_names_interner.vec[name_id].clone();
            type_names_interner.map.remove(name_to_remove.as_ref());
            type_names_interner.vec[name_id] = Rc::from("[deleted_uv]");
        }
    }

    pub fn get_primitive_type(&self, primitive: PrimitiveKind) -> TypeSymbolId {
        self.builtin_types.primitives[primitive as usize]
    }

    pub fn create_error(&self, kind: ErrorKind, primary_span: Span, spans: &[Span]) -> BoxedError {
        let lines = Span::get_all_lines(self.lines.clone(), spans);
        Error::from_multiple_errors(kind, primary_span, lines, self.file_path.clone())
    }

    pub fn set_source(&mut self, lines: Rc<Vec<String>>, file_path: Option<String>, trusted: bool) {
        self.lines = lines.clone();
        self.symbol_table.lines = lines;
        self.file_path = file_path.clone();
        self.symbol_table.file_path = file_path;
        self.trusted = trusted;
    }

    pub fn analyze(&mut self, program: &mut AstNode) -> Result<(), Vec<Error>> {
        macro_rules! pass {
            ($self:ident, $method:ident, $program:expr) => {{
                let pass_errors = $self.$method($program);
                if !pass_errors.is_empty() {
                    return Err(pass_errors);
                }
            }};
        }
        
        pass!(self, generic_constraints_pass, program);
        pass!(self, struct_field_type_collector_pass, program);
        pass!(self, impl_collector_pass, program);
        pass!(self, impl_deduplication_pass, program);
        pass!(self, uv_collector_pass, program);
        pass!(self, unification_pass, program);
        pass!(self, substitution_pass, program);
        pass!(self, never_return_check_pass, program);
        pass!(self, diverging_function_check_pass, program);
        pass!(self, const_check_pass, program);
        pass!(self, generic_value_check_pass, program);
        pass!(self, member_resolution_pass, program);
        // pass!(self, mutability_check_pass, program);
        pass!(self, trait_conformance_pass, program);
        pass!(self, explicit_drop_check_pass, program);

        Ok(())
    }
}

impl std::fmt::Display for InherentImpl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "InherentImpl(scope_id: {}, specialization: {:?}, generic_params: {:?}, span: {:?})",
            self.scope_id, self.specialization, self.generic_params, self.span
        )
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
            ValueSymbolKind::Function(scope_id, captured_items) 
                => format!("{}({})", if !captured_items.is_empty() { "Closure" } else { "Function" }, scope_id).blue(),
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
                if self.symbol.mutable {
                    write!(f, " {}", "mut".red())?;
                }
                write!(f, " {}", self.symbol.qualifier)?;
                Ok(())
            }
        }
        Displayer { symbol, table: self }
    }

    // TODO: Make display_type_symbol more robust.
    pub fn display_type_symbol<'a>(&'a self, symbol: &'a TypeSymbol) -> impl std::fmt::Display + 'a {
        struct Displayer<'a> {
            symbol: &'a TypeSymbol,
            table: &'a SymbolTable,
        }
        impl std::fmt::Display for Displayer<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let name = self.table.get_type_name(self.symbol.name_id);
                let type_variant = match &self.symbol.kind {
                    TypeSymbolKind::Struct((id, scopes)) => format!("Struct({}, {:?})", id, scopes).blue(),
                    TypeSymbolKind::Trait(id) => format!("Trait({})", id).cyan(),
                    TypeSymbolKind::Enum((id, scopes)) => format!("Enum({}, {:?})", id, scopes).blue(),
                    TypeSymbolKind::TypeAlias(id) => format!("TypeAlias({:?})", id).white(),
                    TypeSymbolKind::TraitSelf(id) => format!("TraitSelf({})", id).green(),
                    TypeSymbolKind::Primitive(k) => format!("Builtin({})", k).green(),
                    TypeSymbolKind::FunctionSignature {
                        params, return_type, ..
                    } => {
                        let params_str = params
                            .iter()
                            .map(|p_ty| self.table.display_type(p_ty))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("fn({}): {}", params_str, self.table.display_type(return_type)).blue()
                    }
                    TypeSymbolKind::Generic(constraints) => format!("Generic({:?})", constraints).white(),
                    TypeSymbolKind::UnificationVariable(id) => format!("UnificationVariable({})", id).red(),
                    TypeSymbolKind::OpaqueTypeProjection { ty, tr, member } =>
                        format!("[{:?} as {:?}]::{:?}", ty, tr, member).white()
                };
                write!(f, "[{}] {}", type_variant, name.cyan().bold())?;
                if !self.symbol.generic_parameters.is_empty() {
                    let params = self
                        .symbol
                        .generic_parameters
                        .iter()
                        .map(|id| if let Some(symbol) = self.table.registry.type_symbols.get(id) {
                            self.table.get_type_name(symbol.name_id)
                        } else {
                            "[deleted_symbol]"
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "<{}>", params)?;
                }
                Ok(())
            }
        }

        Displayer { symbol, table: self }
    }

    pub fn display_type<'a>(&'a self, ty: &'a Type) -> String {
        let type_symbol = &self.registry.type_symbols[&ty.symbol];
        match &type_symbol.kind {
            TypeSymbolKind::FunctionSignature {
                params,
                return_type,
                ..
            } => {
                let generic_params_str = if !type_symbol.generic_parameters.is_empty() {
                    let params_list = type_symbol
                        .generic_parameters
                        .iter()
                        .map(|p_id| {
                            self.get_type_name(self.get_type_symbol(*p_id).unwrap().name_id)
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("<{}>", params_list)
                } else {
                    "".to_string()
                };

                let params_str = params
                    .iter()
                    .map(|p_ty| self.display_type(p_ty))
                    .collect::<Vec<_>>()
                    .join(", ");

                let is_null_return = if let Some(symbol) = self.get_type_symbol(return_type.symbol) {
                    matches!(symbol.kind, TypeSymbolKind::Primitive(PrimitiveKind::Void))
                } else {
                    false
                };

                if is_null_return {
                    format!("fn{}({})", generic_params_str, params_str)
                } else {
                    format!(
                        "fn{}({}) -> {}",
                        generic_params_str,
                        params_str,
                        self.display_type(return_type)
                    )
                }
            }
            _ => {
                let base_name = self.get_type_name(type_symbol.name_id);
                if ty.args.is_empty() {
                    base_name.to_string()
                } else {
                    let arg_str = ty.args
                        .iter()
                        .map(|arg| self.display_type(arg))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{}>", base_name, arg_str)
                }
            }
        }
    }

    fn display_scope(
        &self,
        scope_id: ScopeId,
        indent: usize,
        f: &mut std::fmt::Formatter,
    ) -> std::fmt::Result {
        let scope = self.scopes.get(&scope_id).unwrap();
        for symbol_id in scope.values.values() {
            let symbol = &self.registry.value_symbols[symbol_id];
            writeln!(
                f,
                "{:indent$}[Value({})] {}",
                "",
                symbol_id,
                self.display_value_symbol(symbol),
                indent = indent
            )?;
        }
        for symbol_id in scope.types.values() {
            let symbol = &self.registry.type_symbols[symbol_id];
            writeln!(
                f,
                "{:indent$}[Type({})] {}",
                "",
                symbol_id,
                self.display_type_symbol(symbol),
                indent = indent
            )?;
        }
        let mut child_scope_ids: Vec<ScopeId> = self
            .scopes
            .values()
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
        let scope = self.real_starting_scope;

        writeln!(f, "--- User Scope ({}) ---", scope)?;
        self.display_scope(scope, 0, f)
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
                for (trait_id, impls) in &self.registry.register {
                    let trait_symbol = &self.table.registry.type_symbols[trait_id];
                    let trait_name = self.table.get_type_name(trait_symbol.name_id);

                    if self.registry.default_traits.contains_key(trait_name) {
                        continue;
                    }

                    writeln!(
                        f,
                        "{}",
                        format!("[Trait({})] {}", trait_id, trait_name).underline()
                    )?;
                    for (type_id, impl_details) in impls {
                        let type_symbol = &self.table.registry.type_symbols[type_id];
                        let type_name = self.table.get_type_name(type_symbol.name_id);
                        write!(f, "  for [Type({})] {}: ", type_id, type_name)?;
                        for (i, impl_detail) in impl_details.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{:?}", impl_detail)?;
                        }
                        writeln!(f)?;
                    }
                }
                Ok(())
            }
        }
        Displayer {
            registry: self,
            table: symbol_table,
        }
    }
}

impl Constraint {
    fn fmt<'a>(&'a self, table: &'a SymbolTable) -> impl std::fmt::Display + 'a {
        struct C<'a> {
            c: &'a Constraint,
            t: &'a SymbolTable,
        }
        impl std::fmt::Display for C<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                use Constraint::*;
                match self.c {
                    Equality(lhs, rhs) => write!(
                        f,
                        "{} {} {}",
                        self.t.display_type(lhs).yellow(),
                        "=".blue(),
                        self.t.display_type(rhs).yellow()
                    ),
                    NonVoidEquality(lhs, rhs) => write!(
                        f,
                        "{} {} {} [non-void]",
                        self.t.display_type(lhs).yellow(),
                        "!".blue(),
                        self.t.display_type(rhs).yellow()
                    ),
                    MethodCall(instance, callee, ps, r) => {
                        let ps_str = ps
                            .iter()
                            .map(|p| self.t.display_type(p))
                            .collect::<Vec<_>>()
                            .join(", ");
                        write!(
                            f,
                            "({}).call({}) -> {} where callee is {}",
                            self.t.display_type(instance).yellow(),
                            ps_str,
                            self.t.display_type(r),
                            self.t.display_type(callee).cyan()
                        )
                    },
                    FunctionSignature(callee, ps, r) => {
                        let ps_str = ps
                            .iter()
                            .map(|p| self.t.display_type(p))
                            .collect::<Vec<_>>()
                            .join(", ");
                        write!(
                            f,
                            "{} {} fn({}) -> {}",
                            self.t.display_type(callee).yellow(),
                            "=".blue(),
                            ps_str,
                            self.t.display_type(r)
                        )
                    }
                    Operation(result, trait_ty, lhs, rhs, operation) => {
                        let op_str = if let Some(r) = rhs {
                            format!("{}({}, {})", operation, self.t.display_type(lhs), self.t.display_type(r))
                        } else {
                            format!("{}({})", operation, self.t.display_type(lhs))
                        };

                        write!(
                            f,
                            "{} = {} where {}: {}<{}>",
                            self.t.display_type(result).yellow(),
                            op_str,
                            self.t.display_type(lhs),
                            self.t.display_type(trait_ty).cyan(),
                            if let Some(rhs) = rhs {
                                self.t.display_type(rhs)
                            } else {
                                "Self".to_string()
                            }
                        )
                    }
                    InstanceMemberAccess(result, base, m) => write!(
                        f,
                        "{} = {}.{}",
                        self.t.display_type(result).yellow(),
                        self.t.display_type(base),
                        m.green()
                    ),
                    StaticMemberAccess(result, base, m) => write!(
                        f,
                        "{} = {}::{}",
                        self.t.display_type(result).yellow(),
                        self.t.display_type(base).bright_blue(),
                        m.green()
                    ),
                    FullyQualifiedAccess(result, ty, tr, m) => {
                        write!(f, "{} = <{}", self.t.display_type(result).yellow(), self.t.display_type(ty))?;
                        if let Some(tr) = tr {
                            write!(f, " as {}", self.t.display_type(tr))?;
                        }
                        write!(f, ">.{}", m.green())
                    },
                    Cast(initial, r#final) => write!(
                        f,
                        "{} -> {}",
                        self.t.display_type(initial).yellow(),
                        self.t.display_type(r#final).yellow()
                    ),
                    ExpressionStatement(inner, result) => write!(
                        f,
                        "{} = {};",
                        self.t.display_type(result).yellow(),
                        self.t.display_type(inner)
                    )
                }
            }
        }
        C { c: self, t: table }
    }
}

impl UnificationContext {
    pub fn display<'a>(&'a self, table: &'a SymbolTable) -> impl std::fmt::Display + 'a {
        use colored::*;

        struct D<'a> {
            ctx: &'a UnificationContext,
            tbl: &'a SymbolTable,
        }
        
        impl std::fmt::Display for D<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                if self.ctx.substitutions.is_empty() {
                    writeln!(f, "{}", "* Substitutions: (none)".dimmed())?;
                } else {
                    writeln!(f, "* {}", "Substitutions:".bold())?;
                    let mut subs: Vec<_> = self.ctx.substitutions.iter().collect();
                    subs.sort_by_key(|(uv, _)| *uv);
                    for (uv_symbol_id, sym) in subs {
                        let uv_name = self.tbl.get_type_name(self.tbl.get_type_symbol(*uv_symbol_id).unwrap().name_id);
                        let lhs = uv_name.red().bold();
                        let rhs = self.tbl.display_type(sym).green();
                        writeln!(f, "    {} {} [{}]({})", lhs, "->".blue(), rhs, sym.symbol)?;
                    }
                }

               let unresolved_uvs: Vec<&TypeSymbol> = self.tbl.registry.type_symbols
                    .values()
                    .filter(|symbol| {
                        if let TypeSymbolKind::UnificationVariable(_) = symbol.kind {
                            !self.ctx.substitutions.contains_key(&symbol.id)
                        } else {
                            false
                        }
                    })
                    .collect();

                if unresolved_uvs.is_empty() {
                    writeln!(f, "{}", "* Unresolved UVs: (none)".dimmed())?;
                } else {
                    let mut uv_names: Vec<String> = unresolved_uvs
                        .iter()
                        .map(|s| self.tbl.get_type_name(s.name_id).red().to_string())
                        .collect();
                    uv_names.sort();
                    let list = uv_names.join(", ");
                    writeln!(f, "* {} {}", "Unresolved UVs:".bold(), list)?;
                }

                // --- constraints ------------------------------------------------------------
                if self.ctx.constraints.is_empty() {
                    writeln!(f, "{}", "* Constraints: (none)".dimmed())
                } else {
                    writeln!(f, "* {}", "Constraints:".bold())?;
                    for (i, c) in self.ctx.constraints.iter().enumerate() {
                        writeln!(f, "    {}) {}", i + 1, c.0.fmt(self.tbl))?;
                    }
                    Ok(())
                }
            }
        }

        D {
            ctx: self,
            tbl: table,
        }
    }
}

impl std::fmt::Display for SemanticAnalyzer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}", "Symbol Table:".bold().underline())?;
        writeln!(f, "{}", self.symbol_table)?;
        writeln!(f, "\n{}", "Trait Registry:".bold().underline())?;
        writeln!(f, "{}", self.trait_registry.display(&self.symbol_table))?;
        writeln!(f, "\n{}", "Unification Context:".bold().underline())?;
        writeln!(f, "{}", self.unification_context.display(&self.symbol_table))?;

        Ok(())
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let base_name = format!("TypeSymbol({})", self.symbol);
            if self.args.is_empty() {
                write!(f, "{}", base_name)
            } else {
                let arg_str = self.args
                    .iter()
                    .map(|arg| format!("{}", arg))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{}<{}>", base_name, arg_str)
            }
    }
}