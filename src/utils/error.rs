use colored::Colorize;

use crate::boxed;

use super::kind::Span;

#[derive(Debug, Clone, PartialEq)]
pub enum ErrorKind {
    UnrecognizedSymbol(String),
    UnexpectedEOF,
    InvalidDigit(String),
    InvalidEscapeSequence(String),
    UnterminatedString,
    UnterminatedDirective,
    InvalidDirective(String),
    InvalidChar(String),
    UnterminatedChar,
    UnexpectedToken(String, String, String),
    UnknownIdentifier(String),
    UnresolvedType(String),
    AlreadyDeclared(String),
    UnknownType,
    InvalidImpl(Option<String>),
    ExpectedType,
    InvalidConstraint(String),
    ConstraintNotAllowed,
    UnimplementedTrait(String, String),
    ConflictingTraitImpl(String),
    DuplicateDefinitionInImpl(String, String),
    DeformedTraitImpl {
        trait_name: String,
        missing: Vec<String>,
        extra: Vec<String>,
    },
    ConflictingInherentImpl(String),
    InvalidDereference(String),
    ExpectedScopedItem,
    MemberNotFound(String, String),
    InvalidFieldAccess(String),
    IncorrectFieldAccessRhs,
    TypeAnnotationNeeded(usize),
    SelfOutsideImpl,
    InvalidSelf(&'static str),
    ExpectedIdentifier,
    ExpectedInteger,
    ExpectedString,
    TypeMismatch(String, String, Option<String>),
    NotCallable(String),
    ArityMismatch(usize, usize),
    InvalidReturn,
    InvalidStructLiteral(String),
    InvalidField(String, String),
    MismatchedStructFields {
        struct_name: String,
        missing_fields: Vec<String>,
        extra_fields: Vec<String>,
    },
    InvalidCast(String, String),
    DuplicateSymbolsInInherentImpl(String, String),
    InvalidPathQualifier,
    OutsideOfLoop,
    InvalidTypeReference(String, usize, usize),
    UnusedGenericParameter(String),
    MutatingImmutableData(String),
    ExpectedValue,
    PrivateMemberAccess(String, String),
    VariableOfVoidType,
    GenericFunctionAsValue(String),
    NeedsHeapAllocation(String),
    ClosureWithGenerics(String),
    NonConstantInitializer(String, String),
    InvalidImport(String, String),
    InvalidCall(String, String),
    UntrustedContext(String),
    ExplicitDestruction,
    NonDivergingNeverFunction(String),
    DivergingFunctionWithNonNeverReturnType(String, String)
}

impl ErrorKind {
    fn as_str(&self) -> String {
        match self {
            ErrorKind::UnrecognizedSymbol(symbol) => format!("unrecognized symbol {symbol}"),
            ErrorKind::UnexpectedEOF => "unexpected <eof> while parsing".to_string(),
            ErrorKind::InvalidDigit(digit) => format!("invalid digit {digit}"),
            ErrorKind::InvalidEscapeSequence(sequence) => format!("invalid escape sequence {sequence}"),
            ErrorKind::UnterminatedString => "string left unterminated".to_string(),
            ErrorKind::UnterminatedDirective => "compiler directive left unterminated".to_string(),
            ErrorKind::InvalidDirective(directive) => format!("unknown compiler directive {directive}"),
            ErrorKind::InvalidChar(char) => format!("invalid char {char}"),
            ErrorKind::UnterminatedChar => "unterminated or degenerate char".to_string(),
            ErrorKind::UnexpectedToken(symbol, found, expected) => format!(
                "unexpected token: found \"{symbol}\" of type {found}, expected {expected}"
            ),
            ErrorKind::UnknownIdentifier(name) => format!("could not find \"{name}\" in scope"),
            ErrorKind::UnresolvedType(name) => format!(
                "type for symbol \"{name}\" has not been determined by this line"
            ),
            ErrorKind::AlreadyDeclared(variable) => format!(
                "attempted to declare {variable}, but it already exists in scope"
            ),
            ErrorKind::UnknownType => "could not determine type of data by this line".to_string(),
            ErrorKind::InvalidImpl(type_ref) => format!(
                "cannot construct impl block for {}",
                type_ref.as_ref().map_or("an unnamed identifier", |v| v)
            ),
            ErrorKind::ExpectedType => "expected this to resolve to a type".to_string(),
            ErrorKind::InvalidConstraint(constraint) => format!(
                "expected constraint to be a trait, instead found \"{constraint}\""
            ),
            ErrorKind::ConstraintNotAllowed => "type variable cannot be constrained to a trait in this position".to_string(),
            ErrorKind::UnimplementedTrait(tr, ty) => {
                format!("trait {tr} not implemented for type {ty}")
            }
            ErrorKind::ConflictingTraitImpl(namespace) => {
                format!("conflicting implementations of trait: {}", namespace)
            }
            ErrorKind::DuplicateDefinitionInImpl(name, namespace) => {
                format!("symbol `{name}` defined multiple times in impls for `{namespace}`")
            }
            ErrorKind::DeformedTraitImpl {
                trait_name,
                missing,
                extra,
            } => {
                let mut message = format!("deformed implementation of trait `{}`", trait_name);
                if !missing.is_empty() {
                    message.push_str(&format!("\n  - missing items: {}", missing.join(", ")));
                }
                if !extra.is_empty() {
                    message.push_str(&format!("\n  - extraneous items: {}", extra.join(", ")));
                }
                message
            }
            ErrorKind::ConflictingInherentImpl(ty) => {
                format!("conflicting implementations for type {ty}")
            }
            ErrorKind::InvalidDereference(ty) => {
                format!("attempted to dereference non-pointer type {ty}")
            },
            ErrorKind::ExpectedScopedItem => "expected an item with a scope".to_string(),
            ErrorKind::MemberNotFound(field, type_name) => {
                format!("member \"{field}\" not found in type {type_name}")
            }
            ErrorKind::InvalidFieldAccess(type_name) => {
                format!("type {type_name} does not comprise fields")
            }
            ErrorKind::IncorrectFieldAccessRhs => "cannot access this field".to_string(),
            ErrorKind::TypeAnnotationNeeded(id) => format!("cannot infer type for this; a type annotation may be needed (#uv_{})", id),
            ErrorKind::SelfOutsideImpl => "use of Self outside of an impl block".to_string(),
            ErrorKind::InvalidSelf(place) => format!("found \"self\" {place}"),
            ErrorKind::ExpectedIdentifier => "expected an identifier for the rhs of a field access operation".to_string(),
            ErrorKind::ExpectedInteger => "expected an integer literal in this position".to_string(),
            ErrorKind::ExpectedString => "expected a string literal in this position".to_string(),
            ErrorKind::TypeMismatch(t1, t2, str) => {
                format!("types {t1} and {t2} are incompatible{}", match str {
                    Some(s) => format!(" [{s}]"),
                    None => "".to_string()
                })
            },
            ErrorKind::NotCallable(ty) => format!("{ty} is not callable"),
            ErrorKind::ArityMismatch(expected, given) => format!("expected {expected} arguments, got {given} arguments"),
            ErrorKind::InvalidReturn => "return statement found outside of function".to_string(),
            ErrorKind::InvalidStructLiteral(ty) => format!("attempted to construct {ty} as a struct literal, but it is not a struct"),
            ErrorKind::InvalidField(struct_name, field_name) => format!("struct {struct_name} does not have field {field_name}"),
            ErrorKind::MismatchedStructFields {
                struct_name,
                missing_fields,
                extra_fields,
            } => {
                let mut message = format!("mismatched fields for struct `{}`", struct_name);
                if !missing_fields.is_empty() {
                    message.push_str(&format!(
                        "\n  - missing fields: {}",
                        missing_fields.join(", ")
                    ));
                }
                if !extra_fields.is_empty() {
                    message.push_str(&format!(
                        "\n  - extra fields: {}",
                        extra_fields.join(", ")
                    ));
                }
                message
            },
            ErrorKind::InvalidCast(from, to) => format!("cannot cast type `{from}` to `{to}`"),
            ErrorKind::DuplicateSymbolsInInherentImpl(name, namespace) => {
                format!("symbol `{name}` defined multiple times in inherent impls for namespace {namespace}")
            },
            ErrorKind::InvalidPathQualifier => "path qualifier can only be used on the left side of a member access".to_string(),
            ErrorKind::OutsideOfLoop => "use of control flow keyword outside of loop".to_string(),
            ErrorKind::InvalidTypeReference(ty, given, expected) => {
                format!("type {ty} was given {given} generic parameters but expects {expected} generic parameters")
            },
            ErrorKind::UnusedGenericParameter(name) => format!("unused generic parameter `{}`", name),
            ErrorKind::MutatingImmutableData(ident) => format!("cannot mutable immutable data {ident}"),
            ErrorKind::ExpectedValue => "expected a value".to_string(),
            ErrorKind::PrivateMemberAccess(member, ty) => format!("member `{}` is private to type `{}`", member, ty),
            ErrorKind::VariableOfVoidType => "variable cannot take on void type".to_string(),
            ErrorKind::GenericFunctionAsValue(name) => format!("generic function `{}` cannot be used as a value without being called", name),
            ErrorKind::NeedsHeapAllocation(value_symbol) => format!("{value_symbol} needs to be heap allocated"),
            ErrorKind::ClosureWithGenerics(name) => format!("closure \"{}\" defines generic parameters", if name.is_empty() { "[unnamed closure]" } else { name }),
            ErrorKind::NonConstantInitializer(constant, reason) => format!("initializer for constant {} is not a constant expression: {}", constant, reason),
            ErrorKind::InvalidImport(path, reason) => format!("invalid import of {}: {}", path, reason),
            ErrorKind::InvalidCall(method, ty) => format!("method `{}` is an instance method, not a static method, and cannot be called on type `{}` directly", method, ty),
            ErrorKind::UntrustedContext(reason) => format!("attempted to use trusted feature in untrusted context: {reason}"),
            ErrorKind::ExplicitDestruction => "cannot explicitly call the Drop implementation for a value".to_string(),
            ErrorKind::NonDivergingNeverFunction(name) => format!("function `{}` is declared to return 'never' but has a path that may return", name),
            ErrorKind::DivergingFunctionWithNonNeverReturnType(name, return_type) => format!("function `{}` diverges on all paths, so its return type must be 'never', not '{}'", name, return_type)
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Error {
    kind: ErrorKind,
    span: Span,
    source_lines: Vec<(String, usize)>,
    file_path: Option<String>,
}

pub type BoxedError = Box<Error>;

impl Error {
    pub fn new(kind: ErrorKind, file_path: Option<String>) -> BoxedError {
        boxed!(Error {
            kind,
            span: Span::default(),
            source_lines: vec![],
            file_path
        })
    }

    pub fn from_one_error(
        kind: ErrorKind,
        span: Span,
        source_line: (String, usize),
        file_path: Option<String>,
    ) -> BoxedError {
        boxed!(Error {
            kind,
            span,
            source_lines: vec![source_line],
            file_path,
        })
    }

    pub fn from_multiple_errors(
        kind: ErrorKind,
        span: Span,
        source_lines: Vec<(String, usize)>,
        file_path: Option<String>,
    ) -> BoxedError {
        boxed!(Error {
            kind,
            span,
            source_lines,
            file_path,
        })
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "[{}] {}", "error".red().bold(), self.kind.as_str())?;
        let file_name = self.file_path.as_ref().map(|path| path.split('/').next_back().unwrap_or(path)).unwrap_or("[insert_file_here]");
        writeln!(f, "as found in {}:{}:{}", file_name, self.span.start_pos.line, self.span.start_pos.column)?;

        let mut used_numbers = vec![];
        for (content, number) in self.source_lines.iter() {
            if used_numbers.contains(number) {
                continue;
            } else {
                used_numbers.push(*number);
            }

            writeln!(f, "    {}", content)?;

            if *number == self.span.start_pos.line {
                writeln!(
                    f,
                    "    {}^{}^",
                    " ".repeat(self.span.start_pos.column - 1),
                    "^".repeat(
                        self.span
                            .end_pos
                            .column
                            .saturating_sub(self.span.start_pos.column)
                    )
                )?;
            }
        }

        Ok(())
    }
}

impl std::error::Error for Error {}