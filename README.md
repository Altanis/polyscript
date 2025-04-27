# PolyScript

Toy language that can both be interpreted and compiled to machine code. It can be embedded into games with variables being read at runtime by any language.

## planning board thing
Whitespaces: Ignored
Comments: Started by '#', lasts until end of line (maybe use //)
Operations:
    Not // !,
    BitwiseNegate // ~,
    Increment // ++,
    Decrement // --,

    Add // +,
    Sub // -,
    Mul // *,
    Exp // **,
    Div // /,
    Mod // %,
    AddEq // +=,
    SubEq // -=,
    MulEq // *=,
    DivEq // /=,
    ModEq // %=,
    BitwiseAnd // &,
    BitwiseOr // |,
    BitwiseXor // ^,
    RightBitShift // >>,
    LeftBitShift // <<,
    Assign // =,

    And // &&,
    Or // ||,
    GreaterThan // >,
    Geq, // ≥
    LessThan // <,
    Leq, // ≤
    Equivalence // ==

Numbers:
    42 -> decimal
    0b1010/0B1010 -> binary
    0o7373/0O7373 -> octal
    0xFF/0XFF -> hex
    3.14 -> float
    314e-2/314E-2 -> float

Identifiers:
    int/float/bool/string -> variable types
    int/float/bool/string/void -> return types from function
    let -> mutable var decl
    const -> immutable var decl
    class -> class decl
    override -> polymorphism invocation
    true/false -> boolean literals
    fn -> function decl
    for -> for loop init
    while -> while loop init
    return/break/continue/throw -> control flow keywords
    if/else -> if/else condition init

Symbols:
    ; -> ends line
    () -> starts/ends expression
        ex: (2 + 3 * 4) * 5
    {} -> starts/ends scope
        if (x + 2 == 3) { ... }
    [] -> unused so far
    , -> separator of lists
        function(1, 2, 3)
    : -> invokes type/class inheritance
        let x: int = 5;
        class Dog : Animal { ... }

Example Grammar Templates:
    Variable Declaration:
        ```
        let a = "Hello, world!"; # implicit types should be fine
        let b: int = 5;
        const c: float = 3.0;
        let d; # maybe dont allow for no expr.
        ```
    Function Declaration:
        ```
        fn name() {}
        fn name(x: int): void { .. }
        fn name(x: int, y: int): int { .. }
        fn name(x: int = 3, y: int): float { .. }
        ```
    Blocks:
        ```
        {
            let x: int = 5;
        }

        # x is not accessible here by scoping
        # maybe let blocks return a value?
        ```
    Loops:
        ```
        # While Loop
        while (0) {}

        # For Loop
        for (int i = 0; i < 5; ++i) { .. }

        int j = 0;
        for (;j < 5; ++j) { .. }

        for (;;) { .. }
        ```
    Classes:
        ```
        class Animal {
            public const SPECIES: string = "Animal"; # static, accessible via Animal.SPECIES
            private let age: int = 42; # instance field

            ## STATIC METHODS / CTORS ##
            public fn from_x(x: int): Animal {
                
            }

            public fn from_y(y: int): Animal {

            }

            ## INSTANCE METHODS ##
            public fn speak(this) {
                this.talk();
            }

            private fn talk(this) { .. }
        }

        class Dog: Animal {}
        ```
    Control Flow:
        ```
            while (true) {
                break;
            }

            for (let i = 0; i < 5; ++i) {
                continue;
            }

            fn add(a: int, b: int = 0) {
                return a + b;
            }

            fn panic(message: string) {
                throw message;
            }
        ```

### todo
- fix error messages to be better

### notes
most complicated features would be functions/closures, classes/inheritance, imports/exports, async, and a stdlib that supports i/o function (printing, reading files, sockets, event loop, etc.)

builtin functions:
-> io.ps
    -> #print()
    -> #error()
    -> #write_file()
    -> #read_file()
-> sys.ps

    -> #exit()