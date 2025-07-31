const FILES = [
    "frontend/syntax/ast.rs",
    "frontend/syntax/lexer.rs",
    "frontend/syntax/parser.rs",
    "frontend/semantics/analyzer.rs", 
    "frontend/semantics/symbols.rs",
    "frontend/semantics/uv_collector.rs",
    "frontend/semantics/unification.rs",
    "backend/codegen/codegen.rs",
    "utils/error.rs",
    "utils/kind.rs"
];

const fs = require("fs");

let contents = "";

for (const file of FILES) {
    contents += `// ${file}\n`;
    contents += fs.readFileSync(`./src/${file}`);
    contents += "\n\n";
}

fs.writeFileSync("reproduced.txt", contents);