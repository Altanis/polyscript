const FILES = [
    "frontend/ast.rs",
    "frontend/lexer.rs",
    "frontend/token_parser.rs",
    "middle/semantic_analyzer.rs", 
    "middle/symbols.rs",
    "middle/uv_collector.rs",
    "middle/unification.rs",
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