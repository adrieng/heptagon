# Scripts

## `clean_heptc`
* Arguments: none.
* Usages: used to remove heptc binaries and compiled files. It's main goal is to do a fresh compilation. heptc script may be called right after this to recompile all the things needed.

## `heptc`
* Arguments: see `heptc -h`
* Usages: wrap the real compiler in order to recompile it if it doesn't exists, and to recompile pervasives if needed. calling clean_heptc before it will ensure recompilation of everything.

# Code organization
```mermaid
flowchart TD
subgraph Heptagon
Lexer[Lexer heptagon/parsing/hept_lexer.mll] --> Parser[Parser heptagon/hept_parser.mly]
Parser --> Parsetree(Parsetree heptagon/parsing/hept_parsetree.ml)
Parsetree --> Scoping(Scoping heptagon/parsing/hept_scoping.ml)
Scoping --> Heptagon(Heptagon AST heptagon/heptagon.ml)
end
```

- `global/` contains modules used in all the compiler: types, clocks, idents, signatures, names, modules
- `utilities/` contains various utilities
- `heptagon/` contains AST definition of Heptagon, parsing, analysis and internal Heptagon transformations
- `minils/` contains AST definition of MiniLS, analysis (clocking, interferences), internal MiniLS transformations, code generation towards Ctrln
- `obc/` contains AST definition of Object code (Obc), internal Obc transformations, and code generation towards C and Java
