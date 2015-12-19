# C Verifier

### Introduction
This repository contains the implementation of a sound software verification tool for a subset of the C programming language.

The verifier is using the following tools or components :
- A Java parser using [Antlr](http://www.antlr.org/) for constructing the AST
- A Semantic analysis component (check class tool.Typechecker)
- The [Z3 SMT Solver](https://github.com/z3prover/z3/wiki)
- The [LIT testing tool](https://pypi.python.org/pypi/lit) for automatic execution of testcases

### Grammar
The language that is verified is a subset of C. It includes the most basic elements of C, except some features (like structs etc.)

The grammar of the language has the following rules :
```sh
Program := VarDecl* ProcedureDecl*
VarDecl := 'int' ID ';'
ProcedureDecl := 'int' ID '(' -FormalParam- ')' -Prepost-
                 '{' Stmt* 'return' Expr ';' '}'
FormalParam := 'int' ID
Prepost := Requires | Ensures | CandidateRequires | CandidateEnsures
Requires := 'requires' Expr
Ensures := 'ensures' Expr
Stmt := VarDecl | AssignStmt | AssertStmt | AssumeStmt | HavocStmt | CallStmt | IfStmt | WhileStmt | BlockStmt
AssignStmt := ID '=' Expr ';'
AssertStmt := 'assert' Expr ';'
AssumeStmt := 'assume' Expr ';'
HavocStmt := 'havoc' ID ';'
IfStmt := 'if' '(' Expr ') BlockStmt ('else' BlockStmt)?
BlockStmt := '{' Stmt* '}'
Expr := Expr '?' Expr ':' Expr | Expr BinaryOp Expr | UnaryOp Expr | 
        non-negative decimal integer | ID | '(' Expr ')
        '\result' | '\old' '(' ID')'
BinaryOp := '||' | '&&' | '|' | '^' | '&' | '==' | '!=' |
            '<' | '<=' | '>' | '>=' | '<<' | '>>' |
            '+' | '-' | '*' | '/' | '%'
UnaryOp := '+' | '-' | '!' | '~'
ID := any legal C identifier

CandidateRequires := 'candidate_requires' Expr
CandidateEnsures := 'candidate_ensures' Expr
CallStmt := ID '=' ID '(' -Expr- ')' ';'
WhileStmt :=  'while' '(' Expr ')' -LoopInvariant- BlockStmt
LoopInvariant := Invariant | CandidateInvariant
Invariant := 'invariant' Expr
CandidateInvariant := 'candidateInvariant' Expr
```

* Also available in [grammar.pdf](https://github.com/dimosr7/c_verifier/blob/master/grammar.pdf)

### Compilation on terminal

- To compile the whole program :
```sh
make
```

- To execute the program with a test file
```sh
./srtool . tests/part1/correct/divzero.c
```

- To just auto-generate from ANTLR the Visitor for grammar in [SimpleC.g](https://github.com/dimosr7/c_verifier/blob/master/parser/SimpleC.g):
```sh
java -cp ../antlr-4.5.1-complete.jar org.antlr.v4.Tool -visitor -package parser SimpleC.g
```

### Using IDE

- Import the project in IDE using mode "from existing sources"
- Add the library file antlr-4.5.1-complete.jar in the root folder to the project
- Set tool.SRTool as the Main Class
- Make sure that the working directory is the root folder of the project (so that .z3 executable is found)

### Automatic testing

To execute tests with Lit, you will have to :
- change the static field of SRTool, Z3_PATH to "z3"
- add z3 in your PATH

- Install lit, using python pip
```sh
pip install lit
```

- Run a single test
```sh
lit --max-time=1800 tests/part1/correct/divzero.c 1> lit_report.txt 2> lit_error.txt
```

- Run only a part of tests
```sh
lit --max-time=1800 tests/part1/correct 1> lit_report.txt 2> lit_error.txt
```

- Run all tests (resource intensive)
```sh
lit --max-time=1800 tests 1> lit_report.txt 2> lit_error.txt
```