# C Verifier

### Introduction
This repository contains the implementation of a verification tool for a subset of the C programming language.

The verifier is using the following tools or components :
- A Java parser using [Antlr](http://www.antlr.org/) for constructing the AST
- [JUnit](http://junit.org/) for the unit testing 
- A typechecker
- The [Z3 SMT Solver](https://github.com/z3prover/z3/wiki) 

### Grammar
The language that is verified is a subset of C. It includes the most basic of the elements of C, except pointers, structures etc.

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

### Compilation

- To compile the whole program :
```sh
javac -cp antlr-4.5.1-complete.jar */*.java
```

- To execute the program with test file
```sh
./srtool tests/correct/divzero.c
```

- To just compile (auto-generate through ANTLR grammar) the Visitor :
```sh
java -cp ../antlr-4.5.1-complete.jar org.antlr.v4.Tool -visitor -package parser SimpleC.g
```