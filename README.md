# C Verifier

This repository contains the implementation of a sound software verification tool for a subset of the C programming language.

### Dependencies

The verifier is using the following tools or components :
- A Java parser using [Antlr](http://www.antlr.org/) for constructing the AST
- A Semantic analysis component (check class tool.Typechecker)
- The [Z3 SMT Solver](https://github.com/z3prover/z3/wiki)
- The [LIT testing tool](https://pypi.python.org/pypi/lit) for automatic execution of testcases

### Introduction

The software verifier makes use of **assert** to encode possible bugs (like division by zero), but it can also be used by the programmer to add specific conditions that have to be satisfied for the program to be correct at specific places.
It also makes use of **loop invariants**, where there are regular invariants defined by the programmer and candidate loop invariants, that are defined by the developer, but remain to be confirmed by the tool that are indeed inductive loop invariants.
In the same approach, it makes use of **pre-conditions** (*requires*) and **post-conditions** (*ensures*) of procedures, where the regular pre-conditions and post-conditions are defined by the programmer and are definitely genuine specs, while the candidate ones remain to be confirmed by the tool.
The tool also makes use of **assume** and **havoc**, to achieve and over-approximation during the verification of the program. The operators *\result* and *\old* are used to represent the result of a procedure and the value of the variable before entering the current procedure.

For example, let's see the following example (globals.c in part1) :
```c
int g;

int globals() {

	g = 0;
	int a;
	a = 2;
	if(a == 2) {
		int g;
		g = 5;
	}
	else {
		g = 7;
	}
	assert(g == 5);
	return 0;
}
```
This program is buggy, since the assignment inside the if block statement is done in a new scope and the global variable g is not affected. Thus, the final assertion fails. This example can be run as shown below.

### Architecture

The SRTool is the bootstrap class. It initially uses the Typechecker to see if there is any semantic or syntactic problem with the program. If there is no such error, it uses the GeneratorVisitor that creates an instance of the whole program, that also contains an instance of each procedure of the program. Then, the VerifierVisitor is used to apply several verification methods, until one of them gives a useful result. Briefly, simple summarisation is initially executed, then the Houdini Algorithm is applied to conclude about which candidate invariants and conditions are regular and finally verification with incremental bounded model checking (loop unwinding) is applied.

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

The only slight differences from C are the following :
- The *int* type denotes 32-bit integers that have wrap around behaviour (contrary to undefined behaviour of C standards). It is assumed that the only type is int for simplicity and booleans are represented through booleans 0,1
- Reading from an unitialised variable gives an arbitrary value (contrary to undefined behaviour of C standards)
- Global variables are initially uninitialised (while in C they are initialised to 0)
- Shifting a 32-bit value by more than 32 bits yields the result 0 (contrary to undefined behaviour of C standards)
- x/0 and x%0 is defined to be 0 (contrary to undefined behaviour of C standards) 

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

To execute tests with Lit, you will initially have to change the static field of SRTool, Z3_PATH to "z3" and add z3 in your PATH

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