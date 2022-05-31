# Type Inference Program

## Background

This program implements a constraint-based type inference algorithm for a typed lambda calculus with pairs, integers, booleans, let-definitions, and recursive functions, which is summarized by the following syntax:

![alt text](/assets/img/language.png "Language")

### Parsing

See ./main/lexer.mll and ./main/parser.mly for parsing technicalities. 

See ./main/ast.ml for abstract types.

### Constraints and Unification

See ./main/check.ml where the functions check and unify are implemented. The function check takes in a context and an expression and generates a type and a set of constraints. The function unify takes a set of constraints and unifies them or throws an error when there is a contradiction in the constraints, meaning that the expression is not well-typed.

## Usage

1. Go into ./main and run make to compile executables.
2. Type an expression in a file such as [FILENAME].lam
3. Run ./main/lam [FILENAME].lam