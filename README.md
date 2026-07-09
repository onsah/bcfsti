# Context-Free Session Types with Borrowing

This repository contains an implementation of a typechecker
for the language from the paper *Context-Free Session Types with Borrowing*.

The implementation supports all features for CSTB mentioned in the paper and additionally supports the following features:

- unrestricted base types `String`, `Int`, and `Bool` with the usual operations
- a function that prints to stdout.
- `new S` differs from the paper that it's not a function but it's as if already applied to `Unit`
- let binding with explicit type annotation
- type aliasing to better showcase the examples from the appaer

## Installation

### Docker

1.  Build the image via

    ```bash
    docker-compose build
    ```

2.  Run the image via

    ```bash
    docker-compose run cstb
    ```

    This drops you into an interactive bash shell, where the compiled
    interpreter `cstb` is already on the `PATH`.

3.  Typecheck and interpret a program via e.g.

    ```bash
    cstb examples/positive/renderUser.bgv
    ```

    The current host directory is mounted into the current guest directory, so
    it is possible to change or add examples on the host without having to
    rebuild the image.

### From Source

Install a recent version of stable rust. See the following URL for instructions:

https://www.rust-lang.org/tools/install

The following command will compile the project and its dependencies (if necessary),
and then typecheck and run the file `SOURCE_FILE`:

```bash
cargo run -- SOURCE_FILE
```

## Syntax

The following grammar describes the complete, concrete syntax supported by the interpreter.
For readability, operator precedence, associativity and whitespace are omitted.

```
Mobilities
m ::= 'm'                           (mobile)
    | 's'                           (static)

Multiplicities
d ::= 'u' | 'unr'                   (unrestricted)
    | 'p' | 'lin'                   (linear/"parallel")
    | 'l' | 'left'                  (left ordered)
    | 'r' | 'right'                 (right ordered)

Effects
E ::= '0'                           (pure)
    | '1'                           (impure)

Types
t ::= t '-[' m ';'? d ';'? E ']->' t(function type)
    | t '*[' d ']' t                (product type)
    | '<' (l ':' t ',')* '>'        (variant type)
    | 'Chan'? s                     (session type)
    | 'Unit'                        (unit type)
    | 'Int'                         (64bit signed integer type)
    | 'Bool'                        (boolean t type)
    | 'String'                      (unicode string type)

Session Types
s ::=  s ';' s                      (sequential composition)
     | 'Return'                     (sending end of protocol of borrowed session)
     | 'Acq'                        (receiving end of protocol of borrowed session)
     | 'Wait'                       (receiving end of protocol of owned session)
     | 'Close'                      (sending end of protocol of owned session)
     | 'Skip'                       (empty session type)
     | '!' t                        (sending session type)
     | '?' t                        (receiving session type)
     | '&{' (l ':' s ',')* '}'      (external choice type)
     | '+{' (l ':' s ',')* '}'      (internal choice type)
     | 'mu' x '.' s                 (recursive session type)
     | x                            (session variable)
     | '(' s ')'                    (parenthesized session type)

Expressions
e ::= x                             (variable)
    | '\' x '.' e                   (lambda abstraction)
    | e e                           (unr/lin/right function application)

    | 'let' x '=' e 'in' e          (let expression)
    | e ';' e                       (sequencing)

    | '(' e ',' e ')'               (pairs)
    | 'let' x ',' x '=' e 'in' e    (product elimination)

    | 'inj' l e                     (variant introduction)
    | 'case' e '{'                  (variant elimination)
        (l x '->' '{' e '}')*
      '}'

    | 'let' x ':' t '\n'
            x x '=' e 'in' e        (let expression for recursive functions)

    | 'fork' e                      (thread spawning)
    | 'new' s                       (channel allocation)
    | 'send' @t e1 e2               (channel send operation)
    | 'recv' @t e                   (channel receive operation)
    | 'branch' e                    (external choice operation)
    | 'select' l e                  (internal choice operation)
    | 'drop' e                      (elimination of borrowed channels)
    | 'acquire' e                   (elimination of borrowed channels)
    | 'close' e                     (elimination of owned channels)
    | 'wait' e                      (elimination of owned channels)
    | 'lsplit' e                    (local channel split)
    | 'rsplit' e                    (remove channel split)
    

    | 'true' | 'false'              (boolean introduction)
    | 'if' e 'then' e 'else' e      (boolean elimination)
    | e '&&' e                      (boolean conjunction)
    | e '||' e                      (boolean disjunction)
    | '!' e                         (boolean negation)

    | 'unit'                        (unit introduction)

    | <str>                         (string literals)
    | e '+' e                       (string concatenation)
    | 'str' e                       (conversion to string)
    | 'print' e                     (printing to stdout)

    | <int>                         (integer literals)
    | '-' e                         (integer negation)
    | e '+' e                       (integer addition)
    | e '-' e                       (integer subtraction)
    | e '*' e                       (integer multiplication)
    | e '/' e                       (integer division)

    | e '<' e                       (comparison)
    | e '<=' e                      (comparison)
    | e '>' e                       (comparison)
    | e '>=' e                      (comparison)
    | e '==' e                      (equality)
    | e '!=' e                      (inequality)

    | e ':' t                       (type annotation)
    
Variables
x ::= [a-zA-Z_]+[a-zA-Z0-9_]*

Labels
l ::= [a-zA-Z_]+[a-zA-Z0-9_]*

Integer Literals
<int> ::= '-'? [0-9]+

String Literals
<str> ::= '"' [^"]* '"'             (strings like "foo")
        | '\'' [^"]* '\''           (strings like 'foo')
        | '\'\'\'' [^"]* '\'\'\''   (strings like '''foo''')

Patterns
p ::= x                             (variable pattern)
    | '(' p1 ',' p2 ')'             (pair pattern)
    
Program
P ::= e                             (main expression)
```

We also provide unicode alternatives for certain tokens:

- A lambda `\x. e` can also be written as `λx. e`

- A function type `t1 -[ d E ]-> t2` can also be written as `t1 –[ d E ]→ t2`

- An unordered product type `t1 *[ p ] t2` can also be written as `t1 ⊗ t2`

- A left-ordered product type `t1 *[ l ] t2` can also be written as `t1 ⊙ t2`

- A recursive session type `mu x. s` can also be written as `µ x. s`

Comments are started with a `#` and range until the end of the line.

## Examples

Examples from the paper are adjusted to the implementation language. For instance, in [sendTree](./example/positive/sendTree.bgv) example, it doesn't take a `tree` parameter, instead the pattern matching is emulated with a if expression on `true`, with then arm corresponding to the tree leaf case and else to the node. For type checking purposes, this is equivalent to the example in the paper.
