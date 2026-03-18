# A Modal Effect Types implementation

An implementation of a functionnal progamming language with effect handlers
tracked by a modal effect type system as described in the papers: Tang, Wenhao,
et al. "Modal effect types." Proceedings of the ACM on Programming Languages
9.OOPSLA1 (2025): 1130-1157. and Tang, Wenhao, and Sam Lindley. "Rows and
Capabilities as Modal Effects." Proceedings of the ACM on Programming Languages
10.POPL (2026): 923-950. The language has value and effect polymorphism. All
type applications are explicit, other branches contain experiments with
inference.

This program type checks and interprets source programs.

## Building
This project uses the `dune` build system; you can build it with:

``` sh
dune build
```

## Using
The previous step produces an executable `bin/met.exe`. Running it without any
argument spawns a REPL, and giving it a file name typechecks it. The program
does not interpret input files by default, to do give it the flag `--eval`, in
which case the source file should contain a function `main` of type `unit ->
unit`.

The REPL takes as input valid declarations and expressions followed by two
semicolons and file inclusion with the syntax `open "<file>";;`.

## Examples
Standard functions on lists:
```
val iter : forall a . []((a -> unit) -> list a -> unit)
let iter f l =
  match l with
  | Nil -> ()
  | Cons (hd, tl) -> f hd; iter @a f tl
  end
let append l l' =
  match l with
  | Nil -> l'
  | Cons (hd, tl) -> Cons (hd, append @a tl l')
  end
```

Declaring and handling an effect:
```
eff gen a = yield : a => unit

val as_list : [](<gen int>(unit -> unit) -> list int)
let as_list f =
  handle<gen int> f () with
  | return u => Nil
  | yield x r => Cons (x, r ())
  end
```

The directory `examples/` contains more examples.

## Demo
The `demo/ directory contains a longer example: `faux-tt.mle`. It is an elaborator
for a dependently-typed language with holes. This implementation follows [Andrej
Bauer's
faux-type-theory](https://github.com/andrejbauer/faux-type-theory/tree/main/algebraic-fauxtt)
in its use of effects to handle (meta-)variables.

This type checker can be tested by running `dune exec -- demo/repl.exe
demo/faux-tt.mle` which spawns a REPL implemented in OCaml that parses terms
written with the following syntax (followed by `;;`) and gives them to the type
checker implemented by `faux-tt.mle`.

```
M,N ::= x (variable)
     |  M N (application)
     | fun x => M (abstraction)
     | fun (x : M) => N (abstraction)
     | (x : M) -> N (dependent product)
     | * (type of types, with have type in type)
     | (M @ N) (type ascription)
```
