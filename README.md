An implementation of an ML-like language based on modal effect types and Fresco
type inference. This interpreter also has a [web interface](https://www.normalesup.org/~boussaa/met/playground/).

## Building
This interpreter is written in OCaml and uses the dune build system. It uses the
`menhir`, `bindlib`, and `multicont` libraries. To build a binary you can then
run:
```sh
opam install menhir bindlib multicont
dune build bin/met.exe
```

The following command spawns a REPL accepting definitions and expressions
terminated by `;;`:
```sh
dune exec bin/met.exe
```
You can use it with `rlwrap` to have navigation and history:
```
rlwrap -- dune exec bin/met.exe
```
The type checker can take a file as input:
```sh
dune exec -- bin/met.exe <file>
```
The `--eval` flag, which has to be put before the file's name, runs the
interpreter on the file. This flags expects a `main` function in the file.

The `--debug` flag prints a tree of the typing rules used for the input file.

## Examples
We can define a `gen` parametric effect and use it as follows with the `iter`
function.
```
type unit = Unit
type list a = Nil | Cons of a, list a
type option a = None | Some of a
type bool = True | False

eff gen [a] = yield : a => unit

val as_list : [](<gen int>(unit -> unit) -> list int)
let as_list f =
  handle f () with
  | return u => Nil
  | yield x r => Cons (x, r ())
  end

val iter : forall a . []((a -> unit) -> list a -> unit)
let iter f l =
  match l with
  | Nil -> ()
  | Cons (hd, tl) -> f hd; iter f tl
  end

val find : forall [a] . []((a -> bool) -> list a -> option a)
let find p xs =
  handle (iter (fun x -> if mask<gen> (p x) then do yield x else ()) xs) with
  | return _ => None
  | yield x k => Some (x)
  end
```

The `tests/pass` directory contains more examples such as a fragment of a Unix
interface (`unix.mle`) or an elaboration algorithm for a dependently-typed
language (`faux-tt.mle`). 

## Overview
The `lib` directory contains the core of the language and it contains the
following file:
+ `lexer.mll` implements a lexer
+ `parser.mly` implements a parser
+ `syntax.ml` defines the syntax of the language
+ `context.ml` defines contexts and implements context manipulation
+ `effects.ml` implements basic functions on effects
+ `type.ml` implements type checking
+ `eval.ml` implements an interpreter for the language
+ `pprint.ml` implements pretty printing of types
+ `error.ml` and `errors.ml` implement error messages

### Mapping functions to judgements
We map important functions in `type.ml` to the corresponding judgements in the
paper.
+ `finfer` implements type inference
+ `sk_infer` implements skeleton inference
+ `join_sk`, `join_var`, and `assign` implement consistency
+ `sub` and `sub_flex` implement subtyping
+ `look` implements looking
+ `constr_collect_sub` and `constr_collect_eq` implement constraint collection
+ `solve_eq`, `solve_sub`, and `constr_solve` implement constraint solving
Consistency functions, and the ones that mimic them, also have versions that work on
modalities.
