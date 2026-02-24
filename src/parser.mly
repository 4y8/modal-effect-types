%{
open Syntax
%}

%token EOF
%token <string> IDENT
%token HANDLE DO WITH RETURN EFFECT FUN DATA IF THEN ELSE FORALL CASE OF
%token LANGLE RANGLE LSQUARE RSQUARE LCURLY RCURLY LPAR RPAR
%token COMMA PIPE ARROW DARROW DOT DCOL EQU WILDCARD AT
%token ONE

%type <(string * surface_decl) list> file 
%start file

%%
(*
sexpr:
  | e = atom_expr { e }
;

let loc_type(t) ==
  stype = t; { { stype; tloc = $startpos, $endpos } }

let stype :=
  | loc_type ( ONE; { STUnit } )


let loc_expr(expr) ==
  sexpr = expr; { { sexpr; loc = $startpos, $endpos } }

let atom_expr :=
 | LPAR; ~ = sexpr; RPAR; <>
 | loc_expr(
   | ~ = IDENT; <SVar>
   | HANDLE; ~ = sexpr; <> )


eff:
 | x = IDENT DCOL tin = stype DARROW tout = stype { x, (tin, tout) }
;

eff_args:
  | { [] }
  | LSQUARE l = separated_list(COMMA, IDENT) RSQUARE { l }
;

decl_eff:
  | EFFECT x = IDENT args = eff_args EQU l = separated_list(PIPE, eff)
    { x, SDEff (args, l) }
;

decl_sig:
  | x = IDENT DCOL t = stype { x, SDSig t }
;

decl_fun:
  | x = IDENT EQU e = sexpr { x, e }
;

adt:
  | x = IDENT t = stype { x, t }
;

decl_adt:
  | DATA x = IDENT args = IDENT* EQU l = separated_list(PIPE, adt)
    { x, SDADT (args, l)}
;

decl:
  | d = decl_eff { d }
  | d = decl_sig { d }
  | d = decl_fun { d }
  | d = decl_adt { d }
;

file: d = decl* EOF { d };
*)
file: EOF { [] };
