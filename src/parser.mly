%{
open Syntax

let wrap =
  List.fold_right (fun (x, loc) e -> { loc; sexpr = SLam (x, e) })
%}

%token EOF
%token <string> IDENT
%token <int> INT
%token HANDLE DO WITH RETURN EFFECT FUN TYPE IF THEN ELSE FORALL MATCH MASK LET
%token IN INL INR END VAL SCOL
%token PLUS MINUS TIMES
%token LANGLE RANGLE LSQUARE RSQUARE LCURLY RCURLY LPAR RPAR
%token COMMA PIPE ARROW DARROW DOT DCOL EQU WILDCARD AT
%token UNIT

%right ARROW
%left PLUS
%left TIMES

%type <((string * surface_decl) * loc) list> file 
%start file

%%

let string_loc :=
  | x = IDENT; { x, Some ($startpos, $endpos) }

let seff :=
  | seff_name = IDENT; seff_args = stype*;
    { { seff_name; seff_args; eloc = Some ($startpos, $endpos) } }

let loc_type(t) ==
  stype = t; { { stype; tloc = Some ($startpos, $endpos) } }

let smod :=
  | LSQUARE; l = separated_list(COMMA, seff); RSQUARE;
    { { smod = SMAbs l; mloc = Some ($startpos, $endpos) } }
  | LANGLE; l = separated_list(COMMA, seff); RANGLE;
    { { smod = SMRel ([], l); mloc = Some ($startpos, $endpos) } }

let atom_type :=
  | LPAR; ~ = stype; RPAR; <>
  | loc_type (
    | ~ = IDENT; <STVar>
    | ~ = smod; ~ = atom_type; <STMod>)

let stype :=
  | ~ = atom_type; <>
  | loc_type (
    | t1 = stype; TIMES; t2 = stype; <STProd>
    | t1 = stype; ARROW; t2 = stype; <STArr>
    | t1 = stype; PLUS; t2 = stype; <STSum>)

let pattern :=
  | ~ = IDENT; <PVar>

let loc_expr(expr) ==
  sexpr = expr; { { sexpr; loc = Some ($startpos, $endpos) } }

let handle_clause :=
  | PIPE; l = string_loc; p = pattern; r = IDENT; DARROW; n = sexpr;
    { (fst l, snd l, p, r, n) }

let atom_expr :=
 | LPAR; ~ = sexpr; RPAR; <>
 | loc_expr(
   | ~ = IDENT; <SVar>
   | ~ = INT; <SInt>
   | UNIT; { SUnit }
   | HANDLE; LANGLE; d = separated_list (COMMA, seff); RANGLE; m = sexpr; WITH;
     PIPE; RETURN; p = pattern; DARROW; n = sexpr;
     h = handle_clause*;
     END; { SHand (m, d, (h, (p, n))) })

let app_expr :=
  | ~ = atom_expr; <>
  | loc_expr(
    | INL; ~ = atom_expr; <SInl>
    | INR; ~ = atom_expr; <SInr>
    | ~ = app_expr; ~ = atom_expr; <SApp>)

let pair_expr :=
  | ~ = app_expr; <>
  | loc_expr( | ~ = pair_expr; COMMA; ~ = app_expr; <SPair>)

let do_expr :=
  | ~ = pair_expr; <>
  | loc_expr(
    | DO; ~ = IDENT; ~ = do_expr; <SDo>)

let seq_expr :=
  | ~ = do_expr; <>
  | loc_expr( | ~ = do_expr; SCOL; ~ = sexpr; <SSeq> )

let sexpr :=
  | ~ = seq_expr; <>
  | loc_expr(
    | LET; LPAR; x = IDENT; y = IDENT; RPAR; EQU; m = sexpr; IN; n = sexpr; <SLetP>
    | FUN; ~ = IDENT; ARROW; ~ = sexpr; <SLam>)

eff:
  | x = IDENT DCOL tin = stype DARROW tout = stype { x, (tin, tout) }
;

decl_eff:
  | EFFECT x = IDENT args = IDENT* EQU l = separated_list(PIPE, eff)
    { x, SDEff (args, l) }
;

decl_sig:
  | VAL x = IDENT DCOL t = stype { x, SDSig t }
;

decl_fun:
  | LET x = IDENT args = string_loc* EQU e = sexpr { x, SDFun (wrap args e) }
;

adt:
  | x = IDENT DCOL t = stype { x, t }
;

decl_adt:
  | TYPE x = IDENT args = IDENT* EQU l = separated_list(PIPE, adt)
    { x, SDADT (args, l)}
;

decl:
  | d = decl_eff { d, Some ($startpos, $endpos) }
  | d = decl_sig { d, Some ($startpos, $endpos) }
  | d = decl_fun { d, Some ($startpos, $endpos) }
  | d = decl_adt { d, Some ($startpos, $endpos) }
;

file: d = decl* EOF { d };
