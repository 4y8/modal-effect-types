%{
open Syntax

let fresh_name =
  let k = ref 0 in
  fun () -> (incr k; Printf.sprintf "x%d" !k)

let wrap_lam =
  List.fold_right (fun (x, loc) e -> { loc; sexpr = SLam (x, e) })

let wrap_type =
  List.fold_right (fun (x, k, tloc) t -> { tloc; stype = STForA (x, k, t) })

let wrap_ann e t = { sexpr = SAnn (e, t); loc = e.loc }

let wrap_let x m n = SLet (x, m, n)

let bool = { stype = STCons ("bool", []); tloc = None }

let wrap_if c t f loc =
  let x = fresh_name () in
  wrap_let x (wrap_ann c bool)
    { sexpr = SMatch ({sexpr = SVar x; loc = c.loc},
          [{spat = SPCons ("True", []); ploc = None}, t;
           {spat = SPCons ("False", []); ploc = None}, f;])
      ; loc = Some loc }
%}

%token EOF
%token <string> IDENT
%token <string> MIDENT
%token <int> INT
%token HANDLE DO WITH RETURN EFFECT FUN TYPE IF THEN ELSE FORALL MATCH MASK LET
%token IN END VAL OF
%token PLUS MINUS TIMES
%token LANGLE RANGLE LSQUARE RSQUARE LCURLY RCURLY LPAR RPAR
%token COMMA PIPE ARROW DARROW DOT DCOL EQU WILDCARD AT SCOL
%token UNIT

%left EQU
%right ARROW
%left PLUS MINUS
%left TIMES

%type <((string * surface_decl) * loc) list> file
%start file

%%

let string_loc :=
  | x = IDENT; { x, Some ($startpos, $endpos) }

let seff :=
  | seff_name = IDENT; seff_args = atom_type*;
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

let cons_type :=
  | ~ = atom_type; <>
  | loc_type (
    | ~ = IDENT; ~ = atom_type+; <STCons>)

let prop_type :=
  | ~ = cons_type; <>
  | loc_type (
    | t1 = prop_type; TIMES; t2 = prop_type; <STProd>
    | t1 = prop_type; ARROW; t2 = prop_type; <STArr>)

(* maybe the distinction between abs and any kind arguments should not be done
by the programmer as it can be infered *)

let targ :=
  | LSQUARE; x = IDENT; RSQUARE; { (x, Abs, Some ($startpos, $endpos)) }
  | x = IDENT; { (x, Any, Some ($startpos, $endpos)) }

let stype :=
  | ~ = prop_type; <>
  | FORALL;  l = targ+; DOT; t = stype; { wrap_type l t }

let loc_expr(expr) ==
  sexpr = expr; { { sexpr; loc = Some ($startpos, $endpos) } }

let pattern :=
  | LPAR; ~ = pattern; RPAR; <>
  | p = midrule(
        | WILDCARD; { SPWild }
        | ~ = IDENT; <SPVar>
        | ~ = MIDENT; LPAR; ~ = separated_list(COMMA, pattern); RPAR; <SPCons>
        | c = MIDENT; { SPCons (c, []) }
     (*   | c = MIDENT; p = tpattern; { SPCons (c, [p]) } *)
);
    { { spat = p; ploc = Some ($startpos, $endpos) } }

let handle_clause :=
  | PIPE; l = string_loc; p = IDENT; r = IDENT; DARROW; n = sexpr;
    { (fst l, snd l, p, r, n) }

let match_clause :=
  | PIPE; ~ = pattern; ARROW; ~ = sexpr; <>

let atom_expr :=
 | LPAR; ~ = sexpr; RPAR; <>
 | loc_expr(
   | ~ = IDENT; <SVar>
   | ~ = INT; <SInt>
   | UNIT; { SUnit }
   | HANDLE; LANGLE; d = separated_list (COMMA, seff); RANGLE; m = sexpr; WITH;
     PIPE; RETURN; p = IDENT; DARROW; n = sexpr;
     h = handle_clause*;
     END; { SHand (m, d, (h, (p, n))) }
   | MATCH; ~ = sexpr; WITH; ~ = match_clause*; END; <SMatch>)

let single_cons := loc_expr (| c = MIDENT; { SCons (c, []) })

let app_expr :=
  | ~ = atom_expr; <>
  | loc_expr(
    | ~ = MIDENT; LPAR; ~ = separated_list(COMMA, sexpr); RPAR; <SCons>
    | ~ = app_expr; ~ = atom_expr; <SApp>
    | ~ = app_expr; ~ = single_cons; <SApp>
    | ~ = app_expr; AT; ~ = atom_type; <SAppT>)

let op ==
  | loc_expr( | EQU; { SVar "=" }
              | PLUS; { SVar "+" }
              | MINUS; { SVar "-" }
              | TIMES; { SVar "*" })

let op_expr :=
  | ~ = app_expr; <>
  | ~ = single_cons; <>
  | loc_expr( | l = op_expr; o = op; r = op_expr;
              { SApp ({sexpr = SApp (o, l); loc = l.loc }, r) } )

let pair_expr :=
  | ~ = op_expr; <>
  | loc_expr( | LPAR; ~ = pair_expr; COMMA; ~ = op_expr; RPAR; <SPair>)

let do_expr :=
  | ~ = pair_expr; <>
  | loc_expr(
    | DO; ~ = IDENT; ~ = do_expr; <SDo>)

let if_expr :=
  | ~ = do_expr; <>
  | loc_expr(
    | IF; c = sexpr; THEN; t = sexpr; ELSE; f = if_expr;
      { wrap_if c t f ($startpos, $endpos) })

let seq_expr :=
  | ~ = if_expr; <>
  | loc_expr( | ~ = if_expr; SCOL; ~ = sexpr; <SSeq> )

let sexpr :=
  | ~ = seq_expr; <>
  | loc_expr(
    | LET; x = IDENT; DCOL; t = stype; EQU; m = sexpr; IN; n = sexpr;
    { SMatch (wrap_ann m t, [{spat = SPVar x ; ploc = None}, n]) }
    | LET; x = IDENT; EQU; m = sexpr; IN; n = sexpr;
    { SMatch (m, [{spat = SPVar x ; ploc = None}, n]) }
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
  | LET x = IDENT args = string_loc* EQU e = sexpr
    { x, SDFun (wrap_lam args e) }
;

adt:
  | x = MIDENT OF l = separated_list(COMMA, stype) { x, l }
  | x = MIDENT { x, [] }
;

decl_adt:
  | TYPE x = IDENT args = IDENT* EQU l = separated_list(PIPE, adt)
    { x, SDADT (args, l)}
;

let decl :=
  | d = decl_eff; { d, Some ($startpos, $endpos) }
  | d = decl_sig; { d, Some ($startpos, $endpos) }
  | d = decl_fun; { d, Some ($startpos, $endpos) }
  | d = decl_adt; { d, Some ($startpos, $endpos) }

file: d = decl* EOF { d };
