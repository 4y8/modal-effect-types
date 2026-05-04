%{
open Syntax

let fresh_name =
  let k = ref 0 in
  fun () -> (incr k; Printf.sprintf "x%d" !k)

let wrap_lam =
  List.fold_right (fun ((x, t), loc) e -> { loc; sexpr = SLam (x, t, e) })

let wrap_type =
  List.fold_right (fun (x, k, tloc) t -> { tloc; stype = STForA (x, k, t) })

let wrap_ann e t = { sexpr = SAnn (e, t); loc = e.loc }

let bool = { stype = STCons ("bool", []); tloc = None }

let wrap_if c t f loc =
  let x = fresh_name () in
  SLet (x, (wrap_ann c bool),
    { sexpr = SMatch ({sexpr = SVar x; loc = c.loc},
          [{spat = SPCons ("True", []); ploc = None}, t;
           {spat = SPCons ("False", []); ploc = None}, f;])
      ; loc = Some loc })

let wrap_let_pat (p, m, n) =
  let x = fresh_name () in
  SLet (x, m, { sexpr = SMatch ({sexpr = SVar x; loc = p.ploc}, [p, n]) ; loc = p.ploc})

let mask_of_seffs = List.map (function { seff_name ; eloc ; seff_args = [] } -> (seff_name, eloc) | _ -> raise Not_found )

let stprod (a, b) = STCons ("pair", [a; b])
let spair (a, b) = SCons ("Pair", [a; b])

let stunit = { stype = STCons ("unit", []); tloc = None }
%}

%token EOF
%token <string> IDENT
%token <string> MIDENT
%token <string> STRING
%token <int> INT
%token HANDLE DO WITH RETURN EFF FUN TYPE IF THEN ELSE FORALL MATCH MASK LET
%token IN END VAL OF EFFECT OPEN
%token PLUS MINUS TIMES AND CARET DSCOL
%token LANGLE RANGLE LSQUARE RSQUARE LCURLY RCURLY LPAR RPAR LFREEZE RFREEZE
%token COMMA PIPE ARROW DARROW DOT DCOL EQU WILDCARD AT SCOL BANG
%token UNIT

%left AND
%left EQU
%right CARET
%right ARROW
%left PLUS MINUS
%left TIMES

%type <((string * surface_decl) * loc) list> file
%start file
%type <surface_top_level> top_level
%start top_level

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
  | LANGLE; d = separated_list(COMMA, seff); RANGLE;
    { { smod = SMRel ([], d); mloc = Some ($startpos, $endpos) } }
  | LANGLE; l = separated_list(COMMA, seff); PIPE; d = separated_list(COMMA, seff); RANGLE;
    { let l = mask_of_seffs l in
      { smod = SMRel (l, d); mloc = Some ($startpos, $endpos) } }
(*
let mod_id :=
  | ~ = smod; <>
  | { { smod = SMRel ([], []); mloc = Some ($startpos, $endpos) } }
*)

let atom_type :=
  | LPAR; ~ = stype; RPAR; <>
  | loc_type (
    | LCURLY; t = stype; RCURLY;
    { STArr (stunit, t) }
    | LSQUARE; ~ = separated_list(COMMA, seff); RSQUARE ; <SECtx>
    | ~ = IDENT; <STVar>)

let mod_type :=
  | ~ = atom_type; <>
  | loc_type ( | ~ = smod; ~ = atom_type; <STMod>)

let cons_type :=
  | ~ = mod_type; <>
  | loc_type (
    | ~ = IDENT; ~ = atom_type+; <STCons>)

let prop_type :=
  | ~ = cons_type; <>
  | loc_type (
    | t1 = prop_type; TIMES; t2 = prop_type; <stprod>
    | t1 = prop_type; ARROW; t2 = prop_type; <STArr>)

(* maybe the distinction between abs and any kind arguments should not be done
by the programmer as it can be infered *)

let targ :=
  | LSQUARE; x = IDENT; RSQUARE; { (x, Abs) }
  | LPAR; x = IDENT; DCOL; EFFECT; RPAR; { (x, Effect) }
  | x = IDENT; { (x, Any) }

let targ_loc :=
  | p = targ; { (fst p, snd p, Some ($startpos, $endpos)) }

let stype :=
  | ~ = prop_type; <>
  | FORALL;  l = targ_loc+; DOT; t = stype; { wrap_type l t }

let loc_expr(expr) ==
  sexpr = expr; { { sexpr; loc = Some ($startpos, $endpos) } }

let pattern_list :=
  | ~ = pattern; <>
  | l = pattern_list; COMMA; p = pattern;
    { { spat = SPCons ("Pair", [l; p]); ploc = Some ($startpos, $endpos) } }

let pattern :=
  | LPAR; ~ = pattern_list; RPAR; <>
  | p = midrule(
        | UNIT; { SPCons ("Unit", []) }
        | WILDCARD; { SPWild }
        | ~ = IDENT; <SPVar>
        | ~ = MIDENT; LPAR; ~ = separated_list(COMMA, pattern); RPAR; <SPCons>
        | c = MIDENT; { SPCons (c, []) }
     (*   | c = MIDENT; p = tpattern; { SPCons (c, [p]) } *)
);
    { { spat = p; ploc = Some ($startpos, $endpos) } }

let handle_clause :=
  | PIPE; l = string_loc; p = untyped_arg; r = IDENT; DARROW; n = sexpr;
    { (fst l, (snd l, p, r, n)) }

let match_clause :=
  | PIPE; ~ = pattern_list; ARROW; ~ = sexpr; <>

let atom_expr :=
 | LPAR; ~ = sexpr; RPAR; <>
 | loc_expr(
   | LPAR; l = sexpr; COMMA; r = sexpr; RPAR; <spair>
   | LCURLY; e = sexpr; RCURLY; { SLam ("", Some stunit, e) }
   | ~ = IDENT; <SVar>
   | LFREEZE; ~ = sexpr; RFREEZE; <SFreeze>
   | ~ = INT; <SInt>
   | ~ = STRING; <SStr>
   | MASK; LANGLE; ~ = separated_list(COMMA, string_loc); RANGLE; ~ = atom_expr;
     <SMask>
   | UNIT; { SCons ("Unit", []) }
   | HANDLE; d = midrule (LANGLE; ~ = separated_list (COMMA, seff); RANGLE; <>)?;
     m = sexpr; WITH;
     PIPE; RETURN; p = untyped_arg; DARROW; n = sexpr;
     h = handle_clause*;
     END; { SHand (m, d, (h, (p, n))) }
   | MATCH; ~ = sexpr; WITH; ~ = match_clause*; END; <SMatch>)

let single_cons := loc_expr (| c = MIDENT; { SCons (c, []) })

let unit_arg :=
  | loc_expr(| BANG; { SCons ("Unit", []) })

let app_expr :=
  | ~ = atom_expr; <>
  | loc_expr(
    | ~ = MIDENT; LPAR; ~ = separated_list(COMMA, sexpr); RPAR; <SCons>
    | ~ = app_expr; ~ = atom_expr; <SApp>
    | ~ = app_expr; ~ = unit_arg; <SApp>
    | ~ = app_expr; ~ = single_cons; <SApp>
    | ~ = app_expr; AT; ~ = atom_type; <SAppT>)

let op ==
  | loc_expr( | EQU; { SVar "=" }
              | PLUS; { SVar "+" }
              | MINUS; { SVar "-" }
              | AND; { SVar "&&" }
              | CARET; { SVar "^" }
              | TIMES; { SVar "*" })

let op_expr :=
  | ~ = app_expr; <>
  | ~ = single_cons; <>
  | loc_expr( | l = op_expr; o = op; r = op_expr;
              { SApp ({sexpr = SApp (o, l); loc = l.loc }, r) } )

let do_expr :=
  | ~ = op_expr; <>
  | loc_expr(
    | DO; ~ = IDENT; ~ = if_expr; <SDo>)

let if_expr :=
  | ~ = do_expr; <>
  | loc_expr(
    | IF; c = sexpr; THEN; t = sexpr; ELSE; f = if_expr;
      { wrap_if c t f ($startpos, $endpos) })

let seq_expr :=
  | ~ = if_expr; <>
  | loc_expr( | ~ = if_expr; SCOL; ~ = sexpr; <SSeq> )

let fun_expr :=
  | ~ = seq_expr; <>
  | FUN; args = arg_loc+; ARROW; m = sexpr; { wrap_lam args m }

let sexpr :=
  | ~ = fun_expr; <>
  | loc_expr(
    | LET; p = pattern_list; DCOL; t = stype; EQU; m = sexpr; IN; n = sexpr;
    { wrap_let_pat (p, wrap_ann m t, n) }
    | LET; p = pattern_list; EQU; m = sexpr; IN; n = sexpr; <wrap_let_pat>)

eff:
  | x = IDENT DCOL tin = stype DARROW tout = stype { x, (tin, tout) }
;

acc:
  | { false }
  | BANG { true }
;

decl_eff:
  | EFF ho = acc x = IDENT args = targ* EQU l = separated_list(PIPE, eff)
    { x, SDEff (ho, args, l) }
;

decl_sig:
  | VAL x = IDENT DCOL t = stype { x, SDSig t }
;

let arg :=
  | x = IDENT; { x, None }
  | UNIT; { "", Some stunit }
  | BANG; { "", Some stunit }
  | WILDCARD; { "", None }
  | LPAR; x = IDENT; DCOL; t = stype; RPAR; { x, Some t }

let arg_loc :=
  | x = arg; { x, Some ($startpos, $endpos) }

let untyped_arg :=
  (* sloppy *)
  | a = arg; { fst a }

decl_fun:
  | LET x = IDENT args = arg_loc* EQU e = sexpr
    { x, SDFun (wrap_lam args e) }
;

adt:
  | x = MIDENT OF l = separated_list(COMMA, stype) { x, l }
  | x = MIDENT { x, [] }
;

decl_adt:
  | TYPE x = IDENT args = targ* EQU l = separated_list(PIPE, adt)
    { x, SDADT (args, l)}
;

let decl :=
  | d = decl_eff; { d, Some ($startpos, $endpos) }
  | d = decl_sig; { d, Some ($startpos, $endpos) }
  | d = decl_fun; { d, Some ($startpos, $endpos) }
  | d = decl_adt; { d, Some ($startpos, $endpos) }

file: d = decl* EOF { d };

top_level:
  | d = decl DSCOL { TLDecl (fst d) }
  | m = fun_expr DSCOL { TLExpr m }
  | OPEN s = STRING DSCOL { TLOpen s }
