type loc = (Lexing.position * Lexing.position) option
let pp_loc _ _ = ()

type kind = Abs | Any | Effect
[@@deriving show]

type surface_mdesc
  = SMAbs of surface_effect list
  | SMRel of (string * loc) list * surface_effect list
and surface_mod = { smod : surface_mdesc ; mloc : loc }

and surface_effect =
  { seff_name : string ;
    seff_args : surface_type list ; eloc : loc }

and surface_tdsec
  = STArr of surface_type * surface_type
  | STMod of surface_mod * surface_type
  | STVar of string
  | STCons of string * surface_type list
  | STForA of string * kind * surface_type
and surface_type = { stype : surface_tdsec ; tloc : loc }
[@@deriving show]

type surface_pdesc
  = SPVar of string
  | SPCons of string * surface_pat list
  | SPWild
and surface_pat = { spat : surface_pdesc ; ploc : loc }
[@@deriving show]

type surface_desc
  = SDo of string * surface_expr
  | SVar of string
  | SInt of int
  | SStr of string
  | SLam of string * surface_expr
  | SApp of surface_expr * surface_expr
  | SAnn of surface_expr * surface_type
  | SSeq of surface_expr * surface_expr
  | SLet of string * surface_expr * surface_expr
  | SAppT of surface_expr * surface_type
  | SMask of surface_expr * (string * loc) list
  | SHand of surface_expr * surface_effect list * surface_handler
  | SCons of string * surface_expr list
  | SMatch of surface_expr * (surface_pat * surface_expr) list
and surface_expr = { sexpr : surface_desc ; loc : loc }

and surface_handler = (string * (loc * string * string * surface_expr)) list *
                      (string * surface_expr)
[@@deriving show]

type surface_decl
  = SDEff of string list * (string * (surface_type * surface_type)) list
  | SDSig of surface_type
  | SDFun of surface_expr
  | SDADT of string list * ((string * surface_type list) list)
[@@deriving show]

(* uncomment for debugging
open Bindlib

let pp_var _ _  _ = ()
let pp_binder _ _ _ _ = ()
*)

type pure_mod
  = MAbs of effect_ctx
  | MRel of string list * effect_ctx

and pure_effect
  = { eff_name : string ; eff_type : pure_type * pure_type }

and effect_ctx = pure_effect list

and pure_type
  = TArr of pure_type * pure_type
  | TMod of pure_mod * pure_type
  | TVar of tvar
  (* use arrays to use Bindlib's mbinders *)
  | TCon of string * pure_type array
  | TForA of kind * (pure_type, pure_type) Bindlib.binder

and tvar = pure_type Bindlib.var

let tvar_ = Bindlib.box_var

let tmod_ m = Bindlib.box_apply (fun a -> TMod (m, a))

let tarr_ = Bindlib.box_apply2 (fun a b -> TArr (a, b))

let tcon_ c l = Bindlib.box_apply (fun l -> TCon (c, l)) (Bindlib.box_array l)

let tfora_ k = Bindlib.box_apply (fun a -> TForA (k, a))

let rec box_type = function
  | TVar v -> tvar_ v
  | TMod (m, a) -> tmod_ m (box_type a)
  | TArr (a, b) -> tarr_ (box_type a) (box_type b)
  | TCon (c, l) -> tcon_ c (Array.map box_type l)
  | TForA (k, a) -> tfora_ k (Bindlib.box_binder box_type a)

let box_effect_ctx e =
  let pure_effect_ eff_name = Bindlib.box_apply2
      (fun a b -> { eff_name; eff_type = a, b })
  in
  let box_effect { eff_name; eff_type = (a, b) } =
    pure_effect_ eff_name (box_type a) (box_type b)
  in
  Bindlib.box_list (List.map box_effect e)

type concrete_mod = pure_mod * effect_ctx

type lit = Int of int | Str of string

type expr
  = Do of string * expr
  | Var of var
  | Lit of lit
  | Lam of pure_type * (expr, expr) Bindlib.binder
  | App of expr * expr
  | Let of expr * pure_type * (expr, expr) Bindlib.binder
  | Con of string * expr list
  | Hand of expr * effect_ctx *
            (expr, expr) Bindlib.binder *
            (string * (expr, (expr, expr) Bindlib.binder) Bindlib.binder) list
  | Match of expr * (pat * (expr, expr) Bindlib.mbinder) list

and pat =
  | PCon of string * pat list
  | PVar of pure_type
  | PWild

and var = expr Bindlib.var

let do_ e = Bindlib.box_apply (fun m -> Do (e, m))

let var_ = Bindlib.box_var

let lit_ l = Bindlib.box (Lit l)

let lam_ = Bindlib.box_apply2 (fun a m -> Lam (a, m))

let app_ = Bindlib.box_apply2 (fun m n -> App (m, n))

let let_ = Bindlib.box_apply3 (fun m a n -> Let (m, a, n))

let con_ c l = Bindlib.box_apply (fun l -> Con (c, l)) (Bindlib.box_list l)

let hand_ m d ret h =
  let h = List.map (fun (e, b) -> Bindlib.box_apply (fun b -> (e, b)) b) h
       |> Bindlib.box_list in
  Bindlib.box_apply3 (fun m ret h -> Hand (m, d, ret, h)) m ret h

let match_ m l =
  Bindlib.box_apply2 (fun m l -> Match (m, l)) m (Bindlib.box_list l)

let pcon_ s = Bindlib.box_apply (fun l -> PCon (s, l))

let pvar_ = Bindlib.box_apply (fun a -> PVar a)

let pwild_ = Bindlib.box PWild

let rec box_pat = function
  | PWild -> pwild_
  | PVar a -> pvar_ (box_type a)
  | PCon (c, l) -> pcon_ c (Bindlib.box_list @@ List.map box_pat l)

let rec box_expr = function
  | Do (e, m) -> do_ e (box_expr m)
  | Var v -> var_ v
  | Lit l -> lit_ l
  | Lam (a, m) -> lam_ (box_type a) (Bindlib.box_binder box_expr m)
  | App (m, n) -> app_ (box_expr m) (box_expr n)
  | Let (m, a, n) ->
    let_ (box_expr m) (box_type a) (Bindlib.box_binder box_expr n)
  | Con (c, l) -> con_ c (List.map box_expr l)
  | Hand (m, d, ret, h) ->
    hand_ (box_expr m) d (Bindlib.box_binder box_expr ret)
      (List.map (fun (e, b) ->
           e, Bindlib.(box_binder (box_binder box_expr) b)) h)
  | Match (m, c) ->
    match_ (box_expr m)
      (List.map (fun (p, c) ->
           Bindlib.box_pair (box_pat p) (Bindlib.box_mbinder box_expr c)) c)
