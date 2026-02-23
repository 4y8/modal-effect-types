type loc = Lexing.position * Lexing.position

type surface_mdesc
  = SMAbs of surface_effect list
  | SMRel of string list * surface_effect list
and surface_mod = { smod : surface_mdesc ; loc : loc }

and surface_effect =
  { seff_name : string ;
    seff_args : surface_type list ; eloc : loc }

and surface_tdsec
  = STArr of surface_type * surface_type
  | STMod of surface_mod * surface_type
  | STVar of string
  | STSum of surface_type * surface_type
  | STProd of surface_type * surface_type
  | STUnit
and surface_type = { stype : surface_tdsec ; tloc : loc }

type pattern = PVar of string

type surface_desc
  = SDo of string * surface_expr
  | SVar of string
  | SLam of string * surface_expr
  | SApp of surface_expr * surface_expr
  | SAnn of surface_expr * surface_type
  | STApp of surface_expr * surface_type
  | SMask of surface_expr * string list
  | SHand of surface_handler
and surface_expr = { sexpr : surface_desc ; loc : loc }

and surface_handler = (string * pattern list * surface_expr) list *
                      (string * surface_expr)

type kind = Abs | Any | Effect

type pure_mod
  = MAbs of pure_effect list
  | MRel of pure_effect list * pure_effect list

and pure_effect
  = { eff_name : string ; eff_type : (pure_type * pure_type) option }

and pure_type
  = TArr of pure_type * pure_type
  | TMod of pure_mod * pure_type
  | TVar of string
  | TSum of pure_type * pure_type
  | TProd of pure_type * pure_type
  | TUnit

type concrete_mod = pure_mod * pure_effect list
