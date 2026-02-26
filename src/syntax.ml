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
  | STProd of surface_type * surface_type
  | STForA of string * kind * surface_type
and surface_type = { stype : surface_tdsec ; tloc : loc }
[@@deriving show]

type pattern = PVar of string
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
  | SLam of string * surface_expr
  | SApp of surface_expr * surface_expr
  | SAnn of surface_expr * surface_type
  | SSeq of surface_expr * surface_expr
  | SUnit
  | SLetP of string * string * surface_expr * surface_expr
  | SPair of surface_expr * surface_expr
  | SAppT of surface_expr * surface_type
  | SMask of surface_expr * (string * loc) list
  | SHand of surface_expr * surface_effect list * surface_handler
  | SCons of string * surface_expr list
  | SMatch of surface_expr * (surface_pat * surface_expr) list
and surface_expr = { sexpr : surface_desc ; loc : loc }

and surface_handler = (string * loc * pattern * string * surface_expr) list *
                      (pattern * surface_expr)
[@@deriving show]

type surface_decl
  = SDEff of string list * (string * (surface_type * surface_type)) list
  | SDSig of surface_type
  | SDFun of surface_expr
  | SDADT of string list * ((string * surface_type list) list)
[@@deriving show]

type pure_mod
  = MAbs of effect_ctx
  | MRel of string list * effect_ctx

and pure_effect
  = { eff_name : string ; eff_type : pure_type * pure_type }

and effect_ctx = pure_effect list

and pure_type
  = TArr of pure_type * pure_type
  | TMod of pure_mod * pure_type
  | TVar of string * kind
  | TProd of pure_type * pure_type
  | TCons of string * pure_type list
  | TForA of string * kind * pure_type
[@@deriving show]

type concrete_mod = pure_mod * effect_ctx
