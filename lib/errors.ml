open Error
open Pprint
open Format
open Context

let text fmt = Fun.compose (fprintf fmt) format_text

let kind_mismatch loc ~expected ~got a =
  error loc
    (fun fmt -> text fmt
        "Kind mismatch: type %a has kind %a but expected a type of kind %a"
        ty a kind got kind expected)

let unknown_var loc x = error_str loc ("Unknown variable " ^ x)
let unknown_eff loc x = error_str loc ("Unknown effect " ^ x)
let unknown_cons loc c t = error loc (fun fmt ->
    match t with
    | Some t -> text fmt "Unknown constructor %s of type %s" c t
    | None -> text fmt "Unknown constructor %s" c)

let type_mismatch loc ~expected ~got =
  error loc
    (fun fmt -> text fmt
        "Type mismatch: this expression has type %a but expected an expression of type %a"
        ty got ty expected)

let cannot_unify loc a b =
  error loc
    (fun fmt -> text fmt
        "Type mimsatch: cannot unify types %a and %a"
        ty a ty b)

let function_non_arr loc a = error loc
    (fun fmt -> text fmt
        "Checking a function against type %a which is not an arrow" ty a)

let expected_arr loc a = error loc
    (fun fmt -> text fmt "Expected an arrow type but got %a" ty a)

let apply_non_arr loc a = error loc
    (fun fmt ->
       text fmt "Applying to an expression of type %a which is not a function type" ty a)

let expected_cons loc _ =
  error_str loc "Expected algebraic data type todo"

let expected_forall loc a =
  error loc
    (fun fmt ->
       text fmt
         "Type mismatch: this expression has type %a but expected a function \
prefixed by a forall as it is applied to a type_mismatch"
         ty a)

let expected_val loc _ =
  error_str loc "Expected a value"

let mod_mismatch loc ~expected ~got e =
  error loc
    (fun fmt ->
       text fmt "Modality mismatch: this expression has top-level \
modality %a but expected an expression with modality %a; the former \
is not a submodality of the latter at context %a "
         mu got mu expected ectx e)

let missing_declaration loc x =
  error loc (fun fmt -> text fmt "Missing declaration for function %s" x)

let not_cons loc c a = error loc
    (fun fmt -> text fmt
        "Constructor %s is not of the type %a" c ty a)

let nb_arg_mismatch loc e n l = error loc
    (fun fmt -> text fmt
        "Wrong number of arguments for %s, expected %d, got %d"
        e n (List.length l))

let no_apply_abs loc _ = error_str loc
    "Cannot treat an absolute type variable as an function type"

let no_apply_type loc _ = error_str loc
    "Cannot apply to a value of type todo"

let no_access loc x v e =
  let* _, a, _ = get_type_context v in
  error loc
    (fun fmt ->
       text fmt
         "Cannot access variable %s of type %a in effect context %a"
         x ty a ectx e)

let no_unboxing loc m e =
  error loc
    (fun fmt -> text fmt
        "Cannot unbox modality %a in effect context %a; it is not a submodality of identity"
        mu m ectx e)

let higher_order_effect_not_first loc op e =
  error loc
    (fun fmt -> text fmt "Operation %s is in a higher order effect which is not first in effect context %a"
        op Pprint.ectx e)

let two_effect_var loc =
  error loc
    (fun fmt -> text fmt "Cannot have two effect variables in a single row")

let non_last_evar loc e = error loc
    (fun fmt -> text fmt
        "Effect type variable %s should be at the end of the row" e)

let cannot_infer_expr loc =
  error_str loc "Cannot infer the type of expression"
