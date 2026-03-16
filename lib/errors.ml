open Error
open Pprint
open Format
open Context

let kind_mismatch loc _ _ _ = error_str loc "Kind mismatch todo"

let unknown_var loc x = error_str loc ("Unknown variable " ^ x)
let unknown_eff loc x = error_str loc ("Unknown effect " ^ x)
let unknown_cons loc c t = error loc (fun fmt ->
    match t with
    | Some t -> fprintf fmt "Unknown constructor %s of type %s" c t
    | None -> fprintf fmt "Unknown constructor %s" c)

let type_mismatch loc a b =
  error loc
    (fun fmt -> fprintf fmt "Type mismatch: expected %a and got %a" ty a ty b)

let function_non_arr loc a = error loc
    (fun fmt -> fprintf fmt "Checking a function against type %a which is not an arrow" ty a)

let expected_arr loc a = error loc
    (fun fmt -> fprintf fmt "Expected an arrow type but got %a" ty a)

let apply_non_arr loc a = error loc
    (fun fmt -> fprintf fmt "Applying to an expression of type %a which is not a function type" ty a)

let expected_cons loc _ =
  error_str loc "Expected algebraic data type todo"
let expected_forall loc _ =
  error_str loc "Expected forall type for type application todo"
let expected_val loc _ = error_str loc "Expected a value todo"

let mod_mismatch loc m n e =
  error loc
    (fun fmt ->
       fprintf fmt "Modality mismatch: expected %a got %a at context %a"
        mu n mu m ectx e)

let missing_declaration loc x =
  error_str loc ("Missing declaration for function " ^ x)

let not_cons loc c a = error loc
    (fun fmt -> fprintf fmt
        "Constructor %s is not of the type %a" c ty a)

let nb_arg_mismatch loc e n l = error loc
    (fun fmt -> Format.fprintf fmt
        "Wrong number of arguments for %s, expected %d, got %d"
        e n (List.length l))

let no_apply_abs loc _ = error_str loc
    "Cannot treat an absolute type variable as an function type"

let no_apply_type loc _ = error_str loc
    "Cannot apply to a value of type todo"

let no_access loc x v ctx e =
  let _, a, _ = get_type_context ctx.gamma v in
  
  error loc
    (fun fmt -> fprintf fmt
        "Cannot access variable %s of type %a in effect context %a"
        x ty a ectx e)

let no_unboxing loc m e =
  error loc
    (fun fmt -> fprintf fmt
        "Cannot unbox function with modality %a in effect context %a"
        mu m ectx e)

let two_effect_var loc =
  Error.error_str loc "Cannot have two effect variables in a single row"

let non_last_evar loc e = error loc
    (fun fmt -> fprintf fmt
        "Effect type variable %s should be at the end of the row" e)

