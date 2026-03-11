open Error
open Pprint
open Format

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

let expected_arr loc _ = error_str loc "Expected function type todo"
let expected_prod loc _ = error_str loc "Expected product type todo"
let expected_cons loc _ =
  error_str loc "Expected algebraic data type todo"
let expected_forall loc _ =
  error_str loc "Expected forall type for type application todo"
let expected_val loc _ = error_str loc "Expected a value todo"

let mod_mismatch loc _ _ _ = error_str loc "Modality mismatch todo"

let no_access loc _ _ _ = error_str loc "Cannot access variable todo"

let no_unboxing loc _ _ =
  error_str loc "Cannot unbox function in application todo"

let missing_declaration loc x =
  error_str loc ("Missing declaration for function " ^ x)

let not_cons loc c _ = error loc
    (fun fmt -> Format.fprintf fmt
        "Constructor %s is not of the good type" c)

let nb_arg_mismatch loc e n l = error loc
    (fun fmt -> Format.fprintf fmt
        "Wrong number of arguments for %s, expected %d, got %d"
        e n (List.length l))

let no_apply_abs loc _ = error_str loc
    "Cannot treat an absolute type variable as an function type"

let no_apply_type loc _ = error_str loc
    "Cannot apply to a value of type todo"
