open Error
open Pprint
open Format
open Context
open Syntax

let kind_mismatch loc _ _ _ = error_str loc "Kind mismatch todo"

let unknown_var loc x = error_str loc ("Unknown variable " ^ x)
let unknown_eff loc x = error_str loc ("Unknown effect " ^ x)
let unknown_cons loc c t = error loc (fun fmt ->
    match t with
    | Some t -> fprintf fmt "Unknown constructor %s of type %s" c t
    | None -> fprintf fmt "Unknown constructor %s" c)

let type_mismatch loc ~expected ~got =
  error loc
    (fun fmt -> fprintf fmt
        "Type mismatch: this expression has type %a but expected an expression of type %a"
        ty got ty expected)

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

exception End

let rec sub_eff fmt d d' =
  match d with
  | [] -> ()
  | { eff_args; eff_name } :: tl ->
    match Effects.find_label_eff eff_name d' with
    | None ->
      fprintf fmt "effect %s appears more times in the wrong side" eff_name;
      raise End
    | Some ({ eff_args = eff_args'; _ }, d') ->
      Array.iter2
        (fun a b ->
           if not Effects.(eq_ty a b) then begin
             fprintf fmt "argument of effect %s do not match: %a on the one hand and %a on the other"
               eff_name ty a ty b;
             raise End
           end
        ) eff_args eff_args';
      sub_eff fmt tl d'

let eq_eff_var fmt eps eps' =
  if not Effects.(eq_eff_var eps eps') then begin
    fprintf fmt "effect variables %a and %a do not match"
      ectx ([], Some eps) ectx ([], Some eps');
    raise End
  end

let sub_eff_ctx fmt (d, eps) (d', eps') =
  sub_eff fmt d d';
  match eps, eps' with
  | None, _ -> ()
  | Some eps, Some eps' ->
    eq_eff_var fmt eps eps';
    fprintf fmt "in presence of effect variables, the prefixes should be equivalent but: ";
    sub_eff fmt d' d
  | Some _, _ ->
    fprintf fmt "there is an effect variable in the former but not in the latter"

let sub_mod fmt mu nu f = match mu, nu with
  | MAbs e, _ ->
    fprintf fmt "%a should be a sub context of %a, but: "
      ectx e ectx Effects.(apply_mod nu f);
    sub_eff_ctx fmt e Effects.(apply_mod nu f)
  | MRel (l1, d1), MRel (l2, d2) ->
    let l, d = Effects.(l1 >< d1) in
    let l', d' = Effects.(l2 >< d2) in
    begin match Effects.mask_diff l l' with
    | [] -> ()
    | l ->
      fprintf fmt "labels %a are removed by a side but not the other" mask l;
      raise End
    end;
    begin match Effects.mask_diff l' l with
    | [] -> ()
    | l ->
      fprintf fmt "labels %a are removed by a side but not the other" mask l;
      raise End
    end;
    sub_eff fmt d d';
    sub_eff fmt d' d;

    if Effects.(extract (fst f) l1 = None || extract (fst f) l2 = None) then
      begin
        fprintf fmt "todo";
        raise End
      end
  | MRel _, MAbs _ ->
    fprintf fmt "a relative modality cannot be a submodality of an absolute modality"

let mod_mismatch loc ~expected ~got e =
  error loc
    (fun fmt ->
       fprintf fmt "Modality mismatch: this expression has top-level modality %a but expected an expression with modality %a;@ the former is not a submodality of the latter at context %a because: "
         mu got mu expected ectx e;
       try sub_mod fmt got expected e
       with End -> ())

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
        "Cannot unbox modality %a in effect context %a; it is not a submodality of identity because: "
        mu m ectx e;
      try sub_mod fmt m Effects.id e
      with End -> ())

let two_effect_var loc =
  error_str loc "Cannot have two effect variables in a single row"

let non_last_evar loc e = error loc
    (fun fmt -> fprintf fmt
        "Effect type variable %s should be at the end of the row" e)

let cannot_infer_expr loc =
  error_str loc "Cannot infer the type of expression"
