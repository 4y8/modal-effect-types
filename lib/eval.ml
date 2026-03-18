open Syntax
open Effect
open Effect.Deep

module VMap = Map.Make(struct
    type t = var
    let compare = Bindlib.compare_vars
  end)

let rec pp_value fmt = function
  | VClo _ -> Format.fprintf fmt "<fun>"
  | VMask v -> pp_value fmt v
  | VInt n -> Format.fprintf fmt "%d" n
  | VStr s -> Format.fprintf fmt "\"%s\"" s
  | VCon (c, []) -> Format.fprintf fmt "%s" c
  | VCon (c, [v]) -> Format.fprintf fmt "%s %a" c pp_value v
  | VCon (c, l) ->
    Format.(fprintf fmt "%s (@[<hv>%a@])" c
              (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@;<1 1>")
                 pp_value) l)

type _ Effect.t += Do : string * value -> value t

let unint = function
  | VInt n -> n
  | _ -> failwith "internal error"

let unstr = function
  | VStr s -> s
  | _ -> failwith "internal error"

let vbool = function
  | true -> VCon ("True", [])
  | false -> VCon ("False", [])

let unbool = (=) (VCon ("True", []))

exception Fail

let stdlib =
  [ "+", VClo (fun x -> VClo (fun y -> VInt (unint x + unint y)))
  ; "-", VClo (fun x -> VClo (fun y -> VInt (unint x - unint y)))
  ; "*", VClo (fun x -> VClo (fun y -> VInt (unint x - unint y)))
  ; "=", VClo (fun x -> VClo (fun y -> vbool (unint x = unint y)))
  ; "string_eq", VClo (fun x -> VClo (fun y -> vbool (unstr x = unstr y)))
  ; "^", VClo (fun x -> VClo (fun y -> VStr (unstr x ^ unstr y)))
  ; "&&", VClo (fun x -> VClo (fun y -> vbool (unbool x && unbool y)))
  ; "fail", VClo (fun _ -> raise Fail)
  ; "print", VClo (fun x -> print_endline (unstr x); VCon ("Unit", []))
  ; "string_of_int", VClo (fun x -> VStr (string_of_int (unint x)))
  ]

let build_stdlib_map ctx =
  Context.(List.map (fun (x, v) -> List.assoc x ctx.id, v) stdlib
           |> VMap.of_list)

let rec eval ctx = function
  | Val v -> v
  | Lit (Int n) -> VInt n
  | Lit (Str s) -> VStr s
  | Con (c, l) -> VCon (c, List.map (eval ctx) l)
  | Var x ->
    begin match VMap.find_opt x !ctx with
      | Some v -> v
      | None -> Error.error_str None "missing a definition"
    end
  | Lam (_, m) ->
    VClo (fun v -> eval ctx (Bindlib.subst m (Val v)))
  | App (m, n) ->
    begin match eval ctx m with
      | VClo f -> f (eval ctx n)
      | _ -> failwith "internal error"
    end
  | Do (e, m) -> perform (Do (e, eval ctx m))
  | Mask (l, m) ->
    begin try
        eval ctx m
      with
      | effect (Do (e, v)), k ->
        if List.mem e l then
          continue k (perform (Do (e, VMask v)))
        else
        continue k (perform (Do (e, v)))
    end
  | Let (m, _, n) -> eval ctx (Bindlib.subst n (Val (eval ctx m)))
  | Match (m, l) ->
    let v = eval ctx m in
      begin match List.find_map (fun (p, n) -> Option.map (fun vals -> vals, n)
                                    (eval_pat v [] p)) l with
      | None ->
        Error.error_str None "missing case in pattern matching"
      | Some (vals, n) ->
        eval ctx (Bindlib.msubst n (Array.of_list vals))
    end
  | Hand (m, _, ht, r, h) ->
    let handled = ref [] in
    try
      let v = eval ctx m in
      eval ctx (Bindlib.subst r (Val v))
    with
    | effect (Do (e, v)), k ->
      match List.assoc_opt e h, v with
      | Some _, VMask v
      | None, v -> continue k (perform (Do (e, v)))
      | Some _, v when ht = Shallow && List.mem e !handled ->
        continue k (perform (Do (e, v)))
      | Some ni, v ->
        let open Multicont.Deep in
        let k = promote k in
        handled := e :: !handled;
        eval ctx (Bindlib.(subst (subst ni (Val v)) (Val (VClo (resume k)))))

and eval_pat v vals = function
  | PWild -> Some vals
  | PVar _ -> Some (Val v :: vals)
  | PCon (c, l) ->
    match v with
    | VCon (c', l') when c = c' ->
      List.fold_right
        (fun (p, v) -> function
          | None -> None
          | Some vals -> eval_pat v vals p)
        (List.combine l l') (Some vals)
    | _ -> None

let eval_prog ectx p =
  let first _ x y = match x with None -> y | _ -> x in
  ectx :=
    VMap.(merge first (of_list (List.map (Pair.map_snd (eval ectx)) p)) !ectx)
