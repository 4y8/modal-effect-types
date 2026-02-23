open Syntax
open Context

let unknown_var loc x = Error.error_str loc ("Unknown variable " ^ x)

let rec check ctx m a e = match m.sexpr with
  | _ ->
    match a with
    | TMod (mu, a) -> check (Lock (mu, e) :: ctx) m a (Effect.apply_mod mu e)
    | _ -> failwith "todo"

and infer ctx m e = match m.sexpr with
  | SVar x ->
    begin match get_type_context ctx x with
      | None -> unknown_var m.loc x
      | Some (a, gamma') ->
        let nu, f = locks e gamma' in
        across ctx a nu f
    end
