%{

open Core.Eval

let vlam (x, m) =
  List.fold_right (fun (x, t) m -> VCon ("SLam", [x; t; m])) x m

%}

%token EOF
%token <string> IDENT
%token LPAR RPAR ARROW DARROW DCOL AT
%token FUN TYPE
%token END

%type <value> prog
%start prog

%%

let id :=
  | x = IDENT; { VStr x }

let arg :=
  | x = id; { x, VCon ("None", []) }
  | LPAR; x = id; DCOL; t = expr; RPAR; { x, VCon ("Some", [t]) }

let atom_expr :=
  | LPAR; ~ = expr; RPAR; <>
  | LPAR; m = expr; AT; t = expr; RPAR; { VCon ("SAs", [m; t]) }
  | x = id; { VCon ("SVar", [x]) }
  | TYPE; { VCon ("SType", []) }

let app_expr :=
  | ~ = atom_expr; <>
  | f = app_expr; x = atom_expr; { VCon ("SApp", [f; x]) }

let expr :=
  | ~ = app_expr; <>
  | LPAR; x = id; DCOL; t = expr; RPAR; ARROW; u = expr;
    { VCon ("SPi", [x; t; u]) }
  | FUN; ~ = arg+; DARROW; ~ = expr; <vlam>

let prog :=
  | ~ = expr; END; <>
