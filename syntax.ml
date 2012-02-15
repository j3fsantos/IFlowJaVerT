open List

(* syntax *)
type bin_op =
  | Plus
  | Minus
  | Times
  | Div
  | And
  | Or
  | Equal
  | Concat
  
type var = string

type exp = { offset : int; stx : exp_syntax }
and exp_syntax =
  | Num of int            (* 17 *)
  | String of string      (* "abc" *)
  | Undefined             (* undefined *)
  | Null                  (* null *)
  | Seq of exp * exp      (* e; e *)
  | Var of var            (* x *)
  | If of exp * exp * exp (* if (e){e}{e} *)
  | While of exp * exp    (* while (e){e}*)
  | VarDec of var         (* var x *)
  | This                  (* this *)
  | Delete of exp         (* delete e *)
  | BinOp of exp * bin_op * exp  (* e op e*)
  | Access of exp * string (* e.x *)
  | Call of exp * exp     (* e(e) *)
  | Assign of exp * exp   (* e = e*)
  | AnnonymousFun of var * exp (* function (x){e} *)
  | NamedFun of string * var * exp (* function x(x){e} *)
  | New of exp * exp      (* new e(e) *)
  | Obj of (string * exp) list (* {x_i : e_i} *)
  | CAccess of exp * exp  (* e[e] *)
  | With of exp * exp     (* with (e){e} *)
  | Skip

let mk_exp s o =
  { offset = o; stx = s }

let string_of_bin_op x =
  match x with
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Div -> "/"
    | And -> "&&"
    | Or -> "||"
    | Equal -> "=="
    | Concat -> "."

let string_of_var x = x

let rec string_of_exp e =
  let f = string_of_exp in
  match e.stx with
    | Num n -> string_of_int n
    | String x -> Printf.sprintf "\"%s\"" x
    | Undefined -> "undefined"
    | Null -> "null"
    | Seq (e1, e2) -> Printf.sprintf "(%s;\n%s)" (f e1) (f e2)
    | Var x -> string_of_var x
    | If (e1, e2, e3) -> Printf.sprintf "if (%s) {\n%s\n} else {\n%s\n}" (f e1) (f e2) (f e3)
    | While (e1, e2) -> Printf.sprintf "while (%s) {\n%s\n}" (f e1) (f e2)
    | VarDec x -> Printf.sprintf "var %s" (string_of_var x)
    | This -> "this"
    | Delete e -> Printf.sprintf "delete %s" (f e)
    | BinOp (e1, op, e2) -> Printf.sprintf "(%s) %s (%s)" (f e1) (string_of_bin_op op) (f e2)
    | Access (e, x) -> Printf.sprintf "(%s).%s" (f e) x
    | Call (e1, e2) -> Printf.sprintf "(%s)(%s)" (f e1) (f e2)
    | Assign (e1, e2) -> Printf.sprintf "%s = %s" (f e1) (f e2)
    | AnnonymousFun (x, e) -> Printf.sprintf "function (%s){\n%s\n}" (string_of_var x) (f e)
    | NamedFun (n, x, e) -> Printf.sprintf "function %s(%s){\n%s\n}" n (string_of_var x) (f e)
    | New (e1, e2) -> Printf.sprintf "new (%s)(%s)" (f e1) (f e2)
    | Obj l -> Printf.sprintf "{%s}" 
               (String.concat "; " (map (fun (x, e) -> Printf.sprintf "%s : %s" x (f e)) l))
    | CAccess (e1, e2) -> Printf.sprintf "(%s)[%s]" (f e1) (f e2)
    | With (e1, e2) -> Printf.sprintf "with (%s){\n%s\n}" (f e1) (f e2)
    | Skip -> "Skip"

