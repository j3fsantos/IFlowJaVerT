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