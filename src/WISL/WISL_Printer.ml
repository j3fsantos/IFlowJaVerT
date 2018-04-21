open WISL_Syntax
open Format

let pp_list (* list pretty-printer from frama-c *)
    ?(pre=format_of_string "@[")
    ?(sep=format_of_string ", ")
    ?(last=sep)
    ?(suf=format_of_string "@]")
    ?(empty=format_of_string "")
    pp_elt f l =
  let rec aux f = function
    | [] -> assert false
    | [ e ] -> fprintf f "%a" pp_elt e
    | [ e1; e2 ] -> fprintf f "%a%(%)%a" pp_elt e1 last pp_elt e2
    | e :: l -> fprintf f "%a%(%)%a" pp_elt e sep aux l
  in
  match l with
  | [] -> Format.fprintf f "%(%)" empty
  | _ :: _ as l -> Format.fprintf f "%(%)%a%(%)" pre aux l suf

let pp_number fmt = function
  | Int i -> fprintf fmt "@[%i@]" i
  | Float f -> fprintf fmt "@[%g@]" f

let rec pp_value fmt = function
  | Bool true -> fprintf fmt "@[%s@]" "true"
  | Bool false -> fprintf fmt "@[%s@]" "false"
  | Loc s -> fprintf fmt "@[%s@]" s
  | Num n -> fprintf fmt "@[%a@]" pp_number n
  | Str s -> fprintf fmt "@[%s@]" s
  | Null -> fprintf fmt "@[%s@]" "null"
  | VList l -> pp_list 
               ~pre:(format_of_string "@[[")
               ~suf:(format_of_string "]@]")
               ~empty:(format_of_string "@[nil@]")
               pp_value fmt l
    
let pp_binop fmt = 
  let s = fprintf fmt "@[%s@]" in 
    function 
    | EQUAL -> s "="
    | LESSTHAN -> s "<"
    | GREATERTHAN -> s ">"
    | LESSEQUAL -> s "<="
    | GREATEREQUAL -> s ">="
    | PLUS -> s "+"
    | MINUS -> s "-"
    | TIMES -> s "*"
    | DIV -> s "/"
    | MOD -> s "%"
    | AND -> s "&&"
    | OR -> s "||"
    | NEQ -> s "!="
    | LSTCAT -> s "@"
    | LSTCONS -> s "::"

let pp_unop fmt = 
  let s = fprintf fmt "@[%s@]" in 
    function 
    | NOT -> s "!"
    | HEAD -> s "hd"
    | TAIL -> s "tl"
    | LEN -> s "len"

let rec pp_expr fmt = function
  | Val v -> pp_value fmt v
  | Var s -> fprintf fmt "@[%s@]" s
  | BinOp (e1, b, e2) -> fprintf fmt "@[%a@ %a@ %a@]"
    pp_expr e1 pp_binop b pp_expr e2
  | UnOp (u, e) -> fprintf fmt "@[%a@ %a@]" pp_unop u pp_expr e
  
let pp_pn_e fmt = 
    function (pn, e)-> fprintf fmt "@[%s: %a@]" pn pp_expr e

let pp_record = pp_list pp_pn_e
let pp_expr_list = pp_list pp_expr
let pp_var_list = pp_list (fun fmt s -> fprintf fmt "@[%s@]" s)


let rec pp_stmt_meta_list fmt = (pp_list ~sep:(format_of_string ";@.") pp_stmt_with_metadata) fmt
and pp_stmt fmt = function
  | Skip -> fprintf fmt "@[%s@]" "skip"
  | VarAssign (v, e) -> fprintf fmt "@[%s := %a@]" v pp_expr e
  | New (v, r) -> fprintf fmt "@[%s := new(%a)@]" v pp_record r
  | Delete e -> fprintf fmt "@[delete@ %a@]" pp_expr e
  | PropLookup (v, e, pn) -> fprintf fmt "@[%s := %a.%s@]" v pp_expr e pn
  | PropUpdate (e1, pn, e2) -> fprintf fmt "@[%a.%s := %a@]" pp_expr e1 pn pp_expr e2 
  | FunCall (v, f, el) -> fprintf fmt "@[%s := %s(%a)@]" v f pp_expr_list el 
  | While (e, s) -> fprintf fmt "@[while(%a) {\n@[<1>%a @]\n}@]" pp_expr e pp_stmt_meta_list s 
  | If (e, s1, s2) -> fprintf fmt "@[if(%a) {\n%a\n} else {\n%a\n} @]"
                         pp_expr e pp_stmt_meta_list s1 pp_stmt_meta_list s2
and pp_stmt_with_metadata fmt = fun (met, stmt) -> pp_stmt fmt stmt
                         
let pp_wisl_type fmt = fun t ->
  let s = fprintf fmt "@[%s@]" in
  match t with
  | WList -> s "List"
  | WNull -> s "NullType"
  | WBool -> s "Bool"
  | WString -> s "String"
  | WObj -> s "Object"
  | WNum -> s "Num"

let rec pp_logic_expr fmt expr =
  match expr with
  | LVal v -> pp_value fmt v
  | LVar lx -> fprintf fmt "@[%s@]" lx
  | PVar x -> fprintf fmt "@[%s@]" x
  | LBinOp (le1, b, le2) -> fprintf fmt "@[(%a %a %a)@]"
                            pp_logic_expr le1 pp_binop b
                            pp_logic_expr le2
  | LUnOp (u, le) -> fprintf fmt "@[(%a %a)@]" pp_unop u pp_logic_expr le
  | LEList lel -> pp_list
                  ~pre:(format_of_string "@[[")
                  ~suf:(format_of_string "]@]")
                  ~empty:(format_of_string "@[nil@]")
                  pp_logic_expr fmt lel
                          

let rec pp_logic_assert fmt asser =
  let pp_params = pp_list pp_logic_expr in
  match asser with
  | LTrue -> pp_print_string fmt "True"
  | LFalse -> pp_print_string fmt "False"
  | LNot a -> fprintf fmt "@[!(%a)@]" pp_logic_assert a
  | LAnd (a1, a2) -> fprintf fmt "@[(%a) /\\ (%a)@]"
              pp_logic_assert a1 pp_logic_assert a2
  | LOr (a1, a2) -> fprintf fmt "@[(%a) \\/ (%a)@]"
                    pp_logic_assert a1 pp_logic_assert a2
  | LEmp -> pp_print_string fmt "emp"
  | LStar (a1, a2) -> fprintf fmt "@[(%a) * (%a)@]"
                    pp_logic_assert a1 pp_logic_assert a2
  | LPred (pname, lel) -> fprintf fmt "@[%s(%a)@]" pname
                          pp_params lel
  | LPointsTo (le1, pn, le2) -> fprintf fmt "@[(%a, %s) -> %a@]"
                              pp_logic_expr le1 pn pp_logic_expr le2
  | LEq (le1, le2) -> fprintf fmt "@[(%a) == (%a)@]" pp_logic_expr le1
                      pp_logic_expr le2
  | LLess (le1, le2) -> fprintf fmt "@[(%a) <# (%a)@]" pp_logic_expr le1
                      pp_logic_expr le2
  | LGreater (le1, le2) -> fprintf fmt "@[(%a) ># (%a)@]" pp_logic_expr le1
                      pp_logic_expr le2
  | LLessEq (le1, le2) -> fprintf fmt "@[(%a) <=# (%a)@]" pp_logic_expr le1
                      pp_logic_expr le2
  | LGreaterEq (le1, le2) -> fprintf fmt "@[(%a) >=# (%a)@]" pp_logic_expr le1
                      pp_logic_expr le2
            
                          

let pp_fct fmt = function f ->
  Format.fprintf fmt "@[function %s(%a) {@.%a;@.return %a@.}@]" f.name
  pp_var_list f.params pp_stmt_meta_list f.body pp_expr f.return_expr

let pp_fct_context = pp_list ~sep:(format_of_string "@.@.") pp_fct

let pp_prog fmt = function prog ->
  match prog.entry_point with
  | None -> Format.fprintf fmt "%a" pp_fct_context prog.context
  | Some stmt -> Format.fprintf fmt "@[%a@.@.%a@]" pp_fct_context prog.context
  pp_stmt_meta_list stmt