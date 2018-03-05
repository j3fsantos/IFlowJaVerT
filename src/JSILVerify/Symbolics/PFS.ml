(** JSIL Pure Formulae *)

open CCommon
open SCommon
open JSIL_Syntax

type t = jsil_logic_assertion DynArray.t

(**************************************)
(** Pure formulae functions          **)
(**************************************)

(** Returns a new (empty) predicate set *)
let init () : t = DynArray.make medium_tbl_size

(** Returns the serialization of --pfs-- as a list *)
let to_list (pfs : t) : jsil_logic_assertion list = DynArray.to_list pfs

(** Returns a PFS.t array given a list of assertions *)
let of_list (pfs : jsil_logic_assertion list) : t = DynArray.of_list pfs