open Batteries_uni
open List
open Monad
open Option.Monad

let flat_map f l = flatten (map f l)

(* This exception is raised when Gareth thinks something is impossible,
   but it happens anyway. *)
exception ThereAreMorePossibilitiesThanYouThink of string
exception NotImplemented

(* For some reason, ocaml doesn't seem to have a boolean implication operator. Weird. *)

let (==>) a b = (! a) || b

(* Apparently data constructors can't /quite/ be used as
   functions. They can't be composed, for example. *)
let some x = Some x

let unescape_html s =
  Str.global_substitute
    (Str.regexp "&lt;\\|&gt;\\|&amp;\\|&quot;")
    (fun s ->
      match Str.matched_string s with
          "&lt;" -> "<"
        | "&gt;" -> ">"
        | "&amp;" -> "&"
        | "&quot;" -> "\""
        | _ -> assert false)
    s
    
let (>>=) = bind                        (* This SHOULD be in batteries dammit. *)
