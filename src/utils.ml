open List

let flat_map f l = flatten (map f l)

(* This exception is raised when Gareth thinks something is impossible,
   but it happens anyway. *)
exception ThereAreMorePossibilitiesThanYouThink

(* For some reason, ocaml doesn't seem to have a boolean implication operator. Weird. *)

let (==>) a b = (! a) || b
