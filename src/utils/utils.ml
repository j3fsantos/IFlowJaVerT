open Batteries
open List
open BatResult
open Option.Monad

let flat_map f l = flatten (map f l)

(* This exception is raised when Gareth thinks something is impossible,
   but it happens anyway. *)
exception ThereAreMorePossibilitiesThanYouThink of string
exception NotImplemented
exception CannotHappen
exception InvalidArgument of string * string
exception NotAFunction

(* For some reason, ocaml doesn't seem to have a boolean implication operator. Weird. *)

let (==>) a b = (! a) || b

(* Apparently data constructors can't /quite/ be used as
   functions. They can't be composed, for example. *)
let some x = Some x

let escape_html s =
  Str.global_substitute
    (Str.regexp "<\\|>\\|&\\|\"")
    (fun s ->
      match Str.matched_string s with
          "<" -> "&lt;"
        | ">" -> "&gt;"
        | "&" -> "&amp;"
        | "\"" -> "&quot;"
        | _ -> assert false)
    s
    
let (>>=) = bind                        (* This SHOULD be in batteries dammit. *)

(* This should always be "false" in checked-in code. Use it to check
   if you should be printing debug messages in other modules. *)
let debug = false
  
let debugPrint (s:string) =
  if debug then
    Printf.printf "\nDEBUG:\n%s\n\n" s
  else
    ()
    
let is_int (f : float) : bool =
  f -. floor f < Float.epsilon
  
let rec float_to_string_inner n = (* TODO *)
  let string_of_number n =
    let inum = int_of_float n in
    if (float_of_int inum = n) then string_of_int inum
    else if n > 1e+9 && n < 1e+21 then Printf.sprintf "%.0f" n
    else if n < 0.1 && n > 1e-7 then Printf.sprintf "%f" n
    else
      let re = Str.regexp "e\\([-+]\\)0" in (* e+0 -> e+ *)
      Str.replace_first re "e\\1" (string_of_float n) in
  if Float.is_nan n then "NaN"
  else if n = 0.0 or n = -0.0 then "0"
  else if n = Float.infinity then "Infinity"
  else if n < 0. then "-" ^ (float_to_string_inner (-. n))
  else string_of_number n
    
