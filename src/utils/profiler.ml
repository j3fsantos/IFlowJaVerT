(* ./src/utils/profiler.ml
 *
 * Copyright (C) 2016 Imperial College London
 * All rights reserved.
 *
 * This software is distributed under the BSD license.
 * See the LICENSE file for details.
 *)


(* Different kinds of code we want to keep track of. *)
type profile =
  | Untracked
  | Parser
  | CoreStar
  | SymExec
  | Graph

let string_of_profile p =
  match p with
    | Untracked -> "Untracked"
    | Parser -> "Parser"
    | CoreStar -> "CoreStar"
    | SymExec -> "SymExec"
    | Graph -> "Graph"

(* Map from profile to time spend by the profiled code. *)
let counters : (profile, float) Hashtbl.t = Hashtbl.create 10

(* Profile kind of currently running code. *)
let current_profile = ref Untracked

(* Timestamp when we entered current profile. *)
let last_timestamp = ref 0.0

(* Returns total ellapsed time spent in given profile *)
let get_ellapsed_time (p : profile) =
  try
    Hashtbl.find counters p
  with Not_found -> 0.0

(* Adds to the total ellapsed time for the given profile. *)
let add_ellapsed_times (p : profile) ellapsed_time =
	let old_ellapsed_time = get_ellapsed_time p in
	Hashtbl.replace counters p (ellapsed_time +. old_ellapsed_time)

(* Initializes profile counters. Forgets previous data. Enters *)
(* 'Unknown' profile by default. *)
let reset_counters () =
  Hashtbl.clear counters;
  current_profile := Untracked;
  last_timestamp := Unix.gettimeofday ()

(* Switches between profiles: closes the old profile and adds the *)
(* ellapsed time to counters. Opens the given profile. *)
let change_profile (p : profile) =
	let timestamp = Unix.gettimeofday () in
	add_ellapsed_times !current_profile (timestamp -. !last_timestamp);
	last_timestamp := timestamp;
	current_profile := p

(* Executes the given closure f in profile p. Closes old profile at *)
(* the start and restores it at the end. *)
let track (p : profile) (f : unit -> 'a) : 'a =
  let old_profile = !current_profile in
  change_profile p;
  let res = f() in
  change_profile old_profile;
  res

(* Prints profiler information to standard output. *)
let print_counters () =
  (* add ellapsed time in the current profile. *)
  change_profile !current_profile;
  let total = Hashtbl.fold (fun _ x y -> x +. y) counters 0.0 in
  let entries = Hashtbl.fold (fun p x l -> (p, x) :: l) counters [] in
  (* sort profiles according to ellapsed time *)
  let entries = List.sort (fun (_, x) (_, x') -> compare x x') entries in
  List.iter (fun (p, ellapsed_time) ->
    Printf.printf "Time used by %10s: %.3fs [%2.0f%%]\n"
      (string_of_profile p) ellapsed_time (100.0 *. ellapsed_time /. total)
  ) entries;
  Printf.printf "Total ellapsed time: %.3fs \n" total
  