(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

exception EMPTY_LIST

(* Sets are defined using a functional interface given a type *)
module SS = Set.Make(String)
type timestamp = int
type timepoint = int
(* (atomic propositions satisfied at that event * timestamp) *)
type event = SS.t * timestamp
type trace = event list
type mode = SAT | VIOL | ALL
type out_mode = PLAIN | JSON | DEBUG

let max_list = List.fold_left max 0
let min_list = List.fold_left min 0

let rec loop f x = loop f (f x)

(* Make the list [i, i+1, i+2, ..., j] *)
let rec ( -- ) i j =
  if i > j then [] else i :: (i + 1 -- j)

let thd el = match el with
  | (_, _, t) -> t

let last l = List.nth l (List.length l - 1)

let paren h k x = if h>k then "("^^x^^")" else x

let sum mes = List.fold_left (fun a b -> a + mes b) 0

let prod p q r s = p r s && q r s

let lex p q r s = p r s || (not (p s r) && q r s)

let mk_le f r s = f r <= f s

let sl_le a b le = (le a b) && not (le b a)

let eat s t = s ^ String.trim t

let list_to_string indent f = function
  | [] -> indent ^ "[]"
  | [x] -> indent ^ eat "[" (f indent x ^ "]")
  | x :: xs ->
      List.fold_left (fun s el -> eat (s ^ "\n" ^ indent ^ "; ") (f indent el))
        (indent ^ eat "[ " (f indent x)) xs ^ " ]"

(*stolen from https://github.com/Octachron/ocaml/blob/posets_for_parmatch/typing/parmatch.ml#L1501*)
let get_mins le ps =
  let rec select_rec r = function
    | [] -> r
    | p::ps ->
      if List.exists (fun x -> le x p) r
      then select_rec r ps
      else select_rec (p :: List.filter (fun x -> not (le p x)) r) ps in
  List.rev (select_rec [] ps)

let drop_front l =
  match l with
  | [] -> []
  | _ :: xs -> xs

let count_lines file =
  let in_ch = open_in file in
  let n = ref 0 in
  let rec read_line () =
    try
      let _ = input_line in_ch in
      let () = n := !n + 1 in
      read_line ()
    with End_of_file -> () in
  let () = read_line () in
  !n

let prepend_uniq xs x = if List.mem x xs then xs else x :: xs

let remove_duplicates xs = List.rev (List.fold_left prepend_uniq [] xs)

(* JSON-related *)
let list_to_json l =
  match l with
  | [] -> "[]"
  | _ -> let els_str = String.concat "" (List.map (fun el -> "\"" ^ el ^ "\",")  l) in
         "[" ^ (String.sub els_str 0 ((String.length els_str)-1)) ^ "]"
