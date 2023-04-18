(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base

(* Unbounded [i,+∞) *)
type ut = UI of int

(* Bounded [i,j] *)
type bt = BI of int * int

type t = B of bt | U of ut

let lclosed_UI i = U (UI i)
let lopen_UI i = U (UI (i + 1))

let nonempty_BI l r = if l <= r then BI (l, r) else raise (Invalid_argument "empty interval")
let lopen_ropen_BI i j = B (nonempty_BI (i + 1) (j - 1))
let lopen_rclosed_BI i j = B (nonempty_BI (i + 1) j)
let lclosed_ropen_BI i j = B (nonempty_BI i (j - 1))
let lclosed_rclosed_BI i j = B (nonempty_BI i j)

let full = U (UI 0)

let case f1 f2 = function
  | B i -> f1 i
  | U i -> f2 i

let map f1 f2 = case (fun i -> B (f1 i)) (fun i -> U (f2 i))

let mem t =
  let mem_UI t (UI l) = l <= t in
  let mem_BI t (BI (l, r)) = l <= t && t <= r in
  case (mem_BI t) (mem_UI t)

let left =
  let left_UI (UI l) = l in
  let left_BI (BI (l, r)) = l in
  case left_BI left_UI

let right =
  let right_UI (UI l) = None in
  let right_BI (BI (l, r)) = Some(r) in
  case right_BI right_UI

let to_string_BI = function
  | BI (i, j) -> Printf.sprintf "[%d,%d]" i j

let to_string = function
  | U (UI i) -> Printf.sprintf "[%d,∞)" i
  | B i -> Printf.sprintf "%a" (fun x -> to_string_BI) i

let lex error l i j r =
  (match j with
    | "INFINITY" | "∞" ->
      (match l with
      | '[' -> lclosed_UI (int_of_string i)
      | '(' -> lopen_UI (int_of_string i)
      | _ -> error ())
    | _ ->
      (match l, r with
      | '[',']' -> lclosed_rclosed_BI (int_of_string i) (int_of_string j)
      | '(',']' -> lopen_rclosed_BI (int_of_string i) (int_of_string j)
      | '[',')' -> lclosed_ropen_BI (int_of_string i) (int_of_string j)
      | '(',')' -> lopen_ropen_BI (int_of_string i) (int_of_string j)
      | _ -> error ()))