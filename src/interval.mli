(*******************************************************************)
(*     This is part of Aerial, it is distributed under the         *)
(*  terms of the GNU Lesser General Public License version 3       *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util

type uinterval = UI of int
type binterval = BI of int * int 
type interval = B of binterval | U of uinterval
type rel = Below | Inside | Above

val case_I: (binterval -> 'a) -> (uinterval -> 'a) -> interval -> 'a
val lclosed_UI: int -> interval
val lclosed_rclosed_BI: int -> int -> interval
val lclosed_ropen_BI: int -> int -> interval
val lopen_UI: int -> interval
val lopen_rclosed_BI: int -> int -> interval
val lopen_ropen_BI: int -> int -> interval
val right_BI: binterval -> int
val right_I: interval -> int
val full: interval
val subtract_I: int -> interval -> interval
val multiply_I: int -> interval -> interval
val mem_I: int -> interval -> bool
val where_I: int -> interval -> rel
val interval_to_string: interval -> string
val lex_interval: (unit -> interval) -> char -> string -> string -> char -> interval
val etp: ts -> ts_asc_list -> ts
val ltp: ts -> ts_desc_list -> ts
