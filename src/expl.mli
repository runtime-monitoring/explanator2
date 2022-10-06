(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Hashcons

type 'a hlist = ('a hlist_) hash_consed
and 'a hlist_ =
  | HNil
  | HCons of 'a hash_consed * 'a hlist

type sexpl = sexpl_ hash_consed
and sexpl_ =
  | STT of int
  | SAtom of int * string
  | SNeg of vexpl
  | SDisjL of sexpl
  | SDisjR of sexpl
  | SConj of sexpl * sexpl
  | SImplL of vexpl
  | SImplR of sexpl
  | SIffSS of sexpl * sexpl
  | SIffVV of vexpl * vexpl
  | SPrev of sexpl
  | SNext of sexpl
  | SOnce of int * sexpl
  | SHistorically of int * int * sexpl_ hlist
  | SHistoricallyOutL of int
  | SEventually of int * sexpl
  | SAlways of int * int * sexpl_ hlist
  | SSince of sexpl * sexpl_ hlist
  | SUntil of sexpl * sexpl_ hlist
and vexpl = vexpl_ hash_consed
and vexpl_ =
  | VFF of int
  | VAtom of int * string
  | VNeg of sexpl
  | VDisj of vexpl * vexpl
  | VConjL of vexpl
  | VConjR of vexpl
  | VImpl of sexpl * vexpl
  | VIffSV of sexpl * vexpl
  | VIffVS of vexpl * sexpl
  | VPrev0
  | VPrevOutL of int
  | VPrevOutR of int
  | VPrev of vexpl
  | VNextOutL of int
  | VNextOutR of int
  | VNext of vexpl
  | VOnceOutL of int
  | VOnce of int * int * vexpl_ hlist
  | VHistorically of int * vexpl
  | VEventually of int * int * vexpl_ hlist
  | VAlways of int * vexpl
  | VSince of int * vexpl * vexpl_ hlist
  | VSinceInf of int * int * vexpl_ hlist
  | VSinceOutL of int
  | VUntil of int * vexpl * vexpl_ hlist
  | VUntilInf of int * int * vexpl_ hlist

type expl = S of sexpl | V of vexpl

exception VEXPL
exception SEXPL

val shnil: sexpl_ hlist
val shcons: sexpl -> sexpl_ hlist -> sexpl_ hlist
val vhnil: vexpl_ hlist
val vhcons: vexpl -> vexpl_ hlist -> vexpl_ hlist

val stt: int -> sexpl
val satom: int * string -> sexpl
val sneg: vexpl -> sexpl
val sdisjl: sexpl -> sexpl
val sdisjr: sexpl -> sexpl
val sconj: sexpl * sexpl -> sexpl
val simpll: vexpl -> sexpl
val simplr: sexpl -> sexpl
val siffss: sexpl * sexpl -> sexpl
val siffvv: vexpl * vexpl -> sexpl
val sprev: sexpl -> sexpl
val snext: sexpl -> sexpl
val sonce: int * sexpl -> sexpl
val shistorically: int * int * sexpl_ hlist -> sexpl
val shistoricallyoutl: int -> sexpl
val seventually: int * sexpl -> sexpl
val salways: int * int * sexpl_ hlist -> sexpl
val ssince: sexpl * sexpl_ hlist -> sexpl
val suntil: sexpl * sexpl_ hlist -> sexpl

val vff: int -> vexpl
val vatom: int * string -> vexpl
val vneg: sexpl -> vexpl
val vdisj: vexpl * vexpl -> vexpl
val vconjl: vexpl -> vexpl
val vconjr: vexpl -> vexpl
val vimpl: sexpl * vexpl -> vexpl
val viffsv: sexpl * vexpl -> vexpl
val viffvs: vexpl * sexpl -> vexpl
val vprev0: vexpl
val vprevoutl: int -> vexpl
val vprevoutr: int -> vexpl
val vprev: vexpl -> vexpl
val vnextoutl: int -> vexpl
val vnextoutr: int -> vexpl
val vnext: vexpl -> vexpl
val vonceoutl: int -> vexpl
val vonce: int * int * vexpl_ hlist -> vexpl
val vhistorically: int * vexpl -> vexpl
val veventually: int * int * vexpl_ hlist -> vexpl
val valways: int * vexpl -> vexpl
val vsince: int * vexpl * vexpl_ hlist -> vexpl
val vsinceinf: int * int * vexpl_ hlist -> vexpl
val vsinceoutl: int -> vexpl
val vuntil: int * vexpl * vexpl_ hlist -> vexpl
val vuntilinf: int * int * vexpl_ hlist -> vexpl

val is_hnil: 'a hlist -> bool
val hfold_left: ('a -> 'b hash_consed -> 'a) -> 'a -> 'b hlist -> 'a
val shmap: ('a hash_consed -> 'b) -> 'a hlist -> 'b list
val vhmap: ('a hash_consed -> 'b) -> 'a hlist -> 'b list
val shmap_sexpl: (sexpl_ hash_consed -> sexpl) -> sexpl_ hlist -> sexpl_ hlist
val vhmap_vexpl: (vexpl_ hash_consed -> vexpl) -> vexpl_ hlist -> vexpl_ hlist
val hlist_list: 'a hlist -> 'a list
val shrev: sexpl_ hlist -> sexpl_ hlist
val vhrev: vexpl_ hlist -> vexpl_ hlist
val hlength: 'a hlist -> int

val unS: expl -> sexpl
val unV: expl -> vexpl

val sappend: sexpl -> sexpl -> sexpl
val vappend: vexpl -> vexpl -> vexpl
val sdrop: sexpl -> sexpl option
val vdrop: vexpl -> vexpl option

val size: expl -> int
val size_le: expl -> expl -> bool
val minsize: expl -> expl -> expl
val minsize_list: expl list -> expl

(* val wsize: (string, int) Hashtbl.t -> expl -> int *)
(* val wsize_le: (string, int) Hashtbl.t -> expl -> expl -> bool *)

(* val high: expl -> int *)
(* val high_le: expl -> expl -> bool *)

(* val low: expl -> int *)
(* val low_le: expl -> expl -> bool *)

(* val predicates: expl -> int *)
(* val predicates_le: expl -> expl -> bool *)

val s_at: sexpl -> int
val v_at: vexpl -> int
val s_ltp: sexpl -> int
val v_etp: vexpl -> int
val p_at: expl -> int

val s_to_string: string -> sexpl -> string
val v_to_string: string -> vexpl -> string
val expl_to_string: expl -> string
