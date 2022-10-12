(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

type aux = int * int

type sexpl =
  | STT               of aux
  | SAtom             of aux * string
  | SNeg              of aux * vexpl
  | SDisjL            of aux * sexpl
  | SDisjR            of aux * sexpl
  | SConj             of aux * sexpl * sexpl
  | SImplL            of aux * vexpl
  | SImplR            of aux * sexpl
  | SIffSS            of aux * sexpl * sexpl
  | SIffVV            of aux * vexpl * vexpl
  | SPrev             of aux * sexpl
  | SNext             of aux * sexpl
  | SOnce             of aux * sexpl
  | SHistorically     of aux * int * sexpl list
  | SHistoricallyOutL of aux
  | SEventually       of aux * sexpl
  | SAlways           of aux * int * sexpl list
  | SSince            of aux * sexpl * sexpl list
  | SUntil            of aux * int * sexpl * sexpl list
and vexpl =
  | VFF               of aux
  | VAtom             of aux * string
  | VNeg              of aux * sexpl
  | VDisj             of aux * vexpl * vexpl
  | VConjL            of aux * vexpl
  | VConjR            of aux * vexpl
  | VImpl             of aux * sexpl * vexpl
  | VIffSV            of aux * sexpl * vexpl
  | VIffVS            of aux * vexpl * sexpl
  | VPrev0            of aux
  | VPrevOutL         of aux
  | VPrevOutR         of aux
  | VPrev             of aux * vexpl
  | VNextOutL         of aux
  | VNextOutR         of aux
  | VNext             of aux * vexpl
  | VOnceOutL         of aux
  | VOnce             of aux * int * vexpl list
  | VHistorically     of aux * vexpl
  | VEventually       of aux * int * vexpl list
  | VAlways           of aux * vexpl
  | VSince            of aux * vexpl * vexpl list
  | VSinceInf         of aux * int * vexpl list
  | VSinceOutL        of aux
  | VUntil            of aux * int * vexpl * vexpl list
  | VUntilInf         of aux * int * vexpl list

type expl = S of sexpl | V of vexpl

exception VEXPL
exception SEXPL

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

(* val wsize: (string, int) Hashtbl.t -> expl -> int
 * val wsize_le: (string, int) Hashtbl.t -> expl -> expl -> bool
 *
 * val high: expl -> int
 * val high_le: expl -> expl -> bool
 *
 * val low: expl -> int
 * val low_le: expl -> expl -> bool
 *
 * val predicates: expl -> int
 * val predicates_le: expl -> expl -> bool *)

val s_at: sexpl -> int
val v_at: vexpl -> int
val s_ltp: sexpl -> int
val v_etp: vexpl -> int
val p_at: expl -> int

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
val shistorically: int * int * sexpl list -> sexpl
val shistoricallyoutl: int -> sexpl
val seventually: int * sexpl -> sexpl
val salways: int * int * sexpl list -> sexpl
val ssince: sexpl * sexpl list -> sexpl
val suntil: sexpl * sexpl list -> sexpl

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
val vonce: int * int * vexpl list -> vexpl
val vhistorically: int * vexpl -> vexpl
val veventually: int * int * vexpl list -> vexpl
val valways: int * vexpl -> vexpl
val vsince: int * vexpl * vexpl list -> vexpl
val vsinceinf: int * int * vexpl list -> vexpl
val vsinceoutl: int -> vexpl
val vuntil: int * vexpl * vexpl list -> vexpl
val vuntilinf: int * int * vexpl list -> vexpl

val s_to_string: string -> sexpl -> string
val v_to_string: string -> vexpl -> string
val expl_to_string: expl -> string
