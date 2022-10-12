(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Util

(* (size, tp) *)
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
  | SUntil            of aux * sexpl * sexpl list
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
  | VUntil            of aux * vexpl * vexpl list
  | VUntilInf         of aux * int * vexpl list

type expl = S of sexpl | V of vexpl

exception VEXPL
exception SEXPL

let unS = function S p -> p | _ -> raise VEXPL
let unV = function V p -> p | _ -> raise SEXPL

(***********************************
 *                                 *
 * Measure: size                   *
 *                                 *
 ***********************************)
let rec s_size = function
  | STT _ -> 1
  | SAtom _ -> 1
  | SNeg (_, vphi) -> 1 + v_size vphi
  | SDisjL (_, sphi) -> 1 + s_size sphi
  | SDisjR (_, spsi) -> 1 + s_size spsi
  | SConj (_, sphi, spsi) -> 1 + s_size sphi + s_size spsi
  | SImplL (_, vphi) -> 1 + v_size vphi
  | SImplR (_, spsi) -> 1 + s_size spsi
  | SIffSS (_, sphi, spsi) -> 1 + s_size sphi + s_size spsi
  | SIffVV (_, vphi, vpsi) -> 1 + v_size vphi + v_size vpsi
  | SPrev (_, sphi) -> 1 + s_size sphi
  | SNext (_, sphi) -> 1 + s_size sphi
  | SOnce (_, sphi) -> 1 + s_size sphi
  | SHistorically (_, _, sphis) -> 1 + sum s_size sphis
  | SHistoricallyOutL _ -> 1
  | SEventually (_, sphi) -> 1 + s_size sphi
  | SAlways (_, _, sphis) -> 1 + sum s_size sphis
  | SSince (_, spsi, sphis) -> 1 + s_size spsi + sum s_size sphis
  | SUntil (_, spsi, sphis) -> 1 + s_size spsi + sum s_size sphis
and v_size = function
  | VFF _ -> 1
  | VAtom (_, _) -> 1
  | VNeg (_, sphi) -> 1 + s_size sphi
  | VDisj (_, vphi, vpsi) -> 1 + v_size vphi + v_size vpsi
  | VConjL (_, vphi) -> 1 + v_size vphi
  | VConjR (_, vpsi) -> 1 + v_size vpsi
  | VImpl (_, sphi, vpsi) -> 1 + s_size sphi + v_size vpsi
  | VIffSV (_, sphi, vpsi) -> 1 + s_size sphi + v_size vpsi
  | VIffVS (_, vphi, spsi) -> 1 + v_size vphi + s_size spsi
  | VPrev0 _ -> 1
  | VPrevOutL _ -> 1
  | VPrevOutR _ -> 1
  | VPrev (_, vphi) -> 1 + v_size vphi
  | VNextOutL _ -> 1
  | VNextOutR _ -> 1
  | VNext (_, vphi) -> 1 + v_size vphi
  | VOnceOutL _ -> 1
  | VOnce (_, _, vphis) -> 1 + sum v_size vphis
  | VHistorically (_, vphi) -> 1 + v_size vphi
  | VEventually (_, _, vphis) -> 1 + sum v_size vphis
  | VAlways (_, vphi) -> 1 + v_size vphi
  | VSince (_, vphi, vpsis) -> 1 + v_size vphi + sum v_size vpsis
  | VSinceInf (_, _, vpsis) -> 1 + sum v_size vpsis
  | VSinceOutL _ -> 1
  | VUntil (_, vphi, vpsis) -> 1 + v_size vphi + sum v_size vpsis
  | VUntilInf (_, _, vpsis) -> 1 + sum v_size vpsis

let size = function
  | S s_p -> s_size s_p
  | V v_p -> v_size v_p

let size_le = mk_le size

let minsize a b = if size a <= size b then a else b
let minsize_list = function
  | [] -> failwith "empty list for minsize_list"
  | x::xs -> List.fold_left minsize x xs

(* time-point calculation *)
(* note that we only use the explicit time-points for the cases
 * where the return value might be dubious (besides atomic prop/constants) *)
let rec s_at = function
  | STT (_, i) -> i
  | SAtom ((_, i), _) -> i
  | SNeg (_, vphi) -> v_at vphi
  | SDisjL (_, sphi) -> s_at sphi
  | SDisjR (_, spsi) -> s_at spsi
  | SConj (_, sphi, _) -> s_at sphi
  | SImplL (_, vphi) -> v_at vphi
  | SImplR (_, spsi) -> s_at spsi
  | SIffSS (_, sphi, _) -> s_at sphi
  | SIffVV (_, vphi, _) -> v_at vphi
  | SPrev (_, sphi) -> s_at sphi + 1
  | SNext (_, sphi) -> s_at sphi - 1
  | SOnce ((_, i), _) -> i
  | SHistorically ((_, i), _, _) -> i
  | SHistoricallyOutL (_, i) -> i
  | SEventually ((_, i), _) -> i
  | SAlways ((_, i), _, _) -> i
  | SSince (_, spsi, sphis) -> (match sphis with
      | [] -> s_at spsi
      | _ -> s_at (last sphis))
  | SUntil (_, spsi, sphis) -> (match sphis with
      | [] -> s_at spsi
      | x :: _ -> s_at x)
and v_at = function
  | VFF (_, i) -> i
  | VAtom ((_, i), _) -> i
  | VNeg (_, sphi) -> s_at sphi
  | VDisj (_, vphi, _) -> v_at vphi
  | VConjL (_, vphi) -> v_at vphi
  | VConjR (_, vpsi) -> v_at vpsi
  | VImpl (_, sphi, _) -> s_at sphi
  | VIffSV (_, sphi, _) -> s_at sphi
  | VIffVS (_, vphi, _) -> v_at vphi
  | VPrev0 _ -> 0
  | VPrevOutL (_, i) -> i
  | VPrevOutR (_, i) -> i
  | VPrev (_, vphi) -> v_at vphi + 1
  | VNextOutL (_, i) -> i
  | VNextOutR (_, i) -> i
  | VNext (_, vphi) -> v_at vphi - 1
  | VOnceOutL (_, i) -> i
  | VOnce ((_, i), _, _) -> i
  | VHistorically ((_, i), _) -> i
  | VEventually ((_, i), _, _) -> i
  | VAlways ((_, i), _) -> i
  | VSince ((_, i), _, _) -> i
  | VSinceInf ((_, i), _, _) -> i
  | VSinceOutL (_, i) -> i
  | VUntil ((_, i), _, _) -> i
  | VUntilInf ((_, i), _, _) -> i

let s_ltp sp = match sp with
  | SUntil (_, sp2, _) -> s_at sp2
  | _ -> failwith "Bad arguments for s_ltp"

let v_etp vp = match vp with
  | VUntil ((_, i), _, []) -> i
  | VUntil (_, _, vp2::_) -> v_at vp2
  | _ -> failwith "Bad arguments for v_etp"

let p_at = function
| S s_p -> s_at s_p
| V v_p -> v_at v_p

(* Smart constructors *)

(* arbitrary value as a placeholder (this is ignored) *)
let foo = (0, 0)

let stt i =
  let s = s_size (STT foo) in
  STT (s, i)

let satom (i, x) =
  let s = s_size (SAtom (foo, x)) in
  SAtom ((s, i), x)

let sneg p =
  let s = s_size (SNeg (foo, p)) in
  let i = s_at (SNeg (foo, p)) in
  SNeg ((s, i), p)

let sdisjl p =
  let s = s_size (SDisjL (foo, p)) in
  let i = s_at (SDisjL (foo, p)) in
  SDisjL ((s, i), p)

let sdisjr p =
  let s = s_size (SDisjR (foo, p)) in
  let i = s_at (SDisjR (foo, p)) in
  SDisjR ((s, i), p)

let sconj (p1, p2) =
  let s = s_size (SConj (foo, p1, p2)) in
  let i = s_at (SConj (foo, p1, p2)) in
  SConj ((s, i), p1, p2)

let simpll p =
  let s = s_size (SImplL (foo, p)) in
  let i = s_at (SImplL (foo, p)) in
  SImplL ((s, i), p)

let simplr p =
  let s = s_size (SImplR (foo, p)) in
  let i = s_at (SImplR (foo, p)) in
  SImplR ((s, i), p)

let siffss (p1, p2) =
  let s = s_size (SIffSS (foo, p1, p2)) in
  let i = s_at (SIffSS (foo, p1, p2)) in
  SIffSS ((s, i), p1, p2)

let siffvv (p1, p2) =
  let s = s_size (SIffVV (foo, p1, p2)) in
  let i = s_at (SIffVV (foo, p1, p2)) in
  SIffVV ((s, i), p1, p2)

let sprev p =
  let s = s_size (SPrev (foo, p)) in
  let i = s_at (SPrev (foo, p)) in
  SPrev ((s, i), p)

let snext p =
  let s = s_size (SNext (foo, p)) in
  let i = s_at (SNext (foo, p)) in
  SNext ((s, i), p)

let sonce (i, p) =
  let s = s_size (SOnce (foo, p)) in
  SOnce ((s, i), p)

let shistorically (i, li, ps) =
  let s = s_size (SHistorically (foo, 0, ps)) in
  SHistorically ((s, i), li, ps)

let shistoricallyoutl i =
  let s = s_size (SHistoricallyOutL foo) in
  SHistoricallyOutL (s, i)

let seventually (i, p) =
  let s = s_size (SEventually (foo, p)) in
  SEventually ((s, i), p)

let salways (i, hi, ps) =
  let s = s_size (SAlways (foo, 0, ps)) in
  SAlways ((s, i), hi, ps)

let ssince (p1, p2s) =
  let s = s_size (SSince (foo, p1, p2s)) in
  let i = s_at (SSince (foo, p1, p2s)) in
  SSince ((s, i), p1, p2s)

let suntil (p1, p2s) =
  let s = s_size (SUntil (foo, p1, p2s)) in
  let i = s_at (SUntil (foo, p1, p2s)) in
  SUntil ((s, i), p1, p2s)

let vff i =
  let s = v_size (VFF foo) in
  VFF (s, i)

let vatom (i, x) =
  let s = v_size (VAtom (foo, x)) in
  VAtom ((s, i), x)

let vneg p =
  let s = v_size (VNeg (foo, p)) in
  let i = v_at (VNeg (foo, p)) in
  VNeg ((s, i), p)

let vdisj (p1, p2) =
  let s = v_size (VDisj (foo, p1, p2)) in
  let i = v_at (VDisj (foo, p1, p2)) in
  VDisj ((s, i), p1, p2)

let vconjl p =
  let s = v_size (VConjL (foo, p)) in
  let i = v_at (VConjL (foo, p)) in
  VConjL ((s, i), p)

let vconjr p =
  let s = v_size (VConjR (foo, p)) in
  let i = v_at (VConjR (foo, p)) in
  VConjR ((s, i), p)

let vimpl (p1, p2) =
  let s = v_size (VImpl (foo, p1, p2)) in
  let i = v_at (VImpl (foo, p1, p2)) in
  VImpl ((s, i), p1, p2)

let viffsv (p1, p2) =
  let s = v_size (VIffSV (foo, p1, p2)) in
  let i = v_at (VIffSV (foo, p1, p2)) in
  VIffSV ((s, i), p1, p2)

let viffvs (p1, p2) =
  let s = v_size (VIffVS (foo, p1, p2)) in
  let i = v_at (VIffVS (foo, p1, p2)) in
  VIffVS ((s, i), p1, p2)

let vprev0 =
  let s = v_size (VPrev0 foo) in
  let i = v_at (VPrev0 foo) in
  VPrev0 (s, i)

let vprevoutl i =
  let s = v_size (VPrevOutL foo) in
  VPrevOutL (s, i)

let vprevoutr i =
  let s = v_size (VPrevOutR foo) in
  VPrevOutR (s, i)

let vprev p =
  let s = v_size (VPrev (foo, p)) in
  let i = v_at (VPrev (foo, p)) in
  VPrev ((s, i), p)

let vnextoutl i =
  let s = v_size (VNextOutL foo) in
  VNextOutL (s, i)

let vnextoutr i =
  let s = v_size (VNextOutR foo) in
  VNextOutR (s, i)

let vnext p =
  let s = v_size (VNext (foo, p)) in
  let i = v_at (VNext (foo, p)) in
  VNext ((s, i), p)

let vonceoutl i =
  let s = v_size (VOnceOutL foo) in
  VOnceOutL (s, i)

let vonce (i, li, ps) =
  let s = v_size (VOnce (foo, 0, ps)) in
  VOnce ((s, i), li, ps)

let vhistorically (i, p) =
  let s = v_size (VHistorically (foo, p)) in
  VHistorically ((s, i), p)

let veventually (i, hi, ps) =
  let s = v_size (VEventually (foo, 0, ps)) in
  VEventually ((s, i), hi, ps)

let valways (i, p) =
  let s = v_size (VAlways (foo, p)) in
  VAlways ((s, i), p)

let vsince (i, p1, p2s) =
  let s = v_size (VSince (foo, p1, p2s)) in
  VSince ((s, i), p1, p2s)

let vsinceinf (i, li, p2s) =
  let s = v_size (VSinceInf (foo, li, p2s)) in
  VSinceInf ((s, i), li, p2s)

let vsinceoutl i =
  let s = v_size (VSinceOutL foo) in
  VSinceOutL (s, i)

let vuntil (i, p1, p2s) =
  let s = v_size (VUntil (foo, p1, p2s)) in
  VUntil ((s, i), p1, p2s)

let vuntilinf (i, hi, p2s) =
  let s = v_size (VUntilInf (foo, hi, p2s)) in
  VUntilInf ((s, i), hi, p2s)

(* Operations on proofs *)
let sappend sp sp1 = match sp with
  | SSince (_, sp2, sp1s) -> ssince (sp2, List.append sp1s [sp1])
  | SUntil (_, sp2, sp1s) -> suntil (sp2, sp1 :: sp1s)
  | _ -> failwith "Bad arguments for sappend"

let vappend vp vp2 = match vp with
  | VSince ((_, tp), vp1, vp2s) -> vsince (tp, vp1, List.append vp2s [vp2])
  | VSinceInf ((_, tp), etp, vp2s) -> vsinceinf (tp, etp, List.append vp2s [vp2])
  | VUntil ((_, tp), vp1, vp2s) -> vuntil (tp, vp1, vp2 :: vp2s)
  | VUntilInf ((_, tp), ltp, vp2s) -> vuntilinf (tp, ltp, vp2 :: vp2s)
  | _ -> failwith "Bad arguments for vappend"

let sdrop sp = match sp with
  | SUntil (_, _, []) -> None
  | SUntil (_, sp2, sp1s) -> Some (suntil (sp2, drop_front sp1s))
  | _ -> failwith "Bad arguments for sdrop"

let vdrop vp = match vp with
  | VUntil (_, _, _::[]) -> None
  | VUntil ((_, tp), vp1, vp2s) -> Some (vuntil (tp, vp1, drop_front vp2s))
  | VUntilInf (_, _, []) -> None
  | VUntilInf ((_, tp), ltp, vp2s) -> Some (vuntilinf (tp, ltp, drop_front vp2s))
  | _ -> failwith "Bad arguments for vdrop"

(***********************************
 *                                 *
 * Measure: wsize                  *
 *                                 *
 ***********************************)
(* let rec s_wsize ws = function
 *   | STT _ -> 1
 *   | SAtom (_, s) -> (match Hashtbl.find_opt ws s with
 *                      | None -> 1
 *                      | Some(w) -> w)
 *   | SNeg vphi -> 1 + v_wsize ws vphi
 *   | SDisjL sphi -> 1 + s_wsize ws sphi
 *   | SDisjR spsi -> 1 + s_wsize ws spsi
 *   | SConj (sphi, spsi) -> 1 + (s_wsize ws sphi) + (s_wsize ws spsi)
 *   | SImplL vphi -> 1 + v_wsize ws vphi
 *   | SImplR spsi -> 1 + s_wsize ws spsi
 *   | SIffSS (sphi, spsi) -> 1 + (s_wsize ws sphi) + (s_wsize ws spsi)
 *   | SIffVV (vphi, vpsi) -> 1 + (v_wsize ws vphi) + (v_wsize ws vpsi)
 *   | SPrev sphi -> 1 + s_wsize ws sphi
 *   | SNext sphi -> 1 + s_wsize ws sphi
 *   | SOnce (_, sphi) -> 1 + s_wsize ws sphi
 *   | SHistorically (_, _, sphis) -> 1 + (sum (s_wsize ws) sphis)
 *   | SHistoricallyOutL _ -> 1
 *   | SEventually (_, sphi) -> 1 + s_wsize ws sphi
 *   | SAlways (_, _, sphis) -> 1 + (sum (s_wsize ws) sphis)
 *   | SSince (spsi, sphis) -> 1 + (s_wsize ws spsi) + (sum (s_wsize ws) sphis)
 *   | SUntil (spsi, sphis) -> 1 + (s_wsize ws spsi) + (sum (s_wsize ws) sphis)
 * and v_wsize ws = function
 *   | VFF _ -> 1
 *   | VAtom (_, s) -> (match Hashtbl.find_opt ws s with
 *                      | None -> 1
 *                      | Some(w) -> w)
 *   | VNeg sphi -> 1 + s_wsize ws sphi
 *   | VDisj (vphi, vpsi) -> 1 + v_wsize ws vphi + v_wsize ws vpsi
 *   | VConjL vphi -> 1 + v_wsize ws vphi
 *   | VConjR vpsi -> 1 + v_wsize ws vpsi
 *   | VImpl (sphi, vpsi) -> 1 + (s_wsize ws sphi) + (v_wsize ws vpsi)
 *   | VIffSV (sphi, vpsi) -> 1 + (s_wsize ws sphi) + (v_wsize ws vpsi)
 *   | VIffVS (vphi, spsi) -> 1 + (v_wsize ws vphi) + (s_wsize ws spsi)
 *   | VPrev0 -> 1
 *   | VPrevOutL _ -> 1
 *   | VPrevOutR _ -> 1
 *   | VPrev vphi -> 1 + v_wsize ws vphi
 *   | VNextOutL _ -> 1
 *   | VNextOutR _ -> 1
 *   | VNext vphi -> 1 + v_wsize ws vphi
 *   | VOnceOutL _ -> 1
 *   | VOnce (_, _, vphis) -> 1 + (sum (v_wsize ws) vphis)
 *   | VHistorically (_, vphi) -> 1 + v_wsize ws vphi
 *   | VEventually (_, _, vphis) -> 1 + (sum (v_wsize ws) vphis)
 *   | VAlways (_, vphi) -> 1 + v_wsize ws vphi
 *   | VSince (_, vphi, vpsis) -> 1 + v_wsize ws vphi + (sum (v_wsize ws) vpsis)
 *   | VSinceInf (_, _, vphis) -> 1 + (sum (v_wsize ws) vphis)
 *   | VSinceOutL _ -> 1
 *   | VUntil (_, vphi, vpsis) -> 1 + v_wsize ws vphi + (sum (v_wsize ws) vpsis)
 *   | VUntilInf (_, _, vpsis) -> 1 + (sum (v_wsize ws) vpsis)
 *
 * let wsize ws = function
 *   | S sp -> s_wsize ws sp
 *   | V vp -> v_wsize ws vp
 *
 * let wsize_le ws = mk_le (wsize ws) *)

(***********************************
 *                                 *
 * Measure: width                  *
 *                                 *
 ***********************************)
(* let rec s_high = function
 *   | STT i -> i
 *   | SAtom (i, _) -> i
 *   | SNeg vphi -> v_high vphi
 *   | SDisjL sphi -> s_high sphi
 *   | SDisjR spsi -> s_high spsi
 *   | SConj (sphi, spsi) -> max (s_high sphi) (s_high spsi)
 *   | SImplL vphi -> v_high vphi
 *   | SImplR spsi -> s_high spsi
 *   | SIffSS (sphi, spsi) -> max (s_high sphi) (s_high spsi)
 *   | SIffVV (vphi, vpsi) -> max (v_high vphi) (v_high vpsi)
 *   | SPrev sphi -> s_high sphi
 *   | SNext sphi -> s_high sphi
 *   | SOnce (_, sphi) -> s_high sphi
 *   | SHistorically (_, _, sphis) -> max_list (List.map s_high sphis)
 *   | SHistoricallyOutL i -> i
 *   | SEventually (_, sphi) -> s_high sphi
 *   | SAlways (_, _, sphis) -> max_list (List.map s_high sphis)
 *   | SSince (spsi, sphis) -> max (s_high spsi) (max_list (List.map s_high sphis))
 *   | SUntil (spsi, sphis) -> max (s_high spsi) (max_list (List.map s_high sphis))
 * and v_high p = match p with
 *   | VFF i -> i
 *   | VAtom (i, _) -> i
 *   | VNeg sphi -> s_high sphi
 *   | VDisj (vphi, vpsi) -> max (v_high vphi) (v_high vpsi)
 *   | VConjL vphi -> v_high vphi
 *   | VConjR vpsi -> v_high vpsi
 *   | VImpl (sphi, vpsi) -> max (s_high sphi) (v_high vpsi)
 *   | VIffSV (sphi, vpsi) -> max (s_high sphi) (v_high vpsi)
 *   | VIffVS (vphi, spsi) -> max (v_high vphi) (s_high spsi)
 *   | VPrev0 -> 0
 *   | VPrevOutL i -> i
 *   | VPrevOutR i -> i
 *   | VPrev vphi -> max (v_at (VPrev vphi)) (v_high vphi)
 *   | VNextOutL i -> i
 *   | VNextOutR i -> i
 *   | VNext vphi -> max (v_at (VNext vphi)) (v_high vphi)
 *   (\* TODO: Check if we should consider i here *\)
 *   | VOnceOutL i -> i
 *   | VOnce (_, _, vphis) -> max_list (List.map v_high vphis)
 *   | VHistorically (_, vphi) -> v_high vphi
 *   | VEventually (_, _, vphis) -> max_list (List.map v_high vphis)
 *   | VAlways (_, vphi) -> v_high vphi
 *   | VSince (_, vphi, vpsis) -> max (v_high vphi) (max_list (List.map v_high vpsis))
 *   | VSinceInf (_, _, vphis) -> max_list (List.map v_high vphis)
 *   | VSinceOutL i -> i
 *   | VUntil (_, vphi, vpsis) -> max (v_high vphi) (max_list (List.map v_high vpsis))
 *   | VUntilInf (_, _, vpsis) -> max_list (List.map v_high vpsis)
 *
 * let rec s_low = function
 *   | STT i -> i
 *   | SAtom (i, _) -> i
 *   | SNeg vphi -> v_low vphi
 *   | SDisjL sphi -> s_low sphi
 *   | SDisjR spsi -> s_low spsi
 *   | SConj (sphi, spsi) -> min (s_low sphi) (s_low spsi)
 *   | SImplL vphi -> v_low vphi
 *   | SImplR spsi -> s_low spsi
 *   | SIffSS (sphi, spsi) -> min (s_low sphi) (s_low spsi)
 *   | SIffVV (vphi, vpsi) -> min (v_low vphi) (v_low vpsi)
 *   | SPrev sphi -> s_low sphi
 *   | SNext sphi -> s_low sphi
 *   | SOnce (_, sphi) -> s_low sphi
 *   | SHistorically (_, _, sphis) -> min_list (List.map s_low sphis)
 *   | SHistoricallyOutL i -> i
 *   | SEventually (_, sphi) -> s_low sphi
 *   | SAlways (_, _, sphis) -> min_list (List.map s_low sphis)
 *   | SSince (spsi, sphis) -> min (s_low spsi) (min_list (List.map s_low sphis))
 *   | SUntil (spsi, sphis) -> min (s_low spsi) (min_list (List.map s_low sphis))
 * and v_low p = match p with
 *   | VFF i -> i
 *   | VAtom (i, _) -> i
 *   | VNeg sphi -> s_low sphi
 *   | VDisj (vphi, vpsi) -> min (v_low vphi) (v_low vpsi)
 *   | VConjL vphi -> v_low vphi
 *   | VConjR vpsi -> v_low vpsi
 *   | VImpl (sphi, vpsi) -> min (s_low sphi) (v_low vpsi)
 *   | VIffSV (sphi, vpsi) -> min (s_low sphi) (v_low vpsi)
 *   | VIffVS (vphi, spsi) -> min (v_low vphi) (s_low spsi)
 *   | VPrev0 -> 0
 *   | VPrevOutL i -> i
 *   | VPrevOutR i -> i
 *   | VPrev vphi -> min (v_at (VPrev vphi)) (v_low vphi)
 *   | VNextOutL i -> i
 *   | VNextOutR i -> i
 *   | VNext vphi -> min (v_at (VNext vphi)) (v_low vphi)
 *   | VOnceOutL i -> i
 *   | VOnce (_, _, vphis) -> min_list (List.map v_low vphis)
 *   | VHistorically (_, vphi) -> v_low vphi
 *   | VEventually (_, _, vphis) -> min_list (List.map v_low vphis)
 *   | VAlways (_, vphi) -> v_low vphi
 *   (\* TODO: Check if we should consider i here *\)
 *   | VSince (_, vphi, vpsis) -> min (v_low vphi) (min_list (List.map v_low vpsis))
 *   | VSinceInf (_, _, vphis) -> min_list (List.map v_low vphis)
 *   | VSinceOutL i -> i
 *   | VUntil (_, vphi, vpsis) -> min (v_low vphi) (min_list (List.map v_low vpsis))
 *   | VUntilInf (_, _, vpsis) -> min_list (List.map v_low vpsis)
 *
 * let high p = match p with
 *   | S s_p -> s_high s_p
 *   | V v_p -> v_high v_p
 *
 * let low p = match p with
 *   | S s_p -> s_low s_p
 *   | V v_p -> v_low v_p
 *
 * (\* let width p = high p - low p *\)
 *
 * let high_le = mk_le high
 * let low_le = mk_le (fun p -> - low p) *)

(***********************************
 *                                 *
 * Measure: pred                   *
 *                                 *
 ***********************************)
(* let rec s_pred = function
 *   | STT _ -> 0
 *   | SAtom (_, _) -> 1
 *   | SNeg sphi -> v_pred sphi
 *   | SDisjL sphi -> s_pred sphi
 *   | SDisjR spsi -> s_pred spsi
 *   | SConj (sphi, spsi) -> s_pred sphi + s_pred spsi
 *   | SImplL vphi -> v_pred vphi
 *   | SImplR spsi -> s_pred spsi
 *   | SIffSS (sphi, spsi) -> s_pred sphi + s_pred spsi
 *   | SIffVV (vphi, vpsi) -> v_pred vphi + v_pred vpsi
 *   | SPrev sphi -> s_pred sphi
 *   | SNext sphi -> s_pred sphi
 *   | SOnce (_, sphi) -> s_pred sphi
 *   | SHistorically (_, _, sphis) -> sum s_pred sphis
 *   | SHistoricallyOutL _ -> 0
 *   | SEventually (_, sphi) -> s_pred sphi
 *   | SAlways (_, _, sphis) -> sum s_pred sphis
 *   | SSince (spsi, sphis) -> s_pred spsi + sum s_pred sphis
 *   | SUntil (spsi, sphis) -> s_pred spsi + sum s_pred sphis
 * and v_pred = function
 *   | VFF _ -> 0
 *   | VAtom (_, _) -> 1
 *   | VNeg sphi -> s_pred sphi
 *   | VDisj (vphi, vpsi) -> v_pred vphi + v_pred vpsi
 *   | VConjL vphi -> v_pred vphi
 *   | VConjR vpsi -> v_pred vpsi
 *   | VImpl (sphi, vpsi) -> s_pred sphi + v_pred vpsi
 *   | VIffSV (sphi, vpsi) -> s_pred sphi + v_pred vpsi
 *   | VIffVS (vphi, spsi) -> v_pred vphi + s_pred spsi
 *   | VPrev0 -> 0
 *   | VPrevOutL _ -> 0
 *   | VPrevOutR _ -> 0
 *   | VPrev vphi -> v_pred vphi
 *   | VNextOutL _ -> 0
 *   | VNextOutR _ -> 0
 *   | VNext vphi -> v_pred vphi
 *   | VOnceOutL _ -> 0
 *   | VOnce (_, _, vphis) -> sum v_pred vphis
 *   | VHistorically (_, vphi) -> v_pred vphi
 *   | VEventually (_, _, vphis) -> sum v_pred vphis
 *   | VAlways (_, vphi) -> v_pred vphi
 *   | VSince (_, vphi, vpsis) -> v_pred vphi + sum v_pred vpsis
 *   | VSinceInf (_, _, vphis) -> sum v_pred vphis
 *   | VSinceOutL _ -> 0
 *   | VUntil (_, vphi, vpsis) -> v_pred vphi + sum v_pred vpsis
 *   | VUntilInf (_, _, vpsis) -> sum v_pred vpsis
 *
 * let predicates = function
 *   | S s_p -> s_pred s_p
 *   | V v_p -> v_pred v_p
 *
 * let predicates_le = mk_le predicates *)

(* Printing functions *)
let rec s_to_string indent p =
  let indent' = "\t" ^ indent in
  match p with
  | STT (_, i) -> Printf.sprintf "%strue{%d}" indent i
  | SAtom ((_, i), a) -> Printf.sprintf "%s%s{%d}" indent a i
  | SNeg (_, vphi) -> Printf.sprintf "%sSNeg{%d}\n%s" indent (s_at p) (v_to_string indent' vphi)
  | SDisjL (_, sphi) -> Printf.sprintf "%sSDisjL{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SDisjR (_, spsi) -> Printf.sprintf "%sSDisjR{%d}\n%s" indent (s_at p) (s_to_string indent' spsi)
  | SConj (_, sphi, spsi) -> Printf.sprintf "%sSConj{%d}\n%s\n%s" indent (s_at p) (s_to_string indent' sphi) (s_to_string indent' spsi)
  | SImplL (_, vphi) -> Printf.sprintf "%sSImplL{%d}\n%s" indent (s_at p) (v_to_string indent' vphi)
  | SImplR (_, spsi) -> Printf.sprintf "%sSImplR{%d}\n%s" indent (s_at p) (s_to_string indent' spsi)
  | SIffSS (_, sphi, spsi) -> Printf.sprintf "%sSIffSS{%d}\n%s\n%s" indent (s_at p) (s_to_string indent' sphi) (s_to_string indent' spsi)
  | SIffVV (_, vphi, vpsi) -> Printf.sprintf "%sSIffVV{%d}\n%s\n%s" indent (s_at p) (v_to_string indent' vphi) (v_to_string indent' vpsi)
  | SPrev (_, sphi) -> Printf.sprintf "%sSPrev{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SNext (_, sphi) -> Printf.sprintf "%sSNext{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SOnce (_, sphi) -> Printf.sprintf "%sSOnce{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SHistorically (_, _, sphis) -> Printf.sprintf "%sSHistorically{%d}\n%s" indent (s_at p) (list_to_string indent' s_to_string sphis)
  | SHistoricallyOutL (_, i) -> Printf.sprintf "%sSHistoricallyOutL{%d}" indent' i
  | SEventually (_, sphi) -> Printf.sprintf "%sSEventually{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SAlways (_, _, sphis) -> Printf.sprintf "%sSAlways{%d}\n%s" indent (s_at p) (list_to_string indent' s_to_string sphis)
  | SSince (_, spsi, sphis) ->
      Printf.sprintf "%sSSince{%d}\n%s\n%s" indent (s_at p) (s_to_string indent' spsi) (list_to_string indent' s_to_string sphis)
  | SUntil (_, spsi, sphis) ->
      Printf.sprintf "%sSUntil{%d}\n%s\n%s" indent (s_at p) (list_to_string indent' s_to_string sphis) (s_to_string indent' spsi)
and v_to_string indent p =
  let indent' = "\t" ^ indent in
  match p with
  | VFF (_, i) -> Printf.sprintf "%sfalse{%d}" indent i
  | VAtom ((_, i), a) -> Printf.sprintf "%s!%s{%d}" indent a i
  | VNeg (_, sphi) -> Printf.sprintf "%sVNeg{%d}\n%s" indent (v_at p) (s_to_string indent' sphi)
  | VDisj (_, vphi, vpsi) -> Printf.sprintf "%sVDisj{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vphi) (v_to_string indent' vpsi)
  | VConjL (_, vphi) -> Printf.sprintf "%sVConjL{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VConjR (_, vpsi) -> Printf.sprintf "%sVConjR{%d}\n%s" indent (v_at p) (v_to_string indent' vpsi)
  | VImpl (_, sphi, vpsi) -> Printf.sprintf "%sVImpl{%d}\n%s\n%s" indent (v_at p) (s_to_string indent' sphi) (v_to_string indent' vpsi)
  | VIffSV (_, sphi, vpsi) -> Printf.sprintf "%sVIffSV{%d}\n%s\n%s" indent (v_at p) (s_to_string indent' sphi) (v_to_string indent' vpsi)
  | VIffVS (_, vphi, spsi) -> Printf.sprintf "%sVIffVS{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vphi) (s_to_string indent' spsi)
  | VPrev0 _ -> Printf.sprintf "%sVPrev0{0}" indent'
  | VPrevOutL (_, i) -> Printf.sprintf "%sVPrevOutL{%d}" indent' i
  | VPrevOutR (_, i) -> Printf.sprintf "%sVPrevOutR{%d}" indent' i
  | VPrev (_, vphi) -> Printf.sprintf "%sVPrev{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VNextOutL (_, i) -> Printf.sprintf "%sVNextOutL{%d}" indent' i
  | VNextOutR (_, i) -> Printf.sprintf "%sVNextOutR{%d}" indent' i
  | VNext (_, vphi) -> Printf.sprintf "%sVNext{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VOnceOutL (_, i) -> Printf.sprintf "%sVOnceOutL{%d}" indent' i
  | VOnce (_, _, vphis) ->
     Printf.sprintf "%sVOnce{%d}\n%s" indent (v_at p) (list_to_string indent' v_to_string vphis)
  | VHistorically (_, vphi) -> Printf.sprintf "%sVHistorically{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VEventually (_, _, vphis) ->
     Printf.sprintf "%sVEventually{%d}\n%s" indent (v_at p) (list_to_string indent' v_to_string vphis)
  | VAlways (_, vphi) -> Printf.sprintf "%sVAlways{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VSince (_, vphi, vpsis) ->
     Printf.sprintf "%sVSince{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vphi) (list_to_string indent' v_to_string vpsis)
  | VSinceInf (_, _, vphis) ->
     Printf.sprintf "%sVSinceInf{%d}\n%s" indent (v_at p) (list_to_string indent' v_to_string vphis)
  | VSinceOutL (_, i) -> Printf.sprintf "%sVSinceOutL{%d}" indent' i
  | VUntil (_, vphi, vpsis) ->
      Printf.sprintf "%sVUntil{%d}\n%s\n%s" indent (v_at p) (list_to_string indent' v_to_string vpsis) (v_to_string indent' vphi)
  | VUntilInf (_, _, vpsis) ->
     Printf.sprintf "%sVUntilInf{%d}\n%s" indent (v_at p) (list_to_string indent' v_to_string vpsis)

let expl_to_string = function
  | S p -> s_to_string "" p
  | V p -> v_to_string "" p
