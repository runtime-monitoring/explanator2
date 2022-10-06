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

let m1 = Hashcons.create 271
let m2 = Hashcons.create 271
let m3 = Hashcons.create 271
let m4 = Hashcons.create 271

let hash x = x.hkey
let head x = x.node

let shlist_hashcons =
  let hash = function
    | HNil -> Hashtbl.hash 2
    | HCons (x, xs) -> Hashtbl.hash (3, x.hkey, xs.hkey) in
  let equal x y = match x, y with
    | HNil, HNil -> true
    | HCons (z, zs), HCons (z', zs') -> z == z' && zs == zs'
    | _ -> false in
  Hashcons.hashcons hash equal m1

let shnil = shlist_hashcons HNil
let shcons (x: sexpl) (xs: sexpl_ hlist) = shlist_hashcons (HCons (x, xs))

let vhlist_hashcons =
  let hash = function
    | HNil -> Hashtbl.hash 2
    | HCons (x, xs) -> Hashtbl.hash (3, x.hkey, xs.hkey) in
  let equal x y = match x, y with
    | HNil, HNil -> true
    | HCons (z, zs), HCons (z', zs') -> z == z' && zs == zs'
    | _ -> false in
  Hashcons.hashcons hash equal m2

let vhnil = vhlist_hashcons HNil
let vhcons (x: vexpl) (xs: vexpl_ hlist) = vhlist_hashcons (HCons (x, xs))

let s_hash = function
  | STT i -> Hashtbl.hash (2, i)
  | SAtom (i, x) -> Hashtbl.hash (3, i, x)
  | SNeg vphi -> Hashtbl.hash (5, vphi.hkey)
  | SDisjL sphi -> Hashtbl.hash (7, sphi.hkey)
  | SDisjR spsi -> Hashtbl.hash (11, spsi.hkey)
  | SConj (sphi, spsi) -> Hashtbl.hash (13, sphi.hkey, spsi.hkey)
  | SImplL vphi -> Hashtbl.hash (17, vphi.hkey)
  | SImplR spsi -> Hashtbl.hash (19, spsi.hkey)
  | SIffSS (sphi, spsi) -> Hashtbl.hash (23, sphi.hkey, spsi.hkey)
  | SIffVV (vphi, vpsi) -> Hashtbl.hash (29, vphi.hkey, vpsi.hkey)
  | SPrev sphi -> Hashtbl.hash (31, sphi.hkey)
  | SNext sphi -> Hashtbl.hash (37, sphi.hkey)
  | SOnce (i, sphi) -> Hashtbl.hash (41, i, sphi.hkey)
  | SHistorically (i, li, sphis) -> Hashtbl.hash (43, i, li, sphis.hkey)
  | SHistoricallyOutL i -> Hashtbl.hash (47, i)
  | SEventually (i, sphi) -> Hashtbl.hash (53, i, sphi.hkey)
  | SAlways (i, hi, sphis) -> Hashtbl.hash (59, i, hi, sphis.hkey)
  | SSince (spsi, sphis) -> Hashtbl.hash (61, spsi.hkey, sphis.hkey)
  | SUntil (spsi, sphis) -> Hashtbl.hash (67, spsi.hkey, sphis.hkey)
and v_hash = function
  | VFF i -> Hashtbl.hash (71, i)
  | VAtom (i, x) -> Hashtbl.hash (73, i, x)
  | VNeg sphi -> Hashtbl.hash (79, sphi.hkey)
  | VDisj (vphi, vpsi) -> Hashtbl.hash (83, vphi.hkey, vpsi.hkey)
  | VConjL vphi -> Hashtbl.hash (89, vphi.hkey)
  | VConjR vpsi -> Hashtbl.hash (97, vpsi.hkey)
  | VImpl (sphi, vpsi) -> Hashtbl.hash (101, sphi.hkey, vpsi.hkey)
  | VIffSV (sphi, vpsi) -> Hashtbl.hash (103, sphi.hkey, vpsi.hkey)
  | VIffVS (vphi, spsi) -> Hashtbl.hash (107, vphi.hkey, spsi.hkey)
  | VPrev0 -> Hashtbl.hash (109)
  | VPrevOutL i -> Hashtbl.hash (113, i)
  | VPrevOutR i -> Hashtbl.hash (127, i)
  | VPrev vphi -> Hashtbl.hash (131, vphi.hkey)
  | VNextOutL i -> Hashtbl.hash (137, i)
  | VNextOutR i -> Hashtbl.hash (139, i)
  | VNext vphi -> Hashtbl.hash (149, vphi.hkey)
  | VOnceOutL i -> Hashtbl.hash (151, i)
  | VOnce (i, li, vphis) -> Hashtbl.hash (157, i, li, vphis.hkey)
  | VHistorically (i, vphi) -> Hashtbl.hash (163, i, vphi.hkey)
  | VEventually (i, hi, vphis) -> Hashtbl.hash (167, i, hi, vphis.hkey)
  | VAlways (i, vphi) -> Hashtbl.hash (173, i, vphi.hkey)
  | VSince (i, vphi, vpsis) -> Hashtbl.hash (173, i, vphi.hkey, vpsis.hkey)
  | VSinceInf (i, li, vpsis) -> Hashtbl.hash (179, i, li, vpsis.hkey)
  | VSinceOutL i -> Hashtbl.hash (181, i)
  | VUntil (i, vphi, vpsis) -> Hashtbl.hash (191, i, vphi.hkey, vpsis.hkey)
  | VUntilInf (i, hi, vpsis) -> Hashtbl.hash (193, i, hi, vpsis.hkey)

let s_hashcons =
  let s_equal x y = match x, y with
    | STT i, STT i' -> i = i'
    | SAtom (i, x), SAtom (i', x') -> i = i' && x = x'
    | SNeg p, SNeg p' -> p == p'
    | SImplL p, SImplL p' -> p == p'
    | SImplR p, SImplR p' -> p == p'
    | SDisjL p, SDisjL p'
    | SDisjR p, SDisjR p'
    | SPrev p, SPrev p'
    | SNext p, SNext p' -> p == p'
    | SConj (p1, p2), SConj (p1', p2') -> p1 == p1' && p2 == p2'
    | SIffSS (p1, p2), SIffSS (p1', p2') -> p1 == p1' && p2 == p2'
    | SIffVV (p1, p2), SIffVV (p1', p2') -> p1 == p1' && p2 == p2'
    | SOnce (i, p), SOnce (i', p')
    | SEventually (i, p), SEventually (i', p') -> i = i' && p == p'
    | SHistoricallyOutL i, SHistoricallyOutL i' -> i = i'
    | SHistorically (i, j, ps), SHistorically (i', j', ps')
    | SAlways (i, j, ps), SAlways (i', j', ps') -> i = i' && j = j' && ps == ps'
    | SSince (p2, p1s), SSince (p2', p1s')
    | SUntil (p2, p1s), SUntil (p2', p1s') -> p2 == p2' && p1s == p1s'
    | _ -> false in
  Hashcons.hashcons s_hash s_equal m3

let v_hashcons =
  let v_equal x y = match x, y with
    | VFF i, VFF i' -> i = i'
    | VAtom (i, x), VAtom (i', x') -> i = i' && x = x'
    | VNeg p, VNeg p' -> p == p'
    | VImpl (p1, p2), VImpl (p1', p2') -> p1 == p1' && p2 == p2'
    | VIffSV (p1, p2), VIffSV (p1', p2') -> p1 == p1' && p2 == p2'
    | VIffVS (p1, p2), VIffVS (p1', p2') -> p1 == p1' && p2 == p2'
    | VConjL p, VConjL p'
    | VConjR p, VConjR p'
    | VPrev p, VPrev p'
    | VNext p, VNext p' -> p == p'
    | VPrev0, VPrev0 -> true
    | VPrevOutL i, VPrevOutL i'
    | VPrevOutR i, VPrevOutR i'
    | VNextOutL i, VNextOutL i'
    | VNextOutR i, VNextOutR i'
    | VOnceOutL i, VOnceOutL i'
    | VSinceOutL i, VSinceOutL i' -> i = i'
    | VDisj (p1, p2), VDisj (p1', p2') -> p1 == p1' && p2 == p2'
    | VHistorically (i, p), VHistorically (i', p')
    | VAlways (i, p), VAlways (i', p') -> i = i' && p == p'
    | VOnce (i, j, ps), VOnce (i', j', ps')
    | VEventually (i, j, ps), VEventually (i', j', ps')
    | VSinceInf (i, j, ps), VSinceInf (i', j', ps')
    | VUntilInf (i, j, ps), VUntilInf (i', j', ps') -> i = i' && j = j' && ps == ps'
    | VSince (i, p1, p2s), VSince (i', p1', p2s')
    | VUntil (i, p1, p2s), VUntil (i', p1', p2s') -> i = i' && p1 == p1' && p2s == p2s'
    | _ -> false in
  Hashcons.hashcons v_hash v_equal m4

let stt i = s_hashcons (STT i)
let satom (i, x) = s_hashcons (SAtom (i, x))
let sneg p = s_hashcons (SNeg p)
let sdisjl p = s_hashcons (SDisjL p)
let sdisjr p = s_hashcons (SDisjR p)
let sconj (p1, p2) = s_hashcons (SConj (p1, p2))
let simpll p = s_hashcons (SImplL p)
let simplr p = s_hashcons (SImplR p)
let siffss (p1, p2) = s_hashcons (SIffSS (p1, p2))
let siffvv (p1, p2) = s_hashcons (SIffVV (p1, p2))
let sprev p = s_hashcons (SPrev p)
let snext p = s_hashcons (SNext p)
let sonce (i, p) = s_hashcons (SOnce (i, p))
let shistorically (i, li, ps) = s_hashcons (SHistorically (i, li, ps))
let shistoricallyoutl i = s_hashcons (SHistoricallyOutL i)
let seventually (i, p) = s_hashcons (SEventually (i, p))
let salways (i, hi, ps) = s_hashcons (SAlways (i, hi, ps))
let ssince (p1, p2s) = s_hashcons (SSince (p1, p2s))
let suntil (p1, p2s) = s_hashcons (SUntil (p1, p2s))

let vff i = v_hashcons (VFF i)
let vatom (i, x) = v_hashcons (VAtom (i, x))
let vneg p = v_hashcons (VNeg p)
let vdisj (p1, p2) = v_hashcons (VDisj (p1, p2))
let vconjl p = v_hashcons (VConjL p)
let vconjr p = v_hashcons (VConjR p)
let vimpl (p1, p2) = v_hashcons (VImpl (p1, p2))
let viffsv (p1, p2) = v_hashcons (VIffSV (p1, p2))
let viffvs (p1, p2) = v_hashcons (VIffVS (p1, p2))
let vprev0 = v_hashcons VPrev0
let vprevoutl i = v_hashcons (VPrevOutL i)
let vprevoutr i = v_hashcons (VPrevOutR i)
let vprev p = v_hashcons (VPrev p)
let vnextoutl i = v_hashcons (VNextOutL i)
let vnextoutr i = v_hashcons (VNextOutR i)
let vnext p = v_hashcons (VNext p)
let vonceoutl i = v_hashcons (VOnceOutL i)
let vonce (i, li, ps) = v_hashcons (VOnce (i, li, ps))
let vhistorically (i, p) = v_hashcons (VHistorically (i, p))
let veventually (i, hi, ps) = v_hashcons (VEventually (i, hi, ps))
let valways (i, p) = v_hashcons (VAlways (i, p))
let vsince (i, p1, p2s) = v_hashcons (VSince (i, p1, p2s))
let vsinceinf (i, li, p2s) = v_hashcons (VSinceInf (i, li, p2s))
let vsinceoutl i = v_hashcons (VSinceOutL i)
let vuntil (i, p1, p2s) = v_hashcons (VUntil (i, p1, p2s))
let vuntilinf (i, hi, p2s) = v_hashcons (VUntilInf (i, hi, p2s))

let memo_rec f =
  let t1 = ref Hmap.empty in
  let t2 = ref Hmap.empty in
  let rec s_aux sp =
    try Hmap.find sp !t1
    with Not_found ->
      let z = f s_aux v_aux (S sp) in
      t1 := Hmap.add sp z !t1; z
  and v_aux vp =
    try Hmap.find vp !t2
    with Not_found ->
      let z = f s_aux v_aux (V vp) in
      t2 := Hmap.add vp z !t2; z
  in (s_aux, v_aux)

let is_hnil hl =
  match hl.node with
  | HNil -> true
  | HCons (_, _) -> false

let is_hcons_hnil hl =
  match hl.node with
  | HCons (_, t) when is_hnil t -> true
  | _ -> false

let shrev hl =
  let rec aux acc tail = match tail.node with
    | HNil -> acc
    | HCons (h, t) -> aux (shcons h acc) t in
  aux shnil hl

let vhrev hl =
  let rec aux acc tail = match tail.node with
    | HNil -> acc
    | HCons (h, t) -> aux (vhcons h acc) t in
  aux vhnil hl

let htail hl = match hl.node with
  | HNil -> failwith "htail"
  | HCons (_, t) -> t

let rec shmap f hl = match hl.node with
  | HNil -> []
  | HCons (a1, tl) ->
     let r1 = f a1 in
     r1 :: (shmap f tl)

let rec vhmap f hl = match hl.node with
  | HNil -> []
  | HCons (a1, tl) ->
     let r1 = f a1 in
     r1 :: (vhmap f tl)

let rec shmap_sexpl f hl = match hl.node with
  | HNil -> shnil
  | HCons (a1, tl) ->
     let r1 = f a1 in
     shcons r1 (shmap_sexpl f tl)

let rec vhmap_vexpl f hl = match hl.node with
  | HNil -> vhnil
  | HCons (a1, tl) ->
     let r1 = f a1 in
     vhcons r1 (vhmap_vexpl f tl)

let rec shsnoc (hl: sexpl_ hlist) a = match hl.node with
  | HNil -> shcons a shnil
  | HCons (x, xs) -> shcons x (shsnoc xs a)

let rec vhsnoc (hl: vexpl_ hlist) a = match hl.node with
  | HNil -> vhcons a vhnil
  | HCons (x, xs) -> vhcons x (vhsnoc xs a)

let rec hfold_left f acc hl =
  match hl.node with
  | HNil -> acc
  | HCons (x, xs) -> hfold_left f (f acc x) xs

let hlist_to_string indent f hl = match hl.node with
  | HNil -> indent ^ "[]"
  | HCons (x, hnil) -> indent ^ eat "[" (f indent x ^ "]")
  | HCons (x, xs) -> hfold_left (fun s el -> eat (s ^ "\n" ^ indent ^ "; ") (f indent el))
                       (indent ^ eat "[ " (f indent x)) xs ^ " ]"

let hnth hl n =
  if n < 0 then invalid_arg "hnth" else
  let rec hnth_aux hl n =
    match hl.node with
    | HNil -> failwith "hnth"
    | HCons (x, xs) -> if n = 0 then x else hnth_aux xs (n-1)
  in hnth_aux hl n

let hlength hl =
  let rec hlength_aux len hl = match hl.node with
    | HNil -> len
    | HCons (_, xs) -> hlength_aux (len + 1) xs in
  hlength_aux 0 hl

let hlast hl = hnth hl (hlength hl - 1)

let hhead hl = match hl.node with
  | HNil -> failwith "hhead"
  | HCons (x, _) -> x

let hlist_list hl =
  let rec hlist_list_aux acc hl =
    match hl.node with
    | HNil -> acc
    | HCons (x, xs) -> hlist_list_aux (x.node :: acc) xs in
  hlist_list_aux [] hl

let sum mes = hfold_left (fun a b -> a + mes b) 0

exception VEXPL
exception SEXPL

let unS = function S p -> p | _ -> raise VEXPL
let unV = function V p -> p | _ -> raise SEXPL

let expl_to_bool = function
  | S _ -> true
  | V _ -> false

let sappend sp sp1 = match sp.node with
  | SSince (sp2, sp1s) -> ssince (sp2, shsnoc sp1s sp1)
  | SUntil (sp2, sp1s) -> suntil (sp2, shcons sp1 sp1s)
  | _ -> failwith "Bad arguments for sappend"

let vappend vp vp2 = match vp.node with
  | VSince (tp, vp1, vp2s) -> vsince (tp,  vp1, vhsnoc vp2s vp2)
  | VSinceInf (tp, etp, vp2s) -> vsinceinf (tp, etp, vhsnoc vp2s vp2)
  | VUntil (tp, vp1, vp2s) -> vuntil (tp, vp1, vhcons vp2 vp2s)
  | VUntilInf (tp, ltp, vp2s) -> vuntilinf (tp, ltp, vhcons vp2 vp2s)
  | _ -> failwith "Bad arguments for vappend"

let sdrop sp = match sp.node with
  | SUntil (_, sp1s) when is_hnil sp1s -> None
  | SUntil (sp2, sp1s) -> Some (suntil (sp2, htail sp1s))
  | _ -> failwith "Bad arguments for sdrop"

let vdrop vp = match vp.node with
  | VUntil (_, _, vp2s) when is_hcons_hnil vp2s -> None
  | VUntil (tp, vp1, vp2s) -> Some (vuntil (tp, vp1, htail vp2s))
  | VUntilInf (_, _, vp2s) when is_hnil vp2s -> None
  | VUntilInf (tp, ltp, vp2s) -> Some (vuntilinf (tp, ltp, htail vp2s))
  | _ -> failwith "Bad arguments for vdrop"

let (s_at, v_at) =
  memo_rec (fun s_at v_at p ->
      match p with
      | S sp -> (match sp.node with
                 | STT i -> i
                 | SAtom (i, _) -> i
                 | SNeg vphi -> v_at vphi
                 | SDisjL sphi -> s_at sphi
                 | SDisjR spsi -> s_at spsi
                 | SConj (sphi, _) -> s_at sphi
                 | SImplL vphi -> v_at vphi
                 | SImplR spsi -> s_at spsi
                 | SIffSS (sphi, _) -> s_at sphi
                 | SIffVV (vphi, _) -> v_at vphi
                 | SPrev sphi -> s_at sphi + 1
                 | SNext sphi -> s_at sphi - 1
                 | SOnce (i, _) -> i
                 | SHistorically (i, _, _) -> i
                 | SHistoricallyOutL i -> i
                 | SEventually (i, _) -> i
                 | SAlways (i, _, _) -> i
                 | SSince (spsi, sphis) -> (match sphis.node with
                                            | HNil -> s_at spsi
                                            | HCons _ -> s_at (hlast sphis))
                 | SUntil (spsi, sphis) -> (match sphis.node with
                                            | HNil -> s_at spsi
                                            | HCons (x, _) -> s_at x))
      | V vp -> (match vp.node with
                 | VFF i -> i
                 | VAtom (i, _) -> i
                 | VNeg sphi -> s_at sphi
                 | VDisj (vphi, _) -> v_at vphi
                 | VConjL vphi -> v_at vphi
                 | VConjR vpsi -> v_at vpsi
                 | VImpl (sphi, _) -> s_at sphi
                 | VIffSV (sphi, _) -> s_at sphi
                 | VIffVS (vphi, _) -> v_at vphi
                 | VPrev0 -> 0
                 | VPrevOutL i -> i
                 | VPrevOutR i -> i
                 | VPrev vphi -> v_at vphi + 1
                 | VNextOutL i -> i
                 | VNextOutR i -> i
                 | VNext vphi -> v_at vphi - 1
                 | VOnceOutL i -> i
                 | VOnce (i, _, _) -> i
                 | VHistorically (i, _) -> i
                 | VEventually (i, _, _) -> i
                 | VAlways (i, _) -> i
                 | VSince (i, _, _) -> i
                 | VSinceInf (i, _, _) -> i
                 | VSinceOutL i -> i
                 | VUntil (i, _, _) -> i
                 | VUntilInf (i, _, _) -> i))

let s_ltp sp = match sp.node with
  | SUntil (sp2, _) -> s_at sp2
  | _ -> failwith "Bad arguments for s_ltp"

let v_etp vp = match vp.node with
  | VUntil (i, _, vp2s) when is_hnil vp2s -> i
  | VUntil (_, _, vp2s) -> v_at (hhead vp2s)
  | _ -> failwith "Bad arguments for v_etp"

let p_at = function
| S s_p -> s_at s_p
| V v_p -> v_at v_p

(***********************************
 *                                 *
 * Measure: size                   *
 *                                 *
 ***********************************)
let (s_size, v_size) =
  memo_rec (fun s_size v_size p ->
      match p with
      | S sp -> (match sp.node with
                 | STT _ -> 1
                 | SAtom (_, _) -> 1
                 | SNeg vphi -> 1 + v_size vphi
                 | SDisjL sphi -> 1 + s_size sphi
                 | SDisjR spsi -> 1 + s_size spsi
                 | SConj (sphi, spsi) -> 1 + s_size sphi + s_size spsi
                 | SImplL vphi -> 1 + v_size vphi
                 | SImplR spsi -> 1 + s_size spsi
                 | SIffSS (sphi, spsi) -> 1 + s_size sphi + s_size spsi
                 | SIffVV (vphi, vpsi) -> 1 + v_size vphi + v_size vpsi
                 | SPrev sphi -> 1 + s_size sphi
                 | SNext sphi -> 1 + s_size sphi
                 | SOnce (_, sphi) -> 1 + s_size sphi
                 | SHistorically (_, _, sphis) -> 1 + sum s_size sphis
                 | SHistoricallyOutL _ -> 1
                 | SEventually (_, sphi) -> 1 + s_size sphi
                 | SAlways (_, _, sphis) -> 1 + sum s_size sphis
                 | SSince (spsi, sphis) -> 1 + s_size spsi + sum s_size sphis
                 | SUntil (spsi, sphis) -> 1 + s_size spsi + sum s_size sphis)
      | V vp -> match vp.node with
                | VFF _ -> 1
                | VAtom (_, _) -> 1
                | VNeg sphi -> 1 + s_size sphi
                | VDisj (vphi, vpsi) -> 1 + v_size vphi + v_size vpsi
                | VConjL vphi -> 1 + v_size vphi
                | VConjR vpsi -> 1 + v_size vpsi
                | VImpl (sphi, vpsi) -> 1 + s_size sphi + v_size vpsi
                | VIffSV (sphi, vpsi) -> 1 + s_size sphi + v_size vpsi
                | VIffVS (vphi, spsi) -> 1 + v_size vphi + s_size spsi
                | VPrev0 -> 1
                | VPrevOutL _ -> 1
                | VPrevOutR _ -> 1
                | VPrev vphi -> 1 + v_size vphi
                | VNextOutL _ -> 1
                | VNextOutR _ -> 1
                | VNext vphi -> 1 + v_size vphi
                | VOnceOutL _ -> 1
                | VOnce (_, _, vphis) -> 1 + sum v_size vphis
                | VHistorically (_, vphi) -> 1 + v_size vphi
                | VEventually (_, _, vphis) -> 1 + sum v_size vphis
                | VAlways (_, vphi) -> 1 + v_size vphi
                | VSince (_, vphi, vpsis) -> 1 + v_size vphi + sum v_size vpsis
                | VSinceInf (_, _, vpsis) -> 1 + sum v_size vpsis
                | VSinceOutL _ -> 1
                | VUntil (_, vphi, vpsis) -> 1 + v_size vphi + sum v_size vpsis
                | VUntilInf (_, _, vpsis) -> 1 + sum v_size vpsis)

let size = function
  | S s_p -> s_size s_p
  | V v_p -> v_size v_p

let size_le = mk_le size

let minsize a b = if size a <= size b then a else b
let minsize_list = function
  | [] -> failwith "empty list for minsize_list"
  | x::xs -> List.fold_left minsize x xs

(***********************************
 *                                 *
 * Measure: wsize                   *
 *                                 *
 ***********************************)
(* let rec s_wsize ws p = function *)
(*   | STT _ -> 1 *)
(*   | SAtom (_, s) -> (match Hashtbl.find_opt ws s with *)
(*                      | None -> 1 *)
(*                      | Some(w) -> w) *)
(*   | SNeg vphi -> 1 + v_wsize ws vphi *)
(*   | SDisjL sphi -> 1 + s_wsize ws sphi *)
(*   | SDisjR spsi -> 1 + s_wsize ws spsi *)
(*   | SConj (sphi, spsi) -> 1 + (s_wsize ws sphi) + (s_wsize ws spsi) *)
(*   | SImplL vphi -> 1 + v_wsize ws vphi *)
(*   | SImplR spsi -> 1 + s_wsize ws spsi *)
(*   | SIffSS (sphi, spsi) -> 1 + (s_wsize ws sphi) + (s_wsize ws spsi) *)
(*   | SIffVV (vphi, vpsi) -> 1 + (v_wsize ws vphi) + (v_wsize ws vpsi) *)
(*   | SPrev sphi -> 1 + s_wsize ws sphi *)
(*   | SNext sphi -> 1 + s_wsize ws sphi *)
(*   | SOnce (_, sphi) -> 1 + s_wsize ws sphi *)
(*   | SHistorically (_, _, sphis) -> 1 + (sum (s_wsize ws) sphis) *)
(*   | SHistoricallyOutL _ -> 1 *)
(*   | SEventually (_, sphi) -> 1 + s_wsize ws sphi *)
(*   | SAlways (_, _, sphis) -> 1 + (sum (s_wsize ws) sphis) *)
(*   | SSince (spsi, sphis) -> 1 + (s_wsize ws spsi) + (sum (s_wsize ws) sphis) *)
(*   | SUntil (spsi, sphis) -> 1 + (s_wsize ws spsi) + (sum (s_wsize ws) sphis) *)
(* and v_wsize ws = function *)
(*   | VFF _ -> 1 *)
(*   | VAtom (_, s) -> (match Hashtbl.find_opt ws s with *)
(*                      | None -> 1 *)
(*                      | Some(w) -> w) *)
(*   | VNeg sphi -> 1 + s_wsize ws sphi *)
(*   | VDisj (vphi, vpsi) -> 1 + v_wsize ws vphi + v_wsize ws vpsi *)
(*   | VConjL vphi -> 1 + v_wsize ws vphi *)
(*   | VConjR vpsi -> 1 + v_wsize ws vpsi *)
(*   | VImpl (sphi, vpsi) -> 1 + (s_wsize ws sphi) + (v_wsize ws vpsi) *)
(*   | VIffSV (sphi, vpsi) -> 1 + (s_wsize ws sphi) + (v_wsize ws vpsi) *)
(*   | VIffVS (vphi, spsi) -> 1 + (v_wsize ws vphi) + (s_wsize ws spsi) *)
(*   | VPrev0 -> 1 *)
(*   | VPrevOutL _ -> 1 *)
(*   | VPrevOutR _ -> 1 *)
(*   | VPrev vphi -> 1 + v_wsize ws vphi *)
(*   | VNextOutL _ -> 1 *)
(*   | VNextOutR _ -> 1 *)
(*   | VNext vphi -> 1 + v_wsize ws vphi *)
(*   | VOnceOutL _ -> 1 *)
(*   | VOnce (_, _, vphis) -> 1 + (sum (v_wsize ws) vphis) *)
(*   | VHistorically (_, vphi) -> 1 + v_wsize ws vphi *)
(*   | VEventually (_, _, vphis) -> 1 + (sum (v_wsize ws) vphis) *)
(*   | VAlways (_, vphi) -> 1 + v_wsize ws vphi *)
(*   | VSince (_, vphi, vpsis) -> 1 + v_wsize ws vphi + (sum (v_wsize ws) vpsis) *)
(*   | VSinceInf (_, _, vphis) -> 1 + (sum (v_wsize ws) vphis) *)
(*   | VSinceOutL _ -> 1 *)
(*   | VUntil (_, vphi, vpsis) -> 1 + v_wsize ws vphi + (sum (v_wsize ws) vpsis) *)
(*   | VUntilInf (_, _, vpsis) -> 1 + (sum (v_wsize ws) vpsis) *)

(* let wsize ws = function *)
(*   | S sp -> s_wsize ws sp *)
(*   | V vp -> v_wsize ws vp *)

(* let wsize_le ws = mk_le (wsize ws) *)

(***********************************
 *                                 *
 * Measure: width                  *
 *                                 *
 ***********************************)
(* let rec s_high = function *)
(*   | STT i -> i *)
(*   | SAtom (i, _) -> i *)
(*   | SNeg vphi -> v_high vphi *)
(*   | SDisjL sphi -> s_high sphi *)
(*   | SDisjR spsi -> s_high spsi *)
(*   | SConj (sphi, spsi) -> max (s_high sphi) (s_high spsi) *)
(*   | SImplL vphi -> v_high vphi *)
(*   | SImplR spsi -> s_high spsi *)
(*   | SIffSS (sphi, spsi) -> max (s_high sphi) (s_high spsi) *)
(*   | SIffVV (vphi, vpsi) -> max (v_high vphi) (v_high vpsi) *)
(*   | SPrev sphi -> s_high sphi *)
(*   | SNext sphi -> s_high sphi *)
(*   | SOnce (_, sphi) -> s_high sphi *)
(*   | SHistorically (_, _, sphis) -> max_list (List.map s_high sphis) *)
(*   | SHistoricallyOutL i -> i *)
(*   | SEventually (_, sphi) -> s_high sphi *)
(*   | SAlways (_, _, sphis) -> max_list (List.map s_high sphis) *)
(*   | SSince (spsi, sphis) -> max (s_high spsi) (max_list (List.map s_high sphis)) *)
(*   | SUntil (spsi, sphis) -> max (s_high spsi) (max_list (List.map s_high sphis)) *)
(* and v_high p = match p with *)
(*   | VFF i -> i *)
(*   | VAtom (i, _) -> i *)
(*   | VNeg sphi -> s_high sphi *)
(*   | VDisj (vphi, vpsi) -> max (v_high vphi) (v_high vpsi) *)
(*   | VConjL vphi -> v_high vphi *)
(*   | VConjR vpsi -> v_high vpsi *)
(*   | VImpl (sphi, vpsi) -> max (s_high sphi) (v_high vpsi) *)
(*   | VIffSV (sphi, vpsi) -> max (s_high sphi) (v_high vpsi) *)
(*   | VIffVS (vphi, spsi) -> max (v_high vphi) (s_high spsi) *)
(*   | VPrev0 -> 0 *)
(*   | VPrevOutL i -> i *)
(*   | VPrevOutR i -> i *)
(*   | VPrev vphi -> max (v_at (VPrev vphi)) (v_high vphi) *)
(*   | VNextOutL i -> i *)
(*   | VNextOutR i -> i *)
(*   | VNext vphi -> max (v_at (VNext vphi)) (v_high vphi) *)
(*   (\* TODO: Check if we should consider i here *\) *)
(*   | VOnceOutL i -> i *)
(*   | VOnce (_, _, vphis) -> max_list (List.map v_high vphis) *)
(*   | VHistorically (_, vphi) -> v_high vphi *)
(*   | VEventually (_, _, vphis) -> max_list (List.map v_high vphis) *)
(*   | VAlways (_, vphi) -> v_high vphi *)
(*   | VSince (_, vphi, vpsis) -> max (v_high vphi) (max_list (List.map v_high vpsis)) *)
(*   | VSinceInf (_, _, vphis) -> max_list (List.map v_high vphis) *)
(*   | VSinceOutL i -> i *)
(*   | VUntil (_, vphi, vpsis) -> max (v_high vphi) (max_list (List.map v_high vpsis)) *)
(*   | VUntilInf (_, _, vpsis) -> max_list (List.map v_high vpsis) *)

(* let rec s_low = function *)
(*   | STT i -> i *)
(*   | SAtom (i, _) -> i *)
(*   | SNeg vphi -> v_low vphi *)
(*   | SDisjL sphi -> s_low sphi *)
(*   | SDisjR spsi -> s_low spsi *)
(*   | SConj (sphi, spsi) -> min (s_low sphi) (s_low spsi) *)
(*   | SImplL vphi -> v_low vphi *)
(*   | SImplR spsi -> s_low spsi *)
(*   | SIffSS (sphi, spsi) -> min (s_low sphi) (s_low spsi) *)
(*   | SIffVV (vphi, vpsi) -> min (v_low vphi) (v_low vpsi) *)
(*   | SPrev sphi -> s_low sphi *)
(*   | SNext sphi -> s_low sphi *)
(*   | SOnce (_, sphi) -> s_low sphi *)
(*   | SHistorically (_, _, sphis) -> min_list (List.map s_low sphis) *)
(*   | SHistoricallyOutL i -> i *)
(*   | SEventually (_, sphi) -> s_low sphi *)
(*   | SAlways (_, _, sphis) -> min_list (List.map s_low sphis) *)
(*   | SSince (spsi, sphis) -> min (s_low spsi) (min_list (List.map s_low sphis)) *)
(*   | SUntil (spsi, sphis) -> min (s_low spsi) (min_list (List.map s_low sphis)) *)
(* and v_low p = match p with *)
(*   | VFF i -> i *)
(*   | VAtom (i, _) -> i *)
(*   | VNeg sphi -> s_low sphi *)
(*   | VDisj (vphi, vpsi) -> min (v_low vphi) (v_low vpsi) *)
(*   | VConjL vphi -> v_low vphi *)
(*   | VConjR vpsi -> v_low vpsi *)
(*   | VImpl (sphi, vpsi) -> min (s_low sphi) (v_low vpsi) *)
(*   | VIffSV (sphi, vpsi) -> min (s_low sphi) (v_low vpsi) *)
(*   | VIffVS (vphi, spsi) -> min (v_low vphi) (s_low spsi) *)
(*   | VPrev0 -> 0 *)
(*   | VPrevOutL i -> i *)
(*   | VPrevOutR i -> i *)
(*   | VPrev vphi -> min (v_at (VPrev vphi)) (v_low vphi) *)
(*   | VNextOutL i -> i *)
(*   | VNextOutR i -> i *)
(*   | VNext vphi -> min (v_at (VNext vphi)) (v_low vphi) *)
(*   | VOnceOutL i -> i *)
(*   | VOnce (_, _, vphis) -> min_list (List.map v_low vphis) *)
(*   | VHistorically (_, vphi) -> v_low vphi *)
(*   | VEventually (_, _, vphis) -> min_list (List.map v_low vphis) *)
(*   | VAlways (_, vphi) -> v_low vphi *)
(*   (\* TODO: Check if we should consider i here *\) *)
(*   | VSince (_, vphi, vpsis) -> min (v_low vphi) (min_list (List.map v_low vpsis)) *)
(*   | VSinceInf (_, _, vphis) -> min_list (List.map v_low vphis) *)
(*   | VSinceOutL i -> i *)
(*   | VUntil (_, vphi, vpsis) -> min (v_low vphi) (min_list (List.map v_low vpsis)) *)
(*   | VUntilInf (_, _, vpsis) -> min_list (List.map v_low vpsis) *)

(* let high p = match p with *)
(*   | S s_p -> s_high s_p *)
(*   | V v_p -> v_high v_p *)

(* let low p = match p with *)
(*   | S s_p -> s_low s_p *)
(*   | V v_p -> v_low v_p *)

(* (\* let width p = high p - low p *\) *)

(* let high_le = mk_le high *)
(* let low_le = mk_le (fun p -> - low p) *)

(***********************************
 *                                 *
 * Measure: pred                   *
 *                                 *
 ***********************************)
(* let rec s_pred = function *)
(*   | STT _ -> 0 *)
(*   | SAtom (_, _) -> 1 *)
(*   | SNeg sphi -> v_pred sphi *)
(*   | SDisjL sphi -> s_pred sphi *)
(*   | SDisjR spsi -> s_pred spsi *)
(*   | SConj (sphi, spsi) -> s_pred sphi + s_pred spsi *)
(*   | SImplL vphi -> v_pred vphi *)
(*   | SImplR spsi -> s_pred spsi *)
(*   | SIffSS (sphi, spsi) -> s_pred sphi + s_pred spsi *)
(*   | SIffVV (vphi, vpsi) -> v_pred vphi + v_pred vpsi *)
(*   | SPrev sphi -> s_pred sphi *)
(*   | SNext sphi -> s_pred sphi *)
(*   | SOnce (_, sphi) -> s_pred sphi *)
(*   | SHistorically (_, _, sphis) -> sum s_pred sphis *)
(*   | SHistoricallyOutL _ -> 0 *)
(*   | SEventually (_, sphi) -> s_pred sphi *)
(*   | SAlways (_, _, sphis) -> sum s_pred sphis *)
(*   | SSince (spsi, sphis) -> s_pred spsi + sum s_pred sphis *)
(*   | SUntil (spsi, sphis) -> s_pred spsi + sum s_pred sphis *)
(* and v_pred = function *)
(*   | VFF _ -> 0 *)
(*   | VAtom (_, _) -> 1 *)
(*   | VNeg sphi -> s_pred sphi *)
(*   | VDisj (vphi, vpsi) -> v_pred vphi + v_pred vpsi *)
(*   | VConjL vphi -> v_pred vphi *)
(*   | VConjR vpsi -> v_pred vpsi *)
(*   | VImpl (sphi, vpsi) -> s_pred sphi + v_pred vpsi *)
(*   | VIffSV (sphi, vpsi) -> s_pred sphi + v_pred vpsi *)
(*   | VIffVS (vphi, spsi) -> v_pred vphi + s_pred spsi *)
(*   | VPrev0 -> 0 *)
(*   | VPrevOutL _ -> 0 *)
(*   | VPrevOutR _ -> 0 *)
(*   | VPrev vphi -> v_pred vphi *)
(*   | VNextOutL _ -> 0 *)
(*   | VNextOutR _ -> 0 *)
(*   | VNext vphi -> v_pred vphi *)
(*   | VOnceOutL _ -> 0 *)
(*   | VOnce (_, _, vphis) -> sum v_pred vphis *)
(*   | VHistorically (_, vphi) -> v_pred vphi *)
(*   | VEventually (_, _, vphis) -> sum v_pred vphis *)
(*   | VAlways (_, vphi) -> v_pred vphi *)
(*   | VSince (_, vphi, vpsis) -> v_pred vphi + sum v_pred vpsis *)
(*   | VSinceInf (_, _, vphis) -> sum v_pred vphis *)
(*   | VSinceOutL _ -> 0 *)
(*   | VUntil (_, vphi, vpsis) -> v_pred vphi + sum v_pred vpsis *)
(*   | VUntilInf (_, _, vpsis) -> sum v_pred vpsis *)

(* let predicates = function *)
(*   | S s_p -> s_pred s_p *)
(*   | V v_p -> v_pred v_p *)

(* let predicates_le = mk_le predicates *)

(* Printing functions *)
let rec s_to_string indent p =
  let indent' = "\t" ^ indent in
  match p.node with
  | STT i -> Printf.sprintf "%strue{%d}" indent i
  | SAtom (i, a) -> Printf.sprintf "%s%s{%d}" indent a i
  | SNeg vphi -> Printf.sprintf "%sSNeg{%d}\n%s" indent (s_at p) (v_to_string indent' vphi)
  | SDisjL sphi -> Printf.sprintf "%sSDisjL{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SDisjR spsi -> Printf.sprintf "%sSDisjR{%d}\n%s" indent (s_at p) (s_to_string indent' spsi)
  | SConj (sphi, spsi) -> Printf.sprintf "%sSConj{%d}\n%s\n%s" indent (s_at p) (s_to_string indent' sphi) (s_to_string indent' spsi)
  | SImplL vphi -> Printf.sprintf "%sSImplL{%d}\n%s" indent (s_at p) (v_to_string indent' vphi)
  | SImplR spsi -> Printf.sprintf "%sSImplR{%d}\n%s" indent (s_at p) (s_to_string indent' spsi)
  | SIffSS (sphi, spsi) -> Printf.sprintf "%sSIffSS{%d}\n%s\n%s" indent (s_at p) (s_to_string indent' sphi) (s_to_string indent' spsi)
  | SIffVV (vphi, vpsi) -> Printf.sprintf "%sSIffVV{%d}\n%s\n%s" indent (s_at p) (v_to_string indent' vphi) (v_to_string indent' vpsi)
  | SPrev sphi -> Printf.sprintf "%sSPrev{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SNext sphi -> Printf.sprintf "%sSNext{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SOnce (_, sphi) -> Printf.sprintf "%sSOnce{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SHistorically (_, _, sphis) -> Printf.sprintf "%sSHistorically{%d}\n%s" indent (s_at p) (hlist_to_string indent' s_to_string sphis)
  | SHistoricallyOutL i -> Printf.sprintf "%sSHistoricallyOutL{%d}" indent' i
  | SEventually (_, sphi) -> Printf.sprintf "%sSEventually{%d}\n%s" indent (s_at p) (s_to_string indent' sphi)
  | SAlways (_, _, sphis) -> Printf.sprintf "%sSAlways{%d}\n%s" indent (s_at p) (hlist_to_string indent' s_to_string sphis)
  | SSince (spsi, sphis) ->
      Printf.sprintf "%sSSince{%d}\n%s\n%s" indent (s_at p) (s_to_string indent' spsi) (hlist_to_string indent' s_to_string sphis)
  | SUntil (spsi, sphis) ->
      Printf.sprintf "%sSUntil{%d}\n%s\n%s" indent (s_at p) (hlist_to_string indent' s_to_string sphis) (s_to_string indent' spsi)
and v_to_string indent p =
  let indent' = "\t" ^ indent in
  match p.node with
  | VFF i -> Printf.sprintf "%sfalse{%d}" indent i
  | VAtom (i, a) -> Printf.sprintf "%s!%s{%d}" indent a i
  | VNeg sphi -> Printf.sprintf "%sVNeg{%d}\n%s" indent (v_at p) (s_to_string indent' sphi)
  | VDisj (vphi, vpsi) -> Printf.sprintf "%sVDisj{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vphi) (v_to_string indent' vpsi)
  | VConjL vphi -> Printf.sprintf "%sVConjL{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VConjR vpsi -> Printf.sprintf "%sVConjR{%d}\n%s" indent (v_at p) (v_to_string indent' vpsi)
  | VImpl (sphi, vpsi) -> Printf.sprintf "%sVImpl{%d}\n%s\n%s" indent (v_at p) (s_to_string indent' sphi) (v_to_string indent' vpsi)
  | VIffSV (sphi, vpsi) -> Printf.sprintf "%sVIffSV{%d}\n%s\n%s" indent (v_at p) (s_to_string indent' sphi) (v_to_string indent' vpsi)
  | VIffVS (vphi, spsi) -> Printf.sprintf "%sVIffVS{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vphi) (s_to_string indent' spsi)
  | VPrev0 -> Printf.sprintf "%sVPrev0{0}" indent'
  | VPrevOutL i -> Printf.sprintf "%sVPrevOutL{%d}" indent' i
  | VPrevOutR i -> Printf.sprintf "%sVPrevOutR{%d}" indent' i
  | VPrev vphi -> Printf.sprintf "%sVPrev{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VNextOutL i -> Printf.sprintf "%sVNextOutL{%d}" indent' i
  | VNextOutR i -> Printf.sprintf "%sVNextOutR{%d}" indent' i
  | VNext vphi -> Printf.sprintf "%sVNext{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VOnceOutL i -> Printf.sprintf "%sVOnceOutL{%d}" indent' i
  | VOnce (_, _, vphis) ->
     Printf.sprintf "%sVOnce{%d}\n%s" indent (v_at p) (hlist_to_string indent' v_to_string vphis)
  | VHistorically (_, vphi) -> Printf.sprintf "%sVHistorically{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VEventually (_, _, vphis) ->
     Printf.sprintf "%sVEventually{%d}\n%s" indent (v_at p) (hlist_to_string indent' v_to_string vphis)
  | VAlways (_, vphi) -> Printf.sprintf "%sVAlways{%d}\n%s" indent (v_at p) (v_to_string indent' vphi)
  | VSince (_, vphi, vpsis) ->
     Printf.sprintf "%sVSince{%d}\n%s\n%s" indent (v_at p) (v_to_string indent' vphi) (hlist_to_string indent' v_to_string vpsis)
  | VSinceInf (_, _, vphis) ->
     Printf.sprintf "%sVSinceInf{%d}\n%s" indent (v_at p) (hlist_to_string indent' v_to_string vphis)
  | VSinceOutL i -> Printf.sprintf "%sVSinceOutL{%d}" indent' i
  | VUntil (_, vphi, vpsis) ->
      Printf.sprintf "%sVUntil{%d}\n%s\n%s" indent (v_at p) (hlist_to_string indent' v_to_string vpsis) (v_to_string indent' vphi)
  | VUntilInf (_, _, vpsis) ->
     Printf.sprintf "%sVUntilInf{%d}\n%s" indent (v_at p) (hlist_to_string indent' v_to_string vpsis)

let expl_to_string = function
  | S p -> s_to_string "" p
  | V p -> v_to_string "" p
