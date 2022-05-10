(*******************************************************************)
(*    This is part of Explanator2, it is distributed under the     *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Mtl
open Expl
open Util
open Interval
open Checker.Explanator2

module Deque = Core_kernel.Deque

type mbuf2 = expl Deque.t * expl Deque.t

module Since : sig
  type msaux = {
      ts_zero: timestamp option
    ; ts_tp_in: (timestamp * timepoint) Deque.t
    ; ts_tp_out: (timestamp * timepoint) Deque.t

    (* sorted deque of S^+ beta [alphas] *)
    ; beta_alphas: (timestamp * expl) Deque.t
    (* deque of S^+ beta [alphas] outside of the interval *)
    ; beta_alphas_out: (timestamp * expl) Deque.t

    (* sorted deque of S^- alpha [betas] *)
    ; alpha_betas: (timestamp * expl) Deque.t
    (* sorted deque of alpha proofs *)
    ; alphas_out: (timestamp * expl) Deque.t
    (* list of beta violations inside the interval *)
    ; betas_in: (timestamp * vexpl) Deque.t
    (* list of alpha/beta violations *)
    ; alphas_betas_out: (timestamp * vexpl option * vexpl option) Deque.t
    ; }
end

module Until : sig
  type muaux = {
      ts_tp_in: (timestamp * timepoint) Deque.t
    ; ts_tp_out: (timestamp * timepoint) Deque.t
    (* deque of sorted deques of U^+ beta [alphas] proofs where
     * ts corresponds to the timestamp of the beta proof *)
    ; alphas_beta: ((timestamp * expl) Deque.t) Deque.t
    (* most recent sequence of alpha satisfactions w/o holes *)
    ; alphas_suffix: (timestamp * sexpl) Deque.t
    (* deque of sorted deques of U^- ~alpha [~betas] proofs where
     * ts corresponds to the timestamp of the ~alpha proof *)
    ; betas_alpha: ((timestamp * expl) Deque.t) Deque.t
    (* sorted deque of alpha proofs outside the interval *)
    ; alphas_out: (timestamp * expl) Deque.t
    (* deque of alpha violations inside the interval *)
    ; alphas_in: (timestamp * expl) Deque.t
    (* deque of beta violations inside the interval *)
    ; betas_suffix_in: (timestamp * vexpl) Deque.t
    ; optimal_proofs: (timestamp * expl) Deque.t
    ; }
end

type mformula =
  | MTT
  | MFF
  | MP of string
  | MNeg of mformula
  | MConj of mformula * mformula * mbuf2
  | MDisj of mformula * mformula * mbuf2
  | MPrev of interval * mformula * bool * expl Deque.t * timestamp Deque.t
  | MNext of interval * mformula * bool * timestamp Deque.t
  | MSince of interval * mformula * mformula * mbuf2 * (timestamp * timepoint) Deque.t * Since.msaux
  | MUntil of interval * mformula * mformula * mbuf2 * (timestamp * timepoint) Deque.t * Until.muaux

type state =
  { tp: timepoint
  ; mf: mformula
  ; events: (Util.SS.t * timestamp) list
  ; tp_ts: (timepoint, timestamp) Hashtbl.t
  }

val monitor: in_channel -> out_channel -> mode -> out_mode -> bool -> (expl -> expl -> bool) ->
	         (string trace -> nat -> string mtl -> (string sproof, string vproof) sum -> bool) -> formula ->
             out_channel
val monitor2: (mformula * state) option -> string -> bool -> (expl -> expl -> bool) -> formula ->
              (mformula * state) option * string