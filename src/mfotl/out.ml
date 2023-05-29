(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Stdio
open Etc
open Checker_interface

module Plain = struct

  type mode = UNVERIFIED | VERIFIED | DEBUG

  type t =
    | Explanation of (timestamp * timepoint) * Expl.t
    | ExplanationCheck of (timestamp * timepoint) * Expl.t * bool
    | ExplanationCheckDebug of (timestamp * timepoint) * Expl.t * bool * Checker_pdt.t * Checker_trace.t
    | Info of string

  let expl = function
    | Explanation ((ts, tp), e) ->
       Stdio.printf "%d:%d\nExplanation: \n%s\n\n" ts tp (Expl.to_string e)
    | ExplanationCheck ((ts, tp), e, b) ->
       Stdio.printf "%d:%d\nExplanation: \n%s\n" ts tp (Expl.to_string e);
       Stdio.printf "\nChecker output: %B\n\n" b;
    | ExplanationCheckDebug ((ts, tp), e, b, c_e, c_t) ->
       Stdio.printf "%d:%d\nExplanation: \n%s\n" ts tp (Expl.to_string e);
       Stdio.printf "\nChecker output: %B\n\n" b;
       Stdio.printf "\n[debug] Checker explanation:\n%s\n\n" (Checker_interface.Checker_pdt.to_string "" c_e);
       Stdio.printf "\n[debug] Checker trace:\n%s" (Checker_interface.Checker_trace.to_string c_t);
    | Info s -> Stdio.printf "\nInfo: %s\n\n" s

  let expls ts_tp_expls checker_es_opt = function
    | UNVERIFIED -> List.iter ts_tp_expls (fun ((ts, tp), e) -> expl (Explanation ((ts, tp), e)))
    | VERIFIED -> List.iter2_exn ts_tp_expls (Option.value_exn checker_es_opt)
                    (fun ((ts, tp), e) (b, _, _) -> expl (ExplanationCheck ((ts, tp), e, b)))
    | DEBUG -> List.iter2_exn ts_tp_expls (Option.value_exn checker_es_opt)
                 (fun ((ts, tp), e) (b, checker_e, trace) -> expl (ExplanationCheckDebug ((ts, tp), e, b, checker_e, trace)))

end

module Json = struct

  let error err =
    Printf.sprintf "ERROR: %s" (Error.to_string_hum err)

  let preamble outc f =
    Stdio.printf outc "{\n  \"columns\": %s\n}\n" (Etc.list_to_json (List.map (Formula.subfs_dfs f) Formula.to_string))

  let table_columns f =
    let preds_columns = List.map (Formula.preds f) Formula.to_string in
    let subfs_columns = List.map (Formula.subfs_dfs f) Formula.op_to_string in
    let subfs = List.map (Formula.subfs_dfs f) Formula.to_string in
    Printf.sprintf "{\n  \"apsColumns\": %s,\n  \"subfsColumns\": %s,\n  \"subformulas\": %s}\n"
      (list_to_json preds_columns) (list_to_json subfs_columns) (list_to_json subfs)

  (* let expls tpts f es = *)
  (*   let ident = "    " in *)
  (*   let ident2 = "    " ^ ident in *)
  (*   String.concat ~sep:",\n" (List.map es ~f:(fun e -> *)
  (*                                 let tp = (Expl.at e) in *)
  (*                                 let ts = Hashtbl.find_exn tpts tp in *)
  (*                                 Printf.sprintf "%s{\n" ident ^ *)
  (*                                   Printf.sprintf "%s\"ts\": %d,\n" ident2 ts ^ *)
  (*                                     Printf.sprintf "%s\"tp\": %d,\n" ident2 tp ^ *)
  (*                                       Printf.sprintf "%s\n" (expl_to_json f e) ^ *)
  (*                                         Printf.sprintf "%s}" ident)) *)

  (* let preds f preds tp ts = *)
  (*   let ident = "    " in *)
  (*   let ident2 = "    " ^ ident in *)
  (*   Printf.sprintf "%s{\n" ident ^ *)
  (*     Printf.sprintf "%s\"ts\": %d,\n" ident2 ts ^ *)
  (*       Printf.sprintf "%s\"tp\": %d,\n" ident2 tp ^ *)
  (*         Printf.sprintf "%s\n" (atoms_to_json f sap tp) ^ *)
  (*           Printf.sprintf "%s}" ident *)

end
