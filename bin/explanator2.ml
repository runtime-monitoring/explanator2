(*******************************************************************)
(*     This is part of Explanator2, it is distributed under the    *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2021:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Src.Util
open Src.Expl
open Src.Mtl
open Src.Io
open Src.Mtl_parser
open Src.Mtl_lexer
open Src.Monitor
open Src.Checker.VerifiedExplanator2

module Explanator2 = struct

  exception UNEXPECTED_EXIT

  let check_ref = ref false
  let debug_ref = ref false
  let json_ref = ref false
  let mode_ref = ref ALL
  let out_mode_ref = ref PLAIN
  let measure_ref = ref ""
  let fmla_ref = ref None
  let log_ref = ref stdin
  let out_ref = ref stdout
  let vis_ref = ref false
  let log_str_ref = ref ""
  let weights_tbl = Hashtbl.create 10

  let usage () =
    Format.eprintf
      "Usage: ./explanator2.exe [ARGUMENTS]
       Example: ./explanator2.exe -check -O size -fmla ex.mtl -log ex.log
       Arguments:
       \t -check   - execute verified checker
       \t -mode
       \t\t all    - output both satisfaction and violation explanations (default)
       \t\t sat    - output only satisfaction explanations
       \t\t viol   - output only violation explanations
       \t -O (measure)
       \t\t size   - optimize proof size (default)
       \t\t none   - pick any proof
       \t -weights
       \t\t <file> - atom weights file
       \t -fmla
       \t\t <file> or <string> - formula to be explained
       \t -log
       \t\t <file> - log file (default: stdin)
       \t -out_mode
       \t\t plain  - plain output (default)
       \t\t debug  - plain verbose output
       \t\t json   - JSON output
       \t -out
       \t\t <file> - output file where the explanation is printed to (default: stdout)\n%!";
    exit 0

  let mode_error () =
    Format.eprintf "mode should be either \"sat\", \"viol\" or \"all\" (without quotes)\n%!";
    raise UNEXPECTED_EXIT

  let out_mode_error () =
    Format.eprintf "out_mode should be either \"plain\", \"json\" or \"debug\" (without quotes)\n%!";
    raise UNEXPECTED_EXIT

  let measure_error () =
    Format.eprintf "measure should be either \"size\" or \"none\" (without quotes)\n%!";
    raise UNEXPECTED_EXIT

  let process_args =
    let rec go = function
      | ("-check" :: args) ->
         check_ref := true;
         go args
      | ("-out_mode" :: out_mode :: args) ->
         out_mode_ref :=
           (match out_mode with
            | "plain" | "PLAIN" | "Plain" -> PLAIN
            | "json"  | "JSON"  | "Json" -> JSON
            | "debug" | "DEBUG" | "Debug" -> DEBUG
            | _ -> mode_error ());
         go args
      | ("-mode" :: mode :: args) ->
         mode_ref :=
           (match mode with
            | "all" | "ALL" | "All" -> ALL
            | "sat" | "SAT" | "Sat" -> SAT
            | "viol" | "VIOL" | "Viol" -> VIOL
            | _ -> mode_error ());
         go args
      | ("-O" :: measure :: args) ->
         measure_ref := measure;
         go args
      | ("-log" :: logfile :: args) ->
         log_ref := open_in logfile;
         go args
      | ("-fmla" :: fmlafile :: args) ->
         (try
            let in_ch = open_in fmlafile in
            fmla_ref := Some(Src.Mtl_parser.formula Src.Mtl_lexer.token (Lexing.from_channel in_ch));
            close_in in_ch
          with
            _ -> fmla_ref := Some(Src.Mtl_parser.formula Src.Mtl_lexer.token (Lexing.from_string fmlafile)));
         go args
      | ("-weights" :: wfile :: args) ->
         let in_ch = open_in wfile in
         let rec get_weights l =
           match input_line in_ch with
           | line -> (match parse_weight_line line with
                      | None -> l
                      | Some(aw) -> get_weights (aw :: l))
           | exception End_of_file -> close_in in_ch; List.rev l in
         let () = List.iter (fun (a, w) -> Hashtbl.add weights_tbl a w) (get_weights []) in
         (* List.iter (fun (atm, w) -> Printf.printf "%s = %d\n" atm w) !weights_ref; *)
         go args
      | ("-out" :: outfile :: args) ->
         out_ref := open_out outfile;
         go args
      | ("-vis" :: fmlafile :: args) ->
         (* Quick sanity check (visualization related) *)
         let in_ch = open_in fmlafile in
         fmla_ref := Some(Src.Mtl_parser.formula Src.Mtl_lexer.token (Lexing.from_channel in_ch));
         log_str_ref := "@0 q\n@1 p\n@2 r\n@3 q";
         measure_ref := "size";
         vis_ref := true;
         go args
      | [] -> ()
      | _ -> usage () in
    go

  let set_measure measure =
    let measure_le =
      match measure with
      | "size" | "SIZE" | "Size" -> (* if (Hashtbl.length weights_tbl) == 0 then *) size_le
                                    (* else wsize_le weights_tbl *)
      (* | "high" | "HIGH" | "High" -> high_le *)
      | "none" | "NONE" | "None" -> (fun _ _ -> true)
      | _ -> measure_error () in
    let is_opt =
      match measure with
      | "size" | "SIZE" | "Size" -> (* if (Hashtbl.length weights_tbl) == 0 then *)
         is_opt_atm (fun s -> nat_of_integer (Z.of_int 1))
                                    (* else *)
                                    (*   is_opt_atm (fun s -> match Hashtbl.find_opt weights_tbl s with *)
                                    (*                        | None -> nat_of_integer (Z.of_int 1) *)
                                    (*                        | Some(w) -> nat_of_integer (Z.of_int w)) *)
      (* | "high" | "HIGH" | "High" -> is_opt_minmaxreach *)
      | "none" | "NONE" | "None" -> (fun _ _ _ _ -> true)
      | _ -> measure_error () in
    (measure_le, is_opt)

  let _ =
    try
      process_args (List.tl (Array.to_list Sys.argv));
      let (measure_le, is_opt) = set_measure !measure_ref in
      let formula = Option.get !fmla_ref in
      if !vis_ref then
        let () = Printf.printf "%s" (json_table_columns formula) in
        let (_, out) = monitor_vis None !log_str_ref measure_le formula in
        Printf.printf "%s" out
      else
        let _ = monitor_cli !log_ref !out_ref !mode_ref !out_mode_ref !check_ref measure_le is_opt formula in ()
    with
    | End_of_file -> (if !out_mode_ref = PLAIN then
                        closing_stdout !out_ref);
                     close_out !out_ref; exit 0
    | UNEXPECTED_EXIT -> close_out !out_ref; exit 1

end
