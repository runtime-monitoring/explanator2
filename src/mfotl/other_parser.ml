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
open Stdio
open Etc

let string_of_token (t: Other_lexer.token) =
  match t with
  | AT -> "'@'"
  | LPA -> "'('"
  | RPA -> "')'"
  | COM -> "','"
  | SEP -> "';'"
  | STR s -> "\"" ^ String.escaped s ^ "\""
  | EOF -> "<EOF>"

module Parsebuf = struct

  type t = { lexbuf: Lexing.lexbuf
           ; mutable token: Other_lexer.token
           ; mutable pred_sig: Pred.Sig.t option
           ; mutable db: Db.t }

  let init lexbuf = { lexbuf = lexbuf
                    ; token = Other_lexer.token lexbuf
                    ; pred_sig = None
                    ; db = Db.db (-1) (-1) [] }

  let next pb = pb.token <- Other_lexer.token pb.lexbuf

  let arity pb = (snd (Option.value_exn pb.pred_sig)).arity

  let pred pb = fst (Option.value_exn pb.pred_sig)

  let ts pb = match pb.db with
    | t, _, _ -> t

  let tp pb = match pb.db with
    | _, t, _ -> t

  let evts pb = match pb.db with
    | _, _, es -> es

  let add_event evt pb = pb.db <- Db.add_event pb.db evt

  let clear pb = pb

end

module Sig = struct

  let token_equal (t1: Other_lexer.token) (t2: Other_lexer.token) =
    match t1, t2 with
    | AT, AT
      | LPA, LPA
      | RPA, RPA
      | COM, COM
      | SEP, SEP
      | EOF, EOF -> true
    | STR s1, STR s2 -> String.equal s1 s2
    | _ -> false

  let parse_string (pb: Parsebuf.t) =
    match pb.token with
    | STR s -> Parsebuf.next pb; s
    | t -> raise (Failure ("expected a string but found " ^ string_of_token t))

  let parse_int pb =
    let s = parse_string pb in
    try Int.of_string s
    with Failure _ -> raise (Failure ("expected an integer but found \"" ^ String.escaped s ^ "\""))

  let parse_ntconst (pb: Parsebuf.t) =
    let expect (pb: Parsebuf.t) t =
      if token_equal pb.token t then Parsebuf.next pb
      else raise (Failure ("expected " ^ string_of_token t ^ " but found " ^ string_of_token pb.token)) in
    let rec parse_ntconst_rec l =
      match pb.token with
      | COM -> Parsebuf.next pb;
               let s = parse_string pb in
               parse_ntconst_rec (s::l)
      | RPA -> Parsebuf.next pb; List.rev l
      | t -> raise (Failure ("expected ',' or ')' but found " ^ string_of_token t)) in
    expect pb LPA;
    match pb.token with
    | RPA -> Parsebuf.next pb; []
    | STR s -> Parsebuf.next pb; parse_ntconst_rec [s]
    | t -> raise (Failure ("expected a string or ')' but found " ^ string_of_token t))

  let convert_types sl =
    List.map sl (fun s -> match String.split s ':' with
                          | [] -> raise (Failure ("unable to parse the variable signature string " ^ s))
                          | name :: ttype :: [] -> (name, Domain.tt_of_string ttype)
                          | _ -> raise (Failure ("unable to parse the variable signature string " ^ s)))

  let rec parse_pred_sigs (pb: Parsebuf.t) =
    match pb.token with
    | EOF -> ()
    | STR s -> Parsebuf.next pb;
               Pred.Sig.add s (convert_types (parse_ntconst pb));
               parse_pred_sigs pb
    | t -> raise (Failure ("unexpected character: " ^ string_of_token t))

  let parse f =
    let inc = In_channel.create f in
    let lexbuf = Lexing.from_channel inc in
    let pb = Parsebuf.init lexbuf in
    let () = Lexing.set_filename lexbuf f in
    try parse_pred_sigs pb
    with Failure s -> failwith ("error while parsing signature\n " ^ s)


end

module Trace = struct

  let tp = ref (-1)
  let next_tp () = tp := !tp + 1; !tp

  let parse_inc lexbuf =
    let pb = Parsebuf.init lexbuf in
    let rec parse_init () =
      match pb.token with
      | AT -> Parsebuf.next pb; parse_ts ()
      | t -> raise (Failure ("expected '@' but found " ^ string_of_token t))
    and parse_ts () =
      match pb.token with
      | STR s -> let ts = try Some (Int.of_string s)
                          with _ -> None in
                 (match ts with
                  | Some ts -> Parsebuf.next pb;
                               pb.db <- Db.db ts (next_tp ()) [];
                               parse_db ()
                  | None -> raise (Failure ("expected a time-stamp but found " ^ s)))
      | t -> raise (Failure ("expected a time-stamp but found " ^ string_of_token t))
    and parse_db () =
      match pb.token with
      | STR s -> (match Hashtbl.find Pred.Sig.table s with
                  | Some props -> (pb.pred_sig <- Some(s, props);
                                   Parsebuf.next pb;
                                   (match pb.token with
                                    | LPA -> Parsebuf.next pb;
                                             parse_tuple ()
                                    | t -> raise (Failure ("expected '(' but found " ^ string_of_token t))))
                  | None -> raise (Failure ("predicate " ^ s ^ " was not specified")))
      | AT | EOF -> pb
      | t -> raise (Failure ("expected a predicate or '@' but found " ^ string_of_token t))
    and parse_tuple () =
      match pb.token with
      | RPA -> parse_tuple_cont (Queue.create ())
      | STR s -> Parsebuf.next pb;
                 parse_tuple_cont (Queue.of_list [s])
      | t -> raise (Failure ("expected a tuple or ')' but found " ^ string_of_token t))
    and parse_tuple_cont q =
      match pb.token with
      | RPA -> Parsebuf.next pb;
               (if Int.equal (Queue.length q) (Parsebuf.arity pb) then
                  let evt = Db.event (Parsebuf.pred pb) (Queue.to_list q) in
                  Parsebuf.add_event evt pb
                else raise (Failure (Printf.sprintf "expected a tuple of arity %d but found %d arguments"
                                       (Parsebuf.arity pb) (Queue.length q))));
               (match pb.token with
                | LPA -> Parsebuf.next pb; parse_tuple ()
                | _ -> parse_db ())
      | COM -> Parsebuf.next pb;
               (match pb.token with
                | STR s -> Parsebuf.next pb;
                           Queue.enqueue q s;
                           parse_tuple_cont q
                | t -> raise (Failure ("expected a tuple but found " ^ string_of_token t)))
      | t -> raise (Failure ("expected ',' or ')' but found " ^ string_of_token t)) in
    parse_init ()

  let parse inc =
    let lexbuf = Lexing.from_channel inc in
    parse_inc lexbuf

end
