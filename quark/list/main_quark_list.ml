(*
  main_quark_list.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let show_digest digest =
  List.iter (fun x ->
    Printf.printf "%.2x" x
  ) digest

(* -------------------------------------------- *)

let time f =
  let start = Sys.time () in
  let res = f () in
  let end_ = Sys.time () in
  (end_ -. start, res)

(* -------------------------------------------- *)

let message = "Quark: a lightweight hash"
let message =
  let ic = open_in "message.txt" in
  try
    let line = input_line ic in
    let _ = (flush stdout; close_in ic) in
    line
  with e ->
    close_in_noerr ic;
    raise e

let byte_len = String.length message

(* -------------------------------------------- *)

type quark = U | D | S

let quark = ref U

let speclist = [
  ("-u", Arg.Unit (fun () -> quark := U), "u quark");
  ("-d", Arg.Unit (fun () -> quark := D), "d quark");
  ("-s", Arg.Unit (fun () -> quark := S), "s quark");
]

let () =
  let _ = Arg.parse speclist (fun s -> ()) "Usage: main_quark [-u] [-d] [-s]" in
  print_string "str_len = "; print_int (String.length message); print_string " byte_len = "; print_int byte_len; print_newline ();
  let data = List.init (String.length message) (fun i -> Char.code message.[i]) in
  match !quark with
    | U ->
      let out = List.init U_quark_list.digest (fun _ -> 0) in
      let (time, res) = time (fun () -> U_quark_list.quark out data byte_len) in
      print_string "u-quark-list hash(message.txt) = "; show_digest res; print_newline ();
      print_string "time = "; print_float time; print_newline (); print_newline ()
    | D ->
      let out = List.init D_quark_list.digest (fun _ -> 0) in
      let (time, res) = time (fun () -> D_quark_list.quark out data byte_len) in
      print_string "d-quark-list hash(message.txt) = "; show_digest res; print_newline ();
      print_string "time = "; print_float time; print_newline (); print_newline ()
    | S ->
      let out = List.init S_quark_list.digest (fun _ -> 0) in
      let (time, res) = time (fun () -> S_quark_list.quark out data byte_len) in
      print_string "s-quark-list hash(message.txt) = "; show_digest res; print_newline ();
      print_string "time = "; print_float time; print_newline (); print_newline ()
