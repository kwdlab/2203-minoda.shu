(*
  main_quark.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let show_digest digest =
  Array.iter (fun x ->
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
  let data = Array.init (String.length message) (fun i -> Char.code message.[i]) in
  match !quark with
    | U ->
      let out = Array.init U_quark.digest (fun _ -> 0) in
      let (time, _) = time (fun () -> U_quark.quark out data byte_len) in
      print_string "u-quark hash(message.txt) = "; show_digest out; print_newline ();
      print_string "time = "; print_float time; print_newline (); print_newline ()
    | D ->
      let out = Array.init D_quark.digest (fun _ -> 0) in
      let (time, _) = time (fun () -> D_quark.quark out data byte_len) in
      print_string "d-quark hash(message.txt) = "; show_digest out; print_newline ();
      print_string "time = "; print_float time; print_newline (); print_newline ()
    | S ->
      let out = Array.init S_quark.digest (fun _ -> 0) in
      let (time, _) = time (fun () -> S_quark.quark out data byte_len) in
      print_string "s-quark hash(message.txt) = "; show_digest out; print_newline ();
      print_string "time = "; print_float time; print_newline (); print_newline ()
