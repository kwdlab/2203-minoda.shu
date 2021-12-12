(*
  main_photon.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let print_digest digest =
  Array.iter (fun x ->
    Printf.printf "%.2x" x
  ) digest

(* -------------------------------------------- *)

let time f =
  let start = Sys.time () in
  let _ = f () in
  let end_ = Sys.time () in
  end_ -. start

let message = "The PHOTON Lightweight Hash Functions Family"
let message =
  let ic = open_in "message.txt" in
  try
    let line = input_line ic in
    let _ = (flush stdout; close_in ic) in
    line
  with e ->
    close_in_noerr ic;
    raise e

(* -------------------------------------------- *)

type photon = P80 | P224 | P256

let photon = ref P80

let speclist = [
  ("-p80", Arg.Unit (fun () -> photon := P80), "photon 80");
  ("-p224", Arg.Unit (fun () -> photon := P224), "photon 224");
  ("-p256", Arg.Unit (fun () -> photon := P256), "photon 256");
]

let bit_len = String.length message * 8
let () =
  let _ = Arg.parse speclist (fun s -> ()) "Usage: main_quark [-p80] [-p224] [-p256]" in
  print_string "str_len = "; print_int (String.length message); print_string " bitlen = "; print_int bit_len; print_newline ();
  match !photon with
    | P80 ->
      let digest = Array.init (Photon80.digest_size / 8) (fun _ -> 0) in
      let time = time (fun () -> Photon80.hash digest (Array.init (String.length message) (fun i -> Char.code message.[i])) bit_len) in
      print_string "photon80 hash(message.txt) = "; print_digest digest; print_newline ();
      print_string "time = "; print_float time; print_newline (); print_newline ()
    | P224 ->
      let digest = Array.init (Photon224.digest_size / 8) (fun _ -> 0) in
      let time = time (fun () -> Photon224.hash digest (Array.init (String.length message) (fun i -> Char.code message.[i])) bit_len) in
      print_string "photon224 hash(message.txt) = "; print_digest digest; print_newline ();
      print_string "time = "; print_float time; print_newline (); print_newline ()
    | P256 ->
      let digest = Array.init (Photon256.digest_size / 8) (fun _ -> 0) in
      let time = time (fun () -> Photon256.hash digest (Array.init (String.length message) (fun i -> Char.code message.[i])) bit_len) in
      print_string "photon256 hash(message.txt) = "; print_digest digest; print_newline ();
      print_string "time = "; print_float time; print_newline (); print_newline ()
