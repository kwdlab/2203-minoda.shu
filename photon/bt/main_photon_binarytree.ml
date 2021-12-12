(*
  main_photon_binarytree.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let print_digest digest =
  let list = Binarytree.inorder digest in
  List.iter (fun (_, x) ->
    Printf.printf "%.2x" x
  ) list

(* -------------------------------------------- *)

let time f =
  let start = Sys.time () in
  let res = f () in
  let end_ = Sys.time () in
  (end_ -. start, res)

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
  let mess = Binarytree.tree_of_list (List.init (String.length message) (fun i -> Char.code message.[i])) in
  match !photon with
    | P80 ->
      let digest = Binarytree.tree_of_list (List.init (Photon80_binarytree.digest_size / 8) (fun _ -> 0)) in
      let (time, res) = time (fun () -> Photon80_binarytree.hash digest mess bit_len) in
      print_string "photon80_binarytree hash(message.txt) = "; print_digest res; print_newline ();
      print_string "time = "; print_float time; print_newline (); print_newline ()
    | P224 ->
      let digest = Binarytree.tree_of_list (List.init (Photon224_binarytree.digest_size / 8) (fun _ -> 0)) in
      let (time, res) = time (fun () -> Photon224_binarytree.hash digest mess bit_len) in
      print_string "photon224_binarytree hash(message.txt) = "; print_digest res; print_newline ();
      print_string "time = "; print_float time; print_newline (); print_newline ()
    | P256 ->
      let digest = Binarytree.tree_of_list (List.init (Photon256_binarytree.digest_size / 8) (fun _ -> 0)) in
      let (time, res) = time (fun () -> Photon256_binarytree.hash digest mess bit_len) in
      print_string "photon256_binarytree hash(message.txt) = "; print_digest res; print_newline ();
      print_string "time = "; print_float time; print_newline (); print_newline ()
