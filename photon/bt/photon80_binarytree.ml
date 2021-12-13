(*
  photon80_binarytree.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let digest_size = 80
let rate = 20
let rate_p = 16
let d = 5
let s = 4
let round = 12
let word_filter = 1 lsl s - 1
let reduction_poly = 0x3

let _rc =
  [[1; 3; 7; 14; 13; 11; 6; 12;  9; 2; 5; 10];
   [0; 2; 6; 15; 12; 10; 7; 13;  8; 3; 4; 11];
   [2; 0; 4; 13; 14;  8; 5; 15; 10; 1; 6;  9];
   [7; 5; 1;  8; 11; 13; 0; 10; 15; 4; 3; 12];
   [5; 7; 3; 10;  9; 15; 2;  8; 13; 6; 1; 14]]

let _mix_col_matrix =
  [[ 1;  2;  9;  9;  2];
   [ 2;  5;  3;  8; 13];
   [13; 11; 10; 12;  1];
   [ 1; 15;  2;  3; 14];
   [14; 14;  8;  5; 12]]

let _sbox = [12; 5; 6; 11; 9; 0; 10; 13; 3; 14; 15; 8; 4; 7; 1; 2]

let rc_length = List.length (List.hd _rc)
let rc = Binarytree.tree_of_list (List.concat _rc)

let mix_col_matrix_length = List.length (List.hd _mix_col_matrix)
let mix_col_matrix = Binarytree.tree_of_list (List.concat _mix_col_matrix)

let sbox = Binarytree.tree_of_list _sbox

(* -------------------------------------------- *)

let rec get tree list_index =
  let index = match list_index with
      Binarytree.Rc (i, j) -> i * rc_length + j
    | Binarytree.Mix_col_matrix (i, j) -> i * mix_col_matrix_length + j
    | Binarytree.State (i, j) -> i * d + j
    | Binarytree.Linear i -> i in
  match tree with
      Binarytree.Leaf -> raise Not_found
    | Binarytree.Node ((i, x), left, right) ->
      if index = i then x
      else if index < i then get left list_index
      else get right list_index

let update tree list_index value =
  let index = match list_index with
      Binarytree.State (i, j) -> i * d + j
    | Binarytree.Linear i -> i
    | _ -> raise (Invalid_argument "update: list_index must be State or Linear") in
  let rec _update tree list_index value continue =
    match tree with
        Binarytree.Leaf -> raise Not_found
      | Binarytree.Node ((i, _), left, right) when index = i -> continue (Binarytree.Node ((index, value), left, right))
      | Binarytree.Node ((i, _) as node, left, right) when index < i -> _update left list_index value (fun n -> continue (Binarytree.Node (node, n, right)))
      | Binarytree.Node ((i, _) as node, left, right) -> _update right list_index value (fun n -> continue (Binarytree.Node (node, left, n))) in
  _update tree list_index value (fun x -> x)

(* -------------------------------------------- *)

let get_byte str bit_off_set = (get str (Binarytree.Linear (bit_off_set lsr 3)) lsr (4-(bit_off_set land 0x4))) land word_filter

let word_xor_byte state str bit_off_set word_off_set no_of_bits =
  let rec loop i state =
    if i < no_of_bits then
      loop (i + s) (
        let index = word_off_set + (i / s) in
        update state
          (Binarytree.State ((index / d), (index mod d)))
          (get state (Binarytree.State ((index / d), (index mod d))) lxor get_byte str (bit_off_set+i) lsl (s - min s (no_of_bits-i)))
      )
    else state in
  loop 0 state

let write_byte str value bit_off_set no_of_bits =
  let byte_index = bit_off_set lsr 3 in
  let bit_index = bit_off_set land 0x7 in
  let local_filter = (1 lsl no_of_bits) - 1 in
  let value = value land local_filter in
  if bit_index + no_of_bits <= 8 then
    let str = update str (Binarytree.Linear byte_index) (get str (Binarytree.Linear byte_index) land lnot (local_filter lsl (8 - bit_index - no_of_bits))) in
    update str (Binarytree.Linear byte_index) (get str (Binarytree.Linear byte_index) lor value lsl (8 - bit_index - no_of_bits))
  else
    let tmp = Int32.logor
      (Int32.logand (Int32.shift_left (Int32.of_int (get str (Binarytree.Linear byte_index))) 8) 0xFF00l)
      (Int32.logand (Int32.of_int (get str (Binarytree.Linear (byte_index+1)))) 0xFFl) in
    let tmp = Int32.logand tmp (Int32.lognot (Int32.shift_left (Int32.logand (Int32.of_int local_filter) 0xFFl) (16 - bit_index - no_of_bits))) in
    let tmp = Int32.logor tmp (Int32.shift_left (Int32.logand (Int32.of_int value) 0xFFl) (16 - bit_index - no_of_bits)) in
    let str = update str (Binarytree.Linear byte_index) (Option.get (Int32.unsigned_to_int (Int32.logand (Int32.shift_right tmp 8) 0xFFl))) in
    update str (Binarytree.Linear (byte_index + 1)) (Option.get (Int32.unsigned_to_int (Int32.logand tmp 0xFFl)))

let word_to_byte state str bit_off_set no_of_bits =
  let rec loop i str =
    if i < no_of_bits then
      loop (i + s)
        (write_byte str ((get state (Binarytree.State ((i/(s*d)), ((i/s) mod d) land word_filter))) lsr (s - min s (no_of_bits-1))) (bit_off_set+i) (min s (no_of_bits-i)))
    else str in
  loop 0 str

let add_key state round =
  let rec loop i state =
    if i < d then loop (i + 1) (update state (Binarytree.State (i, 0)) (get state (Binarytree.State (i, 0)) lxor get rc (Binarytree.Rc (i, round))))
    else state in
  loop 0 state

let sub_cell state =
  let rec loop i state =
    if i < d then loop (i + 1) (
      let rec loop j state =
        if j < d then loop (j + 1) (update state (Binarytree.State (i, j)) (get sbox (Binarytree.Linear (get state (Binarytree.State (i, j))))))
        else state in
      loop 0 state
    )
    else state in
  loop 0 state

let shift_row state =
  let tmp = Binarytree.tree_of_list (List.init d (fun _ -> 0)) in
  let rec loop i state =
    if i < d then loop (i + 1) (
      let rec loop j tmp =
        if j < d then loop (j + 1) (update tmp (Binarytree.Linear j) (get state (Binarytree.State (i, j))))
        else tmp in
      let tmp = loop 0 tmp in
      let rec loop j state =
        if j < d then loop (j + 1) (update state (Binarytree.State (i, j)) (get tmp (Binarytree.Linear ((j+i) mod d))))
        else state in
      loop 0 state
    )
    else state in
  loop 0 state

let field_mult a b =
  let x = a and ret = 0 in
  let rec loop i ret x =
    if i < s then
      loop (i + 1) (
        if (b lsr i) land 1 = 1 then ret lxor x
        else ret
      ) (
        if (x lsr (s-1)) land 1 = 1 then let x = x lsl 1 in x lxor reduction_poly
        else x lsl 1
      )
    else ret land word_filter in
  loop 0 ret x

let mix_column state =
  let tmp = Binarytree.tree_of_list (List.init d (fun _ -> 0)) in
  let rec loop j state =
    if j < d then loop (j + 1) (
      let rec loop i tmp =
        if i < d then loop (i + 1) (
          let rec loop k sum =
            if k < d then loop (k + 1) (sum lxor field_mult (get mix_col_matrix (Binarytree.Mix_col_matrix (i, k))) (get state (Binarytree.State (k, j))))
            else sum in
          let sum = loop 0 0 in
          update tmp (Binarytree.Linear i) sum
        )
        else tmp in
      let tmp = loop 0 tmp in
      let rec loop i state =
        if i < d then loop (i + 1) (update state (Binarytree.State (i, j)) (get tmp (Binarytree.Linear i)))
        else state in
      loop 0 state
    )
    else state in
  loop 0 state

let permutation state r =
  let rec loop i state =
    if i < r then
      loop (i + 1) (
        let state = add_key state i in
        let state = sub_cell state in
        let state = shift_row state in
        mix_column state
      )
    else state in
  loop 0 state

let compress_function state mess bit_off_set =
  let state = word_xor_byte state mess bit_off_set 0 rate in
  permutation state round

let squeeze state digest =
  let rec loop i state digest =
    if i + rate_p >= digest_size then word_to_byte state digest i (min rate_p (digest_size - 1))
    else
      loop (i + rate_p)
        (permutation state round)
        (word_to_byte state digest i (min rate_p (digest_size - 1))) in
  loop 0 state digest

let init state =
  let presets = Binarytree.tree_of_list [(digest_size lsr 2) land 0xFF; rate land 0xFF; rate_p land 0xFF] in
  word_xor_byte state presets 0 (d*d - 24 / s) 24

let hash digest mess bit_len =
  let state = init (Binarytree.tree_of_list (List.init (d * d) (fun _ -> 0))) in
  let padded = Binarytree.tree_of_list (List.init (int_of_float (ceil (float_of_int rate /. 8. +. 1.))) (fun _ -> 0)) in
  let rec absorbing mess_index state =
    if mess_index <= bit_len - rate then absorbing (mess_index + rate) (compress_function state mess mess_index)
    else (mess_index, state) in
  let (mess_index, state) = absorbing 0 state in
  let j = int_of_float (ceil (float_of_int (bit_len - mess_index) /. 8.)) in
  let rec loop i padded =
    if i < j then loop (i + 1) (Binarytree.add padded i (get mess (Binarytree.Linear ((mess_index/8)+i))))
    else padded in
  let padded = loop 0 padded in
  let padded = Binarytree.add padded j 0x80 in
  let state = compress_function state padded (mess_index land 0x7) in
  squeeze state digest
