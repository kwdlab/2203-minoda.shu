(*
  photon80.ml

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

let rc =
  [|[|1; 3; 7; 14; 13; 11; 6; 12;  9; 2; 5; 10|];
    [|0; 2; 6; 15; 12; 10; 7; 13;  8; 3; 4; 11|];
    [|2; 0; 4; 13; 14;  8; 5; 15; 10; 1; 6;  9|];
    [|7; 5; 1;  8; 11; 13; 0; 10; 15; 4; 3; 12|];
    [|5; 7; 3; 10;  9; 15; 2;  8; 13; 6; 1; 14|]|]

let mix_col_matrix =
  [|[| 1;  2;  9;  9;  2|];
    [| 2;  5;  3;  8; 13|];
    [|13; 11; 10; 12;  1|];
    [| 1; 15;  2;  3; 14|];
    [|14; 14;  8;  5; 12|]|]

let sbox = [|12; 5; 6; 11; 9; 0; 10; 13; 3; 14; 15; 8; 4; 7; 1; 2|]

let get_byte str bit_off_set = (str.(bit_off_set lsr 3) lsr (4-(bit_off_set land 0x4))) land word_filter

let word_xor_byte state str bit_off_set word_off_set no_of_bits =
  let rec loop i () =
    if i < no_of_bits then
      loop (i + s) (
        let index = word_off_set + (i / s) in
        state.(index / d).(index mod d) <-
          state.(index / d).(index mod d)
          lxor get_byte str (bit_off_set+i) lsl (s - min s (no_of_bits-i))
      )
    else () in
  loop 0 ()

let write_byte str value bit_off_set no_of_bits =
  let byte_index = bit_off_set lsr 3 in
  let bit_index = bit_off_set land 0x7 in
  let local_filter = (1 lsl no_of_bits) - 1 in
  let value = value land local_filter in
  if bit_index + no_of_bits <= 8 then
    (
      str.(byte_index) <- str.(byte_index) land lnot (local_filter lsl (8 - bit_index - no_of_bits));
      str.(byte_index) <- str.(byte_index) lor value lsl (8 - bit_index - no_of_bits)
    )
  else
    (
      let tmp = Int32.logor
        (Int32.logand (Int32.shift_left (Int32.of_int str.(byte_index)) 8) 0xFF00l)
        (Int32.logand (Int32.of_int str.(byte_index+1)) 0xFFl) in
      let tmp = Int32.logand tmp (Int32.lognot (Int32.shift_left (Int32.logand (Int32.of_int local_filter) 0xFFl) (16 - bit_index - no_of_bits))) in
      let tmp = Int32.logor tmp (Int32.shift_left (Int32.logand (Int32.of_int value) 0xFFl) (16 - bit_index - no_of_bits)) in
      str.(byte_index) <- Option.get (Int32.unsigned_to_int (Int32.logand (Int32.shift_right tmp 8) 0xFFl));
      str.(byte_index + 1) <- Option.get (Int32.unsigned_to_int (Int32.logand tmp 0xFFl))
    )

let word_to_byte state str bit_off_set no_of_bits =
  let rec loop i () =
    if i < no_of_bits then
      loop (i + s)
        (write_byte str ((state.(i/(s*d)).((i/s) mod d) land word_filter) lsr (s - min s (no_of_bits-1))) (bit_off_set+i) (min s (no_of_bits-i)))
    else () in
  loop 0 ()

let add_key state round =
  let rec loop i () =
    if i < d then loop (i + 1) (state.(i).(0) <- state.(i).(0) lxor rc.(i).(round))
    else () in
  loop 0 ()

let sub_cell state =
  let rec loop i () =
    if i < d then loop (i + 1) (
      let rec loop j () =
        if j < d then loop (j + 1) (state.(i).(j) <- sbox.(state.(i).(j)))
        else () in
      loop 0 ()
    )
    else () in
  loop 0 ()

let shift_row state =
  let tmp = Array.init d (fun _ -> 0) in
  let rec loop i () =
    if i < d then loop (i + 1) (
      let rec loop j () =
        if j < d then loop (j + 1) (tmp.(j) <- state.(i).(j))
        else () in
      let _ = loop 0 () in
      let rec loop j () =
        if j < d then loop (j + 1) (state.(i).(j) <- tmp.((j+i) mod d))
        else () in
      loop 0 ()
    )
    else () in
  loop 0 ()

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
  let tmp = Array.init d (fun _ -> 0) in
  let rec loop j () =
    if j < d then loop (j + 1) (
      let rec loop i () =
        if i < d then loop (i + 1) (
          let rec loop k sum =
            if k < d then loop (k + 1) (sum lxor field_mult (mix_col_matrix.(i).(k)) (state.(k).(j)))
            else sum in
          let sum = loop 0 0 in
          tmp.(i) <- sum
        )
        else () in
      let _ = loop 0 () in
      let rec loop i () =
        if i < d then loop (i + 1) (state.(i).(j) <- tmp.(i))
        else () in
      loop 0 ()
    )
    else () in
  loop 0 ()

let permutation state r =
  let rec loop i () =
    if i < r then
      loop (i + 1) (
        let _ = add_key state i in
        let _ = sub_cell state in
        let _ = shift_row state in
        mix_column state
      )
    else () in
  loop 0 ()

let compress_function state mess bit_off_set =
  let _ = word_xor_byte state mess bit_off_set 0 rate in
  permutation state round

let squeeze state digest =
  let rec loop i () =
    if i + rate_p >= digest_size then word_to_byte state digest i (min rate_p (digest_size - 1))
    else
      loop (i + rate_p) (
        let _ = word_to_byte state digest i (min rate_p (digest_size - 1)) in
        permutation state round
      ) in
  loop 0 ()

let init state =
  let presets = [|(digest_size lsr 2) land 0xFF; rate land 0xFF; rate_p land 0xFF|] in
  word_xor_byte state presets 0 (d*d - 24 / s) 24

let hash digest mess bit_len =
  let state = Array.make_matrix d d 0 in
  let padded = Array.init (int_of_float (ceil (float_of_int rate /. 8. +. 1.))) (fun _ -> 0) in
  let _ = init state in
  let rec absorbing mess_index () =
    if mess_index <= bit_len - rate then absorbing (mess_index + rate) (compress_function state mess mess_index)
    else mess_index in
  let mess_index = absorbing 0 () in
  let j = int_of_float (ceil (float_of_int (bit_len - mess_index) /. 8.)) in
  let rec loop i () =
    if i < j then loop (i + 1) (padded.(i) <- mess.((mess_index/8)+i))
    else () in
  let _ = loop 0 () in
  let _ = padded.(j) <- 0x80 in
  let _ = compress_function state padded (mess_index land 0x7) in
  squeeze state digest
