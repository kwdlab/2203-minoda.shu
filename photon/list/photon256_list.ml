(*
  photon256_list.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let digest_size = 256
let rate = 32
let rate_p = 32
let d = 6
let s = 8
let round = 12
let word_filter = 1 lsl s - 1
let reduction_poly = 0x1B

let rc =
  [[1; 3; 7; 14; 13; 11; 6; 12; 9; 2; 5; 10];
   [0; 2; 6; 15; 12; 10; 7; 13; 8; 3; 4; 11];
   [2; 0; 4; 13; 14; 8; 5; 15; 10; 1; 6; 9];
   [6; 4; 0; 9; 10; 12; 1; 11; 14; 5; 2; 13];
   [7; 5; 1; 8; 11; 13; 0; 10; 15; 4; 3; 12];
   [5; 7; 3; 10; 9; 15; 2; 8; 13; 6; 1; 14]]

let mix_col_matrix =
  [[2; 3; 1; 2; 1; 4];
   [8; 14; 7; 9; 6; 17];
   [34; 59; 31; 37; 24; 66];
   [132; 228; 121; 155; 103; 11];
   [22; 153; 239; 111; 144; 75];
   [150; 203; 210; 121; 36; 167]]

let sbox =
  [99; 124; 119; 123; 242; 107; 111; 197; 48; 1; 103; 43; 254; 215; 171;
   118; 202; 130; 201; 125; 250; 89; 71; 240; 173; 212; 162; 175; 156; 164;
   114; 192; 183; 253; 147; 38; 54; 63; 247; 204; 52; 165; 229; 241; 113;
   216; 49; 21; 4; 199; 35; 195; 24; 150; 5; 154; 7; 18; 128; 226; 235; 39;
   178; 117; 9; 131; 44; 26; 27; 110; 90; 160; 82; 59; 214; 179; 41; 227;
   47; 132; 83; 209; 0; 237; 32; 252; 177; 91; 106; 203; 190; 57; 74; 76;
   88; 207; 208; 239; 170; 251; 67; 77; 51; 133; 69; 249; 2; 127; 80; 60;
   159; 168; 81; 163; 64; 143; 146; 157; 56; 245; 188; 182; 218; 33; 16;
   255; 243; 210; 205; 12; 19; 236; 95; 151; 68; 23; 196; 167; 126; 61; 100;
   93; 25; 115; 96; 129; 79; 220; 34; 42; 144; 136; 70; 238; 184; 20; 222;
   94; 11; 219; 224; 50; 58; 10; 73; 6; 36; 92; 194; 211; 172; 98; 145; 149;
   228; 121; 231; 200; 55; 109; 141; 213; 78; 169; 108; 86; 244; 234; 101;
   122; 174; 8; 186; 120; 37; 46; 28; 166; 180; 198; 232; 221; 116; 31; 75;
   189; 139; 138; 112; 62; 181; 102; 72; 3; 246; 14; 97; 53; 87; 185; 134;
   193; 29; 158; 225; 248; 152; 17; 105; 217; 142; 148; 155; 30; 135; 233;
   206; 85; 40; 223; 140; 161; 137; 13; 191; 230; 66; 104; 65; 153; 45; 15;
   176; 84; 187; 22]

(* -------------------------------------------- *)

let double_list_nth list i j = List.nth (List.nth list i) j

let list_inserting list index value =
  let rec loop i = function
      [] -> []
    | x :: xs ->
      if i = index then value :: xs
      else x :: loop (i + 1) xs in
  loop 0 list

let double_list_inserting list i j value =
  list_inserting list i (list_inserting (List.nth list i) j value)

(* -------------------------------------------- *)

let get_byte str bit_off_set =
  if bit_off_set land 0x7 = 0 then List.nth str (bit_off_set lsr 3)
  else (List.nth str (bit_off_set lsr 3) lsl 4) lor (List.nth str (bit_off_set lsr 3 + 1) lsr 4)

let word_xor_byte state str bit_off_set word_off_set no_of_bits =
  let rec loop i state =
    if i < no_of_bits then
      loop (i + s) (
        let index = word_off_set + (i / s) in
        double_list_inserting state
          (index / d)
          (index mod d)
          (double_list_nth state (index / d) (index mod d) lxor get_byte str (bit_off_set+i) lsl (s - min s (no_of_bits-i)))
      )
    else state in
  loop 0 state

let write_byte str value bit_off_set no_of_bits =
  let byte_index = bit_off_set lsr 3 in
  let bit_index = bit_off_set land 0x7 in
  let local_filter = (1 lsl no_of_bits) - 1 in
  let value = value land local_filter in
  if bit_index + no_of_bits <= 8 then
    let str = list_inserting str byte_index (List.nth str byte_index land lnot (local_filter lsl (8 - bit_index - no_of_bits))) in
    list_inserting str byte_index (List.nth str byte_index lor value lsl (8 - bit_index - no_of_bits))
  else
    let tmp = Int32.logor
      (Int32.logand (Int32.shift_left (Int32.of_int (List.nth str byte_index)) 8) 0xFF00l)
      (Int32.logand (Int32.of_int (List.nth str (byte_index+1))) 0xFFl) in
    let tmp = Int32.logand tmp (Int32.lognot (Int32.shift_left (Int32.logand (Int32.of_int local_filter) 0xFFl) (16 - bit_index - no_of_bits))) in
    let tmp = Int32.logor tmp (Int32.shift_left (Int32.logand (Int32.of_int value) 0xFFl) (16 - bit_index - no_of_bits)) in
    let str = list_inserting str byte_index (Option.get (Int32.unsigned_to_int (Int32.logand (Int32.shift_right tmp 8) 0xFFl))) in
    list_inserting str (byte_index + 1) (Option.get (Int32.unsigned_to_int (Int32.logand tmp 0xFFl)))

let word_to_byte state str bit_off_set no_of_bits =
  let rec loop i str =
    if i < no_of_bits then
      loop (i + s)
        (write_byte str ((double_list_nth state (i/(s*d)) ((i/s) mod d) land word_filter) lsr (s - min s (no_of_bits-1))) (bit_off_set+i) (min s (no_of_bits-i)))
    else str in
  loop 0 str

let add_key state round =
  let rec loop i state =
    if i < d then loop (i + 1) (double_list_inserting state i 0 (double_list_nth state i 0 lxor double_list_nth rc i round))
    else state in
  loop 0 state

let sub_cell state =
  let rec loop i state =
    if i < d then loop (i + 1) (
      let rec loop j state =
        if j < d then loop (j + 1) (double_list_inserting state i j (List.nth sbox (double_list_nth state i j)))
        else state in
      loop 0 state
    )
    else state in
  loop 0 state

let shift_row state =
  let tmp = List.init d (fun _ -> 0) in
  let rec loop i state =
    if i < d then loop (i + 1) (
      let rec loop j tmp =
        if j < d then loop (j + 1) (list_inserting tmp j (double_list_nth state i j))
        else tmp in
      let tmp = loop 0 tmp in
      let rec loop j state =
        if j < d then loop (j + 1) (double_list_inserting state i j (List.nth tmp ((j+i) mod d)))
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
  let tmp = List.init d (fun _ -> 0) in
  let rec loop j state =
    if j < d then loop (j + 1) (
      let rec loop i tmp =
        if i < d then loop (i + 1) (
          let rec loop k sum =
            if k < d then loop (k + 1) (sum lxor field_mult (double_list_nth mix_col_matrix i k) (double_list_nth state k j))
            else sum in
          let sum = loop 0 0 in
          list_inserting tmp i sum
        )
        else tmp in
      let tmp = loop 0 tmp in
      let rec loop i state =
        if i < d then loop (i + 1) (double_list_inserting state i j (List.nth tmp i))
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
  let presets = [(digest_size lsr 2) land 0xFF; rate land 0xFF; rate_p land 0xFF] in
  word_xor_byte state presets 0 (d*d - 24 / s) 24

let hash digest mess bit_len =
  let state = init (List.init d (fun _ -> List.init d (fun _ -> 0))) in
  let padded = List.init (int_of_float (ceil (float_of_int rate /. 8. +. 1.))) (fun _ -> 0) in
  let rec absorbing mess_index state =
    if mess_index <= bit_len - rate then absorbing (mess_index + rate) (compress_function state mess mess_index)
    else (mess_index, state) in
  let (mess_index, state) = absorbing 0 state in
  let j = int_of_float (ceil (float_of_int (bit_len - mess_index) /. 8.)) in
  let rec loop i padded =
    if i < j then loop (i + 1) (list_inserting padded i (List.nth mess ((mess_index/8)+i)))
    else padded in
  let padded = loop 0 padded in
  let padded = list_inserting padded j 0x80 in
  let state = compress_function state padded (mess_index land 0x7) in
  squeeze state digest
