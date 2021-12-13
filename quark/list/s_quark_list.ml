(*
  s_quark_list.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let capacity = 28
let rate = 4
let width = 32
let digest = width

type hash_state = { pos: int; x: int list }

let iv = [0x39;0x72;0x51;0xce;0xe1;0xde;0x8a;0xa7;
	   0x3e;0xa2;0x62;0x50;0xc6;0xd7;0xbe;0x12;
	   0x8c;0xd3;0xe7;0x9d;0xd7;0x18;0xc2;0x4b;
	   0x8a;0x19;0xd0;0x9c;0x24;0x92;0xda;0x5d]

(* -------------------------------------------- *)

let list_inserting list index value =
  let rec loop i = function
      [] -> []
    | x :: xs ->
      if i = index then value :: xs
      else x :: loop (i + 1) xs in
  loop 0 list

(* -------------------------------------------- *)

let permute state =
  let rounds = 4 * 256 in
  let n_len = 128 in
  let l_len = 10 in

  let (xs, ys) = List.split (List.init (n_len + rounds) (fun i ->
    if i < n_len then (List.nth state i, List.nth state (i + n_len))
    else (0, 0)
  )) in
  let ls = List.init (l_len + rounds) (fun i ->
    if i < l_len then 0xFFFFFFFF
    else 0
  ) in

  let rec round i xs ys ls =
    if i < rounds then
      let xs = list_inserting xs (n_len + i) (List.nth xs i lxor List.nth ys i) in
      let xs = list_inserting xs (n_len + i) (List.nth xs (n_len + i) lxor
        List.nth xs (i+16) lxor List.nth xs (i+26) lxor List.nth xs (i+39) lxor List.nth xs (i+52) lxor List.nth xs (i+61) lxor
        List.nth xs (i+69) lxor List.nth xs (i+84) lxor List.nth xs (i+97) lxor List.nth xs (i+103) lxor List.nth xs (i+94) lxor
        (List.nth xs (i+111) land List.nth xs (i+103)) lxor
        (List.nth xs (i+69) land List.nth xs (i+61)) lxor
        (List.nth xs (i+28) land List.nth xs (i+16)) lxor
        (List.nth xs (i+103) land List.nth xs (i+97) land List.nth xs (i+84)) lxor
        (List.nth xs (i+61) land List.nth xs (i+52) land List.nth xs (i+39)) lxor
        (List.nth xs (i+111) land List.nth xs (i+84) land List.nth xs (i+52) land List.nth xs (i+16)) lxor
        (List.nth xs (i+103) land List.nth xs (i+97) land List.nth xs (i+69) land List.nth xs (i+61)) lxor
        (List.nth xs (i+111) land List.nth xs (i+103) land List.nth xs (i+39) land List.nth xs (i+28)) lxor
        (List.nth xs (i+111) land List.nth xs (i+103) land List.nth xs (i+97) land List.nth xs (i+84) land List.nth xs (i+69)) lxor
        (List.nth xs (i+61) land List.nth xs (i+52) land List.nth xs (i+39) land List.nth xs (i+28) land List.nth xs (i+16)) lxor
        (List.nth xs (i+97) land List.nth xs (i+84) land List.nth xs (i+69) land List.nth xs (i+61) land List.nth xs (i+52) land List.nth xs (i+39))
      ) in

      let ys = list_inserting ys (n_len + i) (List.nth ys i) in
      let ys = list_inserting ys (n_len + i) (List.nth ys (n_len + i) lxor
        List.nth ys (i+13) lxor List.nth ys (i+30) lxor List.nth ys (i+37) lxor List.nth ys (i+56) lxor List.nth ys (i+65) lxor
        List.nth ys (i+69) lxor List.nth ys (i+79) lxor List.nth ys (i+96) lxor List.nth ys (i+101) lxor List.nth ys (i+92) lxor
        (List.nth ys (i+109) land List.nth ys (i+101)) lxor
        (List.nth ys (i+69) land List.nth ys (i+65)) lxor
        (List.nth ys (i+28) land List.nth ys (i+13)) lxor
        (List.nth ys (i+101) land List.nth ys (i+96) land List.nth ys (i+79)) lxor
        (List.nth ys (i+65) land List.nth ys (i+56) land List.nth ys (i+37)) lxor
        (List.nth ys (i+109) land List.nth ys (i+79) land List.nth ys (i+56) land List.nth ys (i+13)) lxor
        (List.nth ys (i+101) land List.nth ys (i+96) land List.nth ys (i+69) land List.nth ys (i+65)) lxor
        (List.nth ys (i+109) land List.nth ys (i+101) land List.nth ys (i+37) land List.nth ys (i+28)) lxor
        (List.nth ys (i+109) land List.nth ys (i+101) land List.nth ys (i+96) land List.nth ys (i+79) land List.nth ys (i+69)) lxor
        (List.nth ys (i+65) land List.nth ys (i+56) land List.nth ys (i+37) land List.nth ys (i+28) land List.nth ys (i+13)) lxor
        (List.nth ys (i+96) land List.nth ys (i+79) land List.nth ys (i+69) land List.nth ys (i+65) land List.nth ys (i+56) land List.nth ys (i+37))
      ) in

      let ls = list_inserting ls (l_len + i) (List.nth ls i) in
      let ls = list_inserting ls (l_len + i) (List.nth ls (l_len + i) lxor List.nth ls (i+3)) in

      let h = List.nth xs (i+47) lxor List.nth ys (i+111) lxor
        (List.nth ys (i+8) land List.nth xs (i+100)) lxor
        (List.nth xs (i+72) land List.nth xs (i+100)) lxor
        (List.nth xs (i+100) land List.nth ys (i+111)) lxor
        (List.nth ys (i+8) land List.nth xs (i+47) land List.nth xs (i+72)) lxor
        (List.nth ys (i+8) land List.nth xs (i+72) land List.nth xs (i+100)) lxor
        (List.nth ys (i+8) land List.nth xs (i+72) land List.nth ys (i+111)) lxor
        (List.nth xs (i+47) land List.nth xs (i+72) land List.nth ys (i+111) land List.nth ls i) lxor
        (List.nth xs (i+47) land List.nth ls i) in
      let h = h lxor
        List.nth xs (i+1) lxor List.nth ys (i+3) lxor List.nth xs (i+7) lxor List.nth ys (i+18) lxor
        List.nth xs (i+58) lxor List.nth ys (i+80) lxor List.nth xs (i+105) lxor List.nth ls i in
      let h = h lxor
        List.nth ys (i+34) lxor List.nth ys (i+71) lxor List.nth xs (i+90) lxor List.nth ys (i+91) in

      let xs = list_inserting xs (n_len + i) (List.nth xs (n_len + i) lxor h) in
      let ys = list_inserting ys (n_len + i) (List.nth ys (n_len + i) lxor h) in

      round (i + 1) xs ys ls

    else (xs, ys) in

  let (xs, ys) = round 0 xs ys ls in

  let rec update_state i state =
    if i < n_len then
      let state = list_inserting state i (List.nth xs (rounds + i)) in
      update_state (i + 1) (list_inserting state (i + n_len) (List.nth ys (rounds + i)))
    else state in
  update_state 0 state

let init hash_state =
  let rec init i hash_state =
    if i < 8*width then init (i + 1) {
      hash_state with x = list_inserting hash_state.x i ((List.nth iv (i/8) lsr (7 - (i mod 8))) land 1)
    }
    else {hash_state with pos = 0} in
  init 0 hash_state

let update hash_state data data_byte_len =
  let rec update_state i u hash_state =
    if i < 8*hash_state.pos + 8 then update_state (i + 1) u {
      hash_state with x = list_inserting hash_state.x (8*(width - rate) + i) (
        List.nth hash_state.x (8*(width - rate) + i) lxor ((u lsr (i mod 8)) land 1)
      )
    }
    else hash_state in
  let rec update hash_state data data_byte_len =
    if data_byte_len <= 0 then hash_state
    else match data with
        [] -> hash_state
      | u :: data ->
        let hash_state = update_state (8*hash_state.pos) u hash_state in
        let hash_state = {hash_state with pos = hash_state.pos + 1} in
        if hash_state.pos = rate then
          let hash_state = {hash_state with x = permute hash_state.x} in
          update {hash_state with pos = 0} data (data_byte_len-1)
        else update hash_state data (data_byte_len-1) in
  update hash_state data data_byte_len

let final hash_state =
  let hash_state = {hash_state with x = list_inserting hash_state.x (8*(width - rate) + hash_state.pos*8) (
    List.nth hash_state.x (8*(width - rate) + hash_state.pos*8) lxor 1
  )} in
  let hash_state = {hash_state with x = permute hash_state.x} in
  let out = List.init digest (fun _ -> 0) in
  let rec extract_one_byte i outbytes out hash_state =
    if i < 8 then
      let u = List.nth hash_state.x (8*(width - rate) + i + 8*(outbytes mod rate)) land 1 in
      let out = list_inserting out outbytes (List.nth out outbytes lxor (u lsl (7 - i))) in
      extract_one_byte (i + 1) outbytes out hash_state
    else out in
  let rec final outbytes hash_state out =
    if outbytes < digest then
      let out = extract_one_byte 0 outbytes out hash_state in
      let outbytes = outbytes + 1 in
      if outbytes = digest then out
      else
        if outbytes mod rate = 0 then
          let hash_state = {hash_state with x = permute hash_state.x} in
          final outbytes hash_state out
        else
          final outbytes hash_state out
    else out in
  final 0 hash_state out

let quark out in_data in_len =
  let hash_state = {pos = 0; x = List.init (width*8) (fun _ -> 0)} in
  let hash_state = init hash_state in
  let hash_state = update hash_state in_data in_len in
  final hash_state
