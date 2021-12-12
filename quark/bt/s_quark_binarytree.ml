(*
  s_quark_binarytree.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let capacity = 28
let rate = 4
let width = 32
let digest = width

let _iv = [0x39;0x72;0x51;0xce;0xe1;0xde;0x8a;0xa7;
	   0x3e;0xa2;0x62;0x50;0xc6;0xd7;0xbe;0x12;
	   0x8c;0xd3;0xe7;0x9d;0xd7;0x18;0xc2;0x4b;
	   0x8a;0x19;0xd0;0x9c;0x24;0x92;0xda;0x5d]
let iv = Binarytree.tree_of_list _iv

(* -------------------------------------------- *)

type hash_state = { pos: int; x: Binarytree.tree }

let permute state =
  let rounds = 4 * 256 in
  let n_len = 128 in
  let l_len = 10 in

  let (xs, ys) = List.split (List.init (n_len + rounds) (fun i ->
    if i < n_len then (Binarytree.get state i, Binarytree.get state (i + n_len))
    else (0, 0)
  )) in
  let (xs, ys) = (Binarytree.tree_of_list xs, Binarytree.tree_of_list ys) in
  let ls = Binarytree.tree_of_list (List.init (l_len + rounds) (fun i ->
    if i < l_len then 0xFFFFFFFF
    else 0
  )) in

  let rec round i xs ys ls =
    if i < rounds then
      let xs = Binarytree.update_tree xs (n_len + i) (Binarytree.get xs i lxor Binarytree.get ys i) in
      let xs = Binarytree.update_tree xs (n_len + i) (Binarytree.get xs (n_len + i) lxor
        Binarytree.get xs (i+16) lxor Binarytree.get xs (i+26) lxor Binarytree.get xs (i+39) lxor Binarytree.get xs (i+52) lxor Binarytree.get xs (i+61) lxor
        Binarytree.get xs (i+69) lxor Binarytree.get xs (i+84) lxor Binarytree.get xs (i+97) lxor Binarytree.get xs (i+103) lxor Binarytree.get xs (i+94) lxor
        (Binarytree.get xs (i+111) land Binarytree.get xs (i+103)) lxor
        (Binarytree.get xs (i+69) land Binarytree.get xs (i+61)) lxor
        (Binarytree.get xs (i+28) land Binarytree.get xs (i+16)) lxor
        (Binarytree.get xs (i+103) land Binarytree.get xs (i+97) land Binarytree.get xs (i+84)) lxor
        (Binarytree.get xs (i+61) land Binarytree.get xs (i+52) land Binarytree.get xs (i+39)) lxor
        (Binarytree.get xs (i+111) land Binarytree.get xs (i+84) land Binarytree.get xs (i+52) land Binarytree.get xs (i+16)) lxor
        (Binarytree.get xs (i+103) land Binarytree.get xs (i+97) land Binarytree.get xs (i+69) land Binarytree.get xs (i+61)) lxor
        (Binarytree.get xs (i+111) land Binarytree.get xs (i+103) land Binarytree.get xs (i+39) land Binarytree.get xs (i+28)) lxor
        (Binarytree.get xs (i+111) land Binarytree.get xs (i+103) land Binarytree.get xs (i+97) land Binarytree.get xs (i+84) land Binarytree.get xs (i+69)) lxor
        (Binarytree.get xs (i+61) land Binarytree.get xs (i+52) land Binarytree.get xs (i+39) land Binarytree.get xs (i+28) land Binarytree.get xs (i+16)) lxor
        (Binarytree.get xs (i+97) land Binarytree.get xs (i+84) land Binarytree.get xs (i+69) land Binarytree.get xs (i+61) land Binarytree.get xs (i+52) land Binarytree.get xs (i+39))
      ) in

      let ys = Binarytree.update_tree ys (n_len + i) (Binarytree.get ys i) in
      let ys = Binarytree.update_tree ys (n_len + i) (Binarytree.get ys (n_len + i) lxor
        Binarytree.get ys (i+13) lxor Binarytree.get ys (i+30) lxor Binarytree.get ys (i+37) lxor Binarytree.get ys (i+56) lxor Binarytree.get ys (i+65) lxor
        Binarytree.get ys (i+69) lxor Binarytree.get ys (i+79) lxor Binarytree.get ys (i+96) lxor Binarytree.get ys (i+101) lxor Binarytree.get ys (i+92) lxor
        (Binarytree.get ys (i+109) land Binarytree.get ys (i+101)) lxor
        (Binarytree.get ys (i+69) land Binarytree.get ys (i+65)) lxor
        (Binarytree.get ys (i+28) land Binarytree.get ys (i+13)) lxor
        (Binarytree.get ys (i+101) land Binarytree.get ys (i+96) land Binarytree.get ys (i+79)) lxor
        (Binarytree.get ys (i+65) land Binarytree.get ys (i+56) land Binarytree.get ys (i+37)) lxor
        (Binarytree.get ys (i+109) land Binarytree.get ys (i+79) land Binarytree.get ys (i+56) land Binarytree.get ys (i+13)) lxor
        (Binarytree.get ys (i+101) land Binarytree.get ys (i+96) land Binarytree.get ys (i+69) land Binarytree.get ys (i+65)) lxor
        (Binarytree.get ys (i+109) land Binarytree.get ys (i+101) land Binarytree.get ys (i+37) land Binarytree.get ys (i+28)) lxor
        (Binarytree.get ys (i+109) land Binarytree.get ys (i+101) land Binarytree.get ys (i+96) land Binarytree.get ys (i+79) land Binarytree.get ys (i+69)) lxor
        (Binarytree.get ys (i+65) land Binarytree.get ys (i+56) land Binarytree.get ys (i+37) land Binarytree.get ys (i+28) land Binarytree.get ys (i+13)) lxor
        (Binarytree.get ys (i+96) land Binarytree.get ys (i+79) land Binarytree.get ys (i+69) land Binarytree.get ys (i+65) land Binarytree.get ys (i+56) land Binarytree.get ys (i+37))
      ) in

      let ls = Binarytree.update_tree ls (l_len + i) (Binarytree.get ls i) in
      let ls = Binarytree.update_tree ls (l_len + i) (Binarytree.get ls (l_len + i) lxor Binarytree.get ls (i+3)) in

      let h = Binarytree.get xs (i+47) lxor Binarytree.get ys (i+111) lxor
        (Binarytree.get ys (i+8) land Binarytree.get xs (i+100)) lxor
        (Binarytree.get xs (i+72) land Binarytree.get xs (i+100)) lxor
        (Binarytree.get xs (i+100) land Binarytree.get ys (i+111)) lxor
        (Binarytree.get ys (i+8) land Binarytree.get xs (i+47) land Binarytree.get xs (i+72)) lxor
        (Binarytree.get ys (i+8) land Binarytree.get xs (i+72) land Binarytree.get xs (i+100)) lxor
        (Binarytree.get ys (i+8) land Binarytree.get xs (i+72) land Binarytree.get ys (i+111)) lxor
        (Binarytree.get xs (i+47) land Binarytree.get xs (i+72) land Binarytree.get ys (i+111) land Binarytree.get ls i) lxor
        (Binarytree.get xs (i+47) land Binarytree.get ls i) in
      let h = h lxor
        Binarytree.get xs (i+1) lxor Binarytree.get ys (i+3) lxor Binarytree.get xs (i+7) lxor Binarytree.get ys (i+18) lxor
        Binarytree.get xs (i+58) lxor Binarytree.get ys (i+80) lxor Binarytree.get xs (i+105) lxor Binarytree.get ls i in
      let h = h lxor
        Binarytree.get ys (i+34) lxor Binarytree.get ys (i+71) lxor Binarytree.get xs (i+90) lxor Binarytree.get ys (i+91) in

      let xs = Binarytree.update_tree xs (n_len + i) (Binarytree.get xs (n_len + i) lxor h) in
      let ys = Binarytree.update_tree ys (n_len + i) (Binarytree.get ys (n_len + i) lxor h) in

      round (i + 1) xs ys ls

    else (xs, ys) in

  let (xs, ys) = round 0 xs ys ls in

  let rec update_state i state =
    if i < n_len then
      let state = Binarytree.update_tree state i (Binarytree.get xs (rounds + i)) in
      update_state (i + 1) (Binarytree.update_tree state (i + n_len) (Binarytree.get ys (rounds + i)))
    else state in
  update_state 0 state

let init hash_state =
  let rec init i hash_state =
    if i < 8*width then init (i + 1) {
      hash_state with x = Binarytree.update_tree hash_state.x i ((Binarytree.get iv (i/8) lsr (7 - (i mod 8))) land 1)
    }
    else {hash_state with pos = 0} in
  init 0 hash_state

let update hash_state data data_byte_len =
  let rec update_state i u hash_state =
    if i < 8*hash_state.pos + 8 then update_state (i + 1) u {
      hash_state with x = Binarytree.update_tree hash_state.x (8*(width - rate) + i) (
        Binarytree.get hash_state.x (8*(width - rate) + i) lxor ((u lsr (i mod 8)) land 1)
      )
    }
    else hash_state in
  let rec update i hash_state data data_byte_len =
    if data_byte_len <= 0 then hash_state
    else
        let u = Binarytree.get data i in
        let hash_state = update_state (8*hash_state.pos) u hash_state in
        let hash_state = {hash_state with pos = hash_state.pos + 1} in
        if hash_state.pos = rate then
          let hash_state = {hash_state with x = permute hash_state.x} in
          update (i + 1) {hash_state with pos = 0} data (data_byte_len-1)
        else update (i + 1) hash_state data (data_byte_len-1) in
  update 0 hash_state data data_byte_len

let final hash_state =
  let hash_state = {hash_state with x = Binarytree.update_tree hash_state.x (8*(width - rate) + hash_state.pos*8) (
    Binarytree.get hash_state.x (8*(width - rate) + hash_state.pos*8) lxor 1
  )} in
  let hash_state = {hash_state with x = permute hash_state.x} in
  let out = Binarytree.tree_of_list (List.init digest (fun _ -> 0)) in
  let rec extract_one_byte i outbytes out hash_state =
    if i < 8 then
      let u = Binarytree.get hash_state.x (8*(width - rate) + i + 8*(outbytes mod rate)) land 1 in
      let out = Binarytree.update_tree out outbytes (Binarytree.get out outbytes lxor (u lsl (7 - i))) in
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
  let hash_state = {pos = 0; x = Binarytree.tree_of_list (List.init (width*8) (fun _ -> 0))} in
  let hash_state = init hash_state in
  let hash_state = update hash_state in_data in_len in
  final hash_state
