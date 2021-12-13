(*
  u_quark_binarytree.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let capacity = 16
let rate = 1
let width = 17
let digest = width

let _iv = [0xd8; 0xda; 0xca; 0x44; 0x41; 0x4a; 0x09; 0x97;
  0x19; 0xc8; 0x0a; 0xa3; 0xaf; 0x06; 0x56; 0x44; 0xdb]
let iv = Binarytree.tree_of_list _iv

(* -------------------------------------------- *)

type hash_state = { pos: int; x: Binarytree.tree }

let permute state =
  let rounds = 4 * 136 in
  let n_len = 68 in
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
        Binarytree.get xs (i+9) lxor Binarytree.get xs (i+14) lxor Binarytree.get xs (i+21) lxor Binarytree.get xs (i+28) lxor Binarytree.get xs (i+33) lxor
        Binarytree.get xs (i+37) lxor Binarytree.get xs (i+45) lxor Binarytree.get xs (i+52) lxor Binarytree.get xs (i+55) lxor Binarytree.get xs (i+50) lxor
        (Binarytree.get xs (i+59) land Binarytree.get xs (i+55)) lxor
        (Binarytree.get xs (i+37) land Binarytree.get xs (i+33)) lxor
        (Binarytree.get xs (i+15) land Binarytree.get xs (i+9)) lxor
        (Binarytree.get xs (i+55) land Binarytree.get xs (i+52) land Binarytree.get xs (i+45)) lxor
        (Binarytree.get xs (i+33) land Binarytree.get xs (i+28) land Binarytree.get xs (i+21)) lxor
        (Binarytree.get xs (i+59) land Binarytree.get xs (i+45) land Binarytree.get xs (i+28) land Binarytree.get xs (i+9)) lxor
        (Binarytree.get xs (i+55) land Binarytree.get xs (i+52) land Binarytree.get xs (i+37) land Binarytree.get xs (i+33)) lxor
        (Binarytree.get xs (i+59) land Binarytree.get xs (i+55) land Binarytree.get xs (i+21) land Binarytree.get xs (i+15)) lxor
        (Binarytree.get xs (i+59) land Binarytree.get xs (i+55) land Binarytree.get xs (i+52) land Binarytree.get xs (i+45) land Binarytree.get xs (i+37)) lxor
        (Binarytree.get xs (i+33) land Binarytree.get xs (i+28) land Binarytree.get xs (i+21) land Binarytree.get xs (i+15) land Binarytree.get xs (i+9)) lxor
        (Binarytree.get xs (i+52) land Binarytree.get xs (i+45) land Binarytree.get xs (i+37) land Binarytree.get xs (i+33) land Binarytree.get xs (i+28) land Binarytree.get xs (i+21))
      ) in

      let ys = Binarytree.update_tree ys (n_len + i) (Binarytree.get ys i) in
      let ys = Binarytree.update_tree ys (n_len + i) (Binarytree.get ys (n_len + i) lxor
        Binarytree.get ys (i+7) lxor Binarytree.get ys (i+16) lxor Binarytree.get ys (i+20) lxor Binarytree.get ys (i+30) lxor Binarytree.get ys (i+35) lxor
        Binarytree.get ys (i+37) lxor Binarytree.get ys (i+42) lxor Binarytree.get ys (i+51) lxor Binarytree.get ys (i+54) lxor Binarytree.get ys (i+49) lxor
        (Binarytree.get ys (i+58) land Binarytree.get ys (i+54)) lxor
        (Binarytree.get ys (i+37) land Binarytree.get ys (i+35)) lxor
        (Binarytree.get ys (i+15) land Binarytree.get ys (i+7)) lxor
        (Binarytree.get ys (i+54) land Binarytree.get ys (i+51) land Binarytree.get ys (i+42)) lxor
        (Binarytree.get ys (i+35) land Binarytree.get ys (i+30) land Binarytree.get ys (i+20)) lxor
        (Binarytree.get ys (i+58) land Binarytree.get ys (i+42) land Binarytree.get ys (i+30) land Binarytree.get ys (i+7)) lxor
        (Binarytree.get ys (i+54) land Binarytree.get ys (i+51) land Binarytree.get ys (i+37) land Binarytree.get ys (i+35)) lxor
        (Binarytree.get ys (i+58) land Binarytree.get ys (i+54) land Binarytree.get ys (i+20) land Binarytree.get ys (i+15)) lxor
        (Binarytree.get ys (i+58) land Binarytree.get ys (i+54) land Binarytree.get ys (i+51) land Binarytree.get ys (i+42) land Binarytree.get ys (i+37)) lxor
        (Binarytree.get ys (i+35) land Binarytree.get ys (i+30) land Binarytree.get ys (i+20) land Binarytree.get ys (i+15) land Binarytree.get ys (i+7)) lxor
        (Binarytree.get ys (i+51) land Binarytree.get ys (i+42) land Binarytree.get ys (i+37) land Binarytree.get ys (i+35) land Binarytree.get ys (i+30) land Binarytree.get ys (i+20))
      ) in

      let ls = Binarytree.update_tree ls (l_len + i) (Binarytree.get ls i) in
      let ls = Binarytree.update_tree ls (l_len + i) (Binarytree.get ls (l_len + i) lxor Binarytree.get ls (i+3)) in

      let h = Binarytree.get xs (i+25) lxor Binarytree.get ys (i+59) lxor
        (Binarytree.get ys (i+3) land Binarytree.get xs (i+55)) lxor
        (Binarytree.get xs (i+46) land Binarytree.get xs (i+55)) lxor
        (Binarytree.get xs (i+55) land Binarytree.get ys (i+59)) lxor
        (Binarytree.get ys (i+3) land Binarytree.get xs (i+25) land Binarytree.get xs (i+46)) lxor
        (Binarytree.get ys (i+3) land Binarytree.get xs (i+46) land Binarytree.get xs (i+55)) lxor
        (Binarytree.get ys (i+3) land Binarytree.get xs (i+46) land Binarytree.get ys (i+59)) lxor
        (Binarytree.get xs (i+25) land Binarytree.get xs (i+46) land Binarytree.get ys (i+59) land Binarytree.get ls i) lxor
        (Binarytree.get xs (i+25) land Binarytree.get ls i) in
      let h = h lxor
        Binarytree.get xs (i+1) lxor Binarytree.get ys (i+2) lxor Binarytree.get xs (i+4) lxor Binarytree.get ys (i+10) lxor
        Binarytree.get xs (i+31) lxor Binarytree.get ys (i+43) lxor Binarytree.get xs (i+56) lxor Binarytree.get ls i in

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
