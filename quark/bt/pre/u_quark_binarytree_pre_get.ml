(*
  u_quark_binarytree_pre_get.ml

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
      let xs_i = Binarytree.get xs i and ys_i = Binarytree.get ys i in

      let xs_i_1  = Binarytree.get xs (i+1 ) in
      let xs_i_4  = Binarytree.get xs (i+4 ) in
      let xs_i_9  = Binarytree.get xs (i+9 ) in
      let xs_i_14 = Binarytree.get xs (i+14) in
      let xs_i_15 = Binarytree.get xs (i+15) in
      let xs_i_21 = Binarytree.get xs (i+21) in
      let xs_i_25 = Binarytree.get xs (i+25) in
      let xs_i_28 = Binarytree.get xs (i+28) in
      let xs_i_31 = Binarytree.get xs (i+31) in
      let xs_i_33 = Binarytree.get xs (i+33) in
      let xs_i_37 = Binarytree.get xs (i+37) in
      let xs_i_45 = Binarytree.get xs (i+45) in
      let xs_i_46 = Binarytree.get xs (i+46) in
      let xs_i_50 = Binarytree.get xs (i+50) in
      let xs_i_52 = Binarytree.get xs (i+52) in
      let xs_i_55 = Binarytree.get xs (i+55) in
      let xs_i_56 = Binarytree.get xs (i+56) in
      let xs_i_59 = Binarytree.get xs (i+59) in

      let ys_i_2  = Binarytree.get ys (i+2 ) in
      let ys_i_3  = Binarytree.get ys (i+3 ) in
      let ys_i_7  = Binarytree.get ys (i+7 ) in
      let ys_i_10 = Binarytree.get ys (i+10) in
      let ys_i_15 = Binarytree.get ys (i+15) in
      let ys_i_16 = Binarytree.get ys (i+16) in
      let ys_i_20 = Binarytree.get ys (i+20) in
      let ys_i_30 = Binarytree.get ys (i+30) in
      let ys_i_35 = Binarytree.get ys (i+35) in
      let ys_i_37 = Binarytree.get ys (i+37) in
      let ys_i_42 = Binarytree.get ys (i+42) in
      let ys_i_43 = Binarytree.get ys (i+43) in
      let ys_i_49 = Binarytree.get ys (i+49) in
      let ys_i_51 = Binarytree.get ys (i+51) in
      let ys_i_54 = Binarytree.get ys (i+54) in
      let ys_i_58 = Binarytree.get ys (i+58) in
      let ys_i_59 = Binarytree.get ys (i+59) in

      let xs_i_n_len = xs_i lxor ys_i in
      let xs_i_n_len = xs_i_n_len lxor
        xs_i_9 lxor xs_i_14 lxor xs_i_21 lxor xs_i_28 lxor xs_i_33 lxor
        xs_i_37 lxor xs_i_45 lxor xs_i_52 lxor xs_i_55 lxor xs_i_50 lxor
        (xs_i_59 land xs_i_55) lxor
        (xs_i_37 land xs_i_33) lxor
        (xs_i_15 land xs_i_9) lxor
        (xs_i_55 land xs_i_52 land xs_i_45) lxor
        (xs_i_33 land xs_i_28 land xs_i_21) lxor
        (xs_i_59 land xs_i_45 land xs_i_28 land xs_i_9) lxor
        (xs_i_55 land xs_i_52 land xs_i_37 land xs_i_33) lxor
        (xs_i_59 land xs_i_55 land xs_i_21 land xs_i_15) lxor
        (xs_i_59 land xs_i_55 land xs_i_52 land xs_i_45 land xs_i_37) lxor
        (xs_i_33 land xs_i_28 land xs_i_21 land xs_i_15 land xs_i_9) lxor
        (xs_i_52 land xs_i_45 land xs_i_37 land xs_i_33 land xs_i_28 land xs_i_21) in

      let ys_i_n_len = ys_i in
      let ys_i_n_len = ys_i_n_len lxor
        ys_i_7 lxor ys_i_16 lxor ys_i_20 lxor ys_i_30 lxor ys_i_35 lxor
        ys_i_37 lxor ys_i_42 lxor ys_i_51 lxor ys_i_54 lxor ys_i_49 lxor
        (ys_i_58 land ys_i_54) lxor
        (ys_i_37 land ys_i_35) lxor
        (ys_i_15 land ys_i_7) lxor
        (ys_i_54 land ys_i_51 land ys_i_42) lxor
        (ys_i_35 land ys_i_30 land ys_i_20) lxor
        (ys_i_58 land ys_i_42 land ys_i_30 land ys_i_7) lxor
        (ys_i_54 land ys_i_51 land ys_i_37 land ys_i_35) lxor
        (ys_i_58 land ys_i_54 land ys_i_20 land ys_i_15) lxor
        (ys_i_58 land ys_i_54 land ys_i_51 land ys_i_42 land ys_i_37) lxor
        (ys_i_35 land ys_i_30 land ys_i_20 land ys_i_15 land ys_i_7) lxor
        (ys_i_51 land ys_i_42 land ys_i_37 land ys_i_35 land ys_i_30 land ys_i_20) in

      let ls_i = Binarytree.get ls i in
      let ls_i_3 = Binarytree.get ls (i+3) in
      let ls = Binarytree.update_tree ls (l_len + i) (ls_i lxor ls_i_3) in

      let h = xs_i_25 lxor ys_i_59 lxor
        (ys_i_3 land xs_i_55) lxor
        (xs_i_46 land xs_i_55) lxor
        (xs_i_55 land ys_i_59) lxor
        (ys_i_3 land xs_i_25 land xs_i_46) lxor
        (ys_i_3 land xs_i_46 land xs_i_55) lxor
        (ys_i_3 land xs_i_46 land ys_i_59) lxor
        (xs_i_25 land xs_i_46 land ys_i_59 land ls_i) lxor
        (xs_i_25 land ls_i) in
      let h = h lxor
        xs_i_1 lxor ys_i_2 lxor xs_i_4 lxor ys_i_10 lxor
        xs_i_31 lxor ys_i_43 lxor xs_i_56 lxor ls_i in

      let xs = Binarytree.update_tree xs (n_len + i) (xs_i_n_len lxor h) in
      let ys = Binarytree.update_tree ys (n_len + i) (ys_i_n_len lxor h) in

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
