(*
  s_quark_binarytree_pre_get.ml

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
      let xs_i = Binarytree.get xs i and ys_i = Binarytree.get ys i in

      let xs_i_1   = Binarytree.get xs (i+1  ) in
      let xs_i_7   = Binarytree.get xs (i+7  ) in
      let xs_i_16  = Binarytree.get xs (i+16 ) in
      let xs_i_26  = Binarytree.get xs (i+26 ) in
      let xs_i_28  = Binarytree.get xs (i+28 ) in
      let xs_i_39  = Binarytree.get xs (i+39 ) in
      let xs_i_47  = Binarytree.get xs (i+47 ) in
      let xs_i_52  = Binarytree.get xs (i+52 ) in
      let xs_i_58  = Binarytree.get xs (i+58 ) in
      let xs_i_61  = Binarytree.get xs (i+61 ) in
      let xs_i_69  = Binarytree.get xs (i+69 ) in
      let xs_i_72  = Binarytree.get xs (i+72 ) in
      let xs_i_84  = Binarytree.get xs (i+84 ) in
      let xs_i_90  = Binarytree.get xs (i+90 ) in
      let xs_i_94  = Binarytree.get xs (i+94 ) in
      let xs_i_97  = Binarytree.get xs (i+97 ) in
      let xs_i_100 = Binarytree.get xs (i+100) in
      let xs_i_103 = Binarytree.get xs (i+103) in
      let xs_i_105 = Binarytree.get xs (i+105) in
      let xs_i_111 = Binarytree.get xs (i+111) in

      let ys_i_3   = Binarytree.get ys (i+3  ) in
      let ys_i_8   = Binarytree.get ys (i+8  ) in
      let ys_i_13  = Binarytree.get ys (i+13 ) in
      let ys_i_18  = Binarytree.get ys (i+18 ) in
      let ys_i_28  = Binarytree.get ys (i+28 ) in
      let ys_i_30  = Binarytree.get ys (i+30 ) in
      let ys_i_34  = Binarytree.get ys (i+34 ) in
      let ys_i_37  = Binarytree.get ys (i+37 ) in
      let ys_i_56  = Binarytree.get ys (i+56 ) in
      let ys_i_65  = Binarytree.get ys (i+65 ) in
      let ys_i_69  = Binarytree.get ys (i+69 ) in
      let ys_i_71  = Binarytree.get ys (i+71 ) in
      let ys_i_79  = Binarytree.get ys (i+79 ) in
      let ys_i_80  = Binarytree.get ys (i+80 ) in
      let ys_i_91  = Binarytree.get ys (i+91 ) in
      let ys_i_92  = Binarytree.get ys (i+92 ) in
      let ys_i_96  = Binarytree.get ys (i+96 ) in
      let ys_i_101 = Binarytree.get ys (i+101) in
      let ys_i_109 = Binarytree.get ys (i+109) in
      let ys_i_111 = Binarytree.get ys (i+111) in

      let xs_i_n_len = xs_i lxor ys_i in
      let xs_i_n_len = xs_i_n_len lxor
        xs_i_16 lxor xs_i_26 lxor xs_i_39 lxor xs_i_52 lxor xs_i_61 lxor
        xs_i_69 lxor xs_i_84 lxor xs_i_97 lxor xs_i_103 lxor xs_i_94 lxor
        (xs_i_111 land xs_i_103) lxor
        (xs_i_69 land xs_i_61) lxor
        (xs_i_28 land xs_i_16) lxor
        (xs_i_103 land xs_i_97 land xs_i_84) lxor
        (xs_i_61 land xs_i_52 land xs_i_39) lxor
        (xs_i_111 land xs_i_84 land xs_i_52 land xs_i_16) lxor
        (xs_i_103 land xs_i_97 land xs_i_69 land xs_i_61) lxor
        (xs_i_111 land xs_i_103 land xs_i_39 land xs_i_28) lxor
        (xs_i_111 land xs_i_103 land xs_i_97 land xs_i_84 land xs_i_69) lxor
        (xs_i_61 land xs_i_52 land xs_i_39 land xs_i_28 land xs_i_16) lxor
        (xs_i_97 land xs_i_84 land xs_i_69 land xs_i_61 land xs_i_52 land xs_i_39) in

      let ys_i_n_len = ys_i in
      let ys_i_n_len = ys_i_n_len lxor
        ys_i_13 lxor ys_i_30 lxor ys_i_37 lxor ys_i_56 lxor ys_i_65 lxor
        ys_i_69 lxor ys_i_79 lxor ys_i_96 lxor ys_i_101 lxor ys_i_92 lxor
        (ys_i_109 land ys_i_101) lxor
        (ys_i_69 land ys_i_65) lxor
        (ys_i_28 land ys_i_13) lxor
        (ys_i_101 land ys_i_96 land ys_i_79) lxor
        (ys_i_65 land ys_i_56 land ys_i_37) lxor
        (ys_i_109 land ys_i_79 land ys_i_56 land ys_i_13) lxor
        (ys_i_101 land ys_i_96 land ys_i_69 land ys_i_65) lxor
        (ys_i_109 land ys_i_101 land ys_i_37 land ys_i_28) lxor
        (ys_i_109 land ys_i_101 land ys_i_96 land ys_i_79 land ys_i_69) lxor
        (ys_i_65 land ys_i_56 land ys_i_37 land ys_i_28 land ys_i_13) lxor
        (ys_i_96 land ys_i_79 land ys_i_69 land ys_i_65 land ys_i_56 land ys_i_37) in

      let ls_i = Binarytree.get ls i in
      let ls_i_3 = Binarytree.get ls (i+3) in
      let ls = Binarytree.update_tree ls (l_len + i) (ls_i lxor ls_i_3) in

      let h = xs_i_47 lxor ys_i_111 lxor
        (ys_i_8 land xs_i_100) lxor
        (xs_i_72 land xs_i_100) lxor
        (xs_i_100 land ys_i_111) lxor
        (ys_i_8 land xs_i_47 land xs_i_72) lxor
        (ys_i_8 land xs_i_72 land xs_i_100) lxor
        (ys_i_8 land xs_i_72 land ys_i_111) lxor
        (xs_i_47 land xs_i_72 land ys_i_111 land ls_i) lxor
        (xs_i_47 land ls_i) in
      let h = h lxor
        xs_i_1 lxor ys_i_3 lxor xs_i_7 lxor ys_i_18 lxor
        xs_i_58 lxor ys_i_80 lxor xs_i_105 lxor ls_i in
      let h = h lxor
        ys_i_34 lxor ys_i_71 lxor xs_i_90 lxor ys_i_91 in

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
