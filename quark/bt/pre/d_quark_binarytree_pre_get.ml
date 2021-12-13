(*
  d_quark_binarytree_pre_get.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let capacity = 20
let rate = 2
let width = 22
let digest = width

let _iv = [0xcc;0x6c;0x4a;0xb7;0xd1;0x1f;0xa9;0xbd;
	   0xf6;0xee;0xde;0x03;0xd8;0x7b;0x68;0xf9;
	   0x1b;0xaa;0x70;0x6c;0x20;0xe9]
let iv = Binarytree.tree_of_list _iv

type hash_state = { pos: int; x: Binarytree.tree }

let permute state =
  let rounds = 4 * 176 in
  let n_len = 88 in
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
      let xs_i_5  = Binarytree.get xs (i+5 ) in
      let xs_i_11 = Binarytree.get xs (i+11) in
      let xs_i_18 = Binarytree.get xs (i+18) in
      let xs_i_19 = Binarytree.get xs (i+19) in
      let xs_i_27 = Binarytree.get xs (i+27) in
      let xs_i_35 = Binarytree.get xs (i+35) in
      let xs_i_36 = Binarytree.get xs (i+36) in
      let xs_i_40 = Binarytree.get xs (i+40) in
      let xs_i_42 = Binarytree.get xs (i+42) in
      let xs_i_47 = Binarytree.get xs (i+47) in
      let xs_i_48 = Binarytree.get xs (i+48) in
      let xs_i_57 = Binarytree.get xs (i+57) in
      let xs_i_58 = Binarytree.get xs (i+58) in
      let xs_i_64 = Binarytree.get xs (i+64) in
      let xs_i_67 = Binarytree.get xs (i+67) in
      let xs_i_68 = Binarytree.get xs (i+68) in
      let xs_i_71 = Binarytree.get xs (i+71) in
      let xs_i_72 = Binarytree.get xs (i+72) in
      let xs_i_79 = Binarytree.get xs (i+79) in

      let ys_i_2  = Binarytree.get ys (i+2 ) in
      let ys_i_4  = Binarytree.get ys (i+4 ) in
      let ys_i_9  = Binarytree.get ys (i+9 ) in
      let ys_i_12 = Binarytree.get ys (i+12) in
      let ys_i_19 = Binarytree.get ys (i+19) in
      let ys_i_20 = Binarytree.get ys (i+20) in
      let ys_i_24 = Binarytree.get ys (i+24) in
      let ys_i_25 = Binarytree.get ys (i+25) in
      let ys_i_38 = Binarytree.get ys (i+38) in
      let ys_i_44 = Binarytree.get ys (i+44) in
      let ys_i_47 = Binarytree.get ys (i+47) in
      let ys_i_54 = Binarytree.get ys (i+54) in
      let ys_i_55 = Binarytree.get ys (i+55) in
      let ys_i_61 = Binarytree.get ys (i+61) in
      let ys_i_63 = Binarytree.get ys (i+63) in
      let ys_i_67 = Binarytree.get ys (i+67) in
      let ys_i_69 = Binarytree.get ys (i+69) in
      let ys_i_78 = Binarytree.get ys (i+78) in
      let ys_i_79 = Binarytree.get ys (i+79) in

      let xs_i_n_len = xs_i lxor ys_i in
      let xs_i_n_len = xs_i_n_len lxor
        xs_i_11 lxor xs_i_18 lxor xs_i_27 lxor xs_i_36 lxor xs_i_42 lxor
        xs_i_47 lxor xs_i_58 lxor xs_i_67 lxor xs_i_71 lxor xs_i_64 lxor
        (xs_i_79 land xs_i_71) lxor
        (xs_i_47 land xs_i_42) lxor
        (xs_i_19 land xs_i_11) lxor
        (xs_i_71 land xs_i_67 land xs_i_58) lxor
        (xs_i_42 land xs_i_36 land xs_i_27) lxor
        (xs_i_79 land xs_i_58 land xs_i_36 land xs_i_11) lxor
        (xs_i_71 land xs_i_67 land xs_i_47 land xs_i_42) lxor
        (xs_i_79 land xs_i_71 land xs_i_27 land xs_i_19) lxor
        (xs_i_79 land xs_i_71 land xs_i_67 land xs_i_58 land xs_i_47) lxor
        (xs_i_42 land xs_i_36 land xs_i_27 land xs_i_19 land xs_i_11) lxor
        (xs_i_67 land xs_i_58 land xs_i_47 land xs_i_42 land xs_i_36 land xs_i_27) in

      let ys_i_n_len = ys_i in
      let ys_i_n_len = ys_i_n_len lxor
        ys_i_9 lxor ys_i_20 lxor ys_i_25 lxor ys_i_38 lxor ys_i_44 lxor
        ys_i_47 lxor ys_i_54 lxor ys_i_67 lxor ys_i_69 lxor  ys_i_63 lxor
        (ys_i_78 land ys_i_69) lxor
        (ys_i_47 land ys_i_44) lxor
        (ys_i_19 land ys_i_9) lxor
        (ys_i_69 land ys_i_67 land ys_i_54) lxor
        (ys_i_44 land ys_i_38 land ys_i_25) lxor
        (ys_i_78 land ys_i_54 land ys_i_38 land ys_i_9) lxor
        (ys_i_69 land ys_i_67 land ys_i_47 land ys_i_44) lxor
        (ys_i_78 land ys_i_69 land ys_i_25 land ys_i_19) lxor
        (ys_i_78 land ys_i_69 land ys_i_67 land ys_i_54 land ys_i_47) lxor
        (ys_i_44 land ys_i_38 land ys_i_25 land ys_i_19 land ys_i_9) lxor
        (ys_i_67 land ys_i_54 land ys_i_47 land ys_i_44 land ys_i_38 land ys_i_25) in

      let ls_i = Binarytree.get ls i in
      let ls_i_3 = Binarytree.get ls (i+3) in
      let ls = Binarytree.update_tree ls (l_len + i) (ls_i lxor ls_i_3) in

      let h = xs_i_35 lxor ys_i_79 lxor
        (ys_i_4 land xs_i_68) lxor
        (xs_i_57 land xs_i_68) lxor
        (xs_i_68 land ys_i_79) lxor
        (ys_i_4 land xs_i_35 land xs_i_57) lxor
        (ys_i_4 land xs_i_57 land xs_i_68) lxor
        (ys_i_4 land xs_i_57 land ys_i_79) lxor
        (xs_i_35 land xs_i_57 land ys_i_79 land ls_i) lxor
        (xs_i_35 land ls_i) in
      let h = h lxor
        xs_i_1 lxor ys_i_2 lxor xs_i_5 lxor ys_i_12 lxor
        xs_i_40 lxor ys_i_55 lxor xs_i_72 lxor ls_i in
      let h = h lxor
        ys_i_24 lxor xs_i_48 lxor ys_i_61 in

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
