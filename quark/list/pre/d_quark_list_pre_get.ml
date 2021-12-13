(*
  d_quark_list_pre_get.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let capacity = 20
let rate = 2
let width = 22
let digest = width

type hash_state = { pos: int; x: int list }

let iv = [0xcc;0x6c;0x4a;0xb7;0xd1;0x1f;0xa9;0xbd;
	   0xf6;0xee;0xde;0x03;0xd8;0x7b;0x68;0xf9;
	   0x1b;0xaa;0x70;0x6c;0x20;0xe9]

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
  let rounds = 4 * 176 in
  let n_len = 88 in
  let l_len = 10 in

  let (xs, ys) = List.split (List.init (n_len + rounds) (fun i ->
    if i < n_len then (List.nth state i, List.nth state (i + n_len))
    else (0, 0)
  )) in
  let ls = List.init (l_len + rounds) (fun i ->
    if i < l_len then 0xFFFFFFFF
    else 0
  ) in

  let get_list_value index list =
    let rec get_list_value i index = function
        [] -> (0, [])
      | item :: list ->
        if i = index then (item, list)
        else
          get_list_value (i + 1) index list in
    get_list_value 0 index list in

  let rec round i xs ys ls =
    if i < rounds then
      let (xs_i, _xs) = get_list_value i xs and (ys_i, _ys) = get_list_value i ys in

      let (xs_i_1 , _xs) = get_list_value 0 _xs in
      let (xs_i_5 , _xs) = get_list_value 3 _xs in
      let (xs_i_11, _xs) = get_list_value 5 _xs in
      let (xs_i_18, _xs) = get_list_value 6 _xs in
      let (xs_i_19, _xs) = get_list_value 0 _xs in
      let (xs_i_27, _xs) = get_list_value 7 _xs in
      let (xs_i_35, _xs) = get_list_value 7 _xs in
      let (xs_i_36, _xs) = get_list_value 0 _xs in
      let (xs_i_40, _xs) = get_list_value 3 _xs in
      let (xs_i_42, _xs) = get_list_value 1 _xs in
      let (xs_i_47, _xs) = get_list_value 4 _xs in
      let (xs_i_48, _xs) = get_list_value 0 _xs in
      let (xs_i_57, _xs) = get_list_value 8 _xs in
      let (xs_i_58, _xs) = get_list_value 0 _xs in
      let (xs_i_64, _xs) = get_list_value 5 _xs in
      let (xs_i_67, _xs) = get_list_value 2 _xs in
      let (xs_i_68, _xs) = get_list_value 0 _xs in
      let (xs_i_71, _xs) = get_list_value 2 _xs in
      let (xs_i_72, _xs) = get_list_value 0 _xs in
      let (xs_i_79, _) = get_list_value 6 _xs in

      let (ys_i_2 , _ys) = get_list_value 1  _ys in
      let (ys_i_4 , _ys) = get_list_value 1  _ys in
      let (ys_i_9 , _ys) = get_list_value 4  _ys in
      let (ys_i_12, _ys) = get_list_value 2  _ys in
      let (ys_i_19, _ys) = get_list_value 6  _ys in
      let (ys_i_20, _ys) = get_list_value 0  _ys in
      let (ys_i_24, _ys) = get_list_value 3  _ys in
      let (ys_i_25, _ys) = get_list_value 0  _ys in
      let (ys_i_38, _ys) = get_list_value 12 _ys in
      let (ys_i_44, _ys) = get_list_value 5  _ys in
      let (ys_i_47, _ys) = get_list_value 2  _ys in
      let (ys_i_54, _ys) = get_list_value 6  _ys in
      let (ys_i_55, _ys) = get_list_value 0  _ys in
      let (ys_i_61, _ys) = get_list_value 5  _ys in
      let (ys_i_63, _ys) = get_list_value 1  _ys in
      let (ys_i_67, _ys) = get_list_value 3  _ys in
      let (ys_i_69, _ys) = get_list_value 1  _ys in
      let (ys_i_78, _ys) = get_list_value 8  _ys in
      let (ys_i_79, _) = get_list_value 0  _ys in

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

      let (ls_i, _ls) = get_list_value i ls in
      let (ls_i_3, _) = get_list_value 2 _ls in
      let ls = list_inserting ls (l_len + i) (ls_i lxor ls_i_3) in

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

      let xs = list_inserting xs (n_len + i) (xs_i_n_len lxor h) in
      let ys = list_inserting ys (n_len + i) (ys_i_n_len lxor h) in

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
