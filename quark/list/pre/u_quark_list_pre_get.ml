(*
  u_quark_list_pre_get.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let capacity = 16
let rate = 1
let width = 17
let digest = width

type hash_state = { pos: int; x: int list }

let iv = [0xd8; 0xda; 0xca; 0x44; 0x41; 0x4a; 0x09; 0x97;
  0x19; 0xc8; 0x0a; 0xa3; 0xaf; 0x06; 0x56; 0x44; 0xdb]

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
  let rounds = 4 * 136 in
  let n_len = 68 in
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
      let (xs_i_4 , _xs) = get_list_value 2 _xs in
      let (xs_i_9 , _xs) = get_list_value 4 _xs in
      let (xs_i_14, _xs) = get_list_value 4 _xs in
      let (xs_i_15, _xs) = get_list_value 0 _xs in
      let (xs_i_21, _xs) = get_list_value 5 _xs in
      let (xs_i_25, _xs) = get_list_value 3 _xs in
      let (xs_i_28, _xs) = get_list_value 2 _xs in
      let (xs_i_31, _xs) = get_list_value 2 _xs in
      let (xs_i_33, _xs) = get_list_value 1 _xs in
      let (xs_i_37, _xs) = get_list_value 3 _xs in
      let (xs_i_45, _xs) = get_list_value 7 _xs in
      let (xs_i_46, _xs) = get_list_value 0 _xs in
      let (xs_i_50, _xs) = get_list_value 3 _xs in
      let (xs_i_52, _xs) = get_list_value 1 _xs in
      let (xs_i_55, _xs) = get_list_value 2 _xs in
      let (xs_i_56, _xs) = get_list_value 0 _xs in
      let (xs_i_59, _) = get_list_value 2 _xs in

      let (ys_i_2 , _ys) = get_list_value 1 _ys in
      let (ys_i_3 , _ys) = get_list_value 0 _ys in
      let (ys_i_7 , _ys) = get_list_value 3 _ys in
      let (ys_i_10, _ys) = get_list_value 2 _ys in
      let (ys_i_15, _ys) = get_list_value 4 _ys in
      let (ys_i_16, _ys) = get_list_value 0 _ys in
      let (ys_i_20, _ys) = get_list_value 3 _ys in
      let (ys_i_30, _ys) = get_list_value 9 _ys in
      let (ys_i_35, _ys) = get_list_value 4 _ys in
      let (ys_i_37, _ys) = get_list_value 1 _ys in
      let (ys_i_42, _ys) = get_list_value 4 _ys in
      let (ys_i_43, _ys) = get_list_value 0 _ys in
      let (ys_i_49, _ys) = get_list_value 5 _ys in
      let (ys_i_51, _ys) = get_list_value 1 _ys in
      let (ys_i_54, _ys) = get_list_value 2 _ys in
      let (ys_i_58, _ys) = get_list_value 3 _ys in
      let (ys_i_59, _) = get_list_value 0 _ys in

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

      let (ls_i, _ls) = get_list_value i ls in
      let (ls_i_3, _) = get_list_value 2 _ls in
      let ls = list_inserting ls (l_len + i) (ls_i lxor ls_i_3) in

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
