(*
  u_quark_list.ml

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

  let rec round i xs ys ls =
    if i < rounds then
      let xs = list_inserting xs (n_len + i) (List.nth xs i lxor List.nth ys i) in
      let xs = list_inserting xs (n_len + i) (List.nth xs (n_len + i) lxor
        List.nth xs (i+9) lxor List.nth xs (i+14) lxor List.nth xs (i+21) lxor List.nth xs (i+28) lxor List.nth xs (i+33) lxor
        List.nth xs (i+37) lxor List.nth xs (i+45) lxor List.nth xs (i+52) lxor List.nth xs (i+55) lxor List.nth xs (i+50) lxor
        (List.nth xs (i+59) land List.nth xs (i+55)) lxor
        (List.nth xs (i+37) land List.nth xs (i+33)) lxor
        (List.nth xs (i+15) land List.nth xs (i+9)) lxor
        (List.nth xs (i+55) land List.nth xs (i+52) land List.nth xs (i+45)) lxor
        (List.nth xs (i+33) land List.nth xs (i+28) land List.nth xs (i+21)) lxor
        (List.nth xs (i+59) land List.nth xs (i+45) land List.nth xs (i+28) land List.nth xs (i+9)) lxor
        (List.nth xs (i+55) land List.nth xs (i+52) land List.nth xs (i+37) land List.nth xs (i+33)) lxor
        (List.nth xs (i+59) land List.nth xs (i+55) land List.nth xs (i+21) land List.nth xs (i+15)) lxor
        (List.nth xs (i+59) land List.nth xs (i+55) land List.nth xs (i+52) land List.nth xs (i+45) land List.nth xs (i+37)) lxor
        (List.nth xs (i+33) land List.nth xs (i+28) land List.nth xs (i+21) land List.nth xs (i+15) land List.nth xs (i+9)) lxor
        (List.nth xs (i+52) land List.nth xs (i+45) land List.nth xs (i+37) land List.nth xs (i+33) land List.nth xs (i+28) land List.nth xs (i+21))
      ) in

      let ys = list_inserting ys (n_len + i) (List.nth ys i) in
      let ys = list_inserting ys (n_len + i) (List.nth ys (n_len + i) lxor
        List.nth ys (i+7) lxor List.nth ys (i+16) lxor List.nth ys (i+20) lxor List.nth ys (i+30) lxor List.nth ys (i+35) lxor
        List.nth ys (i+37) lxor List.nth ys (i+42) lxor List.nth ys (i+51) lxor List.nth ys (i+54) lxor List.nth ys (i+49) lxor
        (List.nth ys (i+58) land List.nth ys (i+54)) lxor
        (List.nth ys (i+37) land List.nth ys (i+35)) lxor
        (List.nth ys (i+15) land List.nth ys (i+7)) lxor
        (List.nth ys (i+54) land List.nth ys (i+51) land List.nth ys (i+42)) lxor
        (List.nth ys (i+35) land List.nth ys (i+30) land List.nth ys (i+20)) lxor
        (List.nth ys (i+58) land List.nth ys (i+42) land List.nth ys (i+30) land List.nth ys (i+7)) lxor
        (List.nth ys (i+54) land List.nth ys (i+51) land List.nth ys (i+37) land List.nth ys (i+35)) lxor
        (List.nth ys (i+58) land List.nth ys (i+54) land List.nth ys (i+20) land List.nth ys (i+15)) lxor
        (List.nth ys (i+58) land List.nth ys (i+54) land List.nth ys (i+51) land List.nth ys (i+42) land List.nth ys (i+37)) lxor
        (List.nth ys (i+35) land List.nth ys (i+30) land List.nth ys (i+20) land List.nth ys (i+15) land List.nth ys (i+7)) lxor
        (List.nth ys (i+51) land List.nth ys (i+42) land List.nth ys (i+37) land List.nth ys (i+35) land List.nth ys (i+30) land List.nth ys (i+20))
      ) in

      let ls = list_inserting ls (l_len + i) (List.nth ls i) in
      let ls = list_inserting ls (l_len + i) (List.nth ls (l_len + i) lxor List.nth ls (i+3)) in

      let h = List.nth xs (i+25) lxor List.nth ys (i+59) lxor
        (List.nth ys (i+3) land List.nth xs (i+55)) lxor
        (List.nth xs (i+46) land List.nth xs (i+55)) lxor
        (List.nth xs (i+55) land List.nth ys (i+59)) lxor
        (List.nth ys (i+3) land List.nth xs (i+25) land List.nth xs (i+46)) lxor
        (List.nth ys (i+3) land List.nth xs (i+46) land List.nth xs (i+55)) lxor
        (List.nth ys (i+3) land List.nth xs (i+46) land List.nth ys (i+59)) lxor
        (List.nth xs (i+25) land List.nth xs (i+46) land List.nth ys (i+59) land List.nth ls i) lxor
        (List.nth xs (i+25) land List.nth ls i) in
      let h = h lxor
        List.nth xs (i+1) lxor List.nth ys (i+2) lxor List.nth xs (i+4) lxor List.nth ys (i+10) lxor
        List.nth xs (i+31) lxor List.nth ys (i+43) lxor List.nth xs (i+56) lxor List.nth ls i in

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
