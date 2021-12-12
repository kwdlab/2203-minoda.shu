(*
  u_quark.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let capacity = 16
let rate = 1
let width = 17
let digest = width

type hash_state = { pos: int; x: int array }

let iv = [|0xd8; 0xda; 0xca; 0x44; 0x41; 0x4a; 0x09; 0x97;
  0x19; 0xc8; 0x0a; 0xa3; 0xaf; 0x06; 0x56; 0x44; 0xdb|]

let permute state =
  let rounds = 4 * 136 in
  let n_len = 68 in
  let l_len = 10 in

  let (xs, ys) = Array.split (Array.init (n_len + rounds) (fun i ->
    if i < n_len then (state.(i), state.(i + n_len))
    else (0, 0)
  )) in
  let ls = Array.init (l_len + rounds) (fun i ->
    if i < l_len then 0xFFFFFFFF
    else 0
  ) in

  let rec round i =
    if i < rounds then (
      xs.(n_len + i) <- (xs.(i) lxor ys.(i));
      xs.(n_len + i) <- (xs.(n_len + i) lxor
        xs.(i+9) lxor xs.(i+14) lxor xs.(i+21) lxor xs.(i+28) lxor xs.(i+33) lxor
        xs.(i+37) lxor xs.(i+45) lxor xs.(i+52) lxor xs.(i+55) lxor xs.(i+50) lxor
        (xs.(i+59) land xs.(i+55)) lxor
        (xs.(i+37) land xs.(i+33)) lxor
        (xs.(i+15) land xs.(i+9)) lxor
        (xs.(i+55) land xs.(i+52) land xs.(i+45)) lxor
        (xs.(i+33) land xs.(i+28) land xs.(i+21)) lxor
        (xs.(i+59) land xs.(i+45) land xs.(i+28) land xs.(i+9)) lxor
        (xs.(i+55) land xs.(i+52) land xs.(i+37) land xs.(i+33)) lxor
        (xs.(i+59) land xs.(i+55) land xs.(i+21) land xs.(i+15)) lxor
        (xs.(i+59) land xs.(i+55) land xs.(i+52) land xs.(i+45) land xs.(i+37)) lxor
        (xs.(i+33) land xs.(i+28) land xs.(i+21) land xs.(i+15) land xs.(i+9)) lxor
        (xs.(i+52) land xs.(i+45) land xs.(i+37) land xs.(i+33) land xs.(i+28) land xs.(i+21))
      );

      ys.(n_len + i) <- (ys.(i));
      ys.(n_len + i) <- (ys.(n_len + i) lxor
        ys.(i+7) lxor ys.(i+16) lxor ys.(i+20) lxor ys.(i+30) lxor ys.(i+35) lxor
        ys.(i+37) lxor ys.(i+42) lxor ys.(i+51) lxor ys.(i+54) lxor ys.(i+49) lxor
        (ys.(i+58) land ys.(i+54)) lxor
        (ys.(i+37) land ys.(i+35)) lxor
        (ys.(i+15) land ys.(i+7)) lxor
        (ys.(i+54) land ys.(i+51) land ys.(i+42)) lxor
        (ys.(i+35) land ys.(i+30) land ys.(i+20)) lxor
        (ys.(i+58) land ys.(i+42) land ys.(i+30) land ys.(i+7)) lxor
        (ys.(i+54) land ys.(i+51) land ys.(i+37) land ys.(i+35)) lxor
        (ys.(i+58) land ys.(i+54) land ys.(i+20) land ys.(i+15)) lxor
        (ys.(i+58) land ys.(i+54) land ys.(i+51) land ys.(i+42) land ys.(i+37)) lxor
        (ys.(i+35) land ys.(i+30) land ys.(i+20) land ys.(i+15) land ys.(i+7)) lxor
        (ys.(i+51) land ys.(i+42) land ys.(i+37) land ys.(i+35) land ys.(i+30) land ys.(i+20))
      );

      ls.(l_len + i) <- (ls.(i));
      ls.(l_len + i) <- (ls.(l_len + i) lxor ls.(i+3));

      let h = xs.(i+25) lxor ys.(i+59) lxor
        (ys.(i+3) land xs.(i+55)) lxor
        (xs.(i+46) land xs.(i+55)) lxor
        (xs.(i+55) land ys.(i+59)) lxor
        (ys.(i+3) land xs.(i+25) land xs.(i+46)) lxor
        (ys.(i+3) land xs.(i+46) land xs.(i+55)) lxor
        (ys.(i+3) land xs.(i+46) land ys.(i+59)) lxor
        (xs.(i+25) land xs.(i+46) land ys.(i+59) land ls.(i)) lxor
        (xs.(i+25) land ls.(i)) in
      let h = h lxor
        xs.(i+1) lxor ys.(i+2) lxor xs.(i+4) lxor ys.(i+10) lxor
        xs.(i+31) lxor ys.(i+43) lxor xs.(i+56) lxor ls.(i) in

      xs.(n_len + i) <- (xs.(n_len + i) lxor h);
      ys.(n_len + i) <- (ys.(n_len + i) lxor h);

      round (i + 1)
    )
    else () in

  round 0;

  let rec update_state i state =
    if i < n_len then (
      state.(i) <- (xs.(rounds + i));
      (state.(i + n_len) <- (ys.(rounds + i)); update_state (i + 1) state)
    )
    else () in
  update_state 0 state

let init hash_state =
  let rec init i hash_state =
    if i < 8*width then init (i + 1) (
      hash_state.x.(i) <- ((iv.(i/8) lsr (7 - (i mod 8))) land 1);
      hash_state
    )
    else {hash_state with pos = 0} in
  init 0 hash_state

let update hash_state data data_byte_len =
  let rec update_state i u hash_state =
    if i < 8*hash_state.pos + 8 then update_state (i + 1) u (
      hash_state.x.(8*(width - rate) + i) <- (
        hash_state.x.(8*(width - rate) + i) lxor ((u lsr (i mod 8)) land 1)
      );
      hash_state
    )
    else hash_state in
  let rec update i hash_state data data_byte_len =
    if data_byte_len <= 0 then hash_state
    else
      let hash_state = update_state (8*hash_state.pos) data.(i) hash_state in
      let hash_state = {hash_state with pos = hash_state.pos + 1} in
      if hash_state.pos = rate then (
        permute hash_state.x;
        update (i + 1) {hash_state with pos = 0} data (data_byte_len-1)
      )
      else update (i + 1) hash_state data (data_byte_len-1) in
  update 0 hash_state data data_byte_len

let final hash_state out =
  hash_state.x.(8*(width - rate) + hash_state.pos*8) <- (
    hash_state.x.(8*(width - rate) + hash_state.pos*8) lxor 1
  );
  permute hash_state.x;
  let rec extract_one_byte i outbytes out hash_state =
    if i < 8 then (
      let u = hash_state.x.(8*(width - rate) + i + 8*(outbytes mod rate)) land 1 in
      out.(outbytes) <- (out.(outbytes) lxor (u lsl (7 - i)));
      extract_one_byte (i + 1) outbytes out hash_state
    )
    else () in
  let rec final outbytes hash_state =
    if outbytes < digest then (
      extract_one_byte 0 outbytes out hash_state;
      let outbytes = outbytes + 1 in
      if outbytes = digest then ()
      else (
        if outbytes mod rate = 0 then (
          permute hash_state.x;
          final outbytes hash_state
        )
        else
          final outbytes hash_state
      )
    )
    else () in
  final 0 hash_state

let quark out in_data in_len =
  let hash_state = {pos = 0; x = Array.init (width*8) (fun _ -> 0)} in
  let hash_state = init hash_state in
  let hash_state = update hash_state in_data in_len in
  final hash_state out
