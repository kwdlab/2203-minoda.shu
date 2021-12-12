(*
  s_quark.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let capacity = 28
let rate = 4
let width = 32
let digest = width

type hash_state = { pos: int; x: int array }

let iv = [|0x39;0x72;0x51;0xce;0xe1;0xde;0x8a;0xa7;
	   0x3e;0xa2;0x62;0x50;0xc6;0xd7;0xbe;0x12;
	   0x8c;0xd3;0xe7;0x9d;0xd7;0x18;0xc2;0x4b;
	   0x8a;0x19;0xd0;0x9c;0x24;0x92;0xda;0x5d|]

let permute state =
  let rounds = 4 * 256 in
  let n_len = 128 in
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
        xs.(i+16) lxor xs.(i+26) lxor xs.(i+39) lxor xs.(i+52) lxor xs.(i+61) lxor
        xs.(i+69) lxor xs.(i+84) lxor xs.(i+97) lxor xs.(i+103) lxor xs.(i+94) lxor
        (xs.(i+111) land xs.(i+103)) lxor
        (xs.(i+69) land xs.(i+61)) lxor
        (xs.(i+28) land xs.(i+16)) lxor
        (xs.(i+103) land xs.(i+97) land xs.(i+84)) lxor
        (xs.(i+61) land xs.(i+52) land xs.(i+39)) lxor
        (xs.(i+111) land xs.(i+84) land xs.(i+52) land xs.(i+16)) lxor
        (xs.(i+103) land xs.(i+97) land xs.(i+69) land xs.(i+61)) lxor
        (xs.(i+111) land xs.(i+103) land xs.(i+39) land xs.(i+28)) lxor
        (xs.(i+111) land xs.(i+103) land xs.(i+97) land xs.(i+84) land xs.(i+69)) lxor
        (xs.(i+61) land xs.(i+52) land xs.(i+39) land xs.(i+28) land xs.(i+16)) lxor
        (xs.(i+97) land xs.(i+84) land xs.(i+69) land xs.(i+61) land xs.(i+52) land xs.(i+39))
      );

      ys.(n_len + i) <- (ys.(i));
      ys.(n_len + i) <- (ys.(n_len + i) lxor
        ys.(i+13) lxor ys.(i+30) lxor ys.(i+37) lxor ys.(i+56) lxor ys.(i+65) lxor
        ys.(i+69) lxor ys.(i+79) lxor ys.(i+96) lxor ys.(i+101) lxor ys.(i+92) lxor
        (ys.(i+109) land ys.(i+101)) lxor
        (ys.(i+69) land ys.(i+65)) lxor
        (ys.(i+28) land ys.(i+13)) lxor
        (ys.(i+101) land ys.(i+96) land ys.(i+79)) lxor
        (ys.(i+65) land ys.(i+56) land ys.(i+37)) lxor
        (ys.(i+109) land ys.(i+79) land ys.(i+56) land ys.(i+13)) lxor
        (ys.(i+101) land ys.(i+96) land ys.(i+69) land ys.(i+65)) lxor
        (ys.(i+109) land ys.(i+101) land ys.(i+37) land ys.(i+28)) lxor
        (ys.(i+109) land ys.(i+101) land ys.(i+96) land ys.(i+79) land ys.(i+69)) lxor
        (ys.(i+65) land ys.(i+56) land ys.(i+37) land ys.(i+28) land ys.(i+13)) lxor
        (ys.(i+96) land ys.(i+79) land ys.(i+69) land ys.(i+65) land ys.(i+56) land ys.(i+37))
      );

      ls.(l_len + i) <- (ls.(i));
      ls.(l_len + i) <- (ls.(l_len + i) lxor ls.(i+3));

      let h = xs.(i+47) lxor ys.(i+111) lxor
        (ys.(i+8) land xs.(i+100)) lxor
        (xs.(i+72) land xs.(i+100)) lxor
        (xs.(i+100) land ys.(i+111)) lxor
        (ys.(i+8) land xs.(i+47) land xs.(i+72)) lxor
        (ys.(i+8) land xs.(i+72) land xs.(i+100)) lxor
        (ys.(i+8) land xs.(i+72) land ys.(i+111)) lxor
        (xs.(i+47) land xs.(i+72) land ys.(i+111) land ls.(i)) lxor
        (xs.(i+47) land ls.(i)) in
      let h = h lxor
        xs.(i+1) lxor ys.(i+3) lxor xs.(i+7) lxor ys.(i+18) lxor
        xs.(i+58) lxor ys.(i+80) lxor xs.(i+105) lxor ls.(i) in
      let h = h lxor
        ys.(i+34) lxor ys.(i+71) lxor xs.(i+90) lxor ys.(i+91) in

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
