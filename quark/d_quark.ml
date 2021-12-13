(*
  d_quark.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

let capacity = 20
let rate = 2
let width = 22
let digest = width

type hash_state = { pos: int; x: int array }

let iv = [|0xcc;0x6c;0x4a;0xb7;0xd1;0x1f;0xa9;0xbd;
	   0xf6;0xee;0xde;0x03;0xd8;0x7b;0x68;0xf9;
	   0x1b;0xaa;0x70;0x6c;0x20;0xe9|]

let permute state =
  let rounds = 4 * 176 in
  let n_len = 88 in
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
        xs.(i+11) lxor xs.(i+18) lxor xs.(i+27) lxor xs.(i+36) lxor xs.(i+42) lxor
        xs.(i+47) lxor xs.(i+58) lxor xs.(i+67) lxor xs.(i+71) lxor xs.(i+64) lxor
        (xs.(i+79) land xs.(i+71)) lxor
        (xs.(i+47) land xs.(i+42)) lxor
        (xs.(i+19) land xs.(i+11)) lxor
        (xs.(i+71) land xs.(i+67) land xs.(i+58)) lxor
        (xs.(i+42) land xs.(i+36) land xs.(i+27)) lxor
        (xs.(i+79) land xs.(i+58) land xs.(i+36) land xs.(i+11)) lxor
        (xs.(i+71) land xs.(i+67) land xs.(i+47) land xs.(i+42)) lxor
        (xs.(i+79) land xs.(i+71) land xs.(i+27) land xs.(i+19)) lxor
        (xs.(i+79) land xs.(i+71) land xs.(i+67) land xs.(i+58) land xs.(i+47)) lxor
        (xs.(i+42) land xs.(i+36) land xs.(i+27) land xs.(i+19) land xs.(i+11)) lxor
        (xs.(i+67) land xs.(i+58) land xs.(i+47) land xs.(i+42) land xs.(i+36) land xs.(i+27))
      );

      ys.(n_len + i) <- (ys.(i));
      ys.(n_len + i) <- (ys.(n_len + i) lxor
        ys.(i+9) lxor ys.(i+20) lxor ys.(i+25) lxor ys.(i+38) lxor ys.(i+44) lxor
        ys.(i+47) lxor ys.(i+54) lxor ys.(i+67) lxor ys.(i+69) lxor  ys.(i+63) lxor
        (ys.(i+78) land ys.(i+69)) lxor
        (ys.(i+47) land ys.(i+44)) lxor
        (ys.(i+19) land ys.(i+9)) lxor
        (ys.(i+69) land ys.(i+67) land ys.(i+54)) lxor
        (ys.(i+44) land ys.(i+38) land ys.(i+25)) lxor
        (ys.(i+78) land ys.(i+54) land ys.(i+38) land ys.(i+9)) lxor
        (ys.(i+69) land ys.(i+67) land ys.(i+47) land ys.(i+44)) lxor
        (ys.(i+78) land ys.(i+69) land ys.(i+25) land ys.(i+19)) lxor
        (ys.(i+78) land ys.(i+69) land ys.(i+67) land ys.(i+54) land ys.(i+47)) lxor
        (ys.(i+44) land ys.(i+38) land ys.(i+25) land ys.(i+19) land ys.(i+9)) lxor
        (ys.(i+67) land ys.(i+54) land ys.(i+47) land ys.(i+44) land ys.(i+38) land ys.(i+25))
      );

      ls.(l_len + i) <- (ls.(i));
      ls.(l_len + i) <- (ls.(l_len + i) lxor ls.(i+3));

      let h = xs.(i+35) lxor ys.(i+79) lxor
      (ys.(i+4) land xs.(i+68)) lxor
      (xs.(i+57) land xs.(i+68)) lxor
      (xs.(i+68) land ys.(i+79)) lxor
      (ys.(i+4) land xs.(i+35) land xs.(i+57)) lxor
      (ys.(i+4) land xs.(i+57) land xs.(i+68)) lxor
      (ys.(i+4) land xs.(i+57) land ys.(i+79)) lxor
      (xs.(i+35) land xs.(i+57) land ys.(i+79) land ls.(i)) lxor
      (xs.(i+35) land ls.(i)) in
      let h = h lxor
        xs.(i+1) lxor ys.(i+2) lxor xs.(i+5) lxor ys.(i+12) lxor
        xs.(i+40) lxor ys.(i+55) lxor xs.(i+72) lxor ls.(i) in
      let h = h lxor
        ys.(i+24) lxor xs.(i+48) lxor ys.(i+61) in

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
