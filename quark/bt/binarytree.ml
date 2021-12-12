(*
  binarytree.ml

  Created by Shu Minoda on 2021/12/12
  Copyright (c) 2021 Shu Minoda
 *)

type tree = Leaf | Node of (int * int) * tree * tree

let add tree index value =
  let rec _add tree index value continue =
    match tree with
        Leaf -> continue (Node ((index, value), Leaf, Leaf))
      | Node ((i, _), left, right) when index = i -> continue (Node ((index, value), left, right))
      | Node ((i, _) as node, left, right) when index < i -> _add left index value (fun n -> continue (Node (node, n, right)))
      | Node ((i, _) as node, left, right) -> _add right index value (fun n -> continue (Node (node, left, n))) in
  _add tree index value (fun x -> x)

let tree_of_list list =
  let rec split index left length = function
      [] -> ([], None, [])
    | x :: xs ->
      if index < length / 2 then split (index + 1) (x :: left) length xs
      else (left, (Some x), xs) in
  let rec init tree list continue =
    let (left, x, right) = split 0 [] (List.length list) list in
    match x with
        None -> continue tree
      | Some (i, x) -> init (add tree i x) left (fun t -> init t right continue) in
  init Leaf (List.mapi (fun i x -> (i, x)) list) (fun t -> t)

let rec get tree index =
  match tree with
      Leaf -> raise Not_found
    | Node ((i, x), left, right) ->
      if index = i then x
      else if index < i then get left index
      else get right index

let update_tree tree index value =
  let rec _update tree value continue =
    match tree with
        Leaf -> raise Not_found
      | Node ((i, _), left, right) when index = i -> continue (Node ((index, value), left, right))
      | Node ((i, _) as node, left, right) when index < i -> _update left value (fun n -> continue (Node (node, n, right)))
      | Node ((i, _) as node, left, right) -> _update right value (fun n -> continue (Node (node, left, n))) in
  _update tree value (fun x -> x)

let rec inorder = function
    Leaf -> []
  | Node (x, left, right) -> (inorder left) @ (x :: inorder right)
