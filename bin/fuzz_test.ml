open Core
open Crowbar

let dist x x' = Float.abs (x -. x')

let check_m_tree pts =
  let pts =
    List.map pts ~f:(fun i -> Float.of_int i /. Float.of_int Int.max_value)
  in
  let tree = M_tree.Private.create dist in
  List.iter pts ~f:(M_tree.Private.insert tree);
  M_tree.Private.invariant tree;

  let pts = List.dedup_and_sort ~compare:Float.compare pts in
  let pts' =
    M_tree.Private.iter tree |> Iter.to_list
    |> List.dedup_and_sort ~compare:Float.compare
  in
  check (List.equal Float.equal pts pts');

  List.iter [ 0.; 0.1; 0.2 ] ~f:(fun radius ->
      List.iter pts ~f:(fun p ->
          M_tree.Private.range tree p ~radius (fun p' ->
              if Float.(p -. p' > radius) then
                failf "found point %f outside radius %f of %f" p' radius p)))

let m_tree_gen = map [ list int ] Fun.id
let () = add_test ~name:"insert" [ m_tree_gen ] check_m_tree
