open Core
open M_tree.Private

[@@@warning "-30"]

type 'a obj = 'a M_tree.Private.obj = {
  value : 'a;
  mutable parent_dist : float; [@default Float.nan] [@sexp_drop_default.compare]
  mutable radius : float; [@default 0.] [@sexp_drop_default.compare]
  mutable tree : 'a node option; [@sexp.option]
}

and 'a opaque_obj = 'a obj = {
  value : 'a;
  mutable parent_dist : float; [@default Float.nan] [@sexp_drop_default.compare]
  mutable radius : float; [@default 0.] [@sexp_drop_default.compare]
  mutable tree : ('a node option[@sexp.opaque]);
}

and 'a node = 'a M_tree.Private.node = {
  is_leaf : bool;
  mutable objects : 'a obj list; [@sexp.list]
  mutable parent : ('a opaque_obj * ('a node[@sexp.opaque])) option;
      [@sexp.option]
}
[@@deriving sexp]

[@@@warning "+30"]

type 'a t = 'a M_tree.Private.t = {
  mutable root : 'a node;
  branching_factor : int;
  distance : 'a -> 'a -> float;
  eq : 'a -> 'a -> bool;
}
[@@deriving sexp]

module Spec = struct
  type 'a t = { mutable elems : 'a list; distance : 'a -> 'a -> float }

  let create distance = { elems = []; distance }
  let insert xs x = xs.elems <- x :: xs.elems

  let range xs ~radius x =
    List.filter xs.elems ~f:(fun x' -> Float.(xs.distance x x' <= radius))
end

let equiv_results compare l l' =
  List.equal
    (fun x x' -> compare x x' = 0)
    (List.sort ~compare l) (List.sort ~compare l')

let abs_dist x x' = Float.abs (x -. x')

let%expect_test "" =
  let o1 = mk_obj 1. and o2 = mk_obj 2. and o3 = mk_obj 1.5 in
  let entries = [ o1; o2; o3 ] in
  let r, r' = promote entries in
  partition abs_dist r r' entries;
  print_s
    [%message
      (r : float obj)
        (r' : float obj)
        (o1 : float obj)
        (o2 : float obj)
        (o3 : float obj)];
  [%expect
    {|
    ((r
      ((value 1.5)
       (tree
        ((is_leaf true)
         (objects (((value 1) (parent_dist 0.5)) ((value 1.5) (parent_dist 0))))))))
     (r'
      ((value 2) (tree ((is_leaf true) (objects (((value 2) (parent_dist 0))))))))
     (o1 ((value 1) (parent_dist 0.5))) (o2 ((value 2) (parent_dist 0)))
     (o3 ((value 1.5) (parent_dist 0)))) |}]

let%expect_test "" =
  let tree = create ~branching_factor:2 abs_dist in
  split tree
    { objects = [ mk_obj 1.; mk_obj 2. ]; parent = None; is_leaf = true }
    (mk_obj 1.5);
  print_s [%message (tree : float t)];
  [%expect
    {|
    (tree
     ((root
       ((is_leaf false)
        (objects
         (((value 2) (radius 0.5)
           (tree
            ((is_leaf true)
             (objects
              (((value 1.5) (parent_dist 0.5)) ((value 2) (parent_dist 0))))
             (parent (((value 2) (radius 0.5) (tree <opaque>)) <opaque>)))))
          ((value 1)
           (tree
            ((is_leaf true) (objects (((value 1) (parent_dist 0))))
             (parent (((value 1) (tree <opaque>)) <opaque>)))))))))
      (branching_factor 2) (distance <fun>) (eq <fun>))) |}]

let points =
  [
    0.1;
    0.2;
    0.15;
    0.5;
    0.6;
    0.9;
    0.95;
    0.8;
    0.65;
    0.01;
    0.21;
    0.23;
    0.88;
    0.74;
    0.62;
    0.55;
    0.32;
    0.12;
    0.14;
  ]

let%expect_test "" =
  let tree = create abs_dist in
  List.iter points ~f:(fun p -> insert tree p);
  let range_spec ps v r =
    Iter.of_list ps
    |> Iter.filter (fun v' -> Float.(abs_dist v v' <= r))
    |> Iter.sort ~cmp:[%compare: float]
    |> Iter.to_list
  in
  let range_test t v r =
    range t v ~radius:r |> Iter.sort ~cmp:[%compare: float] |> Iter.to_list
  in
  List.iter points ~f:(fun p ->
      [%test_result: float * float list]
        ~expect:(p, range_spec points p 0.1)
        (p, range_test tree p 0.1))

let%expect_test "" =
  let tree = create ~branching_factor:4 abs_dist in
  List.iteri points ~f:(fun i p ->
      insert tree p;
      assert (Iter.length @@ iter tree = i + 1);
      print_s [%message (p : float) (tree : float t)];
      invariant tree);
  [%expect
    {|
    ((p 0.1)
     (tree
      ((root ((is_leaf true) (objects (((value 0.1)))))) (branching_factor 4)
       (distance <fun>) (eq <fun>))))
    ((p 0.2)
     (tree
      ((root ((is_leaf true) (objects (((value 0.2)) ((value 0.1))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.15)
     (tree
      ((root
        ((is_leaf true) (objects (((value 0.15)) ((value 0.2)) ((value 0.1))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.5)
     (tree
      ((root
        ((is_leaf true)
         (objects (((value 0.5)) ((value 0.15)) ((value 0.2)) ((value 0.1))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.6)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.1) (radius 0.1)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.15) (parent_dist 0.049999999999999989))
                ((value 0.2) (parent_dist 0.1)) ((value 0.1) (parent_dist 0))))
              (parent (((value 0.1) (radius 0.1) (tree <opaque>)) <opaque>)))))
           ((value 0.5) (radius 0.099999999999999978)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.6) (parent_dist 0.099999999999999978))
                ((value 0.5) (parent_dist 0))))
              (parent
               (((value 0.5) (radius 0.099999999999999978) (tree <opaque>))
                <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.9)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.1) (radius 0.1)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.15) (parent_dist 0.049999999999999989))
                ((value 0.2) (parent_dist 0.1)) ((value 0.1) (parent_dist 0))))
              (parent (((value 0.1) (radius 0.1) (tree <opaque>)) <opaque>)))))
           ((value 0.5) (radius 0.4)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.9) (parent_dist 0.4))
                ((value 0.6) (parent_dist 0.099999999999999978))
                ((value 0.5) (parent_dist 0))))
              (parent (((value 0.5) (radius 0.4) (tree <opaque>)) <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.95)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.1) (radius 0.1)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.15) (parent_dist 0.049999999999999989))
                ((value 0.2) (parent_dist 0.1)) ((value 0.1) (parent_dist 0))))
              (parent (((value 0.1) (radius 0.1) (tree <opaque>)) <opaque>)))))
           ((value 0.5) (radius 0.44999999999999996)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.95) (parent_dist 0.44999999999999996))
                ((value 0.9) (parent_dist 0.4))
                ((value 0.6) (parent_dist 0.099999999999999978))
                ((value 0.5) (parent_dist 0))))
              (parent
               (((value 0.5) (radius 0.44999999999999996) (tree <opaque>))
                <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.8)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.9) (radius 0.049999999999999933)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.95) (parent_dist 0.049999999999999933))
                ((value 0.9) (parent_dist 0))))
              (parent
               (((value 0.9) (radius 0.049999999999999933) (tree <opaque>))
                <opaque>)))))
           ((value 0.1) (radius 0.1)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.15) (parent_dist 0.049999999999999989))
                ((value 0.2) (parent_dist 0.1)) ((value 0.1) (parent_dist 0))))
              (parent (((value 0.1) (radius 0.1) (tree <opaque>)) <opaque>)))))
           ((value 0.8) (radius 0.30000000000000004)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.8) (parent_dist 0))
                ((value 0.6) (parent_dist 0.20000000000000007))
                ((value 0.5) (parent_dist 0.30000000000000004))))
              (parent
               (((value 0.8) (radius 0.30000000000000004) (tree <opaque>))
                <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.65)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.9) (radius 0.049999999999999933)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.95) (parent_dist 0.049999999999999933))
                ((value 0.9) (parent_dist 0))))
              (parent
               (((value 0.9) (radius 0.049999999999999933) (tree <opaque>))
                <opaque>)))))
           ((value 0.1) (radius 0.1)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.15) (parent_dist 0.049999999999999989))
                ((value 0.2) (parent_dist 0.1)) ((value 0.1) (parent_dist 0))))
              (parent (((value 0.1) (radius 0.1) (tree <opaque>)) <opaque>)))))
           ((value 0.8) (radius 0.30000000000000004)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.65) (parent_dist 0.15000000000000002))
                ((value 0.8) (parent_dist 0))
                ((value 0.6) (parent_dist 0.20000000000000007))
                ((value 0.5) (parent_dist 0.30000000000000004))))
              (parent
               (((value 0.8) (radius 0.30000000000000004) (tree <opaque>))
                <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.01)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.9) (radius 0.049999999999999933)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.95) (parent_dist 0.049999999999999933))
                ((value 0.9) (parent_dist 0))))
              (parent
               (((value 0.9) (radius 0.049999999999999933) (tree <opaque>))
                <opaque>)))))
           ((value 0.1) (radius 0.1)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.01) (parent_dist 0.090000000000000011))
                ((value 0.15) (parent_dist 0.049999999999999989))
                ((value 0.2) (parent_dist 0.1)) ((value 0.1) (parent_dist 0))))
              (parent (((value 0.1) (radius 0.1) (tree <opaque>)) <opaque>)))))
           ((value 0.8) (radius 0.30000000000000004)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.65) (parent_dist 0.15000000000000002))
                ((value 0.8) (parent_dist 0))
                ((value 0.6) (parent_dist 0.20000000000000007))
                ((value 0.5) (parent_dist 0.30000000000000004))))
              (parent
               (((value 0.8) (radius 0.30000000000000004) (tree <opaque>))
                <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.21)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.1) (radius 0.090000000000000011)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.01) (parent_dist 0.090000000000000011))
                ((value 0.15) (parent_dist 0.049999999999999989))
                ((value 0.1) (parent_dist 0))))
              (parent
               (((value 0.1) (radius 0.090000000000000011) (tree <opaque>))
                <opaque>)))))
           ((value 0.9) (radius 0.049999999999999933)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.95) (parent_dist 0.049999999999999933))
                ((value 0.9) (parent_dist 0))))
              (parent
               (((value 0.9) (radius 0.049999999999999933) (tree <opaque>))
                <opaque>)))))
           ((value 0.21) (radius 0.0099999999999999811)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.21) (parent_dist 0))
                ((value 0.2) (parent_dist 0.0099999999999999811))))
              (parent
               (((value 0.21) (radius 0.0099999999999999811) (tree <opaque>))
                <opaque>)))))
           ((value 0.8) (radius 0.30000000000000004)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.65) (parent_dist 0.15000000000000002))
                ((value 0.8) (parent_dist 0))
                ((value 0.6) (parent_dist 0.20000000000000007))
                ((value 0.5) (parent_dist 0.30000000000000004))))
              (parent
               (((value 0.8) (radius 0.30000000000000004) (tree <opaque>))
                <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.23)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.1) (radius 0.090000000000000011)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.01) (parent_dist 0.090000000000000011))
                ((value 0.15) (parent_dist 0.049999999999999989))
                ((value 0.1) (parent_dist 0))))
              (parent
               (((value 0.1) (radius 0.090000000000000011) (tree <opaque>))
                <opaque>)))))
           ((value 0.9) (radius 0.049999999999999933)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.95) (parent_dist 0.049999999999999933))
                ((value 0.9) (parent_dist 0))))
              (parent
               (((value 0.9) (radius 0.049999999999999933) (tree <opaque>))
                <opaque>)))))
           ((value 0.21) (radius 0.020000000000000018)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.23) (parent_dist 0.020000000000000018))
                ((value 0.21) (parent_dist 0))
                ((value 0.2) (parent_dist 0.0099999999999999811))))
              (parent
               (((value 0.21) (radius 0.020000000000000018) (tree <opaque>))
                <opaque>)))))
           ((value 0.8) (radius 0.30000000000000004)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.65) (parent_dist 0.15000000000000002))
                ((value 0.8) (parent_dist 0))
                ((value 0.6) (parent_dist 0.20000000000000007))
                ((value 0.5) (parent_dist 0.30000000000000004))))
              (parent
               (((value 0.8) (radius 0.30000000000000004) (tree <opaque>))
                <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.88)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.1) (radius 0.090000000000000011)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.01) (parent_dist 0.090000000000000011))
                ((value 0.15) (parent_dist 0.049999999999999989))
                ((value 0.1) (parent_dist 0))))
              (parent
               (((value 0.1) (radius 0.090000000000000011) (tree <opaque>))
                <opaque>)))))
           ((value 0.9) (radius 0.049999999999999933)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.88) (parent_dist 0.020000000000000018))
                ((value 0.95) (parent_dist 0.049999999999999933))
                ((value 0.9) (parent_dist 0))))
              (parent
               (((value 0.9) (radius 0.049999999999999933) (tree <opaque>))
                <opaque>)))))
           ((value 0.21) (radius 0.020000000000000018)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.23) (parent_dist 0.020000000000000018))
                ((value 0.21) (parent_dist 0))
                ((value 0.2) (parent_dist 0.0099999999999999811))))
              (parent
               (((value 0.21) (radius 0.020000000000000018) (tree <opaque>))
                <opaque>)))))
           ((value 0.8) (radius 0.30000000000000004)
            (tree
             ((is_leaf true)
              (objects
               (((value 0.65) (parent_dist 0.15000000000000002))
                ((value 0.8) (parent_dist 0))
                ((value 0.6) (parent_dist 0.20000000000000007))
                ((value 0.5) (parent_dist 0.30000000000000004))))
              (parent
               (((value 0.8) (radius 0.30000000000000004) (tree <opaque>))
                <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.74)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.21) (radius 0.2)
            (tree
             ((is_leaf false)
              (objects
               (((value 0.1) (parent_dist 0.10999999999999999)
                 (radius 0.090000000000000011)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.01) (parent_dist 0.090000000000000011))
                     ((value 0.15) (parent_dist 0.049999999999999989))
                     ((value 0.1) (parent_dist 0))))
                   (parent
                    (((value 0.1) (parent_dist 0.10999999999999999)
                      (radius 0.090000000000000011) (tree <opaque>))
                     <opaque>)))))
                ((value 0.21) (parent_dist 0) (radius 0.020000000000000018)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.23) (parent_dist 0.020000000000000018))
                     ((value 0.21) (parent_dist 0))
                     ((value 0.2) (parent_dist 0.0099999999999999811))))
                   (parent
                    (((value 0.21) (parent_dist 0) (radius 0.020000000000000018)
                      (tree <opaque>))
                     <opaque>)))))))
              (parent (((value 0.21) (radius 0.2) (tree <opaque>)) <opaque>)))))
           ((value 0.6) (radius 0.35)
            (tree
             ((is_leaf false)
              (objects
               (((value 0.65) (parent_dist 0.050000000000000044)
                 (radius 0.15000000000000002)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.74) (parent_dist 0.089999999999999969))
                     ((value 0.65) (parent_dist 0))
                     ((value 0.8) (parent_dist 0.15000000000000002))))
                   (parent
                    (((value 0.65) (parent_dist 0.050000000000000044)
                      (radius 0.15000000000000002) (tree <opaque>))
                     <opaque>)))))
                ((value 0.9) (parent_dist 0.30000000000000004)
                 (radius 0.049999999999999933)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.88) (parent_dist 0.020000000000000018))
                     ((value 0.95) (parent_dist 0.049999999999999933))
                     ((value 0.9) (parent_dist 0))))
                   (parent
                    (((value 0.9) (parent_dist 0.30000000000000004)
                      (radius 0.049999999999999933) (tree <opaque>))
                     <opaque>)))))
                ((value 0.6) (parent_dist 0) (radius 0.099999999999999978)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.6) (parent_dist 0))
                     ((value 0.5) (parent_dist 0.099999999999999978))))
                   (parent
                    (((value 0.6) (parent_dist 0) (radius 0.099999999999999978)
                      (tree <opaque>))
                     <opaque>)))))))
              (parent (((value 0.6) (radius 0.35) (tree <opaque>)) <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.62)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.21) (radius 0.2)
            (tree
             ((is_leaf false)
              (objects
               (((value 0.1) (parent_dist 0.10999999999999999)
                 (radius 0.090000000000000011)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.01) (parent_dist 0.090000000000000011))
                     ((value 0.15) (parent_dist 0.049999999999999989))
                     ((value 0.1) (parent_dist 0))))
                   (parent
                    (((value 0.1) (parent_dist 0.10999999999999999)
                      (radius 0.090000000000000011) (tree <opaque>))
                     <opaque>)))))
                ((value 0.21) (parent_dist 0) (radius 0.020000000000000018)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.23) (parent_dist 0.020000000000000018))
                     ((value 0.21) (parent_dist 0))
                     ((value 0.2) (parent_dist 0.0099999999999999811))))
                   (parent
                    (((value 0.21) (parent_dist 0) (radius 0.020000000000000018)
                      (tree <opaque>))
                     <opaque>)))))))
              (parent (((value 0.21) (radius 0.2) (tree <opaque>)) <opaque>)))))
           ((value 0.6) (radius 0.35)
            (tree
             ((is_leaf false)
              (objects
               (((value 0.65) (parent_dist 0.050000000000000044)
                 (radius 0.15000000000000002)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.74) (parent_dist 0.089999999999999969))
                     ((value 0.65) (parent_dist 0))
                     ((value 0.8) (parent_dist 0.15000000000000002))))
                   (parent
                    (((value 0.65) (parent_dist 0.050000000000000044)
                      (radius 0.15000000000000002) (tree <opaque>))
                     <opaque>)))))
                ((value 0.9) (parent_dist 0.30000000000000004)
                 (radius 0.049999999999999933)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.88) (parent_dist 0.020000000000000018))
                     ((value 0.95) (parent_dist 0.049999999999999933))
                     ((value 0.9) (parent_dist 0))))
                   (parent
                    (((value 0.9) (parent_dist 0.30000000000000004)
                      (radius 0.049999999999999933) (tree <opaque>))
                     <opaque>)))))
                ((value 0.6) (parent_dist 0) (radius 0.099999999999999978)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.62) (parent_dist 0.020000000000000018))
                     ((value 0.6) (parent_dist 0))
                     ((value 0.5) (parent_dist 0.099999999999999978))))
                   (parent
                    (((value 0.6) (parent_dist 0) (radius 0.099999999999999978)
                      (tree <opaque>))
                     <opaque>)))))))
              (parent (((value 0.6) (radius 0.35) (tree <opaque>)) <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.55)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.21) (radius 0.2)
            (tree
             ((is_leaf false)
              (objects
               (((value 0.1) (parent_dist 0.10999999999999999)
                 (radius 0.090000000000000011)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.01) (parent_dist 0.090000000000000011))
                     ((value 0.15) (parent_dist 0.049999999999999989))
                     ((value 0.1) (parent_dist 0))))
                   (parent
                    (((value 0.1) (parent_dist 0.10999999999999999)
                      (radius 0.090000000000000011) (tree <opaque>))
                     <opaque>)))))
                ((value 0.21) (parent_dist 0) (radius 0.020000000000000018)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.23) (parent_dist 0.020000000000000018))
                     ((value 0.21) (parent_dist 0))
                     ((value 0.2) (parent_dist 0.0099999999999999811))))
                   (parent
                    (((value 0.21) (parent_dist 0) (radius 0.020000000000000018)
                      (tree <opaque>))
                     <opaque>)))))))
              (parent (((value 0.21) (radius 0.2) (tree <opaque>)) <opaque>)))))
           ((value 0.6) (radius 0.35)
            (tree
             ((is_leaf false)
              (objects
               (((value 0.65) (parent_dist 0.050000000000000044)
                 (radius 0.15000000000000002)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.74) (parent_dist 0.089999999999999969))
                     ((value 0.65) (parent_dist 0))
                     ((value 0.8) (parent_dist 0.15000000000000002))))
                   (parent
                    (((value 0.65) (parent_dist 0.050000000000000044)
                      (radius 0.15000000000000002) (tree <opaque>))
                     <opaque>)))))
                ((value 0.9) (parent_dist 0.30000000000000004)
                 (radius 0.049999999999999933)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.88) (parent_dist 0.020000000000000018))
                     ((value 0.95) (parent_dist 0.049999999999999933))
                     ((value 0.9) (parent_dist 0))))
                   (parent
                    (((value 0.9) (parent_dist 0.30000000000000004)
                      (radius 0.049999999999999933) (tree <opaque>))
                     <opaque>)))))
                ((value 0.6) (parent_dist 0) (radius 0.099999999999999978)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.55) (parent_dist 0.049999999999999933))
                     ((value 0.62) (parent_dist 0.020000000000000018))
                     ((value 0.6) (parent_dist 0))
                     ((value 0.5) (parent_dist 0.099999999999999978))))
                   (parent
                    (((value 0.6) (parent_dist 0) (radius 0.099999999999999978)
                      (tree <opaque>))
                     <opaque>)))))))
              (parent (((value 0.6) (radius 0.35) (tree <opaque>)) <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.32)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.21) (radius 0.2)
            (tree
             ((is_leaf false)
              (objects
               (((value 0.1) (parent_dist 0.10999999999999999)
                 (radius 0.090000000000000011)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.01) (parent_dist 0.090000000000000011))
                     ((value 0.15) (parent_dist 0.049999999999999989))
                     ((value 0.1) (parent_dist 0))))
                   (parent
                    (((value 0.1) (parent_dist 0.10999999999999999)
                      (radius 0.090000000000000011) (tree <opaque>))
                     <opaque>)))))
                ((value 0.21) (parent_dist 0) (radius 0.11000000000000001)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.32) (parent_dist 0.11000000000000001))
                     ((value 0.23) (parent_dist 0.020000000000000018))
                     ((value 0.21) (parent_dist 0))
                     ((value 0.2) (parent_dist 0.0099999999999999811))))
                   (parent
                    (((value 0.21) (parent_dist 0) (radius 0.11000000000000001)
                      (tree <opaque>))
                     <opaque>)))))))
              (parent (((value 0.21) (radius 0.2) (tree <opaque>)) <opaque>)))))
           ((value 0.6) (radius 0.35)
            (tree
             ((is_leaf false)
              (objects
               (((value 0.65) (parent_dist 0.050000000000000044)
                 (radius 0.15000000000000002)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.74) (parent_dist 0.089999999999999969))
                     ((value 0.65) (parent_dist 0))
                     ((value 0.8) (parent_dist 0.15000000000000002))))
                   (parent
                    (((value 0.65) (parent_dist 0.050000000000000044)
                      (radius 0.15000000000000002) (tree <opaque>))
                     <opaque>)))))
                ((value 0.9) (parent_dist 0.30000000000000004)
                 (radius 0.049999999999999933)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.88) (parent_dist 0.020000000000000018))
                     ((value 0.95) (parent_dist 0.049999999999999933))
                     ((value 0.9) (parent_dist 0))))
                   (parent
                    (((value 0.9) (parent_dist 0.30000000000000004)
                      (radius 0.049999999999999933) (tree <opaque>))
                     <opaque>)))))
                ((value 0.6) (parent_dist 0) (radius 0.099999999999999978)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.55) (parent_dist 0.049999999999999933))
                     ((value 0.62) (parent_dist 0.020000000000000018))
                     ((value 0.6) (parent_dist 0))
                     ((value 0.5) (parent_dist 0.099999999999999978))))
                   (parent
                    (((value 0.6) (parent_dist 0) (radius 0.099999999999999978)
                      (tree <opaque>))
                     <opaque>)))))))
              (parent (((value 0.6) (radius 0.35) (tree <opaque>)) <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.12)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.21) (radius 0.2)
            (tree
             ((is_leaf false)
              (objects
               (((value 0.1) (parent_dist 0.10999999999999999)
                 (radius 0.090000000000000011)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.12) (parent_dist 0.01999999999999999))
                     ((value 0.01) (parent_dist 0.090000000000000011))
                     ((value 0.15) (parent_dist 0.049999999999999989))
                     ((value 0.1) (parent_dist 0))))
                   (parent
                    (((value 0.1) (parent_dist 0.10999999999999999)
                      (radius 0.090000000000000011) (tree <opaque>))
                     <opaque>)))))
                ((value 0.21) (parent_dist 0) (radius 0.11000000000000001)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.32) (parent_dist 0.11000000000000001))
                     ((value 0.23) (parent_dist 0.020000000000000018))
                     ((value 0.21) (parent_dist 0))
                     ((value 0.2) (parent_dist 0.0099999999999999811))))
                   (parent
                    (((value 0.21) (parent_dist 0) (radius 0.11000000000000001)
                      (tree <opaque>))
                     <opaque>)))))))
              (parent (((value 0.21) (radius 0.2) (tree <opaque>)) <opaque>)))))
           ((value 0.6) (radius 0.35)
            (tree
             ((is_leaf false)
              (objects
               (((value 0.65) (parent_dist 0.050000000000000044)
                 (radius 0.15000000000000002)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.74) (parent_dist 0.089999999999999969))
                     ((value 0.65) (parent_dist 0))
                     ((value 0.8) (parent_dist 0.15000000000000002))))
                   (parent
                    (((value 0.65) (parent_dist 0.050000000000000044)
                      (radius 0.15000000000000002) (tree <opaque>))
                     <opaque>)))))
                ((value 0.9) (parent_dist 0.30000000000000004)
                 (radius 0.049999999999999933)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.88) (parent_dist 0.020000000000000018))
                     ((value 0.95) (parent_dist 0.049999999999999933))
                     ((value 0.9) (parent_dist 0))))
                   (parent
                    (((value 0.9) (parent_dist 0.30000000000000004)
                      (radius 0.049999999999999933) (tree <opaque>))
                     <opaque>)))))
                ((value 0.6) (parent_dist 0) (radius 0.099999999999999978)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.55) (parent_dist 0.049999999999999933))
                     ((value 0.62) (parent_dist 0.020000000000000018))
                     ((value 0.6) (parent_dist 0))
                     ((value 0.5) (parent_dist 0.099999999999999978))))
                   (parent
                    (((value 0.6) (parent_dist 0) (radius 0.099999999999999978)
                      (tree <opaque>))
                     <opaque>)))))))
              (parent (((value 0.6) (radius 0.35) (tree <opaque>)) <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>))))
    ((p 0.14)
     (tree
      ((root
        ((is_leaf false)
         (objects
          (((value 0.21) (radius 0.2)
            (tree
             ((is_leaf false)
              (objects
               (((value 0.15) (parent_dist 0.06)
                 (tree
                  ((is_leaf true) (objects (((value 0.15) (parent_dist 0))))
                   (parent
                    (((value 0.15) (parent_dist 0.06) (tree <opaque>)) <opaque>)))))
                ((value 0.14) (parent_dist 0.069999999999999979) (radius 0.13)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.14) (parent_dist 0))
                     ((value 0.12) (parent_dist 0.020000000000000018))
                     ((value 0.01) (parent_dist 0.13))
                     ((value 0.1) (parent_dist 0.040000000000000008))))
                   (parent
                    (((value 0.14) (parent_dist 0.069999999999999979)
                      (radius 0.13) (tree <opaque>))
                     <opaque>)))))
                ((value 0.21) (parent_dist 0) (radius 0.11000000000000001)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.32) (parent_dist 0.11000000000000001))
                     ((value 0.23) (parent_dist 0.020000000000000018))
                     ((value 0.21) (parent_dist 0))
                     ((value 0.2) (parent_dist 0.0099999999999999811))))
                   (parent
                    (((value 0.21) (parent_dist 0) (radius 0.11000000000000001)
                      (tree <opaque>))
                     <opaque>)))))))
              (parent (((value 0.21) (radius 0.2) (tree <opaque>)) <opaque>)))))
           ((value 0.6) (radius 0.35)
            (tree
             ((is_leaf false)
              (objects
               (((value 0.65) (parent_dist 0.050000000000000044)
                 (radius 0.15000000000000002)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.74) (parent_dist 0.089999999999999969))
                     ((value 0.65) (parent_dist 0))
                     ((value 0.8) (parent_dist 0.15000000000000002))))
                   (parent
                    (((value 0.65) (parent_dist 0.050000000000000044)
                      (radius 0.15000000000000002) (tree <opaque>))
                     <opaque>)))))
                ((value 0.9) (parent_dist 0.30000000000000004)
                 (radius 0.049999999999999933)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.88) (parent_dist 0.020000000000000018))
                     ((value 0.95) (parent_dist 0.049999999999999933))
                     ((value 0.9) (parent_dist 0))))
                   (parent
                    (((value 0.9) (parent_dist 0.30000000000000004)
                      (radius 0.049999999999999933) (tree <opaque>))
                     <opaque>)))))
                ((value 0.6) (parent_dist 0) (radius 0.099999999999999978)
                 (tree
                  ((is_leaf true)
                   (objects
                    (((value 0.55) (parent_dist 0.049999999999999933))
                     ((value 0.62) (parent_dist 0.020000000000000018))
                     ((value 0.6) (parent_dist 0))
                     ((value 0.5) (parent_dist 0.099999999999999978))))
                   (parent
                    (((value 0.6) (parent_dist 0) (radius 0.099999999999999978)
                      (tree <opaque>))
                     <opaque>)))))))
              (parent (((value 0.6) (radius 0.35) (tree <opaque>)) <opaque>)))))))))
       (branching_factor 4) (distance <fun>) (eq <fun>)))) |}]

let%test_unit "" =
  let tree = create abs_dist in
  for _ = 0 to 1000 do
    insert tree (Random.float 1.);
    invariant tree
  done
