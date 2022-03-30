module type T = sig
  type 'a t

  val create :
    ?branching_factor:int ->
    ?eq:('a -> 'a -> bool) ->
    ('a -> 'a -> float) ->
    'a t

  val iter : 'a t -> 'a Iter.t
  val insert : 'a t -> 'a -> unit
  val range : 'a t -> 'a -> radius:float -> 'a Iter.t
end

module Private = struct
  type 'a obj = {
    value : 'a;
    mutable parent_dist : float;
        [@default Float.nan] [@sexp_drop_default.compare]
    mutable radius : float; [@default 0.] [@sexp_drop_default.compare]
    mutable tree : 'a node option; [@sexp.option]
  }

  and 'a node = {
    is_leaf : bool;
    mutable objects : 'a obj list; [@sexp.list]
    mutable parent : ('a obj * ('a node[@sexp.opaque])) option; [@sexp.option]
  }
  [@@deriving sexp]

  type 'a t = {
    mutable root : 'a node;
    branching_factor : int;
    distance : 'a -> 'a -> float;
    eq : 'a -> 'a -> bool;
  }
  [@@deriving sexp]

  let rec iter_obj obj f =
    match obj.tree with None -> f obj.value | Some node -> iter_node node f

  and iter_node { objects; _ } f = List.iter (fun x -> iter_obj x f) objects

  let iter t f = iter_node t.root f

  let invariant t =
    assert (t.branching_factor > 0);
    let rec node parent this =
      (* every node but the root has a parent *)
      assert (Option.is_some this.parent = Option.is_some parent);

      (* the parent router object points to the current node *)
      (match this.parent with
      | Some ({ tree = Some node; _ }, _) -> assert (node == this)
      | _ -> ());

      (* the parent router object is in the parent node *)
      (match this.parent with
      | Some (parent_obj, x) ->
          assert (List.exists (fun obj -> parent_obj == obj) x.objects)
      | _ -> ());

      if this.is_leaf then
        assert (List.for_all (fun o -> Option.is_none o.tree) this.objects)
      else assert (List.exists (fun o -> Option.is_some o.tree) this.objects);

      (* cached parent distances are correct *)
      List.iter
        (fun obj ->
          Option.iter
            (fun (pobj, _) ->
              let expected = t.distance obj.value pobj.value in
              let actual = obj.parent_dist in
              if expected <> actual then
                failwith
                  (Format.sprintf "expected parent dist %f got %f" expected
                     actual))
            parent)
        this.objects;

      (* router radii are large enough *)
      List.iter
        (fun obj ->
          match obj.tree with
          | None -> ()
          | Some node ->
              iter_node node (fun v ->
                  let d = t.distance obj.value v in
                  if obj.radius < d then failwith "radius too small"))
        this.objects;

      List.iter
        (fun obj ->
          Option.iter (fun tree -> node (Some (obj, this)) tree) obj.tree)
        this.objects
    in
    node None t.root

  let create ?(branching_factor = 32) ?eq distance =
    let eq =
      match eq with Some f -> f | None -> fun v v' -> distance v v' = 0.
    in
    {
      root = { is_leaf = true; objects = []; parent = None };
      distance;
      branching_factor;
      eq;
    }

  let mk_obj ?(parent_dist = Float.nan) ?(radius = 0.) ?(tree = None) v =
    { value = v; parent_dist; radius; tree }

  let set_parent p = Option.iter (fun n -> n.parent <- Some p)

  let set_covering_radius r =
    match r.tree with
    | None -> ()
    | Some node ->
        r.radius <-
          List.fold_left
            (fun r obj -> max r (obj.parent_dist +. obj.radius))
            0. node.objects

  let mk_node ?parent objects =
    let node =
      {
        is_leaf = List.for_all (fun o -> Option.is_none o.tree) objects;
        objects;
        parent;
      }
    in
    List.iter
      (fun router ->
        set_parent (router, node) router.tree;
        set_covering_radius router)
      objects;
    node

  let[@inline] is_leaf x = x.is_leaf

  let promote entries =
    let ret = Iter.sample 2 @@ Iter.of_list entries in
    let r = ret.(0) and r' = ret.(1) in
    (mk_obj r.value, mk_obj r'.value)

  let partition distance (r : 'a obj) (r' : 'a obj) objs =
    let l, l' =
      List.partition_map
        (fun v ->
          let left_dist = distance v.value r.value in
          let right_dist = distance v.value r'.value in
          let left_closer = left_dist <= right_dist in
          v.parent_dist <- (if left_closer then left_dist else right_dist);
          if left_closer then Left v else Right v)
        objs
    in
    r.tree <- Some (mk_node l);
    r'.tree <- Some (mk_node l')

  let rec split t split_node v =
    let entries = v :: split_node.objects in
    let r, r' = promote entries in
    partition t.distance r r' entries;

    match split_node.parent with
    | Some (parent_router, parent_node) ->
        let gparent_dist v =
          match parent_node.parent with
          | Some (gparent_router, _) -> t.distance gparent_router.value v
          | None -> Float.nan
        in

        (* replace this node's router with one of the new routers *)
        parent_node.objects <-
          List.map
            (fun r_old ->
              if t.eq r_old.value parent_router.value then r else r_old)
            parent_node.objects;

        (* the new router is going in the parent, so its new parent is the grandparent *)
        r.parent_dist <- gparent_dist r.value;
        set_parent (r, parent_node) r.tree;
        set_covering_radius r;

        (* insert the other router if possible, otherwise split *)
        if List.length parent_node.objects < t.branching_factor then (
          parent_node.objects <- r' :: parent_node.objects;
          r'.parent_dist <- gparent_dist r'.value;
          set_parent (r', parent_node) r'.tree;
          set_covering_radius r')
        else split t parent_node r'
    | None ->
        (* the split node was the root, so create a new root *)
        r.parent_dist <- Float.nan;
        r'.parent_dist <- Float.nan;
        set_covering_radius r;
        set_covering_radius r';
        let root = mk_node [ r; r' ] in
        t.root <- root

  let insert t v =
    let rec insert_node parent_dist node =
      if is_leaf node then
        (* insert into leaf node *)
        if List.length node.objects < t.branching_factor then
          let obj = { value = v; parent_dist; tree = None; radius = 0. } in
          node.objects <- obj :: node.objects
        else
          (* split full leaf node *)
          split t node
            { value = v; parent_dist = Float.nan; radius = 0.; tree = None }
      else
        (* find the closest router that would not need a radius increase *)
        let closest_covering =
          Iter.of_list node.objects
          (* use triangle inequality to filter noncovering routers *)
          |> Iter.filter (fun r ->
                 Float.is_nan parent_dist || Float.is_nan r.parent_dist
                 || Float.abs (parent_dist -. r.parent_dist) <= r.radius)
          |> Iter.map (fun r -> (t.distance r.value v, r))
          (* check that router can cover the new point *)
          |> Iter.filter (fun (d, r) -> d <= r.radius)
          |> Iter.min ~lt:(fun (d, _) (d', _) -> d < d')
        in
        let dist, obj =
          match closest_covering with
          | Some (d, r) -> (d, r)
          | None ->
              (* no router covers the new point, so minimize the increase in covering radius *)
              let dist, obj =
                Iter.of_list node.objects
                |> Iter.map (fun r -> (t.distance r.value v, r))
                |> Iter.min_exn ~lt:(fun (d, r) (d', r') ->
                       d -. r.radius < d' -. r'.radius)
              in
              obj.radius <- dist;
              (dist, obj)
        in
        match obj.tree with
        | Some node -> insert_node dist node
        | None -> assert false
    in
    insert_node Float.nan t.root

  let range t v ~radius f =
    let rec range_node query_parent_dist x =
      List.iter
        (fun obj ->
          if
            Float.is_nan obj.parent_dist
            || Float.is_nan query_parent_dist
            || Float.abs (query_parent_dist -. obj.parent_dist)
               <= radius +. obj.radius
          then
            let query_dist = t.distance obj.value v in
            if query_dist <= radius +. obj.radius then
              match obj.tree with
              | None -> f obj.value
              | Some node -> range_node query_dist node)
        x.objects
    in
    range_node Float.nan t.root
end

include Private
