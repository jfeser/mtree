module type T = sig
  type 'a t

  val create :
    ?branching_factor:int ->
    ?eq:('a -> 'a -> bool) ->
    ('a -> 'a -> float) ->
    'a t
  (** Create an M-tree.
    @param branching_factor The branching factor of the tree (default: 32).
    @param eq An optional equality function for tree elements. If none is provided, then the distance function will be used.
    @param distance {{: https://en.wikipedia.org/wiki/Metric_(mathematics)}Distance metric} between tree elements. *)

  val iter : 'a t -> 'a Iter.t
  (** Iterate over the contents of the tree. *)

  val insert : 'a t -> 'a -> unit
  (** Insert a new point into the tree. *)

  val range : 'a t -> 'a -> radius:float -> 'a Iter.t
  (** Find all points that are within some radius of a query point. *)
end

include T
(** @inline *)

module Private : sig
  type 'a obj = {
    value : 'a;
    mutable parent_dist : float;
    mutable radius : float;
    mutable tree : 'a node option;
  }

  and 'a node = {
    is_leaf : bool;
    mutable objects : 'a obj list;
    mutable parent : ('a obj * 'a node) option;
  }

  type 'a t = {
    mutable root : 'a node;
    branching_factor : int;
    distance : 'a -> 'a -> float;
    eq : 'a -> 'a -> bool;
  }

  include T with type 'a t := 'a t

  val invariant : 'a t -> unit

  val mk_obj :
    ?parent_dist:float -> ?radius:float -> ?tree:'a node option -> 'a -> 'a obj

  val promote : 'a obj list -> 'a obj * 'a obj
  val partition : ('a -> 'a -> float) -> 'a obj -> 'a obj -> 'a obj list -> unit
  val split : 'a t -> 'a node -> 'a obj -> unit
  val iter_obj : 'a obj -> 'a Iter.t
  val iter_node : 'a node -> 'a Iter.t
end
