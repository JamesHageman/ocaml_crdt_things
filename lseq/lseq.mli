open! Core_kernel

(* wishlist:
 * - write quickcheck property tests
 * - change ID.Elt.t to (int * string)
 * - implement [merge : other:'a t -> 'a t -> unit]
 * *)

module Elt : sig
  type 'a t

  val value : 'a t -> 'a
end

type 'a t [@@deriving sexp_of]

val create : ?rng:Random.State.t -> ?boundary:int (* default 10 *) -> unit -> 'a t

(* insertion *)
val insert_first : 'a t -> 'a -> 'a Elt.t
val insert_last : 'a t -> 'a -> 'a Elt.t
val insert_after : 'a t -> 'a Elt.t -> 'a -> 'a Elt.t
val insert_before : 'a t -> 'a Elt.t -> 'a -> 'a Elt.t

(* traversal *)
val next : 'a t -> 'a Elt.t -> 'a Elt.t option
val prev : 'a t -> 'a Elt.t -> 'a Elt.t option
val first_elt : 'a t -> 'a Elt.t option
val last_elt : 'a t -> 'a Elt.t option

(* accessors *)
val length : 'a t -> int
val iteri : f:(int -> 'a -> unit) -> 'a t -> unit
val iter : f:('a -> unit) -> 'a t -> unit
val to_list : 'a t -> 'a list

include Invariant.S1 with type 'a t := 'a t

val quickcheck_generator : 'a Quickcheck.Generator.t -> 'a t Quickcheck.Generator.t
