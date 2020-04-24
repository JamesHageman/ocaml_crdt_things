open! Core_kernel

module ID : sig
  type t [@@deriving sexp, compare]
end

type 'a t [@@deriving sexp_of]

val empty : unit -> 'a t
val iter : f:('a * ID.t -> unit) -> 'a t -> unit
val front : 'a t -> ID.t
val back : 'a t -> ID.t
val insert : after:ID.t -> before:ID.t -> 'a t -> 'a -> ID.t
