open! Base

type 'a t [@@deriving sexp]

val init : node_id:string -> 'a t

(* val insert : 'a t -> i:int -> el:'a -> 'a t *)
val push_front : 'a t -> el:'a -> 'a t
val push_back : 'a t -> el:'a -> 'a t
val merge : other:'a t -> 'a t -> 'a t
val to_list : 'a t -> 'a list
