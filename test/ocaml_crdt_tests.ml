open! Core_kernel
open Ocaml_crdt
open Expect_test_helpers_kernel

let%expect_test "" =
  let p l = print_s [%message "" ~_:(Ordered_list.to_list l : string list)] in
  let l = Ordered_list.init ~node_id:"james" in
  p l;
  [%expect {| () |}];
  let l = Ordered_list.push_front l ~el:"a" in
  p l;
  [%expect {| (a) |}];
  let l = Ordered_list.push_back l ~el:"b" in
  let l = Ordered_list.push_back l ~el:"c" in
  p l;
  [%expect {| (a b c) |}];
  print_s [%sexp (l : string Ordered_list.t)];
  [%expect
    {|
    ((node_id   james)
     (timestamp 4)
     (items (
       ((id (1 james)) (el a))
       ((id (2 james)) (el b))
       ((id (3 james)) (el c))))
     (log ((
       james (
         (Insert (after ((2 james))) (id (3 james)) (el c))
         (Insert (after ((1 james))) (id (2 james)) (el b))
         (Insert (after ()) (id (1 james)) (el a))))))) |}];
  require_does_raise [%here] (fun () -> Ordered_list.merge ~other:l l);
  [%expect {| ("Ordered_list.merge: both lists have the same node_id" (node_id james)) |}]
;;
