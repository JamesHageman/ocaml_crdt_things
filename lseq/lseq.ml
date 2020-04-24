open! Core_kernel

type boundary_t =
  | BoundaryPlus
  | BoundaryMinus
[@@deriving sexp]

module ID = struct
  module Elt = struct
    type t = int [@@deriving sexp, compare, equal]
  end

  type t = Elt.t list [@@deriving sexp, compare]

  let prefix ~depth t : t =
    let len = List.length t in
    assert (len > 0);
    assert (depth > 0);
    if depth <= len
    then List.take t depth
    else List.append t (List.init (depth - len) ~f:(const 0))
  ;;

  let%expect_test "prefix" =
    let id = [ 1; 2; 3; 4 ] in
    for depth = 0 to 6 do
      print_s [%message "" (depth : int) ~_:(prefix ~depth id : t)]
    done;
    [%expect.unreachable]
    [@@expect.uncaught_exn
      {|
    (* CR expect_test_collector: This test expectation appears to contain a backtrace.
       This is strongly discouraged as backtraces are fragile.
       Please change this test to not include a backtrace. *)

    "Assert_failure lseq/lseq.ml:18:4"
    Raised at file "lseq/lseq.ml", line 18, characters 4-22
    Called from file "lseq/lseq.ml", line 27, characters 45-61
    Called from file "collector/expect_test_collector.ml", line 253, characters 12-19 |}]
  ;;

  let add id x : t =
    let len = List.length id in
    assert (len > 0);
    List.mapi id ~f:(fun i y -> if i < len - 1 then y else y + x)
  ;;

  let%expect_test "add" =
    let l = [ 1; 2; 3 ] in
    print_s [%sexp (add l 7 : t)];
    [%expect {| (1 2 10) |}];
    print_s [%sexp (add l (-3) : t)];
    [%expect {| (1 2 0) |}]
  ;;
end

module Tree = struct
  type 'a t =
    { id : ID.Elt.t
    ; el : 'a
    ; size : int
    ; children : 'a t Doubly_linked.t
    }
  [@@deriving sexp, fields]

  let rec iter ~f { id; el; size = _; children } =
    f (el, [ id ]);
    Doubly_linked.iter children ~f:(fun tree ->
        iter ~f:(fun (el, id') -> f (el, id :: id')) tree)
  ;;

  let insert (ts : 'a t Doubly_linked.t) ~(id : ID.t) ~(el : 'a) ~depth =
    assert (depth >= 1);
    let new_tree id el =
      { id; el; size = 16 lsr (depth - 1); children = Doubly_linked.create () }
    in
    match id with
    | [] -> assert false
    | [ (x : ID.Elt.t) ] ->
      let after = Doubly_linked.find_elt ts ~f:(fun tree -> tree.id >= x) in
      (match after with
      | None ->
        let (_ : _ Doubly_linked.Elt.t) = Doubly_linked.insert_last ts (new_tree x el) in
        ()
      | Some tree ->
        if ID.Elt.equal (Doubly_linked.Elt.value tree).id x
        then raise_s [%message "id already exists in tree" (x : ID.Elt.t)]
        else (
          let (_ : _ Doubly_linked.Elt.t) =
            Doubly_linked.insert_before ts tree (new_tree x el)
          in
          ()))
    | _ -> assert false
  ;;
end

type 'a t =
  { boundary : int
  ; init_size : int
  ; s : (int (* depth *), boundary_t) Hashtbl.t
  ; tree : 'a Tree.t Doubly_linked.t
  }
[@@deriving sexp_of]

let empty () =
  let init_size = 16 in
  { boundary = 10; init_size; s = Int.Table.create (); tree = Doubly_linked.create () }
;;

let iter ~f t = Doubly_linked.iter t.tree ~f:(Tree.iter ~f)
let front _ : ID.t = [ 0 ]
let back t : ID.t = [ t.init_size - 1 ]

(* https://hal.archives-ouvertes.fr/hal-00921633/document *)
let alloc ~p ~q t : ID.t =
  let depth = ref 0 in
  let interval = ref 0 in
  while !interval < 1 do
    incr depth;
    let depth = !depth in
    interval
      := List.last_exn (ID.prefix ~depth q) - List.last_exn (ID.prefix ~depth p) - 1
  done;
  let step = Int.min t.boundary !interval in
  let depth = !depth in
  if not (Hashtbl.mem t.s depth)
  then
    Hashtbl.set
      t.s
      ~key:depth
      ~data:
        (match Random.bool () with
        | true -> BoundaryPlus
        | false -> BoundaryMinus);
  let strategy = Hashtbl.find_exn t.s depth in
  print_s
    [%message
      ""
        (p : ID.t)
        (q : ID.t)
        (depth : int)
        ~interval:(!interval : int)
        (step : int)
        (strategy : boundary_t)];
  match strategy with
  | BoundaryPlus ->
    let add_val = Random.int step + 1 in
    ID.add (ID.prefix ~depth p) add_val
  | BoundaryMinus ->
    let sub_val = Random.int step + 1 in
    ID.add (ID.prefix ~depth q) (-sub_val)
;;

let insert ~(after : ID.t) ~before (t : 'a t) (el : 'a) =
  let id = alloc ~p:after ~q:before t in
  Tree.insert t.tree ~id ~el ~depth:1;
  id
;;

let to_list t =
  let ret = ref [] in
  iter t ~f:(fun (el, id) -> ret := (el, id) :: !ret);
  List.rev !ret
;;

let%expect_test "insert" =
  let open Expect_test_helpers_kernel in
  let p t = print_s [%sexp (t : string t)] in
  let pp t = print_s [%sexp (to_list t : (string * ID.t) list)] in
  let l = empty () in
  let _id = insert ~after:(front l) ~before:(back l) l "x" in
  [%expect
    {| ((p (0)) (q (15)) (depth 1) (interval 14) (step 10) (strategy BoundaryPlus)) |}];
  p l;
  [%expect
    {|
    ((boundary  10)
     (init_size 16)
     (s ((1 BoundaryPlus)))
     (tree ((
       (id   3)
       (el   x)
       (size 16)
       (children ()))))) |}];
  pp l;
  [%expect {| ((x (3))) |}]
;;
