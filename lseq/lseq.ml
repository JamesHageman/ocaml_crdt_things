open! Core_kernel

type boundary_t =
  | BoundaryPlus
  | BoundaryMinus
[@@deriving sexp]

module ID = struct
  type t = int list [@@deriving sexp, compare]

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
    [%expect
      {|
      ((depth 0) ())
      ((depth 1) (1))
      ((depth 2) (1 2))
      ((depth 3) (1 2 3))
      ((depth 4) (1 2 3 4))
      ((depth 5) (1 2 3 4 0))
      ((depth 6) (1 2 3 4 0 0)) |}]
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
    | Leaf of
        { id : ID.t
        ; el : 'a
        }
    | Branch of
        { id : ID.t
        ; el : 'a
        ; size : int
        ; children : 'a t list
        }
  [@@deriving sexp]

  let rec iter ~f = function
    | Leaf { id; el } -> f (el, id)
    | Branch { id; el; size = _; children } ->
      f (el, id);
      List.iter children ~f:(iter ~f)
  ;;
end

type 'a t =
  { boundary : int
  ; init_size : int
  ; s : (int (* depth *), boundary_t) Hashtbl.t
  ; tree : 'a Tree.t list
  }
[@@deriving sexp_of]

let empty () =
  let init_size = 16 in
  { boundary = 10; init_size; s = Int.Table.create (); tree = [] }
;;

let iter ~f t = List.iter t.tree ~f:(Tree.iter ~f)
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
      "" (depth : int) ~interval:(!interval : int) (step : int) (strategy : boundary_t)];
  match strategy with
  | BoundaryPlus ->
    let add_val = Random.int step + 1 in
    ID.add (ID.prefix ~depth p) add_val
  | BoundaryMinus ->
    let sub_val = Random.int step + 1 in
    ID.add (ID.prefix ~depth q) (-sub_val)
;;

(* TODO *)
let insert_id ~id ~el:_ _t =
  match id with
  | [] -> assert false
  | [ _x ] -> assert false
  | _ :: _xs -> assert false
;;

let insert ~after ~before t el =
  let id = alloc ~p:after ~q:before t in
  print_s [%message "" (id : ID.t)];
  insert_id ~id ~el t
;;

let%expect_test "insert" =
  let l = empty () in
  insert ~after:(front l) ~before:(back l) l "x"
  [@@expect.uncaught_exn
    {|
  (* CR expect_test_collector: This test expectation appears to contain a backtrace.
     This is strongly discouraged as backtraces are fragile.
     Please change this test to not include a backtrace. *)

  (Failure "TODO insert_id")
  Raised at file "stdlib.ml", line 29, characters 17-33
  Called from file "collector/expect_test_collector.ml", line 253, characters 12-19

  Trailing output
  ---------------
  ((depth 1) (interval 14) (step 10)) |}]
;;
