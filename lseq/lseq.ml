open! Core_kernel

type boundary_t =
  | BoundaryPlus
  | BoundaryMinus
[@@deriving sexp]

module ID : sig
  module Elt : sig
    (* TODO change this to (int, string) to support multiple participants *)
    type t = int [@@deriving sexp, compare, equal]
  end

  type t = Elt.t list [@@deriving sexp, compare]

  include Invariant.S with type t := t

  val add : t -> int -> t
  val sub : t -> int -> t
  val diff : lo:t -> hi:t -> int
  val prefix : depth:int -> t -> t
  val max_id : depth:int -> t
  val min_id : depth:int -> t
end = struct
  module Elt = struct
    type t = int [@@deriving sexp, compare, equal]
  end

  type t = Elt.t list [@@deriving sexp, compare]

  let base depth =
    assert (depth > 0);
    16 lsl (depth - 1)
  ;;

  let invariant t =
    Invariant.invariant [%here] t [%sexp_of: t] (fun () ->
        List.iteri t ~f:(fun i el ->
            let depth = i + 1 in
            assert (0 <= el && el < base depth)))
  ;;

  let%expect_test "base" =
    for depth = 1 to 10 do
      print_s [%sexp (base depth : int)]
    done;
    ();
    [%expect
      {|
      16
      32
      64
      128
      256
      512
      1024
      2048
      4096
      8192 |}]
  ;;

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
    for depth = 1 to 6 do
      print_s [%message "" (depth : int) ~_:(prefix ~depth id : t)]
    done;
    [%expect
      {|
      ((depth 1) (1))
      ((depth 2) (1 2))
      ((depth 3) (1 2 3))
      ((depth 4) (1 2 3 4))
      ((depth 5) (1 2 3 4 0))
      ((depth 6) (1 2 3 4 0 0)) |}]
  ;;

  let%expect_test "compare" =
    let l = [ [ 1 ]; [ 1; 0 ]; [ 1; 0; 1 ]; [ 1; 1; 0 ]; [ 2 ] ] |> List.sort ~compare in
    print_s [%sexp (l : t list)];
    [%expect {| ((1) (1 0) (1 0 1) (1 1 0) (2)) |}]
  ;;

  let rec add id x : t =
    match Ordering.of_int (Int.compare x 0) with
    | Less -> sub id (-x)
    | Equal -> id
    | Greater ->
      let arr = List.to_array id in
      let depth = Array.length arr in
      assert (depth > 0);
      let new_last = Array.last arr + x in
      assert (new_last > 0) (* don't allow actual int overflow *);
      if new_last >= base depth
      then (
        if depth = 1 then raise_s [%message "ID.add: overflow" (id : t) (x : int)];
        (* handle overflow *)
        add (prefix ~depth (add (prefix id ~depth:(depth - 1)) 1)) (new_last - base depth))
      else (
        arr.(depth - 1) <- new_last;
        Array.to_list arr)

  and sub id x : t =
    match Ordering.of_int (Int.compare x 0) with
    | Less -> add id (-x)
    | Equal -> id
    | Greater ->
      let arr = List.to_array id in
      let depth = Array.length arr in
      assert (depth > 0);
      let new_last = Array.last arr - x in
      if new_last < 0
      then (
        if depth = 1 then raise_s [%message "ID.sub id x: underflow" (id : t) (x : int)];
        (* handle underflow *)
        add (prefix ~depth (sub (prefix ~depth:(depth - 1) id) 1)) (base depth + new_last))
      else (
        arr.(depth - 1) <- new_last;
        Array.to_list arr)
  ;;

  let%expect_test "add" =
    let open Expect_test_helpers_kernel in
    let p_add l x =
      invariant l;
      let l' = add l x in
      invariant l';
      (match Ordering.of_int (Int.compare x 0) with
      | Less -> assert (Ordering.equal (Ordering.of_int (compare l' l)) Ordering.Less)
      | Greater -> assert (Ordering.equal (Ordering.of_int (compare l l')) Ordering.Less)
      | Equal -> assert (compare l l' = 0));
      print_s [%sexp (l' : t)];
      assert (compare l' (sub l (-x)) = 0)
    in
    p_add [ 1; 2; 3 ] 1;
    [%expect {| (1 2 4) |}];
    p_add [ 1; 31 ] 1;
    [%expect {| (2 0) |}];
    p_add [ 1; 31; 63 ] 1;
    [%expect {| (2 0 0) |}];
    p_add [ 1; 2; 3 ] (-1);
    [%expect {| (1 2 2) |}];
    p_add [ 1; 2; 3 ] (-3);
    [%expect {| (1 2 0) |}];
    p_add [ 1; 2; 3 ] (-4);
    [%expect {| (1 1 63) |}];
    p_add [ 2; 0; 0 ] (-1);
    [%expect {| (1 31 63) |}];
    require_does_raise [%here] (fun () -> p_add [ 15; 31; 63 ] 1);
    [%expect {| ("ID.add: overflow" (id (15)) (x 1)) |}];
    require_does_raise [%here] (fun () -> p_add [ 0; 0; 0 ] (-1));
    [%expect {| ("ID.sub id x: underflow" (id (0)) (x 1)) |}];
    ()
  ;;

  let depth t = List.length t

  let rec diff ~lo ~hi =
    if depth lo <> depth hi
    then
      raise_s [%message "ID.diff ~lo ~hi: ids must have the same depth" (lo : t) (hi : t)];
    match Ordering.of_int (compare lo hi) with
    | Greater -> -diff ~lo:hi ~hi:lo
    | Equal -> 0
    | Less ->
      let diff_list = List.map2_exn lo hi ~f:(fun lo hi -> hi - lo) in
      let depth = depth diff_list in
      diff_list
      |> List.fold_right ~init:(1, 0, 0) ~f:(fun x (mult, sum, i) ->
             mult * base (depth - i), sum + (x * mult), i + 1)
      |> fun (_, sum, _) -> sum
  ;;

  let%expect_test "diff" =
    let open Expect_test_helpers_kernel in
    [ [ 1 ], [ 2 ]
    ; [ 1; 0 ], [ 2; 0 ]
    ; [ 1; 3 ], [ 2; 0 ]
    ; [ 2; 0 ], [ 1; 0 ]
    ; [ 1; 0; 0 ], [ 2; 0; 0 ]
    ; [ 1; 0; 0 ], sub [ 2; 0; 0 ] 1
    ; [ 1; 0; 0; 0 ], sub [ 2; 0; 0; 0 ] 128
    ]
    |> List.iter ~f:(fun (lo, hi) ->
           let diff = diff ~lo ~hi in
           printf
             !"diff ~lo:%{sexp:t} ~hi:%{sexp:t} = %d\n"
             (lo : t)
             (hi : t)
             (diff : int);
           require_does_not_raise [%here] (fun () ->
               assert (compare hi (add lo diff) = 0)));
    [%expect
      {|
      diff ~lo:(1) ~hi:(2) = 1
      diff ~lo:(1 0) ~hi:(2 0) = 32
      diff ~lo:(1 3) ~hi:(2 0) = 29
      diff ~lo:(2 0) ~hi:(1 0) = -32
      diff ~lo:(1 0 0) ~hi:(2 0 0) = 2048
      diff ~lo:(1 0 0) ~hi:(1 31 63) = 2047
      diff ~lo:(1 0 0 0) ~hi:(1 31 63 0) = 262016 |}];
    require_does_raise [%here] (fun () -> diff ~lo:[ 1 ] ~hi:[ 1; 0 ]);
    [%expect {| ("ID.diff ~lo ~hi: ids must have the same depth" (lo (1)) (hi (1 0))) |}]
  ;;

  let max_id ~depth : t = List.init depth ~f:(fun i -> base (i + 1) - 1)
  let min_id ~depth : t = List.init depth ~f:(const 0)
end

module Elt = struct
  type 'a t =
    { id : ID.t
    ; value : 'a
    }
  [@@deriving fields]
end

module Tree = struct
  type 'a t =
    { id : ID.Elt.t
    ; el : 'a
    ; children : 'a t Doubly_linked.t
    }
  [@@deriving sexp, fields]

  let rec iter_id ~f { id; el; children } =
    f [ id ] el;
    Doubly_linked.iter children ~f:(fun tree ->
        iter_id ~f:(fun id' el -> f (id :: id') el) tree)
  ;;

  let iter ~f t = iter_id ~f:(fun _id el -> f el) t

  let rec insert (ts : 'a t Doubly_linked.t) ~(id : ID.t) ~(el : 'a) =
    let new_tree id el = { id; el; children = Doubly_linked.create () } in
    match id with
    | [] -> assert false
    | [ (x : ID.Elt.t) ] ->
      let after =
        Doubly_linked.find_elt ts ~f:(fun tree -> ID.Elt.compare tree.id x >= 0)
      in
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
    | x :: xs ->
      (match Doubly_linked.find ts ~f:(fun tree -> ID.Elt.compare tree.id x = 0) with
      | None -> assert false
      | Some tree -> insert tree.children ~id:xs ~el)
  ;;

  let next (ts : 'a t Doubly_linked.t) { Elt.id; value } =
    match id with
    | [] -> assert false
    | [ x ] -> failwith "tODO next non-rec"
    | x :: xs -> failwith "TODO next recursive"
  ;;

  let prev (ts : 'a t Doubly_linked.t) { Elt.id; value } = failwith "TODO prev"
end

type 'a t =
  { boundary : int
  ; rng : (Random.State.t[@sexp.opaque])
  ; s : (int (* depth *), boundary_t) Hashtbl.t
  ; tree : 'a Tree.t Doubly_linked.t
  }
[@@deriving sexp_of]

let create ?(rng = Random.State.default) ?(boundary = 10) () =
  { boundary; rng; s = Int.Table.create (); tree = Doubly_linked.create () }
;;

let iteri ~f t =
  let i = ref 0 in
  Doubly_linked.iter
    t.tree
    ~f:
      (Tree.iter ~f:(fun x ->
           f !i x;
           incr i))
;;

let iter ~f t = Doubly_linked.iter t.tree ~f:(Tree.iter ~f)
let iter_id ~f t = Doubly_linked.iter t.tree ~f:(Tree.iter_id ~f)
let front : ID.t = ID.min_id ~depth:1
let back : ID.t = ID.max_id ~depth:1

(* https://hal.archives-ouvertes.fr/hal-00921633/document *)
let alloc ~p ~q ~s ~rng ~boundary : ID.t =
  let depth = ref 0 in
  let interval = ref 0 in
  while !interval < 1 do
    incr depth;
    let depth = !depth in
    interval := ID.diff ~lo:(ID.prefix ~depth p) ~hi:(ID.prefix ~depth q) - 1
  done;
  let step = Int.min boundary !interval in
  let depth = !depth in
  let strategy =
    Hashtbl.find_or_add s depth ~default:(fun () ->
        match Random.State.bool rng with
        | true -> BoundaryPlus
        | false -> BoundaryMinus)
  in
  match strategy with
  | BoundaryPlus ->
    let add_val = Random.State.int rng step + 1 in
    ID.add (ID.prefix ~depth p) add_val
  | BoundaryMinus ->
    let sub_val = Random.State.int rng step + 1 in
    ID.sub (ID.prefix ~depth q) sub_val
;;

let%expect_test "alloc" =
  let rng = Random.State.make [||] in
  let s = Int.Table.create () in
  let boundary = 10 in
  let id = alloc ~p:[ 14 ] ~q:[ 15 ] ~rng ~s ~boundary in
  print_s [%sexp (id : ID.t)];
  [%expect {| (14 1) |}];
  let rng = Random.State.make [| 2 |] in
  let id = alloc ~p:[ 0; 10 ] ~q:[ 0; 11 ] ~rng ~s ~boundary in
  print_s [%sexp (id : ID.t)];
  [%expect {| (0 10 61) |}];
  [%expect {||}];
  ()
;;

let insert_between ~(after : ID.t) ~before (t : 'a t) (value : 'a) =
  let { rng; s; boundary; _ } = t in
  let id = alloc ~p:after ~q:before ~rng ~s ~boundary in
  Tree.insert t.tree ~id ~el:value;
  { Elt.id; value }
;;

let next t elt = Tree.next t.tree elt
let prev t elt = Tree.prev t.tree elt

let first_elt t =
  Doubly_linked.first t.tree
  |> Option.map ~f:(fun { Tree.id; el; _ } -> { Elt.id = [ id ]; value = el })
;;

let last_elt t =
  let rec last_rec ts =
    match Doubly_linked.last ts with
    | None -> None
    | Some { Tree.id; el; children; _ } ->
      (match last_rec children with
      | None -> Some { Elt.id = [ id ]; value = el }
      | Some { Elt.id = id'; value } -> Some { id = id :: id'; value })
  in
  last_rec t.tree
;;

let insert_first t el =
  let after = front in
  let before = Option.value_map (first_elt t) ~f:Elt.id ~default:back in
  insert_between ~after ~before t el
;;

let insert_before t (elt : _ Elt.t) el =
  let after = Option.value_map (prev t elt) ~f:Elt.id ~default:front in
  let before = elt.id in
  insert_between ~after ~before t el
;;

let insert_after t (elt : _ Elt.t) el =
  let before = Option.value_map (next t elt) ~f:Elt.id ~default:back in
  insert_between ~after:elt.Elt.id ~before t el
;;

let insert_last t el =
  let after = Option.value_map (last_elt t) ~f:Elt.id ~default:front in
  let before = back in
  insert_between ~after ~before t el
;;

let to_list t =
  let ret = ref [] in
  iter t ~f:(fun el -> ret := el :: !ret);
  List.rev !ret
;;

let to_alist t =
  let ret = ref [] in
  iter_id t ~f:(fun id el -> ret := (id, el) :: !ret);
  List.rev !ret
;;

open Expect_test_helpers_kernel

let p t = print_s [%sexp (t : string t)]

let pp t =
  let l = t |> to_alist |> List.map ~f:(fun (id, el) -> el, id) in
  print_s [%sexp (l : (string * ID.t) list)]
;;

let%expect_test "insert" =
  let l = create () in
  let elt = insert_first l "x" in
  [%expect {| |}];
  p l;
  [%expect
    {|
    ((boundary 10)
     (rng      <opaque>)
     (s ((1 BoundaryPlus)))
     (tree ((
       (id 3)
       (el x)
       (children ()))))) |}];
  pp l;
  [%expect {| ((x (3))) |}];
  let _elt = insert_after l elt "y" in
  p l;
  [%expect
    {|
    ((boundary 10)
     (rng      <opaque>)
     (s ((1 BoundaryPlus)))
     (tree (
       ((id 3)  (el x) (children ()))
       ((id 12) (el y) (children ()))))) |}];
  pp l;
  [%expect {|
    ((x (3))
     (y (12))) |}]
;;

let%expect_test "big insert" =
  (* mass insertion at the back *)
  let l = create ~rng:(Random.State.make [||]) () in
  (List.init 48 ~f:Int.to_string : string list)
  |> List.iter ~f:(fun x ->
         let (_ : _ Elt.t) = insert_last l x in
         ());
  [%expect {||}];
  p l;
  [%expect
    {|
    ((boundary 10)
     (rng      <opaque>)
     (s (
       (1 BoundaryPlus)
       (2 BoundaryPlus)
       (3 BoundaryMinus)
       (4 BoundaryMinus)
       (5 BoundaryPlus)))
     (tree (
       ((id 1)  (el 0) (children ()))
       ((id 6)  (el 1) (children ()))
       ((id 7)  (el 2) (children ()))
       ((id 10) (el 3) (children ()))
       ((id 14)
        (el 4)
        (children (
          ((id 3)  (el 5)  (children ()))
          ((id 8)  (el 6)  (children ()))
          ((id 16) (el 7)  (children ()))
          ((id 25) (el 8)  (children ()))
          ((id 27) (el 9)  (children ()))
          ((id 30) (el 10) (children ()))
          ((id 31)
           (el 11)
           (children (
             ((id 55)
              (el 12)
              (children ()))
             ((id 63)
              (el 13)
              (children (
                ((id 121) (el 14) (children ()))
                ((id 123) (el 15) (children ()))
                ((id 126) (el 16) (children ()))
                ((id 127)
                 (el 17)
                 (children (
                   ((id 2)   (el 18) (children ()))
                   ((id 11)  (el 19) (children ()))
                   ((id 20)  (el 20) (children ()))
                   ((id 29)  (el 21) (children ()))
                   ((id 31)  (el 22) (children ()))
                   ((id 33)  (el 23) (children ()))
                   ((id 34)  (el 24) (children ()))
                   ((id 35)  (el 25) (children ()))
                   ((id 37)  (el 26) (children ()))
                   ((id 47)  (el 27) (children ()))
                   ((id 56)  (el 28) (children ()))
                   ((id 61)  (el 29) (children ()))
                   ((id 70)  (el 30) (children ()))
                   ((id 78)  (el 31) (children ()))
                   ((id 84)  (el 32) (children ()))
                   ((id 87)  (el 33) (children ()))
                   ((id 95)  (el 34) (children ()))
                   ((id 105) (el 35) (children ()))
                   ((id 106) (el 36) (children ()))
                   ((id 108) (el 37) (children ()))
                   ((id 115) (el 38) (children ()))
                   ((id 120) (el 39) (children ()))
                   ((id 123) (el 40) (children ()))
                   ((id 124) (el 41) (children ()))
                   ((id 130) (el 42) (children ()))
                   ((id 134) (el 43) (children ()))
                   ((id 136) (el 44) (children ()))
                   ((id 137) (el 45) (children ()))
                   ((id 144) (el 46) (children ()))
                   ((id 153) (el 47) (children ()))))))))))))))))) |}]
;;
