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

  include Comparable.S with type t := t
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

  module T = struct
    type t = Elt.t list [@@deriving sexp, compare]
  end

  include T

  type t = Elt.t list [@@deriving sexp, compare]

  let base (depth : int) =
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

  include Comparable.Make (T)
end

module Elt = struct
  type 'a t =
    { id : ID.t
    ; value : 'a
    }
  [@@deriving fields, sexp]

  let of_tuple (id, value) = { id; value }
end

type 'a t =
  { boundary : int
  ; rng : (Random.State.t[@sexp.opaque])
  ; s : (int (* depth *), boundary_t) Hashtbl.t
  ; mutable tree : 'a ID.Map.t
  }
[@@deriving sexp_of, fields]

let create ?(rng = Random.State.default) ?(boundary = 10) () =
  { boundary; rng; s = Int.Table.create (); tree = ID.Map.empty }
;;

let iteri ~f t =
  let i = ref 0 in
  Map.iter t.tree ~f:(fun x ->
      f !i x;
      incr i)
;;

let iter ~f t = Map.iter t.tree ~f
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
  t.tree <- Map.add_exn t.tree ~key:id ~data:value;
  { Elt.id; value }
;;

let next t elt =
  Map.closest_key t.tree `Greater_than elt.Elt.id |> Option.map ~f:Elt.of_tuple
;;

let prev t elt =
  Map.closest_key t.tree `Less_than elt.Elt.id |> Option.map ~f:Elt.of_tuple
;;

let first_elt t = Map.min_elt t.tree |> Option.map ~f:Elt.of_tuple
let last_elt t = Map.max_elt t.tree |> Option.map ~f:Elt.of_tuple

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

let to_list t = Map.to_alist t.tree |> List.map ~f:snd
let to_alist t = Map.to_alist t.tree
let length t = Map.length t.tree
let is_empty t = Map.is_empty t.tree

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
     (tree (((3) x)))) |}];
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
       ((3)  x)
       ((12) y)))) |}];
  pp l;
  [%expect {|
    ((x (3))
     (y (12))) |}]
;;

let invariant check_a t =
  Invariant.invariant [%here] t [%sexp_of: _ t] (fun () ->
      let check f = Invariant.check_field t f in
      Fields.iter
        ~boundary:(check (fun b -> assert (b > 0)))
        ~rng:(check ignore)
        ~s:(check (Hashtbl.invariant (fun depth -> assert (depth > 0)) ignore))
        ~tree:
          (check (fun tree ->
               assert (Map.invariants tree);
               Map.iteri tree ~f:(fun ~key ~data ->
                   ID.invariant key;
                   check_a data))))
;;

let%expect_test "big insert" =
  (* mass insertion at the back *)
  let l = create ~rng:(Random.State.make [||]) () in
  (List.init 48 ~f:Int.to_string : string list)
  |> List.iter ~f:(fun x -> insert_last l x |> (ignore : _ Elt.t -> unit));
  invariant ignore l;
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
       ((1)  0)
       ((6)  1)
       ((7)  2)
       ((10) 3)
       ((14) 4)
       ((14 3)  5)
       ((14 8)  6)
       ((14 16) 7)
       ((14 25) 8)
       ((14 27) 9)
       ((14 30) 10)
       ((14 31) 11)
       ((14 31 55) 12)
       ((14 31 63) 13)
       ((14 31 63 121) 14)
       ((14 31 63 123) 15)
       ((14 31 63 126) 16)
       ((14 31 63 127) 17)
       ((14 31 63 127 2)   18)
       ((14 31 63 127 11)  19)
       ((14 31 63 127 20)  20)
       ((14 31 63 127 29)  21)
       ((14 31 63 127 31)  22)
       ((14 31 63 127 33)  23)
       ((14 31 63 127 34)  24)
       ((14 31 63 127 35)  25)
       ((14 31 63 127 37)  26)
       ((14 31 63 127 47)  27)
       ((14 31 63 127 56)  28)
       ((14 31 63 127 61)  29)
       ((14 31 63 127 70)  30)
       ((14 31 63 127 78)  31)
       ((14 31 63 127 84)  32)
       ((14 31 63 127 87)  33)
       ((14 31 63 127 95)  34)
       ((14 31 63 127 105) 35)
       ((14 31 63 127 106) 36)
       ((14 31 63 127 108) 37)
       ((14 31 63 127 115) 38)
       ((14 31 63 127 120) 39)
       ((14 31 63 127 123) 40)
       ((14 31 63 127 124) 41)
       ((14 31 63 127 130) 42)
       ((14 31 63 127 134) 43)
       ((14 31 63 127 136) 44)
       ((14 31 63 127 137) 45)
       ((14 31 63 127 144) 46)
       ((14 31 63 127 153) 47)))) |}]
;;

module Op = struct
  type 'a t =
    | Insert_first of 'a
    | Insert_last of 'a
    | Insert_before_idx of int * 'a
    | Insert_after_idx of int * 'a
  [@@deriving sexp, quickcheck]

  let ith_elt_exn t idx =
    let elt =
      first_elt t |> Option.value_exn ~here:[%here] ~message:"ith_elt_exn: empty t" |> ref
    in
    for _ = 1 to idx do
      elt
        := next t !elt
           |> Option.value_exn ~here:[%here] ~message:"ith_elt_exn: index out of range"
    done;
    !elt
  ;;

  let apply_to t op =
    match op with
    | Insert_first x -> insert_first t x |> (ignore : _ Elt.t -> unit)
    | Insert_last x -> insert_last t x |> (ignore : _ Elt.t -> unit)
    | Insert_after_idx (idx, x) ->
      if is_empty t
      then insert_last t x |> (ignore : _ Elt.t -> unit)
      else (
        let idx = idx % length t in
        let elt = ith_elt_exn t idx in
        insert_after t elt x |> (ignore : _ Elt.t -> unit))
    | Insert_before_idx (idx, x) ->
      if is_empty t
      then insert_first t x |> (ignore : _ Elt.t -> unit)
      else (
        let idx = idx % length t in
        let elt = ith_elt_exn t idx in
        insert_before t elt x |> (ignore : _ Elt.t -> unit))
  ;;
end

let quickcheck_generator gen_a =
  let module Q = Quickcheck.Generator in
  let open Quickcheck.Generator.Let_syntax in
  let%bind ops = Q.list (Op.quickcheck_generator gen_a)
  and boundary = Q.small_positive_int in
  let t = create ~boundary () in
  List.iter ops ~f:(Op.apply_to t);
  return t
;;

let%expect_test "length" =
  Quickcheck.test
    ~sexp_of:[%sexp_of: char t]
    (quickcheck_generator quickcheck_generator_char)
    ~f:(fun t -> assert (List.length (to_list t) = length t))
;;

let%expect_test "insert_first" =
  let open Quickcheck.Generator in
  Quickcheck.test
    ~sexp_of:[%sexp_of: char t * char]
    (tuple2 (quickcheck_generator quickcheck_generator_char) quickcheck_generator_char)
    ~f:(fun (t, c) ->
      let before = to_list t in
      let elt = insert_first t c in
      assert (List.equal Char.equal (to_list t) (c :: before));
      assert (Char.(Elt.value elt = c)))
;;

let%expect_test "insert_last" =
  let open Quickcheck.Generator in
  Quickcheck.test
    ~sexp_of:[%sexp_of: char t * char]
    (tuple2 (quickcheck_generator quickcheck_generator_char) quickcheck_generator_char)
    ~f:(fun (t, c) ->
      let before = to_list t in
      let elt = insert_last t c in
      assert (List.equal Char.equal (to_list t) (before @ [ c ]));
      assert (Char.(Elt.value elt = c)))
;;
