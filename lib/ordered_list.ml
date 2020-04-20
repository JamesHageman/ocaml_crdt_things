open! Core_kernel

module Item_id : sig
  type t [@@deriving sexp, compare, equal]

  val create : node_id:string -> idx:int -> t
  val timestamp : t -> int
end = struct
  type t = int * string [@@deriving sexp, compare, equal]

  let create ~node_id ~idx = idx, node_id
  let timestamp (ts, _) = ts
end

module List_item = struct
  type 'a t =
    { id : Item_id.t
    ; el : 'a
    }
  [@@deriving sexp]
end

module Log_entry = struct
  type 'a t =
    | Insert of
        { after : Item_id.t option
        ; id : Item_id.t
        ; el : 'a
        }
  [@@deriving sexp]

  let timestamp t =
    match t with
    | Insert { id; _ } -> Item_id.timestamp id
  ;;
end

type 'a t =
  { node_id : string
  ; (* a Lamport Timestamp [https://en.wikipedia.org/wiki/Lamport_timestamps] *)
    timestamp : int
  ; items : 'a List_item.t list
  ; log : 'a Log_entry.t list String.Map.t
  }
[@@deriving sexp]

let init ~node_id = { node_id; timestamp = 1; items = []; log = String.Map.empty }

let add_log_entry ~log_entry ~log ~node_id =
  String.Map.update log node_id ~f:(function
      | None -> [ log_entry ]
      | Some entries -> log_entry :: entries)
;;

let push_front { node_id; timestamp; items; log } ~el =
  let item_id = Item_id.create ~node_id ~idx:timestamp in
  let log_entry = Log_entry.Insert { after = None; id = item_id; el } in
  { node_id
  ; timestamp = timestamp + 1
  ; items = { id = item_id; el } :: items
  ; log = add_log_entry ~log_entry ~log ~node_id
  }
;;

let push_back { node_id; timestamp; items; log } ~el =
  let item_id = Item_id.create ~node_id ~idx:timestamp in
  let after = List.last items |> Option.map ~f:(fun item -> item.id) in
  let log_entry = Log_entry.Insert { after; id = item_id; el } in
  { node_id
  ; timestamp = timestamp + 1
  ; items = items @ [ { id = item_id; el } ]
  ; log = add_log_entry ~log_entry ~log ~node_id
  }
;;

let apply_log_entry log_entry items =
  let rec sift_right items =
    match items with
    | [] -> []
    | [ x ] -> [ x ]
    | (x : _ List_item.t) :: y :: xs ->
      if Item_id.compare x.id y.id < 0 then y :: sift_right (x :: xs) else x :: y :: xs
  in
  match (log_entry : _ Log_entry.t) with
  | Insert { after; id; el } ->
    (match after with
    | None -> sift_right ({ List_item.id; el } :: items)
    | Some after_id ->
      if not (List.exists items ~f:(fun item -> Item_id.equal item.id after_id))
      then
        Error.raise
          (Error.of_string
             (sprintf
                !"Ordered_list.apply_log_entry: trying to insert item after id \
                  %{sexp:Item_id.t}, which is not present in the list"
                after_id));
      List.fold_right items ~init:[] ~f:(fun item new_items ->
          if Item_id.equal item.id after_id
          then item :: sift_right ({ id; el } :: new_items)
          else item :: new_items))
;;

let%expect_test "apply_log_entry" =
  let open Expect_test_helpers_kernel in
  let items : string List_item.t list =
    [ { id = Item_id.create ~idx:1 ~node_id:"a"; el = "a" }
    ; { id = Item_id.create ~idx:2 ~node_id:"a"; el = "b" }
    ; { id = Item_id.create ~idx:3 ~node_id:"a"; el = "c" }
    ]
  in
  print_s [%sexp (items : string List_item.t list)];
  [%expect
    {|
    (((id (1 a)) (el a))
     ((id (2 a)) (el b))
     ((id (3 a)) (el c))) |}];
  (* after = None (insertion at the front) *)
  let items' =
    apply_log_entry
      (Insert { after = None; id = Item_id.create ~idx:1 ~node_id:"b"; el = "x" })
      items
  in
  print_s [%sexp (items' : string List_item.t list)];
  [%expect
    {|
    (((id (1 b)) (el x))
     ((id (1 a)) (el a))
     ((id (2 a)) (el b))
     ((id (3 a)) (el c))) |}];
  (* after = id', id' > id *)
  let items' =
    apply_log_entry
      (Insert
         { after = Some (Item_id.create ~idx:2 ~node_id:"a")
         ; id = Item_id.create ~idx:1 ~node_id:"b"
         ; el = "x"
         })
      items
  in
  print_s [%sexp (items' : string List_item.t list)];
  [%expect
    {|
    (((id (1 a)) (el a))
     ((id (2 a)) (el b))
     ((id (3 a)) (el c))
     ((id (1 b)) (el x))) |}];
  (* after = id', id' < id *)
  let items' =
    apply_log_entry
      (Insert
         { after = Some (Item_id.create ~idx:2 ~node_id:"a")
         ; id = Item_id.create ~idx:4 ~node_id:"b"
         ; el = "x"
         })
      items
  in
  print_s [%sexp (items' : string List_item.t list)];
  [%expect
    {|
    (((id (1 a)) (el a))
     ((id (2 a)) (el b))
     ((id (4 b)) (el x))
     ((id (3 a)) (el c))) |}];
  [%expect {||}]
;;

let merge ~other self =
  if String.(other.node_id = self.node_id)
  then
    raise_s
      [%message
        "Ordered_list.merge: both lists have the same node_id"
          ~node_id:(self.node_id : string)];
  let items = ref self.items in
  let apply_log log items =
    let new_items = List.fold_right log ~init:items ~f:apply_log_entry in
    new_items
  in
  let new_log =
    String.Map.merge self.log other.log ~f:(fun ~key:_ ->
      function
      | `Left log -> Some log
      | `Right log ->
        items := apply_log log !items;
        Some log
      | `Both (_my_log, _their_log) -> failwith "todo merging logs")
  in
  let new_timestamp : int =
    new_log
    |> Map.to_alist
    |> List.map ~f:snd
    |> List.filter_map ~f:List.hd
    |> List.map ~f:Log_entry.timestamp
    |> List.max_elt ~compare:Int.compare
    |> Option.value ~default:self.timestamp
  in
  { self with items = !items; log = new_log; timestamp = new_timestamp }
;;

let to_list { items; _ } = List.map items ~f:(fun items -> items.el)
