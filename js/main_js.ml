open! Core_kernel
open! Incr_dom
open! Async_kernel

module App = struct
  module Model = struct
    type t = { count : int } [@@deriving compare, equal, sexp]

    let cutoff t1 t2 = equal t1 t2
  end

  module State = struct
    type t = unit
  end

  module Action = struct
    type t =
      | Increment
      | Decrement
    [@@deriving sexp]
  end

  let initial_model = { Model.count = 0 }

  let create
      (model : Model.t Incr.t)
      ~old_model:(_ : Model.t Incr.t)
      ~(inject : Action.t -> Virtual_dom.Vdom.Event.t)
    =
    let open Incr.Let_syntax in
    let%map apply_action =
      let%map (model : Model.t) = model in
      fun action _state ~schedule_action:_ ->
        match (action : Action.t) with
        | Increment -> { Model.count = model.count + 1 }
        | Decrement -> { Model.count = model.count - 1 }
    and view =
      let open Virtual_dom.Vdom in
      let%map model = model in
      Node.div
        []
        [ Node.button
            [ Attr.on_click (fun _ev -> inject Action.Decrement) ]
            [ Node.text "-" ]
        ; Node.text (Int.to_string model.count)
        ; Node.button
            [ Attr.on_click (fun _ev -> inject Action.Increment) ]
            [ Node.text "+" ]
        ]
    and model = model in
    Component.create ~apply_action model view
  ;;

  let on_startup ~schedule_action:_ _model = Deferred.unit
end

let () =
  Start_app.start
    (module App)
    ~bind_to_element_with_id:"app"
    ~initial_model:App.initial_model
;;
