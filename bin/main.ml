open! Base

let () =
  let l = Ocaml_crdt.Ordered_list.init ~node_id:"james" in
  Stdio.print_s [%message "Hello" ~_:(l : string Ocaml_crdt.Ordered_list.t)]
;;
