module TLSMem
include FStar.Heap
include FStar.HyperHeap
include FStar.HyperStack
include FStar.ST
include FStar.All

let hh_as_ref = HyperHeap.as_ref

(* TODO:
 - regions from Parse
 - colors: replace with stateful operator giving a fresh color
*)

assume val fresh_color: unit -> ST color (requires (fun h -> True)) (ensures (fun h c h1 -> c not in h /\ c in h1)) // TODO: implement

private
let tls_color_epoch_color_hs_color =
  let t = fresh_color () in
  let e = fresh_color () in
  let h = fresh_color () in
  (t, e, h)

let tls_color = let (t, _, _) = tls_color_epoch_color_hs_color in t
