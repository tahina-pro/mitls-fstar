module TLSMem
include FStar.Heap
include FStar.HyperHeap
include FStar.HyperStack
include FStar.ST
include FStar.All

module MR = FStar.Monotonic.RRef
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

let hh_as_ref = HyperHeap.as_ref
let hh_modifies = HyperHeap.modifies
let hh_modifies_one = HyperHeap.modifies_one

let hs_modifies_0
  (r: HH.rid)
  (h0 h1: HS.mem)
: Tot Type0
= HS.modifies_one r h0 h1 /\
  HH.modifies_rref r !{} (HS.HS?.h h0) (HS.HS?.h h1)

let m_rref_modifies_1
  (r: MR.rid)
  (#a:Type)
  (#b: MR.reln a)
  (ctr: MR.m_rref r a b)
  (h0 h1: HS.mem)
: Tot Type0
= let ctr_as_href = MR.as_hsref ctr in
  HS.modifies_one r h0 h1 /\
  HH.modifies_rref r !{HS.as_ref ctr_as_href} (HS.HS?.h h0) (HS.HS?.h h1)



(* TODO:
 - regions from Parse
 - colors: replace with stateful operator giving a fresh color
*)
(*
assume val fresh_color: unit -> ST color (requires (fun h -> True)) (ensures (fun h c h1 -> True)) // c `not_in` h /\ c `in` h1)) // TODO: implement

(*
private
let tls_color_epoch_color_hs_color =
  let t = fresh_color () in
  let e = fresh_color () in
  let h = fresh_color () in
  (t, e, h)

let tls_color = let (t, _, _) = tls_color_epoch_color_hs_color in t
