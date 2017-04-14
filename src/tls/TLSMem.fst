module TLSMem
include FStar.Heap
include FStar.HyperHeap
include FStar.HyperStack
include FStar.ST
include FStar.All

let hh_as_ref = HyperHeap.as_ref
