module LowParse.Impl.VLBytes.Part4
include LowParse.Spec.VLBytes
open LowParse.Impl.Base

module Seq = FStar.Seq
module S = LowParse.Slice
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module E = FStar.Kremlin.Endianness
module Cast = FStar.Int.Cast

let point_to_vlbytes_contents_correct_precond
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (h: HS.mem)
  (len: bounded_integer sz { f len == true } )
  (b1: S.bslice)
  (b': S.bslice)
: GTot Type0
= parses h (parse_vlbytes_gen sz f p) b (fun _ -> True) /\
  sz <= U32.v (S.length b) /\ (
    let sz' = U32.uint_to_t sz in (
    b1 == S.advanced_slice b sz' /\
    parses h (parse_bounded_integer sz) b (fun (len', _) -> len' == len) /\
    U32.v len <= U32.v (S.length b1) /\
    b' == S.truncated_slice b1 len
  ))

let point_to_vlbytes_contents_postcond
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (h: HS.mem)
  (b': S.bslice)
: GTot Type0
= sz <= U32.v (S.length b) /\ (
  let sz' = U32.uint_to_t sz in
  let b0 = S.truncated_slice b sz' in
  S.is_prefix_gen [b0; b'] b /\
  parses h (parse_vlbytes_gen sz f p) b (fun (v, len) ->
  exactly_parses h p b' (fun v' ->
    U32.v sz' <= U32.v len /\
    S.length b' == U32.sub len sz' /\
    v == v'
  )))

val point_to_vlbytes_contents_correct
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (h: HS.mem)
  (len: bounded_integer sz { f len == true } )
  (b1: S.bslice)
  (b': S.bslice)
: Lemma
  (requires (
    point_to_vlbytes_contents_correct_precond sz f p b h len b1 b'
  ))
  (ensures (
    point_to_vlbytes_contents_postcond sz f p b h b'
  ))
