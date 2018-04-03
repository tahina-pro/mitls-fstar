module LowParse.Spec.Int
include LowParse.Spec.Combinators

module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

let parse_u8_kind : parser_kind = total_constant_size_parser_kind 1

val parse_u8 (#err: Type0) (e: err): parser parse_u8_kind U8.t err

val parse_u8_spec
  (#err: Type0)
  (e: err)
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 1))
  (ensures (
    let pp = parse (parse_u8 e) b in
    Correct? pp /\ (
    let (Correct (v, consumed)) = pp in
    U8.v v == E.be_to_n (Seq.slice b 0 1)
  )))

val parse_u8_spec_error
  (#err: Type0)
  (e: err)
  (b: bytes)
: Lemma
  (requires (Seq.length b < 1))
  (ensures (
    let pp = parse (parse_u8 e) b in
    pp == Error e
  ))

val serialize_u8 (#err: Type0) (e: err) : serializer (parse_u8 e)

inline_for_extraction
let parse_u16_kind : parser_kind =
  total_constant_size_parser_kind 2

val parse_u16 (#err: Type0) (e: err): parser parse_u16_kind U16.t err

val parse_u16_spec
  (#err: Type0)
  (e: err)
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 2))
  (ensures (
    let pp = parse (parse_u16 e) b in
    Correct? pp /\ (
    let (Correct (v, consumed)) = pp in
    U16.v v == E.be_to_n (Seq.slice b 0 2)
  )))

val parse_u16_spec_error
  (#err: Type0)
  (e: err)
  (b: bytes)
: Lemma
  (requires (Seq.length b < 2))
  (ensures (
    let pp = parse (parse_u16 e) b in
    pp == Error e
  ))

val serialize_u16 (#err: Type0) (e: err) : serializer (parse_u16 e)

let parse_u32_kind : parser_kind =
  total_constant_size_parser_kind 4

val parse_u32 (#err: Type0) (e: err): parser parse_u32_kind U32.t err

val parse_u32_spec
  (#err: Type0)
  (e: err)
  (b: bytes)
: Lemma
  (requires (Seq.length b >= 4))
  (ensures (
    let pp = parse (parse_u32 e) b in
    Correct? pp /\ (
    let (Correct (v, consumed)) = pp in
    U32.v v == E.be_to_n (Seq.slice b 0 4)
  )))

val parse_u32_spec_error
  (#err: Type0)
  (e: err)
  (b: bytes)
: Lemma
  (requires (Seq.length b < 4))
  (ensures (
    let pp = parse (parse_u32 e) b in
    pp == Error e
  ))

val serialize_u32 (#err: Type0) (e: err) : serializer (parse_u32 e)
