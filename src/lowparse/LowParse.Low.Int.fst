module LowParse.Low.Int
open LowParse.Low.Combinators

module Aux = LowParse.Low.Int.Aux
module Unique = LowParse.Spec.Int.Unique
module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer

#set-options "--z3rlimit 32"

inline_for_extraction
let parse32_u8 =
  (fun input ->
    let h = HST.get () in
    let _ = Unique.parse_u8_unique (B.as_seq h input) in
    Aux.parse32_u8 input
  )

inline_for_extraction
let parse32_u16 =
  (fun input ->
    let h = HST.get () in
    let _ = Unique.parse_u16_unique (B.as_seq h input) in
    Aux.parse32_u16 input
  )

inline_for_extraction
let parse32_u32 =
  (fun input ->
    let h = HST.get () in
    let _ = Unique.parse_u32_unique (B.as_seq h input) in
    Aux.parse32_u32 input
  )

let serialize32_u8 = fun out lo v ->
  let _ = Unique.serialize_u8_unique v in
  Aux.serialize32_u8 out lo v;
  let h = HST.get () in
  let _ = Unique.parse_u8_unique (B.as_seq h (B.gsub out lo 1ul)) in
  exactly_contains_valid_data_equiv h Aux.parse_u8 out lo v (U32.add lo 1ul);
  exactly_contains_valid_data_equiv h parse_u8 out lo v (U32.add lo 1ul);
  ()

let serialize32_u16 = fun out lo v ->
  let _ = Unique.serialize_u16_unique v in
  Aux.serialize32_u16 out lo v;
  let h = HST.get () in
  let _ = Unique.parse_u16_unique (B.as_seq h (B.gsub out lo 2ul)) in
  exactly_contains_valid_data_equiv h Aux.parse_u16 out lo v (U32.add lo 2ul);
  exactly_contains_valid_data_equiv h parse_u16 out lo v (U32.add lo 2ul);
  ()

let serialize32_u32 = fun out lo v ->
  let _ = Unique.serialize_u32_unique v in
  Aux.serialize32_u32 out lo v;
  let h = HST.get () in
  let _ = Unique.parse_u32_unique (B.as_seq h (B.gsub out lo 4ul)) in
  exactly_contains_valid_data_equiv h Aux.parse_u32 out lo v (U32.add lo 4ul);
  exactly_contains_valid_data_equiv h parse_u32 out lo v (U32.add lo 4ul);
  ()

let serialize32_u8_fail = serializer32_fail_of_serializer serialize32_u8 1l

let serialize32_u16_fail = serializer32_fail_of_serializer serialize32_u16 2l

let serialize32_u32_fail = serializer32_fail_of_serializer serialize32_u32 4l
