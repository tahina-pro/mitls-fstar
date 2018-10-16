module LowParse.Low.Int.Aux
include LowParse.Spec.Int.Aux
include LowParse.Low.Combinators

module Seq = FStar.Seq
module E = LowParse.BigEndianImpl.Low
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B = LowStar.Buffer
module Aux2 = LowParse.Low.Int.Aux2

inline_for_extraction
let parse32_u16 : parser32 parse_u16 =
  decode_u16_injective ();
    make_total_constant_size_parser32 2 2ul
      #U16.t
      decode_u16
      ()
      (fun input ->
        E.be_to_n_2 _ _ (E.u16 ()) input)

inline_for_extraction
let parse32_u32 : parser32 parse_u32 =
    decode_u32_injective ();
    make_total_constant_size_parser32 4 4ul
      #U32.t
      decode_u32
      ()
      (fun input ->
        E.be_to_n_4 _ _ (E.u32 ()) input)

inline_for_extraction
let parse32_u8 : parser32 parse_u8 =
  decode_u8_injective ();
  make_total_constant_size_parser32 1 1ul
    decode_u8
    ()
    (fun b -> B.index b 0ul)

module HST = FStar.HyperStack.ST

#push-options "--z3rlimit 16"

inline_for_extraction
let serialize32_u8' : serializer32' serialize_u8 =
  fun out lo v ->
  let h = HST.get () in
  assert (Seq.length (serialize serialize_u8 v) == 1);
  B.upd (B.sub out lo 1ul) 0ul v;
  let h' = HST.get () in
  Aux2.seq_equal_1 (B.as_seq h' (B.gsub out lo 1ul)) (serialize serialize_u8 v)

#pop-options

inline_for_extraction
let serialize32_u8 : serializer32 serialize_u8 =
  serializer32_of_serializer32' serialize32_u8'

inline_for_extraction
let serialize32_u8_fail = serializer32_fail_of_serializer #_ #_ #parse_u8 #serialize_u8 serialize32_u8 1l

#push-options "--z3rlimit 32"

inline_for_extraction
let serialize32_u16 : serializer32 #_ #_ #parse_u16 serialize_u16 =
  fun out lo v ->
  assert (Seq.length (serialize #_ #_ #parse_u16 serialize_u16 v) == 2);
  let out' = B.sub out lo 2ul in
  assert_norm (pow2 (8 `Prims.op_Multiply` 2) == 65536);
  let h = HST.get () in
  assert (B.live h out'); 
  assert (B.length out' == 2);
  assert (8 `Prims.op_Multiply` 2 <= 16);
  assert (U16.v v < pow2 (8 `Prims.op_Multiply` 2));
  E.n_to_be_2 U16.t 16 (E.u16 ()) v out';
  let h' = HST.get () in
  loc_jbuffer_eq out lo (U32.add lo 2ul);
  exactly_contains_valid_data_equiv h' parse_u16 out lo v (U32.add lo 2ul)

#pop-options

inline_for_extraction
let serialize32_u16_fail = serializer32_fail_of_serializer #_ #_ #parse_u16 #serialize_u16 serialize32_u16 2l

#push-options "--z3rlimit 20"
inline_for_extraction
let serialize32_u32 : serializer32 #_ #_ #parse_u32 serialize_u32 =
  fun out lo v ->
  assert (Seq.length (serialize #_ #_ #parse_u32 serialize_u32 v) == 4);
  let out' = B.sub out lo 4ul in
  assert_norm (pow2 (8 `Prims.op_Multiply` 4) == 4294967296);
  let h = HST.get () in
  assert (B.live h out'); 
  assert (B.length out' == 4);
  assert (8 `Prims.op_Multiply` 4 <= 32);
  assert (U32.v v <= pow2 32 - 1);
  assert (U32.v v < pow2 (8 `Prims.op_Multiply` 4));
  E.n_to_be_4 U32.t 32 (E.u32 ()) v out';
  let h' = HST.get () in
  loc_jbuffer_eq out lo (U32.add lo 4ul);
  exactly_contains_valid_data_equiv h' parse_u32 out lo v (U32.add lo 4ul)
#pop-options

inline_for_extraction
let serialize32_u32_fail = serializer32_fail_of_serializer #_ #_ #parse_u32 #serialize_u32 serialize32_u32 4l
