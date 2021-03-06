module LowParse.Low.Int
include LowParse.Spec.Int
include LowParse.Low.Combinators

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module I32 = FStar.Int32
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies

inline_for_extraction
val parse32_u8: parser32 parse_u8

inline_for_extraction
val parse32_u16: parser32 parse_u16

inline_for_extraction
val parse32_u32: parser32 parse_u32

inline_for_extraction
let validate32_u8 : validator32 parse_u8 =
  validate32_total_constant_size parse_u8 1l ()

inline_for_extraction
let validate32_u16 : validator32 parse_u16 =
  validate32_total_constant_size parse_u16 2l ()

inline_for_extraction
let validate32_u32 : validator32 parse_u32 =
  validate32_total_constant_size parse_u32 4l ()

inline_for_extraction
let validate_nochk32_u8 : validator_nochk32 parse_u8 =
  validate_nochk32_constant_size parse_u8 1ul ()

inline_for_extraction
let validate_nochk32_u16 : validator_nochk32 parse_u16 =
  validate_nochk32_constant_size parse_u16 2ul ()

inline_for_extraction
let validate_nochk32_u32 : validator_nochk32 parse_u32 =
  validate_nochk32_constant_size parse_u32 4ul ()

inline_for_extraction
val serialize32_u16 : serializer32 serialize_u16

inline_for_extraction
val serialize32_u32 : serializer32 serialize_u32

inline_for_extraction
val serialize32_u16_fail : serializer32_fail serialize_u16

inline_for_extraction
val serialize32_u32_fail : serializer32_fail serialize_u32
