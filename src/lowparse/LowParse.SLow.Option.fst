module LowParse.SLow.Option
include LowParse.Low.Option
include LowParse.SLow.Base

module U32 = FStar.UInt32
module B32 = FStar.Bytes
module I32 = FStar.Int32
module HST = FStar.HyperStack.ST

inline_for_extraction
let parse32_option
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v32: validator32 #default_validator32_cls p)
  (p32: parser32 p)
: Tot (parser32 (parse_option p))
= fun input len ->
  if v32 input len `I32.lt` 0l
  then (None, 0l)
  else
    match p32 input len with
    | (x, consumed) -> (Some x, consumed)

inline_for_extraction
let serialize32_option (#k: parser_kind) (#t: Type) (#p: parser k t) (#s: serializer p) (s32: serializer32 s) (u: squash (k.parser_kind_low > 0)) : Tot (serializer32 (serialize_option s u)) =
  fun output len lo input ->
  match input with
  | None ->
    let h = HST.get () in
    contains_valid_serialized_data_or_fail_equiv h (serialize_option s u) output lo None lo;
    lo
  | Some x ->
    let hi = s32 output len lo x in
    let h = HST.get () in
    contains_valid_serialized_data_or_fail_equiv h s output lo x hi;
    contains_valid_serialized_data_or_fail_equiv h (serialize_option s u) output lo (Some x) hi;
    hi

inline_for_extraction
let size32_option (#k: parser_kind) (#t: Type) (#p: parser k t) (#s: serializer p) (s32: size32 s) (u: squash (k.parser_kind_low > 0)) : Tot (size32 (serialize_option s u)) =
  fun input -> ((match input with
  | None -> 0ul
  | Some y -> s32 y) <: (y: U32.t { size32_postcond (serialize_option s u) input y } ))
