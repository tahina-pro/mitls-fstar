module LowParse.SLow.FLData
include LowParse.Low.FLData
include LowParse.SLow.Combinators

module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module I32 = FStar.Int32
module B = LowStar.Buffer
module HST = FStar.HyperStack.ST

inline_for_extraction
let parse32_fldata
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (sz: nat)
  (sz32: I32.t { I32.v sz32 == sz } )
: Tot (parser32 (parse_fldata p sz))
= fun input len ->
  p32 (B.sub input 0ul (Cast.int32_to_uint32 sz32)) sz32

inline_for_extraction
let parse32_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (sz: nat)
  (sz32: I32.t { I32.v sz32 == sz } )
: Tot (parser32 (parse_fldata_strong s sz))
= fun input len -> 
  let h = HST.get () in
  match parse32_fldata p32 sz sz32 input len with
    (v, consumed) ->
    assert (
      parse_fldata_strong_correct s sz (B.as_seq h input) (I32.v consumed) v;
      Seq.length (s v) == sz
    );
    ((v <: parse_fldata_strong_t s sz), consumed)

inline_for_extraction
let serialize32_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (sz: nat)
: Tot (serializer32 (serialize_fldata_strong s sz))
= (fun output len lo (input: parse_fldata_strong_t s sz) ->
    let hi = s32 output len lo input in
    let h = HST.get () in
    contains_valid_serialized_data_or_fail_equiv h s output lo input hi;
    contains_valid_serialized_data_or_fail_equiv h (serialize_fldata_strong s sz) output lo input hi;
    hi
  )

inline_for_extraction
let size32_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (size32 (serialize_fldata_strong s sz))
= size32_constant (serialize_fldata_strong s sz) sz32 ()
