module LowParse.SLow.FLData
include LowParse.Spec.FLData
include LowParse.SLow.Combinators

module B32 = LowParse.Bytes32
module U32 = FStar.UInt32

inline_for_extraction
let parse32_fldata
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (p32: parser32 p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
  (e: err)
: Tot (parser32 (parse_fldata p sz e))
= (fun (input: bytes32) -> ((
    if U32.lt (B32.len input) sz32
    then
      Error e
    else
      match p32 (B32.b32slice input 0ul sz32) with
      | Correct (v, consumed) ->
	if consumed = sz32
	then begin
	  Correct (v, consumed)
	end else Error e
      | Error e' -> Error e'
  ) <: (res: result (t * U32.t) err { parser32_correct (parse_fldata p sz e) input res } )))

inline_for_extraction
let parse32_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (p32: parser32 p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
  (e: err)
: Tot (parser32 (parse_fldata_strong s sz e))
= (fun (input: bytes32) -> ((
    match parse32_fldata p32 sz sz32 e input with
    | Correct (v, consumed) ->
      assert (
        parse_fldata_strong_correct s sz e (B32.reveal input) (U32.v consumed) v;
        Seq.length (s v) == sz
      );
      Correct ((v <: parse_fldata_strong_t s sz), consumed)
    | Error e -> Error e
    )   
    <: (res: result (parse_fldata_strong_t s sz * U32.t) err { parser32_correct (parse_fldata_strong s sz e) input res } )))

inline_for_extraction
let serialize32_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (sz: nat { sz < 4294967296 } )
  (e: err)
: Tot (serializer32 (serialize_fldata_strong s sz e))
= (fun (input: parse_fldata_strong_t s sz) -> s32 input)
