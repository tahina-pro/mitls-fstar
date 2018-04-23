module LowParse.SLow.FLData
open FStar.Error // for Correct, Error
include LowParse.Spec.FLData
include LowParse.SLow.Combinators

module B32 = LowParse.Bytes32
module U32 = FStar.UInt32

inline_for_extraction
let parse32_fldata
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (parser32 (parse_fldata p sz))
= (fun (input: bytes32) -> ((
    if U32.lt (B32.len input) sz32
    then
      Error ("parse32_fldata not enough incoming data, expected " ^ string_of_int sz ^ ", got " ^ string_of_int (U32.v (B32.len input)))
    else
      match p32 (B32.b32slice input 0ul sz32) with
      | Correct (v, consumed) ->
	if consumed = sz32
	then begin
	  Correct (v, consumed)
	end else Error ("parse32_fldata not enough data consumed by payload parser, expected " ^ string_of_int sz ^ ", got " ^ string_of_int (U32.v consumed))
      | Error e -> Error ("parse32_fldata payload: " ^ e)
  ) <: (res: result (t * U32.t) { parser32_correct (parse_fldata p sz) input res } )))

inline_for_extraction
let parse32_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (p32: parser32 p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (parser32 (parse_fldata_strong s sz))
= (fun (input: bytes32) -> ((
    match parse32_fldata p32 sz sz32 input with
    | Correct (v, consumed) ->
      assert (
        parse_fldata_strong_correct s sz (B32.reveal input) (U32.v consumed) v;
        Seq.length (s v) == sz
      );
      Correct ((v <: parse_fldata_strong_t s sz), consumed)
    | Error e -> Error ("parse32_fldata_strong payload: " ^ e)
    )   
    <: (res: result (parse_fldata_strong_t s sz * U32.t) { parser32_correct (parse_fldata_strong s sz) input res } )))

inline_for_extraction
let serialize32_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (sz: nat { sz < 4294967296 } )
: Tot (serializer32 (serialize_fldata_strong s sz))
= (fun (input: parse_fldata_strong_t s sz) -> s32 input)
