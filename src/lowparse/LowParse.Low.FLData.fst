module LowParse.Low.FLData
include LowParse.Low.Combinators
include LowParse.Spec.FLData

module B = LowStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32
module Cast = FStar.Int.Cast

#reset-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false"

inline_for_extraction
let validate32_fldata
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator32 p)
  (sz: nat)
  (sz32: I32.t { I32.v sz32 == sz } )
: Tot (validator32 (parse_fldata p sz))
= fun input len ->
  if len `I32.lt` sz32
  then -1l
  else
    if v (B.sub input 0ul (Cast.int32_to_uint32 sz32)) sz32 <> 0l
    then -2l
    else len `I32.sub` sz32

#reset-options

inline_for_extraction
let validate32_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: validator32 p)
  (sz: nat)
  (sz32: I32.t { I32.v sz32 == sz } )
: Tot (validator32 (parse_fldata_strong s sz))
= fun input len -> validate32_fldata v sz sz32 input len

inline_for_extraction
let validate_nochk32_fldata
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (validator_nochk32 (parse_fldata p sz))
= validate_nochk32_constant_size (parse_fldata p sz) sz32 ()

inline_for_extraction
let validate_nochk32_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (validator_nochk32 (parse_fldata_strong s sz))
= validate_nochk32_constant_size (parse_fldata_strong s sz) sz32 ()

inline_for_extraction
let accessor_fldata'
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (accessor' (parse_fldata p sz) p (fun x y -> x == y))
= fun x ->
    let h = HST.get () in // TODO: WHY WHY WHY is this necessary?
    B.sub x 0ul sz32

inline_for_extraction
let accessor_fldata
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (accessor (parse_fldata p sz) p (fun x y -> x == y))
= mk_accessor (parse_fldata p sz) p (fun x y -> x == y) (accessor_fldata' p sz sz32)

inline_for_extraction
let accessor_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (accessor (parse_fldata_strong s sz) p (fun x y -> x == y))
= mk_accessor (parse_fldata_strong s sz) p (fun x y -> x == y) (fun x -> accessor_fldata' p sz sz32 x)
