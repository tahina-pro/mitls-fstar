module LowParse.Impl.VLBytes.Part3
include LowParse.Impl.VLBytes.Part2

module Seq = FStar.Seq
module S = LowParse.Slice
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module E = FStar.Kremlin.Endianness
module Cast = FStar.Int.Cast

inline_for_extraction
let parse_bounded_integer_st_nochk_1
: parser_st_nochk parse_bounded_integer_1
= parse_synth_st_nochk parse_u8_st_nochk parse_bounded_integer_1_synth

inline_for_extraction
let parse_bounded_integer_st_nochk_2
: parser_st_nochk parse_bounded_integer_2
= parse_synth_st_nochk parse_u16_st_nochk parse_bounded_integer_2_synth

#set-options "--z3rlimit 16"

inline_for_extraction
let parse_bounded_integer_st_nochk_3
: parser_st_nochk parse_bounded_integer_3
= parse_synth_st_nochk
    (parse_nondep_then_nochk parse_u16_st_nochk parse_u8_st_nochk)
    parse_bounded_integer_3_synth

#reset-options

inline_for_extraction
val parse_bounded_integer_st_nochk'
  (i: integer_size)
: Tot (parser_st_nochk (parse_bounded_integer' i))

let parse_bounded_integer_st_nochk' i = match i with
  | 1 -> parse_bounded_integer_st_nochk_1
  | 2 -> parse_bounded_integer_st_nochk_2
  | 3 -> parse_bounded_integer_st_nochk_3
  | 4 -> parse_u32_st_nochk

inline_for_extraction
let parse_bounded_integer_st_nochk
  (i: integer_size)
: Tot (parser_st_nochk (parse_bounded_integer i))
= fun (b: S.bslice) ->
    Classical.forall_intro (parse_bounded_integer'_correct i);
    parse_bounded_integer_st_nochk' i b

inline_for_extraction
let parse_bounded_integer_st
  (i: integer_size)
: Tot (parser_st (parse_bounded_integer i))
= parse_total_constant_size (U32.uint_to_t i) (parse_bounded_integer_st_nochk i)

inline_for_extraction
let validate_vlbytes_payload
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (pv: stateful_validator p)
  (i: bounded_integer sz { f i == true } )
: Tot (stateful_validator (parse_vlbytes_payload sz f p i))
= validate_flbytes pv i

inline_for_extraction
let validate_vlbytes_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (pv: stateful_validator p)
: Tot (stateful_validator (parse_vlbytes_gen sz f p))
= fun (s: S.bslice) ->
  parse_flbytes_and_then_cases_injective sz f p;
  parse_then_check
    #_
    #_
    #(parse_filter (parse_bounded_integer sz) f)
    (parse_filter_st (parse_bounded_integer_st sz) f)
    #_
    #_
    #(parse_vlbytes_payload sz f p)
    (validate_vlbytes_payload sz f pv)
    s

inline_for_extraction
val validate_vlbytes
  (sz: integer_size)
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (pv: stateful_validator p)
: Tot (stateful_validator (parse_vlbytes sz p))

let validate_vlbytes sz #k #t #p pv =
  validate_vlbytes_gen sz (unconstrained_bounded_integer sz) #k #t #p pv

inline_for_extraction
let validate_vlbytes_payload_nochk
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (len: bounded_integer sz { f len == true } )
: Tot (stateful_validator_nochk (parse_vlbytes_payload sz f p len))
= validate_flbytes_nochk p len

inline_for_extraction
let validate_vlbytes_gen_nochk
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (stateful_validator_nochk (parse_vlbytes_gen sz f p))
= parse_flbytes_and_then_cases_injective sz f p;
  parse_nochk_then_nochk
    #_
    #_
    #(parse_filter (parse_bounded_integer sz) f)
    (parse_filter_st_nochk (parse_bounded_integer_st_nochk sz) f)
    #_
    #_
    #(parse_vlbytes_payload sz f p)
    (validate_vlbytes_payload_nochk sz f p)

inline_for_extraction
val validate_vlbytes_nochk
  (sz: integer_size)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (stateful_validator_nochk (parse_vlbytes sz p))

let validate_vlbytes_nochk sz #b #t p =
  validate_vlbytes_gen_nochk sz (unconstrained_bounded_integer sz) p

#set-options "--z3rlimit 16"

inline_for_extraction
let validate_bounded_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (pv: stateful_validator p)
: Tot (stateful_validator (parse_bounded_vlbytes min max p))
= fun (s: S.bslice) ->
  assert (normalize_term (log256 max) == log256 max);
  validate_vlbytes_gen (normalize_term (log256 max)) (in_bounds min max) #k #t #p pv s

#reset-options

inline_for_extraction
let validate_bounded_vlbytes_nochk
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot (stateful_validator_nochk (parse_bounded_vlbytes min max p))
= let sz = log256 max in
  validate_vlbytes_gen_nochk sz (in_bounds min max) #k #t p
