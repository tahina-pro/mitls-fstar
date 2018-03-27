module LowParse.Impl.Array
include LowParse.Impl.FLBytes
include LowParse.Impl.Seq
include LowParse.Spec.Array

module U32 = FStar.UInt32
module S = LowParse.Slice

inline_for_extraction
val validate_array_gen
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (vs: stateful_validator p)
  (#array_byte_size: U32.t)
  (precond: parse_array_precond p array_byte_size)
: Tot (stateful_validator (parse_array precond))

#set-options "--z3rlimit 16"

let validate_array_gen #elem_byte_size #k #t #p vs #array_byte_size precond =
  fun (s: S.bslice) ->
  parse_array_precond_elim precond;
  validate_flbytes (validate_seq vs) array_byte_size s

#reset-options

inline_for_extraction
let validate_array
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (vs: stateful_validator p)
  (#array_byte_size: U32.t)
  (precond: parse_array_precond p array_byte_size)
: Tot (stateful_validator (parse_array precond))
= match k with
  | ConstantSizeTotal ->
    validate_total_constant_size array_byte_size (parse_array precond)
  | _ ->
    validate_array_gen vs precond

include LowParse.Impl.VLBytes

#set-options "--z3rlimit 128"

inline_for_extraction
let validate_vlarray
  (#elem_byte_size: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize elem_byte_size k)) t)
  (vs: stateful_validator p)
  (#array_byte_size_min #array_byte_size_max: U32.t)
  (precond: parse_vlarray_precond p array_byte_size_min array_byte_size_max)
: Tot (stateful_validator (parse_vlarray precond))
= fun (s: S.bslice) ->
  parse_vlarray_precond_elim precond;
  assert (U32.v array_byte_size_max > 0);
  let x = validate_bounded_vlbytes array_byte_size_min array_byte_size_max (validate_seq vs) s in
  x

#reset-options
