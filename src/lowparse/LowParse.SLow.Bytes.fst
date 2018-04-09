module LowParse.SLow.Bytes
include LowParse.Spec.Bytes
include LowParse.SLow.VLData

module B32 = FStar.Bytes
module Seq = FStar.Seq
module U32 = FStar.UInt32

inline_for_extraction
let parse32_flbytes_gen
  (sz: nat { sz < 4294967296 } )
  (x: B32.lbytes sz)
: Tot (y: B32.lbytes sz { y == parse_flbytes_gen sz (B32.reveal x) } )
= B32.hide_reveal x;
  x

#set-options "--z3rlimit 32"

inline_for_extraction
let parse32_flbytes
  (#err: Type)
  (sz: nat)
  (sz' : U32.t { U32.v sz' == sz } )
  (e: err)
: Tot (
     lt_pow2_32 sz;
     parser32 (parse_flbytes sz e)
  )
= lt_pow2_32 sz;
  make_total_constant_size_parser32
    sz
    sz'
    #(B32.lbytes sz)
    #err
    (parse_flbytes_gen sz)
    e
    ()
    (parse32_flbytes_gen sz)

inline_for_extraction
let serialize32_flbytes
  (#err: Type0)
  (sz: nat { sz < 4294967296 } )
  (e: err)
: Tot (serializer32 (serialize_flbytes sz e))
= fun (input: B32.lbytes sz) ->
    B32.hide_reveal input;
    (input <: (res: bytes32 { serializer32_correct (serialize_flbytes sz e) input res } ))

inline_for_extraction
let parse32_all_bytes
  (#err: Type0)
  (e: err)
: Tot (parser32 (parse_all_bytes e))
= fun (input: B32.bytes) ->
    let res = Correct (input, B32.len input) in
    (res <: (res: result (bytes32 * U32.t) err { parser32_correct (parse_all_bytes e) input res } ))

inline_for_extraction
let serialize32_all_bytes
  (#err: Type0)
  (e: err)
: Tot (serializer32 (serialize_all_bytes e))
= fun (input: B32.bytes) ->
  (input <: (res: bytes32 { serializer32_correct (serialize_all_bytes e) input res } ))

inline_for_extraction
let parse32_bounded_vlbytes
  (#err: Type0)
  (min: nat)
  (min32: U32.t { U32.v min32 == min } )
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (max32: U32.t { U32.v max32 == max } )
  (e_size_incomplete e_size_invalid: err)
: Tot (parser32 (parse_bounded_vlbytes min max e_size_incomplete e_size_invalid))
= parse32_synth
    _
    (synth_bounded_vlbytes min max e_size_invalid)
    (fun (x: parse_bounded_vldata_strong_t min max (serialize_all_bytes e_size_invalid)) -> (x <: parse_bounded_vlbytes_t min max))
    (parse32_bounded_vldata_strong min min32 max max32 (serialize_all_bytes e_size_invalid) (parse32_all_bytes e_size_invalid) e_size_incomplete e_size_invalid e_size_invalid)
    ()

inline_for_extraction
let serialize32_bounded_vlbytes
  (#err: Type0)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // max MUST BE less than 2^32 - 4
  (e_size_incomplete e_size_invalid: err)
: Tot (serializer32 (serialize_bounded_vlbytes min max e_size_incomplete e_size_invalid))
= fun (input: parse_bounded_vlbytes_t min max) ->
  serialize32_bounded_vldata_strong
    min
    max
    (total_to_partial_serializer32 (serialize32_all_bytes e_size_invalid))
    e_size_incomplete
    e_size_invalid
    e_size_invalid
    input

#reset-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false"

inline_for_extraction
let size32_all_bytes
  (#err: Type0)
  (e: err)
: Tot (size32 (serialize_all_bytes e))
= fun (input: B32.bytes) ->
  let res = B32.len input in
  (res <: (res: U32.t { size32_postcond (serialize_all_bytes e) input res } ))

inline_for_extraction
let size32_bounded_vlbytes
  (#err: Type0)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967292 } ) // max MUST BE less than 2^32 - 4
  (size_header_byte_size32: U32.t { U32.v size_header_byte_size32 == log256' max } )
  (e_size_incomplete e_size_invalid: err)
: Tot (size32 (serialize_bounded_vlbytes min max e_size_incomplete e_size_invalid))
= fun (input: parse_bounded_vlbytes_t min max) ->
  size32_bounded_vldata_strong
    min
    max
    (size32_all_bytes e_size_invalid)
    size_header_byte_size32
    e_size_incomplete
    e_size_invalid
    e_size_invalid
    input
