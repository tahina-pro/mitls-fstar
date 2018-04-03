module LowParse.Spec.Bytes
include LowParse.Spec.VLData

module B32 = FStar.Bytes
module Seq = FStar.Seq
module U32 = FStar.UInt32

#set-options "--z3rlimit 128 --max_fuel 64 --max_ifuel 64"

let lt_pow2_32
  (x: nat)
: Lemma
  (x < 4294967296 <==> x < pow2 32)
= ()

#reset-options

let parse_flbytes_gen
  (sz: nat { sz < 4294967296 } )
  (s: bytes { Seq.length s == sz } )
: GTot (B32.lbytes sz)
= lt_pow2_32 sz;
  B32.hide s

let parse_flbytes
  (#err: Type0)
  (sz: nat { sz < 4294967296 } )
  (e: err)
: Tot (parser (total_constant_size_parser_kind sz) (B32.lbytes sz) err)
= make_total_constant_size_parser sz (B32.lbytes sz) _ (parse_flbytes_gen sz) e

let serialize_flbytes'
  (sz: nat { sz < 4294967296 } )
: Tot (bare_serializer (B32.lbytes sz))
= fun (x: B32.lbytes sz) -> (
    lt_pow2_32 sz;
    B32.reveal x
  )

let serialize_flbytes_correct
  (#err: Type0)
  (sz: nat { sz < 4294967296 } )
  (e: err)
: Lemma
  (serializer_correct (parse_flbytes sz e) (serialize_flbytes' sz))
= let prf
    (input: B32.lbytes sz)
  : Lemma
    (
      let ser = serialize_flbytes' sz input in
      Seq.length ser == sz /\
      parse (parse_flbytes sz e) ser == Correct (input, sz)
    )
  = ()
  in
  Classical.forall_intro prf

let serialize_flbytes
  (#err: Type0)
  (sz: nat { sz < 4294967296 } )
  (e: err)
: Tot (serializer (parse_flbytes sz e))
= serialize_flbytes_correct sz e;
  serialize_flbytes' sz

(* VLBytes *)

(* For the payload: since the input buffer is truncated at the time of
reading the length header, "parsing" the payload will always succeed,
by just returning it unchanged (unless the length of the input
is greater than 2^32) *)

inline_for_extraction
let parse_all_bytes_kind =
  {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_metadata = {
      parser_kind_metadata_total = false;
    };
    parser_kind_subkind = Some ParserConsumesAll;
  }

let parse_all_bytes'
  (#err: Type0)
  (e: err)
  (input: bytes)
: GTot (result (B32.bytes * consumed_length input) err)
= let len = Seq.length input in
  if len >= 4294967296
  then Error e
  else begin
    lt_pow2_32 len;
    Correct (B32.hide input, len)
  end

#set-options "--z3rlimit 16"

let parse_all_bytes_injective
  (#err: Type0)
  (e: err)
: Lemma
  (injective (parse_all_bytes' e))
= let prf
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond (parse_all_bytes' e) b1 b2))
    (ensures (injective_postcond (parse_all_bytes' e) b1 b2))
  = assert (Seq.length b1 < 4294967296);
    assert (Seq.length b2 < 4294967296);
    lt_pow2_32 (Seq.length b1);
    lt_pow2_32 (Seq.length b2);
    B32.reveal_hide b1;
    B32.reveal_hide b2
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (prf x))

#reset-options

let parse_all_bytes_correct
  (#err: Type0)
  (e: err)
: Lemma
  (parser_kind_prop parse_all_bytes_kind (parse_all_bytes' e))
= parse_all_bytes_injective e;
  injective_consumes_all_no_lookahead_weak (parse_all_bytes' e)

let parse_all_bytes
  (#err: Type0)
  (e: err)
: Tot (parser parse_all_bytes_kind B32.bytes err) =
  parse_all_bytes_correct e;
  parse_all_bytes' e

let serialize_all_bytes'
  (input: B32.bytes)
: GTot bytes
= B32.reveal input

#set-options "--z3rlimit 32"

let serialize_all_bytes_correct
  (#err: Type0)
  (e: err)
: Lemma (serializer_correct (parse_all_bytes e) serialize_all_bytes') =
  let prf
    (input: B32.bytes)
  : Lemma
    (
      let ser = serialize_all_bytes' input in
      let len : consumed_length ser = Seq.length ser in
      parse (parse_all_bytes e) ser == Correct (input, len)
    )
  = assert (Seq.length (serialize_all_bytes' input) == B32.length input);
    lt_pow2_32 (B32.length input);
    B32.hide_reveal input
  in
  Classical.forall_intro prf

#reset-options

let serialize_all_bytes
  (#err: Type0)
  (e: err)
: Tot (serializer (parse_all_bytes e)) =
  serialize_all_bytes_correct e;
  serialize_all_bytes'

let parse_bounded_vlbytes'
  (#err: Type0)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (e_size_incomplete e_size_invalid: err)
: Tot (parser (parse_bounded_vldata_kind min max) (parse_bounded_vldata_strong_t min max (serialize_all_bytes e_size_invalid)) err)
= parse_bounded_vldata_strong min max (serialize_all_bytes e_size_invalid) e_size_incomplete e_size_invalid e_size_invalid

let parse_bounded_vlbytes_pred
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (x: B32.bytes)
: GTot Type0
= let reslen = B32.length x in
  min <= reslen /\ reslen <= max

let parse_bounded_vlbytes_t
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
: Tot Type0
= (x: B32.bytes { parse_bounded_vlbytes_pred min max x } )

let synth_bounded_vlbytes
  (#err: Type0)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 })
  (e: err)
  (x: parse_bounded_vldata_strong_t min max (serialize_all_bytes e))
: Tot (parse_bounded_vlbytes_t min max)
= x

let parse_bounded_vlbytes
  (#err: Type0)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (e_size_incomplete e_size_invalid: err)
: Tot (parser (parse_bounded_vldata_kind min max) (parse_bounded_vlbytes_t min max) err)
= parse_synth (parse_bounded_vlbytes' min max e_size_incomplete e_size_invalid) (synth_bounded_vlbytes min max e_size_invalid)

let serialize_bounded_vlbytes'
  (#err: Type0)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (e_size_incomplete e_size_invalid: err)
: Tot (serializer (parse_bounded_vlbytes' min max e_size_incomplete e_size_invalid))
= serialize_bounded_vldata_strong min max (serialize_all_bytes e_size_invalid) e_size_incomplete e_size_invalid e_size_invalid

let serialize_bounded_vlbytes
  (#err: Type0)
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (e_size_incomplete e_size_invalid: err)
: Tot (serializer (parse_bounded_vlbytes min max e_size_incomplete e_size_invalid))
= serialize_synth
    (parse_bounded_vlbytes' min max e_size_incomplete e_size_invalid)
    (synth_bounded_vlbytes min max e_size_invalid)
    (serialize_bounded_vlbytes' min max e_size_incomplete e_size_invalid)
    (fun (x: parse_bounded_vlbytes_t min max) ->
      (x <: parse_bounded_vldata_strong_t min max (serialize_all_bytes e_size_invalid))
    )
    ()
