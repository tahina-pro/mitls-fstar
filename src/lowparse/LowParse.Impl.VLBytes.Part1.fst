module LowParse.Impl.VLBytes.Part1
include LowParse.Impl.FLBytes
include LowParse.Impl.Int
include LowParse.Spec.VLBytes

module Seq = FStar.Seq
module S = LowParse.Slice
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module E = FStar.Kremlin.Endianness
module Cast = FStar.Int.Cast

val parse_bounded_vlbytes_parse_vlbytes'
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
: Lemma (
    let v = parse (parse_bounded_vlbytes min max p) b in
    Some? v ==> (
    let v' = parse (parse_vlbytes (log256 max) p) b in
    Some? v' /\ (
    let (Some (x, len)) = v in
    let (Some (x', len')) = v' in
    x == x' /\ len == len'
  )))

#set-options "--z3rlimit 16"

let parse_bounded_vlbytes_parse_vlbytes' min max #k #t p s =
  if Some? (parse (parse_bounded_vlbytes min max p) s)
  then begin
    let sz : integer_size = log256 max in
    let f = in_bounds min max in
    assert (Some? (parse (parse_vlbytes_gen sz f p) s));
    let vlen1 = parse (parse_filter (parse_bounded_integer sz) f) s in
    assert (Some? vlen1);
    let (Some (len1, consumed1)) = vlen1 in
    parse_filter_implies (parse_bounded_integer sz) f (unconstrained_bounded_integer sz) s    
  end

#reset-options

val parse_bounded_vlbytes_parse_vlbytes
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
  (#k: parser_kind)
  (#t: Type0)
  (h: HS.mem)
  (p: parser k t)
  (b: S.bslice)
  (pred: ((t * consumed_slice_length b) -> GTot Type0))
: Lemma
  (requires (parses h (parse_bounded_vlbytes min max p) b pred))
  (ensures (parses h (parse_vlbytes (log256 max) p) b pred))

let parse_bounded_vlbytes_parse_vlbytes min max #k #t h p b pred =
  let s = S.as_seq h b in
  parse_bounded_vlbytes_parse_vlbytes' min max p s

inline_for_extraction
let parse_bounded_integer_1_synth
  (x: U8.t)
: Tot (bounded_integer 1)
= Cast.uint8_to_uint32 x

let parse_bounded_integer_1
: parser _ (bounded_integer 1)
= parse_synth parse_u8 parse_bounded_integer_1_synth

inline_for_extraction
let parse_bounded_integer_2_synth
  (x: U16.t)
: Tot (bounded_integer 2)
= Cast.uint16_to_uint32 x

let parse_bounded_integer_2
: parser _ (bounded_integer 2)
= parse_synth parse_u16 parse_bounded_integer_2_synth

#set-options "--z3rlimit 32"

inline_for_extraction
let parse_bounded_integer_3_synth
  (hilo: U16.t * U8.t)
: Tot (bounded_integer 3)
= let (hi, lo) = hilo in
  U32.add (Cast.uint8_to_uint32 lo) (U32.mul 256ul (Cast.uint16_to_uint32 hi))

#reset-options

#set-options "--z3rlimit 16"

let parse_bounded_integer_3_synth_injective () : Lemma
  (forall (x1 x2: (U16.t * U8.t)) . parse_bounded_integer_3_synth x1 == parse_bounded_integer_3_synth x2 ==> x1 == x2)
= ()

#reset-options

let parse_bounded_integer_3
: parser _ (bounded_integer 3)
= parse_bounded_integer_3_synth_injective ();
  (parse_u16 `nondep_then` parse_u8) `parse_synth` parse_bounded_integer_3_synth

val parse_bounded_integer'
  (i: integer_size)
: parser (ParserStrong (StrongConstantSize i ConstantSizeTotal)) (bounded_integer i)

#set-options "--z3rlimit 16"

let parse_bounded_integer' i = match i with
  | 1 -> (parse_bounded_integer_1 <: parser (ParserStrong (StrongConstantSize i ConstantSizeTotal)) (bounded_integer i))
  | 2 -> (parse_bounded_integer_2 <: parser (ParserStrong (StrongConstantSize i ConstantSizeTotal)) (bounded_integer i))
  | 3 -> (parse_bounded_integer_3 <: parser (ParserStrong (StrongConstantSize i ConstantSizeTotal)) (bounded_integer i))
  | 4 -> (parse_u32 <: parser (ParserStrong (StrongConstantSize i ConstantSizeTotal)) (bounded_integer i))

#reset-options
