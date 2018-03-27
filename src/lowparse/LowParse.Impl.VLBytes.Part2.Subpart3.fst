module LowParse.Impl.VLBytes.Part2.Subpart3
include LowParse.Impl.VLBytes.Part1

module U32 = FStar.UInt32
module E = FStar.Kremlin.Endianness
module U8 = FStar.UInt8
module Seq = FStar.Seq
module U16 = FStar.UInt16

#set-options "--z3rlimit 16"

let be_to_n_1 (b: bytes) : Lemma
  (requires (Seq.length b == 1))
  (ensures (
    Seq.length b == 1 /\
    E.be_to_n b == U8.v (Seq.last b)
  ))
= ()

#reset-options

#set-options "--z3rlimit 64"

let parse_bounded_integer'_3_correct_some
  (b: bytes)
: Lemma
  (requires (Some? (parse (parse_bounded_integer' 3) b)))
  (ensures (parse (parse_bounded_integer' 3) b == parse (parse_bounded_integer 3) b))
= assert (Some? (parse (parse_bounded_integer 3) b));
  let (Some (v, consumed)) = parse (parse_bounded_integer 3) b in
  let b1 : bytes = Seq.slice b 0 3 in
  assert (v == decode_bounded_integer 3 b1);
  E.lemma_be_to_n_is_bounded b1;
  assert (E.be_to_n b1 < pow2 24);
  FStar.Math.Lemmas.pow2_lt_compat 32 24;
  assert (E.be_to_n b1 < pow2 32);
  let x = U32.uint_to_t (E.be_to_n b1) in
  assert (v == x);
  let b1l : bytes = Seq.slice b1 0 2 in
  assert (b1l == Seq.slice b 0 2);
  let b1r : bytes = Seq.slice b1 2 3 in
  assert (E.be_to_n b1 == U8.v (Seq.last b1) + FStar.Mul.op_Star (pow2 8) (E.be_to_n b1l));
  assert (Seq.last b1r == Seq.last b1);
  be_to_n_1 b1r;
  assert (U8.v (Seq.last b1) == E.be_to_n b1r);
  let (Some (v', consumed')) = parse (parse_bounded_integer' 3) b in  
  assert (consumed == consumed');
  let (Some (vl, _)) = parse parse_u16 b in
  let b_ : bytes = Seq.slice b 2 (Seq.length b) in
  let (Some (vr, _)) = parse parse_u8 b_ in
  let (Some (vp, _)) = parse (nondep_then parse_u16 parse_u8) b in
  assume (vp == (vl, vr));
  assert (b1l == Seq.slice b 0 2);
  assert (vl == decode_u16 b1l);
  E.lemma_be_to_n_is_bounded b1l;
  assert (E.be_to_n b1l < pow2 16);
  assert (vl == U16.uint_to_t (E.be_to_n b1l));
  assert (U16.v vl == E.be_to_n b1l);
  assert (vr == Seq.index b_ 0);
  Seq.lemma_index_slice b 2 (Seq.length b) 0;
  assert (vr == Seq.index b 2);
  assert (vr == Seq.index b1 2);
  assert (vr == Seq.last b1);
  assert (v' == parse_bounded_integer_3_synth vp);
  assert (v == v')

#reset-options

let parse_bounded_integer'_3_correct
  (b: bytes)
: Lemma
  (parse (parse_bounded_integer' 3) b == parse (parse_bounded_integer 3) b)
= let pv' = parse (parse_bounded_integer' 3) b in
  if Some? pv'
  then parse_bounded_integer'_3_correct_some b
  else ()
