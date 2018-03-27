module LowParse.Impl.VLBytes.Part2.Subpart2
include LowParse.Impl.VLBytes.Part1

#set-options "--z3rlimit 64"

module U32 = FStar.UInt32
module E = FStar.Kremlin.Endianness
module Cast = FStar.Int.Cast
module U16 = FStar.UInt16

let parse_bounded_integer'_2_correct
  (b: bytes)
: Lemma
  (parse (parse_bounded_integer' 2) b == parse (parse_bounded_integer 2) b)
= if Seq.length b < 2
  then ()
  else begin
    let ps' = parse (parse_bounded_integer' 2) b in
    assert (Some? ps');
    let (Some (v', consumes')) = ps' in
    let ps = parse (parse_bounded_integer 2) b in
    assert (Some? ps);
    let (Some (v, consumes)) = ps in
    assert (consumes' == consumes);
    let p16 = parse parse_u16 b in
    assert (Some? p16);
    let (Some (v16, _)) = p16 in
    assert_norm (ps' == parse (parse_synth parse_u16 parse_bounded_integer_2_synth) b);
    assert (v' == parse_bounded_integer_2_synth v16);
    assert (U32.v v' == U16.v v16);
    let s = Seq.slice b 0 2 in
    assert (v16 == decode_u16 s);
    E.lemma_be_to_n_is_bounded s;
    assert (v16 == U16.uint_to_t (E.be_to_n s));
    assert (U16.v v16 == E.be_to_n s);
    assert (v' == v)
  end

#reset-options
