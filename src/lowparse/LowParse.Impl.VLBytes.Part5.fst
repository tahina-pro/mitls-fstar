module LowParse.Impl.VLBytes.Part5
include LowParse.Impl.VLBytes.Part3
include LowParse.Impl.VLBytes.Part4

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
val point_to_vlbytes_contents
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
: HST.Stack S.bslice
  (requires (fun h ->
    parses h (parse_vlbytes_gen sz f p) b (fun _ -> True)
  ))
  (ensures (fun h0 b' h1 ->
    S.modifies_none h0 h1 /\
    point_to_vlbytes_contents_postcond sz f p b h0 b'
  ))

#set-options "--z3rlimit 64"

let point_to_vlbytes_contents sz f #k #t p b =
  let h = HST.get () in
  let (len, _) = parse_bounded_integer_st_nochk sz b in
  let b1 = S.advance_slice b (U32.uint_to_t sz) in
  let b' = S.truncate_slice b1 len in
  assert (point_to_vlbytes_contents_correct_precond sz f p b h len b1 b');
  point_to_vlbytes_contents_correct sz f p b h len b1 b';
  b'

#reset-options

val serialize_vlbytes_gen_correct_aux
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b b1 b2: bytes)
: Lemma
  (requires (
    Seq.length b1 == sz /\ (
    let vlen = parse (parse_bounded_integer sz) b1 in
    Some? vlen /\ (
    let (Some (len, _)) = vlen in
    f len == true /\
    Seq.length b2 == U32.v len /\ (
    let vv = parse p b2 in
    Some? vv /\ (
    let (Some (_, consumed)) = vv in
    consumed == Seq.length b2 /\
    Seq.length b1 <= Seq.length b /\
    Seq.slice b 0 (Seq.length b1) == b1 /\
    Seq.slice b (Seq.length b1) (Seq.length b) == b2
  ))))))
  (ensures (
    let vv = parse p b2 in
    Some? vv /\ (
    let (Some (v, consumed)) = vv in
    let vv' = parse (parse_vlbytes_gen sz f p) b in
    Some? vv' /\ (
    let (Some (v', consumed')) = vv' in
    v == v' /\
    consumed == Seq.length b2 /\
    consumed' == Seq.length b
  ))))

#set-options "--z3rlimit 64"

let serialize_vlbytes_gen_correct_aux sz f #k #t p b b1 b2 =
  let (Some (len, consumed1)) = parse (parse_bounded_integer sz) b1 in
  assert (consumed1 == sz);
  assert (no_lookahead_on (parse_bounded_integer sz) b1 b);
  let v1' = parse (parse_bounded_integer sz) b in
  assert (Some? v1');
  let (Some (len', consumed1')) = v1' in
  assert (consumed1' == sz);
  assert (injective_postcond (parse_bounded_integer sz) b1 b);
  assert (len' == len);
  let v1_ = parse (parse_filter (parse_bounded_integer sz) f) b in
  assert (Some? v1_);
  let (Some (len_, consumed1_)) = v1_ in
  assert (consumed1_ == sz);
  assert ((len_ <: bounded_integer sz) == len);
  ()

#reset-options

#set-options "--z3rlimit 16"

let serialize_vlbytes_gen_correct
  (sz: integer_size)
  (f: (bounded_integer sz -> Tot bool))
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b b1 b2: S.bslice)
  (h: HS.mem)
: Lemma
  (requires (
    S.is_concat b b1 b2 /\ (
    let len = S.length b2 in
    U32.v len < pow2 (FStar.Mul.op_Star 8 sz) /\
    f (len <: bounded_integer sz) == true /\
    exactly_parses h (parse_bounded_integer sz) b1 (fun v -> (v <: U32.t) == len) /\
    exactly_parses h p b2 (fun _ -> True)
  )))
  (ensures (
    exactly_parses h (parse_vlbytes_gen sz f p) b (fun v ->
    exactly_parses h p b2 (fun v' ->
    v == v'
  ))))
= let s = S.as_seq h b in
  let s1 = S.as_seq h b1 in
  let s2 = S.as_seq h b2 in
  serialize_vlbytes_gen_correct_aux sz f p s s1 s2

#reset-options

module B = FStar.Buffer

let serialize_bounded_integer_t
  (sz: integer_size)
: Tot Type
= (i: bounded_integer sz) ->
  (dest: S.bslice) ->
  HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.live h dest /\
    U32.v (S.length dest) >= sz
  ))
  (ensures (fun h (destl, destr) h' ->
    S.is_concat dest destl destr /\
    U32.v (S.length destl) == sz /\
    S.live h' destr /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    exactly_parses h' (parse_bounded_integer' sz) destl (fun i' ->
    i' == i
  )))

let serialize_bounded_integer_3_unsynth
  (i: bounded_integer 3)
: Tot (U16.t * U8.t)
= let lo = Cast.uint32_to_uint8 (U32.rem i 256ul) in
  let i' = U32.div i 256ul in
  let hi = Cast.uint32_to_uint16 i' in
  (hi, lo)

#set-options "--z3rlimit 256 --smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"

let serialize_bounded_integer_3_unsynth_correct
  (i: bounded_integer 3)
: Lemma
  (parse_bounded_integer_3_synth (serialize_bounded_integer_3_unsynth i) == i)
= ()

#reset-options

inline_for_extraction
val serialize_bounded_integer_3
: serialize_bounded_integer_t 3

#set-options "--z3rlimit 64"

let serialize_bounded_integer_3 = fun (i: bounded_integer 3) (dest: S.bslice) ->
  let h = HST.get () in
  let destl = S.truncate_slice dest 3ul in
  let destr = S.advance_slice dest 3ul in
  let (hi, lo) = serialize_bounded_integer_3_unsynth i in
  let (dhi, d1) = serialize_u16 hi destl in
  let h1 = HST.get () in
//  assert (exactly_parses h1 parse_u16 dhi (fun v1 -> v1 == hi));
  let (dlo, _) = serialize_u8 lo d1 in
  let h' = HST.get () in
  assert (dlo == d1);
//  assert (exactly_parses h' parse_u8 dlo (fun v2 -> v2 == lo));
  S.disjoint_truncated_slice_advanced_slice destl 2ul 2ul;
  assert (S.disjoint dhi dlo);
  assert (S.as_seq h' dhi == S.as_seq h1 dhi);
//  assert (exactly_parses h' parse_u16 dhi (fun v1 -> v1 == hi));
  serialize_nondep_then_correct parse_u16 parse_u8 destl dhi dlo h';
//  assert (exactly_parses h' (nondep_then parse_u16 parse_u8) destl (fun v -> v == (hi, lo)));
  parse_bounded_integer_3_synth_injective ();
  serialize_synth_correct (nondep_then parse_u16 parse_u8) parse_bounded_integer_3_synth destl h';
//  assert (exactly_parses h' parse_bounded_integer_3 destl (fun v -> v == parse_bounded_integer_3_synth (hi, lo)));
  serialize_bounded_integer_3_unsynth_correct i;
  (destl, destr)

#reset-options

inline_for_extraction
val serialize_bounded_integer_1
: serialize_bounded_integer_t 1

#set-options "--z3rlimit 16"

let serialize_bounded_integer_1 = fun (i: bounded_integer 1) (dest: S.bslice) ->
  assert (U32.v i < pow2 8);
  assert (U32.v i % pow2 8 == U32.v i);
  assert (Cast.uint8_to_uint32 (Cast.uint32_to_uint8 i) == i);
  let (destl, destr) = serialize_u8 (Cast.uint32_to_uint8 i) dest in
  let h = HST.get () in
  serialize_synth_correct parse_u8 parse_bounded_integer_1_synth destl h;
  (destl, destr)

#reset-options

inline_for_extraction
val serialize_bounded_integer_2
: serialize_bounded_integer_t 2

#set-options "--z3rlimit 16"

let serialize_bounded_integer_2 = fun (i: bounded_integer 2) (dest: S.bslice) ->
  assert (U32.v i < pow2 16);
  assert (U32.v i % pow2 16 == U32.v i);
  assert (Cast.uint16_to_uint32 (Cast.uint32_to_uint16 i) == i);
  let (destl, destr) = serialize_u16 (Cast.uint32_to_uint16 i) dest in
  let h = HST.get () in
  serialize_synth_correct parse_u16 parse_bounded_integer_2_synth destl h;
  (destl, destr)

#reset-options

inline_for_extraction
val serialize_bounded_integer_4
: serialize_bounded_integer_t 4

#set-options "--z3rlimit 16"

let serialize_bounded_integer_4 = fun (i: bounded_integer 4) (dest: S.bslice) ->
  serialize_u32 i dest

#reset-options

inline_for_extraction
let serialize_bounded_integer'
  (sz: integer_size)
: Tot (serialize_bounded_integer_t sz)
= match sz with
  | 1 -> (serialize_bounded_integer_1 <: serialize_bounded_integer_t sz)
  | 2 -> (serialize_bounded_integer_2 <: serialize_bounded_integer_t sz)
  | 3 -> (serialize_bounded_integer_3 <: serialize_bounded_integer_t sz)
  | 4 -> (serialize_bounded_integer_4 <: serialize_bounded_integer_t sz)

inline_for_extraction
val serialize_bounded_integer
  (sz: integer_size)
  (i: bounded_integer sz)
  (dest: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.live h dest /\
    U32.v (S.length dest) >= sz
  ))
  (ensures (fun h (destl, destr) h' ->
    S.is_concat dest destl destr /\
    U32.v (S.length destl) == sz /\
    S.live h' destr /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    exactly_parses h' (parse_bounded_integer sz) destl (fun i' ->
    i' == i
  )))

let serialize_bounded_integer sz i dest =
  Classical.forall_intro (parse_bounded_integer'_correct sz);
  serialize_bounded_integer' sz i dest

#set-options "--z3rlimit 16"

module B = FStar.Buffer

inline_for_extraction
val serialize_vlbytes_gen
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: integer_size)
  (sz' : U32.t)
  (f: (bounded_integer sz -> Tot bool))
  (src: S.bslice)
  (dest: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.live h dest /\
    S.disjoint dest src /\
    exactly_parses h p src (fun _ -> True) /\ (
    let len = S.length src in
    let len' = U32.v len in
    len' < pow2 (FStar.Mul.op_Star 8 sz) /\
    sz + len' <= U32.v (S.length dest) /\
    U32.v sz' == sz /\
    f len == true
  )))
  (ensures (fun h (destl, destr) h' ->
    S.is_concat dest destl destr /\
    U32.v (S.length destl) == sz + U32.v (S.length src) /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    S.live h' destr /\
    exactly_parses h p src (fun v ->
    exactly_parses h' p src (fun v' ->
    exactly_parses h' (parse_vlbytes_gen sz f p) destl (fun v'' ->
    v == v' /\ v == v''
  )))))

#reset-options

#set-options "--z3rlimit 128 --smtencoding.elim_box true"

let serialize_vlbytes_gen #k #t p sz sz' f src dest =
  let len = S.length src in
  let len' = U32.add sz' len in
  let destl = S.truncate_slice dest len' in
  let destr = S.advance_slice dest len' in
  let (d1, d2) = serialize_bounded_integer sz len destl in
  let (d2', _) = serialize_copy p d2 src in
  assert (d2' == d2);
  let h' = HST.get () in
  serialize_vlbytes_gen_correct sz f p destl d1 d2 h' ;
  (destl, destr)

#reset-options

inline_for_extraction
val serialize_vlbytes
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: integer_size)
: (src: S.bslice) ->
  (dest: S.bslice) ->
  HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.live h dest /\
    S.disjoint dest src /\
    exactly_parses h p src (fun _ -> True) /\ (
    let len = S.length src in
    let len' = U32.v len in
    len' < pow2 (FStar.Mul.op_Star 8 sz) /\
    sz + len' <= U32.v (S.length dest)
  )))
  (ensures (fun h (destl, destr) h' ->
    S.is_concat dest destl destr /\
    U32.v (S.length destl) == sz + U32.v (S.length src) /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    S.live h' destr /\
    exactly_parses h p src (fun v ->
    exactly_parses h' p src (fun v' ->
    exactly_parses h' (parse_vlbytes sz p) destl (fun v'' ->
    v == v' /\ v == v''
  )))))
  
let serialize_vlbytes #k #t p sz =
  let sz' = U32.uint_to_t sz in
  serialize_vlbytes_gen p sz sz' (unconstrained_bounded_integer sz)

inline_for_extraction
val serialize_bounded_vlbytes
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (min: U32.t)
  (max: U32.t { U32.v max > 0 } )
: (src: S.bslice) ->
  (dest: S.bslice) ->
  HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.live h dest /\
    S.disjoint dest src /\
    exactly_parses h p src (fun _ -> True) /\ (
    let len = S.length src in
    let len' = U32.v len in
    let sz : integer_size = log256 max in
    U32.v min <= len' /\
    len' <= U32.v max /\
    sz + len' <= U32.v (S.length dest)
  )))
  (ensures (fun h (destl, destr) h' ->
    let sz : integer_size = log256 max in
    S.is_concat dest destl destr /\
    U32.v (S.length destl) == sz + U32.v (S.length src) /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    S.live h' destr /\
    exactly_parses h p src (fun v ->
    exactly_parses h' p src (fun v' ->
    exactly_parses h' (parse_bounded_vlbytes min max p) destl (fun v'' ->
    v == v' /\ v == v''
  )))))
  
let serialize_bounded_vlbytes #k #t p min max =
  let sz : integer_size = log256 max in
  let sz' : U32.t = U32.uint_to_t sz in
  serialize_vlbytes_gen p sz sz' (in_bounds min max)
