module LowParse.Impl.Seq
include LowParse.Impl.Combinators
include LowParse.Spec.Seq

module Seq = FStar.Seq
module L = FStar.List.Tot
module S = LowParse.Slice
module PL = LowParse.Impl.List
module B = FStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module Classical = FStar.Classical
module G = FStar.Ghost

val seq_length
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
: HST.Stack U32.t
  (requires (fun h ->
    parses h (parse_seq p) b (fun _ -> True)
  ))
  (ensures (fun h i h' ->
    S.modifies_none h h' /\
    parses h (parse_seq p) b (fun (l, _) ->
    Seq.length l == U32.v i
  )))

let seq_length #k #t #p sv b =
  let h = HST.get () in
  parse_seq_correct p (S.as_seq h b);
  PL.list_length sv b

(* TODO: move to FStar.Seq.Properties *)

val index_seq_of_list
  (#a: Type)
  (l: list a)
  (i: nat)
: Lemma
  (requires (i < L.length l))
  (ensures (
    i < L.length l /\
    i < Seq.length (Seq.seq_of_list l) /\
    Seq.index (Seq.seq_of_list l) i == L.index l i
  ))
  (decreases i)
  [SMTPat (Seq.index (Seq.seq_of_list l) i)]

let rec index_seq_of_list #a l i =
  if i = 0
  then ()
  else
    let (_ :: l') = l in
    index_seq_of_list l' (i - 1)

val seq_index_spec
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (i: U32.t)
  (h: HS.mem)
: Ghost(* Do not remove this comment or add any whitespace before it,
    this is to guard against gtot_to_tot.sh *)
    S.bslice
  (requires (
    parses h (parse_seq p) b (fun (l, _) ->
    U32.v i < Seq.length l
  )))
  (ensures (fun b' ->
    S.includes b b' /\
    parses h (parse_seq p) b (fun (l, _) ->
    exactly_parses h p b' (fun (x) ->
    U32.v i < Seq.length l /\
    x == Seq.index l (U32.v i)
  ))))

#set-options "--z3rlimit 32"

let seq_index_spec #k #t p b i h =
  parse_seq_correct p (S.as_seq h b);
  PL.list_nth_spec p b i h

#reset-options

val seq_index_spec_ext
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (i: U32.t)
  (h h': HS.mem)
: Lemma
  (requires (
    parses h (parse_seq p) b (fun (l, _) -> U32.v i < Seq.length l) /\
    S.live h' b /\
    S.as_seq h' b == S.as_seq h b
  ))
  (ensures (
    parses h (parse_seq p) b (fun (l, _) -> U32.v i < Seq.length l) /\
    parses h' (parse_seq p) b (fun (l, _) -> U32.v i < Seq.length l) /\
    seq_index_spec p b i h' == seq_index_spec p b i h
  ))

let seq_index_spec_ext #k #t p b i h h' =
  parse_seq_correct p (S.as_seq h b);
  PL.list_nth_spec_ext p b i h h'

val seq_index_spec_disjoint
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (i j: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    U32.v i <> U32.v j /\
    parses h (parse_seq p) b (fun (l, _) ->
    U32.v i < Seq.length l /\
    U32.v j < Seq.length l
  )))
  (ensures (
    U32.v i <> U32.v j /\
    parses h (parse_seq p) b (fun (l, _) ->
    U32.v i < Seq.length l /\
    U32.v j < Seq.length l /\
    S.disjoint (seq_index_spec p b i h) (seq_index_spec p b j h)
  )))

let seq_index_spec_disjoint #k #t p b i j h =
  parse_seq_correct p (S.as_seq h b);
  PL.list_nth_spec_disjoint p b i j h

inline_for_extraction
val seq_index
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
: HST.Stack S.bslice
  (requires (fun h ->
    parses h (parse_seq p) b (fun (l, _) ->
    U32.v i < Seq.length l
  )))
  (ensures (fun h b' h' ->
    S.modifies_none h h' /\
    S.includes b b' /\
    parses h (parse_seq p) b (fun (l, _) ->
      U32.v i < Seq.length l
    ) /\
    b' == seq_index_spec p b i h
  ))

let seq_index #k #t p sv b i =
  let h = HST.get () in
  parse_seq_correct p (S.as_seq h b);
  PL.list_nth p sv b i

inline_for_extraction
val validate_seq
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (sv: stateful_validator p)
: Tot (stateful_validator (parse_seq p))

let validate_seq #k #t #p sv =
  fun (input: S.bslice) ->
    let h = HST.get () in
    parse_seq_correct p (S.as_seq h input);
    seq_of_list_inj t;
    validate_synth (PL.validate_list sv) (Seq.seq_of_list) input

let seq_offset_at_spec_nat_postcond
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes)
  (i: nat)
  (result: nat)
: GTot Type0
=   result <= Seq.length input /\ (
    let v = parse (parse_seq p) input in
    let inputl : bytes = Seq.slice input 0 result in
    let vl = parse (parse_seq p) inputl in
    let inputr : bytes = Seq.slice input result (Seq.length input) in
    let vr = parse (parse_seq p) inputr in
    Some? v /\
    Some? vl /\
    Some? vr /\ (
    let (Some (s, _)) = v in
    let (Some (sl, _)) = vl in
    let (Some (sr, _)) = vr in
    i <= Seq.length s /\
    sl == Seq.slice s 0 i /\
    sr == Seq.slice s i (Seq.length s)
  ))

(* TODO: move to FStar.Seq *)

let slice_cons_r
  (#t: Type0)
  (hd: t)
  (tl: Seq.seq t)
  (lo hi: nat)
: Lemma
  (requires (
    1 <= lo /\  lo <= hi /\ hi <= Seq.length tl + 1
  ))
  (ensures (
    1 <= lo /\  lo <= hi /\ hi <= Seq.length tl + 1 /\
    Seq.slice (Seq.cons hd tl) lo hi == Seq.slice tl (lo - 1) (hi - 1)
  ))
//  [SMTPat (Seq.slice (Seq.cons hd tl) lo hi)]
= assert (Seq.equal (Seq.slice (Seq.cons hd tl) lo hi) (Seq.slice tl (lo - 1) (hi - 1)))

let slice_cons_l
  (#t: Type0)
  (hd: t)
  (tl: Seq.seq t)
  (hi: nat)
: Lemma
  (requires (
    1 <= hi /\ hi <= Seq.length tl + 1
  ))
  (ensures (
    1 <= hi /\ hi <= Seq.length tl + 1 /\
    Seq.slice (Seq.cons hd tl) 0 hi == Seq.cons hd (Seq.slice tl 0 (hi - 1))
  ))
//  [SMTPat (Seq.slice (Seq.cons hd tl) 0 hi)]
= assert (Seq.equal (Seq.slice (Seq.cons hd tl) 0 hi) (Seq.cons hd (Seq.slice tl 0 (hi - 1))))

val seq_offset_at_spec_nat
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes)
  (i: nat)
: Ghost nat
  (requires (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    i <= Seq.length s
  )))
  (ensures (fun _ -> True))
  (decreases i)

let rec seq_offset_at_spec_nat #k #t p input i =
  if i = 0
  then 0
  else
    let (Some (_, len)) = parse p input in
    let intl : bytes = Seq.slice input len (Seq.length input) in
    let len' = seq_offset_at_spec_nat p intl (i - 1) in
    len + len'

val seq_offset_at_spec_nat_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes)
  (i: nat)
: Lemma
  (requires (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    i <= Seq.length s
  )))
  (ensures (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    i <= Seq.length s /\
    seq_offset_at_spec_nat_postcond p input i (seq_offset_at_spec_nat p input i)
  )))
  (decreases i)
  [SMTPat (seq_offset_at_spec_nat p input i)]

#set-options "--z3rlimit 256  --smtencoding.l_arith_repr native"

let rec seq_offset_at_spec_nat_correct #k #t p input i =
  if i = 0
  then ()
  else begin
    let (Some (hd, len)) = parse p input in
    let inhd : bytes = Seq.slice input 0 len in
    let intl : bytes = Seq.slice input len (Seq.length input) in
    let result' = seq_offset_at_spec_nat p intl (i - 1) in
    seq_offset_at_spec_nat_correct p intl (i - 1);
    let inputl' : bytes = Seq.slice intl 0 result' in
    let inputr' : bytes = Seq.slice intl result' (Seq.length intl) in
    let result = len + result' in
    assert (result <= Seq.length input);
    let inputl : bytes = Seq.slice input 0 result in
    let inputr : bytes = Seq.slice input result (Seq.length input) in
    assert (no_lookahead_weak_on p input inputl);
    let (Some (hd', len')) = parse p inputl in
    assert (hd == hd');
    assert ((len <: nat) == (len' <: nat));
    assert (inputl' == Seq.slice inputl len (Seq.length inputl));
    let vl = parse (parse_seq p) inputl in
    assert (Some? vl);
    assert (inputr' == inputr);
    let vr = parse (parse_seq p) inputr in
    assert (Some? vr);
    let (Some (sl, _)) = vl in
    let (Some (sr, _)) = vr in
    let (Some (sl', _)) = parse (parse_seq p) inputl' in
    let (Some (s, _)) = parse (parse_seq p) input in
    let (Some (s', _)) = parse (parse_seq p) intl in
    assert (s == Seq.cons hd s');
    assert (i - 1 <= Seq.length s');
    // works here, but I prefer to speed up the proof somewhat
    assert (sl == Seq.cons hd sl');
    slice_cons_r hd s' i (Seq.length s);
    assert (sr == Seq.slice s i (Seq.length s));
    slice_cons_l hd s' i;
    assert (sl == Seq.slice s 0 i);
    assert (seq_offset_at_spec_nat_postcond p input i result);
    ()
  end

#reset-options

val seq_offset_at_spec
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: S.bslice)
  (h: HS.mem)
  (i: U32.t)
: Ghost U32.t
  (requires (
    parses h (parse_seq p) input (fun (s, _) ->
    U32.v i <= Seq.length s
  )))
  (ensures (fun result ->
    U32.v result <= U32.v (S.length input) /\ (
    let sleft = S.truncated_slice input result in
    let sright = S.advanced_slice input result in
    parses h (parse_seq p) input (fun (s, _) ->
    parses h (parse_seq p) sleft (fun (sl, _) ->
    parses h (parse_seq p) sright (fun (sr, _) ->
    U32.v i <= Seq.length s /\
    sl == Seq.slice s 0 (U32.v i) /\
    sr == Seq.slice s (U32.v i) (Seq.length s)
  ))))))

let seq_offset_at_spec #k #t p input h i =
  U32.uint_to_t (seq_offset_at_spec_nat p (S.as_seq h input) (U32.v i))

val seq_offset_at_spec_nat_add
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes)
  (i1 i2: nat)
: Lemma
  (requires (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    i1 <= Seq.length s /\
    i2 <= Seq.length s - i1
  )))
  (ensures (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    i1 <= Seq.length s /\
    i2 <= Seq.length s - i1 /\ (
    let len1 = seq_offset_at_spec_nat p input i1 in
    let input2 : bytes = Seq.slice input len1 (Seq.length input) in
    let len2 = seq_offset_at_spec_nat p input2 i2 in
    seq_offset_at_spec_nat p input (i1 + i2) == len1 + len2
  ))))
  (decreases i1)

#set-options "--z3rlimit 256 --smtencoding.l_arith_repr native"

let rec seq_offset_at_spec_nat_add #k #t p input i1 i2 =
  if i1 = 0
  then ()
  else begin
    let (Some (_, len)) = parse p input in
    let input' : bytes = Seq.slice input len (Seq.length input) in
    let res = seq_offset_at_spec_nat p input (i1 + i2) in
    let (Some _) = parse (parse_seq p) input in
    let (Some _) = parse (parse_seq p) input' in
    let res' = seq_offset_at_spec_nat p input' (i1 - 1 + i2) in
    assert (res == len + res');
    seq_offset_at_spec_nat_add p input' (i1 - 1) i2;
    let len1' = seq_offset_at_spec_nat p input' (i1 - 1) in
    let input2' : bytes = Seq.slice input' len1' (Seq.length input') in
    let len2' = seq_offset_at_spec_nat p input2' i2 in
    assert (res' == len1' + len2');
    let len1 = seq_offset_at_spec_nat p input i1 in
    assert (len1 == len + len1');
    let input2 : bytes = Seq.slice input len1 (Seq.length input) in
    let f () : Lemma (input2 == input2') =
      Seq.slice_slice input len (Seq.length input) len1' (Seq.length input')
    in
    f ();
    let len2 = seq_offset_at_spec_nat p input2 i2 in
    assert (res == len1 + len2)
  end

#reset-options

val seq_offset_at_spec_nat_increases
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes)
  (i1 i2: nat)
: Lemma
  (requires (
    i1 <= i2 /\ (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    i2 <= Seq.length s
  ))))
  (ensures (
    i1 <= i2 /\ (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    i2 <= Seq.length s /\
    seq_offset_at_spec_nat p input i1 <= seq_offset_at_spec_nat p input i2
  ))))
  (decreases i1)

let rec seq_offset_at_spec_nat_increases #k #t p input i1 i2 =
  if i1 = 0
  then ()
  else
    let (Some (_, len)) = parse p input in
    let input' = Seq.slice input len (Seq.length input) in
    seq_offset_at_spec_nat_increases p input' (i1 - 1) (i2 - 1)

val seq_offset_at_spec_nat_last
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes)
: Lemma
  (requires (Some? (parse (parse_seq p) input)))
  (ensures (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    seq_offset_at_spec_nat p input (Seq.length s) == Seq.length input
  )))
  (decreases (Seq.length input))

let rec seq_offset_at_spec_nat_last #k #t p input =
  if Seq.length input = 0
  then ()
  else
    let (Some (_, len)) = parse p input in
    let input' : bytes = Seq.slice input len (Seq.length input) in
    seq_offset_at_spec_nat_last p input'

val seq_offset_at_spec_nat_truncate
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: bytes)
  (i j: nat)
: Lemma
  (requires (
    i <= j /\ (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    j <= Seq.length s
  ))))
  (ensures (
    i <= j /\ (
    let v = parse (parse_seq p) input in
    Some? v /\ (
    let (Some (s, _)) = v in
    j <= Seq.length s /\ (
    let j_ = seq_offset_at_spec_nat p input j in
    let input' : bytes = Seq.slice input 0 j_ in
    let v' = parse (parse_seq p) input' in
    Some? v' /\ (
    let (Some (s', _)) = v in
    i <= Seq.length s' /\
    seq_offset_at_spec_nat p input' i == seq_offset_at_spec_nat p input i
  ))))))
  (decreases i)

#set-options "--z3rlimit 64"

let rec seq_offset_at_spec_nat_truncate #k #t p input i j =
  if i = 0
  then ()
  else begin
    let (Some (s, _)) = parse (parse_seq p) input in
    let j_ = seq_offset_at_spec_nat p input j in
    seq_offset_at_spec_nat_correct p input j;
    let (Some (v, len)) = parse p input in
    let inputq : bytes = Seq.slice input len (Seq.length input) in
    let (Some (sq, _)) = parse (parse_seq p) inputq in
    assert (s == Seq.cons v sq);
    let j_q = seq_offset_at_spec_nat p inputq (j - 1) in
    seq_offset_at_spec_nat_correct p inputq (j - 1);
    assert (j_ == len + j_q);
    let input' : bytes = Seq.slice input 0 j_ in
    assert (no_lookahead_weak_on p input input');
    let (Some (v', len')) = parse p input' in
    assert (v == v');
    assert ((len <: nat) == (len' <: nat));
    seq_offset_at_spec_nat_truncate p inputq (i - 1) (j - 1)
  end

#reset-options

let seq_offset_at_inv
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
  (h0: G.erased HS.mem)
  (sl: B.buffer U32.t)
  (h: HS.mem)
  (j: nat)
: GTot Type0
= B.disjoint (S.as_buffer b) sl /\
  B.length sl == 1 /\
  B.modifies_1 sl (G.reveal h0) h /\
  parses (G.reveal h0) (parse_seq p) b (fun (s, _) ->
    U32.v i <= Seq.length s
  ) /\
  j <= U32.v i /\
  B.live h sl /\ (
    let i' = Seq.index (B.as_seq h sl) 0 in
    i' == seq_offset_at_spec p b (G.reveal h0) (U32.uint_to_t j)
  )

inline_for_extraction
val seq_offset_at_advance
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
  (h0: G.erased HS.mem)
  (sl: B.buffer U32.t)
  (j: U32.t)
: HST.Stack unit
  (requires (fun h ->
    seq_offset_at_inv p sv b i h0 sl h (U32.v j) /\
    U32.v j < U32.v i
  ))
  (ensures (fun h1 _ h2 ->
    seq_offset_at_inv p sv b i h0 sl h1 (U32.v j) /\
    U32.v j < U32.v i /\
    seq_offset_at_inv p sv b i h0 sl h2 (U32.v j + 1)
  ))

#set-options "--z3rlimit 256"

let seq_offset_at_advance #k #t p sv b i h0 sl j =
  let h1 = HST.get () in
  let i1 = B.index sl 0ul in
  let b' = S.advance_slice b i1 in
  let len = sv b' in
  let i2 = U32.add i1 len in
  let h2 = HST.get () in
  assert (B.modifies_none h1 h2);
  B.upd sl 0ul i2;
  seq_offset_at_spec_nat_add p (S.as_seq (G.reveal h0) b) (U32.v j) (U32.v i - U32.v j);
  seq_offset_at_spec_nat_add p (S.as_seq (G.reveal h0) b) (U32.v j) 1;
  seq_offset_at_spec_nat_add p (S.as_seq (G.reveal h0) b) (U32.v j + 1) (U32.v i - (U32.v j + 1));
  let h3 = HST.get () in
  B.lemma_modifies_none_1_trans sl h1 h2 h3

#reset-options

let seq_offset_at_pcond
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (i: U32.t)
  (h: HS.mem)
  (res: U32.t)
: GTot Type0
=   parses h (parse_seq p) b (fun (s, _) ->
      U32.v i <= Seq.length s
    ) /\
    res == seq_offset_at_spec p b h i

inline_for_extraction
val seq_offset_at
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    parses h (parse_seq p) b (fun (s, _) ->
      U32.v i <= Seq.length s
    )
  ))
  (ensures (fun h1 res h2 ->
    S.modifies_none h1 h2 /\
    seq_offset_at_pcond p b i h1 res
  ))

#set-options "--z3rlimit 16"

let seq_offset_at #k #t p sv b i =
  let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let sl : B.buffer U32.t = B.create 0ul 1ul in
  let h2 = HST.get () in
  C.Loops.for
    0ul
    i
    (fun h j -> seq_offset_at_inv p sv b i (G.hide h2) sl h j)
    (fun j -> seq_offset_at_advance p sv b i (G.hide h2) sl j)
  ;
  let res = B.index sl 0ul in  
  let h3 = HST.get () in
  B.lemma_modifies_0_1' sl h1 h2 h3;
  HST.pop_frame ();
  let h4 = HST.get () in
  B.lemma_modifies_0_push_pop h0 h1 h3 h4;
  res

#reset-options

val seq_slice_spec
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (h: HS.mem)
  (lo hi: U32.t)
: Ghost S.bslice
  (requires (
    U32.v lo <= U32.v hi /\
    parses h (parse_seq p) b (fun (s, _) ->
    U32.v hi <= Seq.length s
  )))
  (ensures (fun res ->
    S.includes b res /\
    U32.v lo <= U32.v hi /\
    parses h (parse_seq p) b (fun (s, _) ->
    U32.v hi <= Seq.length s /\
    parses h (parse_seq p) res (fun (s', _) ->
    s' == Seq.slice s (U32.v lo) (U32.v hi)
  ))))

#set-options "--z3rlimit 512"

let seq_slice_spec #k #t p b h lo hi =
  let len1 = seq_offset_at_spec p b h lo in
  seq_offset_at_spec_nat_correct p (S.as_seq h b) (U32.v lo);
  let b1 = S.advanced_slice b len1 in
  let len2 = seq_offset_at_spec p b1 h (U32.sub hi lo) in
  seq_offset_at_spec_nat_correct p (S.as_seq h b1) (U32.v hi - U32.v lo);
  let b2 = S.truncated_slice b1 len2 in
  seq_offset_at_spec_nat_add p (S.as_seq h b) (U32.v lo) (U32.v hi - U32.v lo);
  b2

#reset-options

val seq_slice_spec'
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (h: HS.mem)
  (lo hi: U32.t)
: Ghost S.bslice
  (requires (
    U32.v lo <= U32.v hi /\
    parses h (parse_seq p) b (fun (s, _) ->
    U32.v hi <= Seq.length s
  )))
  (ensures (fun res ->
    U32.v lo <= U32.v hi /\
    parses h (parse_seq p) b (fun (s, _) ->
      U32.v hi <= Seq.length s
    ) /\
    res == seq_slice_spec p b h lo hi
  ))

#set-options "--z3rlimit 32"

let seq_slice_spec' #k #t p b h lo hi =
  let hi_ = seq_offset_at_spec p b h hi in
  let b1 = S.truncated_slice b hi_ in
  let lo_ = seq_offset_at_spec p b h lo in
  seq_offset_at_spec_nat_increases p (S.as_seq h b) (U32.v lo) (U32.v hi);
  let b2 = S.advanced_slice b1 lo_ in
  S.advanced_slice_truncated_slice b hi_ lo_;
  seq_offset_at_spec_nat_add p (S.as_seq h b) (U32.v lo) (U32.v hi - U32.v lo);
  b2

let seq_slice_spec_le_disjoint
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (h: HS.mem)
  (lo1 hi1 lo2 hi2: U32.t)
: Lemma
  (requires (
    U32.v lo1 <= U32.v hi1 /\
    U32.v hi1 <= U32.v lo2 /\
    U32.v lo2 <= U32.v hi2 /\
    parses h (parse_seq p) b (fun (s, _) ->
    U32.v hi2 <= Seq.length s
  )))
  (ensures (
    U32.v lo1 <= U32.v hi1 /\
    U32.v hi1 <= U32.v lo2 /\
    U32.v lo2 <= U32.v hi2 /\
    parses h (parse_seq p) b (fun (s, _) ->
      U32.v hi2 <= Seq.length s
    ) /\
    S.disjoint (seq_slice_spec p b h lo1 hi1) (seq_slice_spec p b h lo2 hi2)
  ))
= let b1 = seq_slice_spec' p b h lo1 hi1 in
  let b2 = seq_slice_spec p b h lo2 hi2 in
  let hi1_ = seq_offset_at_spec p b h hi1 in
  let bl1_ = S.truncated_slice b hi1_ in
  let lo1_ = seq_offset_at_spec p b h lo1 in
  seq_offset_at_spec_nat_increases p (S.as_seq h b) (U32.v lo1) (U32.v hi1);
  assert (b1 == S.advanced_slice bl1_ lo1_);
  let lo2_ = seq_offset_at_spec p b h lo2 in
  let bl2_ = S.advanced_slice b lo2_ in
  let hi2_ = seq_offset_at_spec p bl2_ h (U32.sub hi2 lo2) in
  seq_offset_at_spec_nat_correct p (S.as_seq h bl2_) (U32.v hi2 - U32.v lo2);
  assert (b2 == S.truncated_slice bl2_ hi2_);
  let inc1 () : Lemma (S.includes bl1_ b1) =
    S.includes_advanced_slice bl1_ lo1_
  in
  let inc2 () : Lemma (S.includes bl2_ b2) =
    S.includes_truncated_slice bl2_ hi2_
  in
  let disj () : Lemma (S.disjoint bl1_ bl2_) =
    seq_offset_at_spec_nat_increases p (S.as_seq h b) (U32.v hi1) (U32.v lo2);
    S.disjoint_truncated_slice_advanced_slice b hi1_ lo2_
  in
  let f () : Lemma (S.disjoint b1 b2) =
    inc1 (); inc2 (); disj ();
    S.disjoint_includes bl1_ bl2_ b1 b2
  in
  f ()

#reset-options

val seq_slice_spec_disjoint
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (h: HS.mem)
  (lo1 hi1 lo2 hi2: U32.t)
: Lemma
  (requires (
    U32.v lo1 <= U32.v hi1 /\
    U32.v lo2 <= U32.v hi2 /\
    (U32.v hi1 <= U32.v lo2 \/ U32.v hi2 <= U32.v lo1) /\
    parses h (parse_seq p) b (fun (s, _) ->
    U32.v hi1 <= Seq.length s /\
    U32.v hi2 <= Seq.length s
  )))
  (ensures (
    U32.v lo1 <= U32.v hi1 /\
    U32.v lo2 <= U32.v hi2 /\
    parses h (parse_seq p) b (fun (s, _) ->
      U32.v hi1 <= Seq.length s /\
      U32.v hi2 <= Seq.length s
    ) /\
    S.disjoint (seq_slice_spec p b h lo1 hi1) (seq_slice_spec p b h lo2 hi2)
  ))

let seq_slice_spec_disjoint #k #t p b h lo1 hi1 lo2 hi2 =
  if U32.v hi1 <= U32.v lo2
  then seq_slice_spec_le_disjoint p b h lo1 hi1 lo2 hi2
  else seq_slice_spec_le_disjoint p b h lo2 hi2 lo1 hi1

#set-options "--z3rlimit 16"

val seq_slice_seq_slice
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (h: HS.mem)
  (lo1 hi1 lo2 hi2: U32.t)
: Lemma
  (requires (
    U32.v lo1 <= U32.v hi1 /\
    U32.v lo2 <= U32.v hi2 /\
    U32.v hi2 <= U32.v hi1 - U32.v lo1 /\
    parses h (parse_seq p) b (fun (s, _) ->
    U32.v hi1 <= Seq.length s
  )))
  (ensures (
    U32.v lo1 <= U32.v hi1 /\
    U32.v lo2 <= U32.v hi2 /\
    U32.v hi2 <= U32.v hi1 - U32.v lo1 /\
    parses h (parse_seq p) b (fun (s, _) ->
      U32.v hi1 <= Seq.length s
    ) /\
    seq_slice_spec p (seq_slice_spec p b h lo1 hi1) h lo2 hi2 ==
    seq_slice_spec p b h (U32.add lo1 lo2) (U32.add lo1 hi2)
  ))

#set-options "--z3rlimit 512"

let seq_slice_seq_slice #k #t p b h lo1 hi1 lo2 hi2 =
  let b1 = seq_slice_spec' p b h lo1 hi1 in
  let b2 = seq_slice_spec' p b1 h lo2 hi2 in
  let hi1_ = seq_offset_at_spec p b h hi1 in
  seq_offset_at_spec_nat_correct p (S.as_seq h b) (U32.v hi1);
  let bl1 = S.truncated_slice b hi1_ in
  let lo1_ = seq_offset_at_spec p b h lo1 in
  seq_offset_at_spec_nat_correct p (S.as_seq h b) (U32.v lo1);
  seq_offset_at_spec_nat_increases p (S.as_seq h b) (U32.v lo1) (U32.v hi1);
  assert (b1 == S.advanced_slice bl1 lo1_);
  let hi2_ = seq_offset_at_spec p b1 h hi2 in
  seq_offset_at_spec_nat_correct p (S.as_seq h b1) (U32.v hi2);
  let bl2 = S.truncated_slice b1 hi2_ in
  let lo2_ = seq_offset_at_spec p b1 h lo2 in
  seq_offset_at_spec_nat_correct p (S.as_seq h b1) (U32.v lo2);
  seq_offset_at_spec_nat_increases p (S.as_seq h b1) (U32.v lo2) (U32.v hi2);
  assert (b2 == S.advanced_slice bl2 lo2_);
  let br1 = S.truncated_slice bl1 (U32.add lo1_ hi2_) in
  let f1 () : Lemma (bl2 == S.advanced_slice br1 lo1_) =
    S.truncated_slice_advanced_slice bl1 lo1_ hi2_
  in
  let f2 () : Lemma (br1 == S.truncated_slice b (U32.add lo1_ hi2_)) =
    S.truncated_slice_truncated_slice b hi1_ (U32.add lo1_ hi2_)
  in
  let f3 () : Lemma (b2 == S.advanced_slice br1 (U32.add lo1_ lo2_)) =
    f1 ();
    S.advanced_slice_advanced_slice br1 lo1_ lo2_
  in
  f2 (); f3 ();
  let b0 = S.advanced_slice b lo1_ in
  seq_offset_at_spec_nat_add p (S.as_seq h b) (U32.v lo1) (U32.v hi1 - U32.v lo1);
  assert (b1 == S.truncated_slice b0 (U32.sub hi1_ lo1_));
  let f4 () : Lemma (lo2_ == seq_offset_at_spec p b0 h lo2) =
    seq_offset_at_spec_nat_truncate p (S.as_seq h b0) (U32.v lo2) (U32.v hi1 - U32.v lo1)
  in
  let f5 () : Lemma (hi2_ == seq_offset_at_spec p b0 h hi2) =
    seq_offset_at_spec_nat_truncate p (S.as_seq h b0) (U32.v hi2) (U32.v hi1 - U32.v lo1)
  in
  f4 (); f5 ();
  seq_offset_at_spec_nat_add p (S.as_seq h b) (U32.v lo1) (U32.v lo2);
  seq_offset_at_spec_nat_add p (S.as_seq h b) (U32.v lo1) (U32.v hi2);
  let b' = seq_slice_spec' p b h (U32.add lo1 lo2) (U32.add lo1 hi2) in
  assert (b2 == b')

#reset-options


inline_for_extraction
val seq_slice
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (lo hi: U32.t)
: HST.Stack S.bslice
  (requires (fun h ->
    U32.v lo <= U32.v hi /\
    parses h (parse_seq p) b (fun (s, _) ->
    U32.v hi <= Seq.length s
  )))
  (ensures (fun h res h' ->
    S.modifies_none h h' /\
    U32.v lo <= U32.v hi /\
    parses h (parse_seq p) b (fun (s, _) ->
      U32.v hi <= Seq.length s
    ) /\
    res == seq_slice_spec p b h lo hi 
  ))

#set-options "--z3rlimit 16"

let seq_slice #k #t #p sv b lo hi =
  let h = HST.get () in
  let len1 = seq_offset_at p sv b lo in
  let h1 = HST.get () in
  assert (U32.v len1 == seq_offset_at_spec_nat p (S.as_seq h b) (U32.v lo));
  seq_offset_at_spec_nat_correct p (S.as_seq h b) (U32.v lo);
  assert (Seq.length (S.as_seq h b) == U32.v (S.length b));
  let b1 = S.advance_slice b len1 in
  let h1 = HST.get () in
  assert (S.as_seq h1 b1 == S.as_seq h b1);
  assert (Seq.length (S.as_seq h b1) == U32.v (S.length b1));
  let len2 = seq_offset_at p sv b1 (U32.sub hi lo) in
  assert (U32.v len2 == seq_offset_at_spec_nat p (S.as_seq h b1) (U32.v hi - U32.v lo));
  seq_offset_at_spec_nat_correct p (S.as_seq h b1) (U32.v hi - U32.v lo);
  let b2 = S.truncate_slice b1 len2 in
  assert (b2 == seq_slice_spec p b h lo hi);
  b2

#reset-options
