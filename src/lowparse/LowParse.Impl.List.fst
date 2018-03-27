module LowParse.Impl.List
include LowParse.Impl.Combinators
include LowParse.Spec.List

module Seq = FStar.Seq
module L = FStar.List.Tot
module S = LowParse.Slice
module B = FStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module Classical = FStar.Classical
module G = FStar.Ghost

(* No stateful parser for lists, because we do not know how to extract the resulting list -- or even the list while it is being constructed *)

let parse_list_exactly_parses
  (h: HS.mem)
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (s: S.bslice)
  (pred: ((list t * consumed_slice_length s) -> GTot Type0))
: Lemma
  (requires (parses h (parse_list p) s pred))
  (ensures (exactly_parses h (parse_list p) s (fun v -> pred (v, S.length s))))
= parses_consumes_all_exactly_parses h (parse_list p) s pred

inline_for_extraction
val list_head_tail
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    parses h (parse_list p) b (fun (l, _) ->
    Cons? l
  )))
  (ensures (fun h r h' ->
    S.modifies_none h h' /\ (
    let (bh, bt) = r in
    S.is_concat_gen b [bh; bt] /\
    parses h (parse_list p) b (fun (l, _) ->
    exactly_parses h p bh (fun a ->
    parses h' (parse_list p) bt (fun (q, _) ->
    l == a :: q
  ))))))

let list_head_tail #k #t #p sv b =
  split sv b

inline_for_extraction
val list_is_empty
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
: HST.Stack bool
  (requires (fun h ->
    parses h (parse_list p) b (fun _ -> True)
  ))
  (ensures (fun h b' h' ->
    S.modifies_none h h' /\
    parses h (parse_list p) b (fun (l, _) ->
    b' == Nil? l
  )))

let list_is_empty #k #t p b =
  S.length b = 0ul

let list_length_inv
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (h0: G.erased HS.mem)
  (sl: B.buffer S.bslice)
  (h: HS.mem)
  (j: nat)
  (interrupt: bool)
: GTot Type0
= B.modifies_1 sl (G.reveal h0) h /\
  B.disjoint sl (S.as_buffer b) /\
  B.length sl == 1 /\
  B.live h sl /\ (
  let s = Seq.index (B.as_seq h sl) 0 in
  S.includes b s /\
  j + U32.v (S.length s) <= U32.v (S.length b) /\
  parses (G.reveal h0) (parse_list p) b (fun (l, _) ->
  parses (G.reveal h0) (parse_list p) s (fun (l', _) ->
    if interrupt
    then
      (L.length l + 1 == j)
    else
      L.length l == j + L.length l'
  )))

inline_for_extraction
val list_length_advance
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (h0: G.erased HS.mem)
  (sl: B.buffer S.bslice)
  (j: U32.t)
: HST.Stack bool
  (requires (fun h ->
    U32.v j < U32.v (S.length b) /\
    list_length_inv p sv b h0 sl h (U32.v j) false
  ))
  (ensures (fun h interrupt h' ->
    U32.v j < U32.v (S.length b) /\
    list_length_inv p sv b h0 sl h (U32.v j) false /\
    list_length_inv p sv b h0 sl h' (U32.v j + 1) interrupt
  ))

#set-options "--z3rlimit 1024"

let list_length_advance #k #t p sv b h0 sl j =
  let s = B.index sl 0ul in
  if S.length s = 0ul
  then true
  else begin
    let h = HST.get () in
    let len = sv s in
    let s' = S.advance_slice s len in
    let h2 = HST.get () in
    assert (B.modifies_none h h2);
    B.lemma_intro_modifies_1 sl h h2;
    B.upd sl 0ul s' ;
    false
  end

#reset-options

inline_for_extraction
val list_length
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
: HST.Stack U32.t
  (requires (fun h ->
    parses h (parse_list p) b (fun _ -> True)
  ))
  (ensures (fun h i h' ->
    S.modifies_none h h' /\
    parses h (parse_list p) b (fun (l, _) ->
    L.length l == U32.v i
  )))

#set-options "--z3rlimit 64"

let list_length #k #t #p sv b =
  let h0 = HST.get () in
  HST.push_frame () ;
  let h1 = HST.get () in
  let sl : B.buffer S.bslice = B.create b 1ul in
  let h2 = HST.get () in
  let len = S.length b in
  let (j, interrupt) = C.Loops.interruptible_for
    0ul
    len
    (fun h j -> list_length_inv p sv b (G.hide h2) sl h j)
    (fun j -> list_length_advance p sv b (G.hide h2) sl j)
  in
  let res =
    if interrupt
    then U32.sub j 1ul
    else j
  in
  let h3 = HST.get () in
  HST.pop_frame () ;
  let h4 = HST.get () in
  B.lemma_modifies_0_push_pop h0 h1 h3 h4;
  res

#reset-options

val list_length_constant_size_parser_correct'
  (#n: U32.t)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize (U32.v n) k)) t)
  (b: S.bslice)
  (h: HS.mem)
: Lemma
  (requires (
    U32.v n <> 0 /\
    parses h (parse_list p) b (fun _ -> True)
  ))
  (ensures (
    U32.v n <> 0 /\
    parses h (parse_list p) b (fun (l, _) ->
    FStar.Mul.op_Star (L.length l) (U32.v n) == U32.v (S.length b) /\
    L.length l == U32.v (U32.div (S.length b) n)
  )))
  (decreases (U32.v (S.length b)))

let list_length_constant_size_parser_correct' #n #k #t p b h =
  let s = S.as_seq h b in
  list_length_constant_size_parser_correct p s;
  let (Some (l, _)) = parse (parse_list p) s in
  FStar.Math.Lemmas.multiple_division_lemma (L.length l) (U32.v n)

inline_for_extraction
val list_length_constant_size_parser
  (#n: U32.t)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize (U32.v n) k)) t)
  (b: S.bslice)
: HST.Stack U32.t
  (requires (fun h ->
    U32.v n <> 0 /\
    parses h (parse_list p) b (fun _ -> True)
  ))
  (ensures (fun h i h' ->
    S.modifies_none h h' /\
    parses h (parse_list p) b (fun (l, _) ->
    L.length l == U32.v i
  )))

let list_length_constant_size_parser #n #b #t p b =
  let h = HST.get () in
  list_length_constant_size_parser_correct' p b h;
  let len = S.length b in
  U32.div len n

val list_nth_spec
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
    parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l
  )))
  (ensures (fun b' ->
    S.includes b b' /\
    parses h (parse_list p) b (fun (l, _) ->
    exactly_parses h p b' (fun (x) ->
    U32.v i < L.length l /\
    x == L.index l (U32.v i)
  ))))
  (decreases (U32.v i))

#set-options "--z3rlimit 16"

let rec list_nth_spec #k #t p b i h =
  let s = S.as_seq h b in
  let (Some (v, len)) = parse p s in
  if i = 0ul
  then begin
    let b' = S.truncated_slice b (U32.uint_to_t len) in
    let s' = S.as_seq h b' in
    assert (no_lookahead_weak_on p s s');
    b'
  end else
    let b' = S.advanced_slice b (U32.uint_to_t len) in
    list_nth_spec p b' (U32.sub i 1ul) h

#reset-options

val list_nth_spec_ext
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (i: U32.t)
  (h h': HS.mem)
: Lemma
  (requires (
    parses h (parse_list p) b (fun (l, _) -> U32.v i < L.length l) /\
    S.live h' b /\
    S.as_seq h' b == S.as_seq h b
  ))
  (ensures (
    parses h (parse_list p) b (fun (l, _) -> U32.v i < L.length l) /\
    parses h' (parse_list p) b (fun (l, _) -> U32.v i < L.length l) /\
    list_nth_spec p b i h' == list_nth_spec p b i h
  ))
  (decreases (U32.v i))

let rec list_nth_spec_ext #k #t p b i h h' =
  if i = 0ul
  then ()
  else
    let s = S.as_seq h b in
    let (Some (v, len)) = parse p s in
    let b' = S.advanced_slice b (U32.uint_to_t len) in
    list_nth_spec_ext p b' (U32.sub i 1ul) h h'

val list_nth_spec_lt_disjoint
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (i j: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    U32.v i < U32.v j /\
    parses h (parse_list p) b (fun (l, _) ->
    U32.v j < L.length l
  )))
  (ensures (
    U32.v i < U32.v j /\
    parses h (parse_list p) b (fun (l, _) ->
    U32.v j < L.length l /\
    S.disjoint (list_nth_spec p b i h) (list_nth_spec p b j h)
  )))
  (decreases (U32.v i))

let rec list_nth_spec_lt_disjoint #k #t p b i j h =
  let s = S.as_seq h b in
  let (Some (v, len)) = parse p s in
  let b' = S.advanced_slice b (U32.uint_to_t len) in
  if i = 0ul
  then begin
    assert (list_nth_spec p b j h == list_nth_spec p b' (U32.sub j 1ul) h);
    assert (S.includes b' (list_nth_spec p b j h));
    assert (S.disjoint (list_nth_spec p b i h) b')
  end else
    list_nth_spec_lt_disjoint p b' (U32.sub i 1ul) (U32.sub j 1ul) h

val list_nth_spec_disjoint
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (i j: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    U32.v i <> U32.v j /\
    parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l /\
    U32.v j < L.length l
  )))
  (ensures (
    U32.v i <> U32.v j /\
    parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l /\
    U32.v j < L.length l /\
    S.disjoint (list_nth_spec p b i h) (list_nth_spec p b j h)
  )))

let list_nth_spec_disjoint #k #t p b i j h =
  if U32.lt i j
  then list_nth_spec_lt_disjoint p b i j h
  else list_nth_spec_lt_disjoint p b j i h

let list_nth_precond
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
  (h: HS.mem)
: GTot Type0
= parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l
  )

let list_nth_inv
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
  (h0: G.erased HS.mem)
  (sl: B.buffer S.bslice)
  (h: HS.mem)
  (j: nat)
: GTot Type0
= B.disjoint (S.as_buffer b) sl /\
  B.length sl == 1 /\
  list_nth_precond p sv b i (G.reveal h0) /\
  B.modifies_1 sl (G.reveal h0) h /\
  j <= U32.v i /\
  B.live h sl /\ (
  let b' = Seq.index (B.as_seq h sl) 0 in (
  S.includes b b' /\ (
  parses (G.reveal h0) (parse_list p) b (fun (l, _) ->
  parses (G.reveal h0) (parse_list p) b' (fun (lr, _) ->
    U32.v i < L.length l /\
    L.length lr == L.length l - j
  ))) /\
  list_nth_spec p b i (G.reveal h0) == list_nth_spec p b' (U32.sub i (U32.uint_to_t j)) (G.reveal h0)
  ))

inline_for_extraction
val list_nth_advance
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
  (h0: G.erased HS.mem)
  (sl: B.buffer S.bslice)
  (j: U32.t)
: HST.Stack unit
  (requires (fun h ->
    list_nth_inv p sv b i h0 sl h (U32.v j) /\
    U32.v j < U32.v i
  ))
  (ensures (fun h1 _ h2 ->
    list_nth_inv p sv b i h0 sl h1 (U32.v j) /\
    U32.v j < U32.v i /\
    list_nth_inv p sv b i h0 sl h2 (U32.v j + 1)
  ))

#set-options "--z3rlimit 1024"

let list_nth_advance #k #t p sv b i h0 sl j =
  let s = B.index sl 0ul in
  let h1 = HST.get () in
  let len = sv s in
  let s' = S.advance_slice s len in
  let h2 = HST.get () in
  assert (B.modifies_none h1 h2);
  B.upd sl 0ul s';
  let h3 = HST.get () in
  B.lemma_modifies_none_1_trans sl h1 h2 h3

#reset-options

inline_for_extraction
val list_nth
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sv: stateful_validator_nochk p)
  (b: S.bslice)
  (i: U32.t)
: HST.Stack S.bslice
  (requires (fun h ->
    parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l
  )))
  (ensures (fun h b' h' ->
    S.modifies_none h h' /\
    S.includes b b' /\
    parses h (parse_list p) b (fun (l, _) ->
      U32.v i < L.length l
    ) /\
    b' == list_nth_spec p b i h
  ))

#set-options "--z3rlimit 64"

let list_nth #k #t p sv b i =
  let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let sl : B.buffer S.bslice = B.create b 1ul in
  let h2 = HST.get () in
  C.Loops.for
    0ul
    i
    (fun h j -> list_nth_inv p sv b i (G.hide h2) sl h j)
    (fun j -> list_nth_advance p sv b i (G.hide h2) sl j)
  ;
  let h3 = HST.get () in
  let tail = B.index sl 0ul in
  let len = sv tail in
  let res = S.truncate_slice tail len in
  let h4 = HST.get () in
  assert (B.modifies_none h3 h4);
  B.lemma_intro_modifies_1 sl h3 h4;
  B.lemma_modifies_1_trans sl h2 h3 h4;
  B.lemma_modifies_0_1' sl h1 h2 h4;
  HST.pop_frame ();
  let h5 = HST.get () in
  B.lemma_modifies_0_push_pop h0 h1 h4 h5;
  list_nth_spec_ext p b i h2 h0;
  res

let list_nth_constant_size_parser_postcond
  (#n: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize n k)) t)
  (b: S.bslice)
  (i: U32.t)
  (h: HS.mem)
: GTot Type0
=    parses h (parse_list p) b (fun (l, _) ->
      U32.v i < L.length l
    ) /\
    Prims.op_Multiply (U32.v i) n <= U32.v (S.length b) /\ (
    let b1 = S.advanced_slice b (U32.mul i (U32.uint_to_t n)) in
    n <= U32.v (S.length b1) /\ (
    let b2 = S.truncated_slice b1 (U32.uint_to_t n) in
    list_nth_spec p b i h == b2
  ))

inline_for_extraction
let bounded_mult (a b c: U32.t) 
  (l: unit -> Lemma (Prims.op_Multiply (U32.v a) (U32.v b) <= U32.v c))
: Pure U32.t
  (requires True)
  (ensures (fun y ->
     FStar.UInt.size (Prims.op_Multiply (U32.v a) (U32.v b)) U32.n /\
     U32.v y == Prims.op_Multiply (U32.v a) (U32.v b) /\
     U32.v y <= U32.v c /\
     y == U32.mul a b
  ))
= l ();
  U32.mul a b

val list_nth_constant_size_parser_correct
  (#n: nat)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize n k)) t)
  (b: S.bslice)
  (i: U32.t)
  (h: HS.mem)
: Lemma
  (requires (
    parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l
  )))
  (ensures (
    list_nth_constant_size_parser_postcond p b i h
  ))
  (decreases (U32.v i))

#set-options "--z3rlimit 1024 --smtencoding.elim_box true"

//  --smtencoding.nl_arith_repr native --smtencoding.l_arith_repr native

let rec list_nth_constant_size_parser_correct #n #k #t p b i h =
  if i = 0ul
  then begin
    S.advanced_slice_zero b;
    assert (list_nth_constant_size_parser_postcond p b i h)
  end else begin
    let b' = S.advanced_slice b (U32.uint_to_t n) in
    assert (list_nth_spec p b i h == list_nth_spec p b' (U32.sub i 1ul) h);
    list_nth_constant_size_parser_correct p b' (U32.sub i 1ul) h;
    assert (list_nth_constant_size_parser_postcond p b' (U32.sub i 1ul) h);
    let ka : U32.t = U32.sub i 1ul in
    let kb : U32.t = U32.uint_to_t n in
    let nj : nat = Prims.op_Multiply (U32.v ka) (U32.v kb) in
    let lemma1 () : Lemma (nj <= U32.v (S.length b')) = () in
    lemma1 ();
    let b1' = S.advanced_slice b' (U32.mul ka kb) in
    FStar.Math.Lemmas.distributivity_add_left 1 (U32.v i - 1) n;
    assert (n + Prims.op_Multiply (U32.v i - 1) n == Prims.op_Multiply (U32.v i) n);
    assert (Prims.op_Multiply (U32.v i) n <= n + U32.v (S.length b'));
    let l () : Lemma (Prims.op_Multiply (U32.v i) n <= U32.v (S.length b)) = () in
    let m : U32.t = bounded_mult i (U32.uint_to_t n) (S.length b) l in
    assert (U32.v m <= U32.v (S.length b));
    let b1 = S.advanced_slice b m in
    assert (b1 == b1');
    assert (list_nth_constant_size_parser_postcond p b i h)
  end

#reset-options

inline_for_extraction
val list_nth_constant_size_parser
  (#n: U32.t)
  (#k: constant_size_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize (U32.v n) k)) t)
  (b: S.bslice)
  (i: U32.t)
: HST.Stack S.bslice
  (requires (fun h ->
    parses h (parse_list p) b (fun (l, _) ->
    U32.v i < L.length l
  )))
  (ensures (fun h b' h' ->
    S.modifies_none h h' /\
    S.includes b b' /\
    parses h (parse_list p) b (fun (l, _) ->
      U32.v i < L.length l
    ) /\
    b' == list_nth_spec p b i h
  ))

#set-options "--z3rlimit 128"

let list_nth_constant_size_parser #n #k #t p b i =
  let h = HST.get () in
  list_nth_constant_size_parser_correct p b i h;
  let b1 = S.advance_slice b (U32.mul i n) in
  let b2 = S.truncate_slice b1 n in
  let h' = HST.get () in
  list_nth_spec_ext p b i h h' ;
  b2

#reset-options

let validate_list_inv
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (sv: stateful_validator p)
  (b: S.bslice)
  (h0: G.erased HS.mem)
  (sl: B.buffer (option S.bslice))
  (h: HS.mem)
  (j: nat)
  (interrupt: bool)
: GTot Type0
= B.disjoint (S. as_buffer b) sl /\
  B.length sl == 1 /\
  S.live (G.reveal h0) b /\
  B.modifies_1 sl (G.reveal h0) h /\
  B.live h sl /\ (
  let sq = S.as_seq (G.reveal h0) b in
  let slo = Seq.index (B.as_seq h sl) 0 in
  if interrupt
  then
    (Some? slo ==> Some? (parse (parse_list p) sq))
  else (
    Some? slo /\ (
    let (Some sl) = slo in (
    S.includes b sl /\
    S.live (G.reveal h0) sl /\
    j <= U32.v (S.length b) /\
    U32.v (S.length sl) <= U32.v (S.length b) - j /\ (
    let sq' = S.as_seq (G.reveal h0) sl in
    (Some? (parse (parse_list p) sq') ==> Some? (parse (parse_list p) sq))
  )))))

inline_for_extraction
val validate_list_advance
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (sv: stateful_validator p)
  (b: S.bslice)
  (h0: G.erased HS.mem)
  (sl: B.buffer (option S.bslice))
  (j: U32.t)
: HST.Stack bool
  (requires (fun h ->
    U32.v j < U32.v (S.length b) /\
    validate_list_inv sv b h0 sl h (U32.v j) false
  ))
  (ensures (fun h1 res h2 ->
    U32.v j < U32.v (S.length b) /\
    validate_list_inv sv b h0 sl h1 (U32.v j) false /\
    validate_list_inv sv b h0 sl h2 (U32.v j + 1) res
  ))

#set-options "--z3rlimit 32"

let validate_list_advance #k #t #p sv b h0 sl j =
  let h1 = HST.get () in
  B.no_upd_lemma_1 (G.reveal h0) h1 sl (S.as_buffer b);
  let os = B.index sl 0ul in
  let (Some s) = os in
  assert (S.as_seq h1 s == S.as_seq (G.reveal h0) s);
  if S.length s = 0ul
  then true
  else begin
    let svs = sv s in
    let h2 = HST.get () in
    assert (S.as_seq h2 s == S.as_seq (G.reveal h0) s);
    B.lemma_intro_modifies_1 sl h1 h2;
    match svs with
    | None ->
      B.upd sl 0ul None;
      true
    | Some off ->
      if off = 0ul
      then begin
	B.upd sl 0ul None;
	true
      end else begin
	let s' = S.advance_slice s off in
	assert (S.as_seq h2 s' == S.as_seq (G.reveal h0) s');
	B.upd sl 0ul (Some s');
	false
      end
  end  

inline_for_extraction
val validate_list
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (sv: stateful_validator p)
: Tot (stateful_validator (parse_list p))

let validate_list #k #t #p sv =
  fun (b: S.bslice) ->
  let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let sl : B.buffer (option S.bslice) = B.create (Some b) 1ul in
  let h2 = HST.get () in
  B.lemma_reveal_modifies_0 h1 h2; // I really need to switch to my new modifies clauses very soon!
  assert (S.as_seq h2 b == S.as_seq h0 b);
  assert (validate_list_inv sv b (G.hide h2) sl h2 0 false);
  let slen = S.length b in
  let (_, interrupt) = C.Loops.interruptible_for
    0ul
    slen
    (fun h j inter -> validate_list_inv sv b (G.hide h2) sl h j inter)
    (fun j -> validate_list_advance sv b (G.hide h2) sl j)
  in
  let h3 = HST.get () in
  B.lemma_reveal_modifies_1 sl h2 h3;
  assert (S.as_seq h3 b == S.as_seq h0 b);
  let tail = B.index sl 0ul in
  let res : option (n: consumed_slice_length b) =
    if interrupt
    then match tail with
    | None -> None
    | Some _ -> Some (S.length b)
    else None
  in
  HST.pop_frame ();
  let h = HST.get () in
  assert (S.as_seq h b == S.as_seq h0 b);
  assert (S.live h0 b);
  let pre : Type0 =
    Some? res
  in
  let post : Type0 =
    pre /\
    S.live h0 b /\ (
    let s = S.as_seq h0 b in
    let pl = parse (parse_list p) s in (
    Some? pl /\ (
    let (Some (_, consumed)) = pl in
    let (Some consumed') = res in
    consumed == U32.v consumed'
  )))
  in
  let f () : Lemma
    (requires pre)
    (ensures post)
  = let s = S.as_seq h0 b in
    parse_list_bare_consumed p s
  in
  Classical.move_requires f ();
  res

#reset-options

(* Serialization: only works if the parser for elements has the prefix property *)

let serialize_list_nil_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (h: HS.mem)
: Lemma
  (requires (S.length b == 0ul /\ S.live h b))
  (ensures (parses h (parse_list p) b (fun (l, _) -> l == [])))
= ()

let serialize_list_cons_correct
  (#k: strong_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong k) t)
  (b bhd btl: S.bslice)
  (h: HS.mem)
: Lemma
  (requires (
    S.is_concat b bhd btl /\
    exactly_parses h p bhd (fun _ -> True) /\
    U32.v (S.length bhd) > 0 /\
    parses h (parse_list p) btl (fun _ -> True)
  ))
  (ensures (
    exactly_parses h p bhd (fun hd ->
    parses h (parse_list p) btl (fun (tl, _) ->
    parses h (parse_list p) b (fun (l, _) ->
    l == hd :: tl
  )))))
= assert (no_lookahead_on p (S.as_seq h bhd) (S.as_seq h b));
  assert (injective_postcond p (S.as_seq h bhd) (S.as_seq h b))

inline_for_extraction
val serialize_list_cons
  (#k: strong_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong k) t)
  (src_hd src_tl: S.bslice)
  (dest: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.disjoint dest src_hd /\
    S.disjoint dest src_tl /\
    S.live h dest /\
    U32.v (S.length dest) >= U32.v (S.length src_hd) + U32.v (S.length src_tl) /\
    exactly_parses h p src_hd (fun _ -> True) /\
    U32.v (S.length src_hd) > 0 /\
    parses h (parse_list p) src_tl (fun _ -> True)
  ))
  (ensures (fun h (destl, destr) h' ->
    S.is_concat dest destl destr /\
    U32.v (S.length dest) >= U32.v (S.length src_hd) + U32.v (S.length src_tl) /\
    S.length destl == U32.add (S.length src_hd) (S.length src_tl) /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    S.live h destr /\
    exactly_parses h p src_hd (fun hd ->
    parses h (parse_list p) src_tl (fun (tl, _) ->
    exactly_parses h' p src_hd (fun hd' ->
    parses h' (parse_list p) src_tl (fun (tl', _) ->
    parses h' (parse_list p) destl (fun (l, _) ->
    hd == hd' /\ tl == tl' /\ l == hd :: tl
  )))))))

#set-options "--z3rlimit 32"

let serialize_list_cons #k #t p src_hd src_tl dest =
  let h = HST.get () in
  parse_list_exactly_parses h p src_tl (fun _ -> True);
  let len_hd = S.length src_hd in
  let len_tl = S.length src_tl in
  let len = U32.add len_hd len_tl in
  let destl = S.truncate_slice dest len in
  let destr = S.advance_slice dest len in
  let (dest_hd, dest_tl) = serialize_copy p destl src_hd in
  let (dest_tl', _) = serialize_copy (parse_list p) dest_tl src_tl in
  assert (dest_tl' == dest_tl);
  let h' = HST.get () in
  serialize_list_cons_correct p destl dest_hd dest_tl h' ;
  (destl, destr)

#reset-options

val serialize_list_append_correct
  (#k: strong_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong k) t)
  (b bl br: S.bslice)
  (h: HS.mem)
: Lemma
  (requires (
    S.is_concat b bl br /\
    parses h (parse_list p) bl (fun _ -> True) /\
    parses h (parse_list p) br (fun _ -> True)
  ))
  (ensures (
    parses h (parse_list p) bl (fun (ll, _) ->
    parses h (parse_list p) br (fun (lr, _) ->
    parses h (parse_list p) b (fun (l, _) ->
    l == List.Tot.append ll lr
  )))))
  (decreases (U32.v (S.length bl)))

#set-options "--z3rlimit 64"

let rec serialize_list_append_correct #k #t p b bl br h =
  if S.length bl = 0ul
  then ()
  else begin
    let sl = S.as_seq h bl in
    let (Some (hd, len)) = parse p sl in
    assert (no_lookahead_on p (S.as_seq h bl) (S.as_seq h b));
    assert (injective_postcond p (S.as_seq h bl) (S.as_seq h b));
    let s = S.as_seq h b in
    let (Some (hd', len')) = parse p s in
    assert (hd == hd');
    assert ((len <: nat) == (len' <: nat));
    let len_ = U32.uint_to_t len in
    let bhd = S.truncated_slice bl len_ in
    assert (bhd == S.truncated_slice b len_);
    let b_ = S.advanced_slice b len_ in
    let bl_ = S.advanced_slice bl len_ in
    serialize_list_append_correct p b_ bl_ br h
  end

#reset-options

inline_for_extraction
val serialize_list_append
  (#k: strong_parser_kind)
  (#t: Type0)
  (p: parser (ParserStrong k) t)
  (srcl srcr: S.bslice)
  (dest: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.disjoint dest srcl /\
    S.disjoint dest srcr /\
    S.live h dest /\
    U32.v (S.length dest) >= U32.v (S.length srcl) + U32.v (S.length srcr) /\
    parses h (parse_list p) srcl (fun _ -> True) /\
    parses h (parse_list p) srcr (fun _ -> True)
  ))
  (ensures (fun h (destl, destr) h' ->
    S.is_concat dest destl destr /\
    U32.v (S.length dest) >= U32.v (S.length srcl) + U32.v (S.length srcr) /\
    S.length destl == U32.add (S.length srcl) (S.length srcr) /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    S.live h destr /\
    parses h (parse_list p) srcl (fun (ll, _) ->
    parses h (parse_list p) srcr (fun (lr, _) ->
    parses h' (parse_list p) srcl (fun (ll', _) ->
    parses h' (parse_list p) srcr (fun (lr', _) ->
    parses h' (parse_list p) destl (fun (l, _) ->
    ll == ll' /\ lr == lr' /\ l == List.Tot.append ll lr
  )))))))

#set-options "--z3rlimit 32"

let serialize_list_append #k #t p srcl srcr dest =
  let h = HST.get () in
  parse_list_exactly_parses h p srcl (fun _ -> True);
  parse_list_exactly_parses h p srcr (fun _ -> True);
  let lenl = S.length srcl in
  let lenr = S.length srcr in
  let len = U32.add lenl lenr in
  let destl = S.truncate_slice dest len in
  let destr = S.advance_slice dest len in
  let (destll, destlr) = serialize_copy (parse_list p) destl srcl in
  let (destlr', _) = serialize_copy (parse_list p) destlr srcr in
  assert (destlr' == destlr);
  let h' = HST.get () in
  serialize_list_append_correct p destl destll destlr h' ;
  (destl, destr)

#reset-options
