module LowParse.Spec.VLData
include LowParse.Spec.FLData

module Seq = FStar.Seq
module U32 = FStar.UInt32
module E = LowParse.BigEndian
module M = LowParse.Math

let integer_size : Type0 = (sz: nat { 1 <= sz /\ sz <= 4 } )

#reset-options "--z3cliopt smt.arith.nl=false --using_facts_from '*  -FStar.UInt8 -FStar.UInt16' --z3rlimit 32"

let integer_size_values (i: integer_size) : Lemma
  (i == 1 \/ i == 2 \/ i == 3 \/ i == 4)
= ()

#reset-options

inline_for_extraction
let bounded_integer
  (i: integer_size)
: Tot Type0
= (u: U32.t { U32.v u < pow2 (FStar.Mul.op_Star 8 i) } )

let decode_bounded_integer
  (i: integer_size)
  (b: bytes { Seq.length b == i } )
: GTot (bounded_integer i)
= E.lemma_be_to_n_is_bounded b;
  U32.uint_to_t (E.be_to_n b)

let decode_bounded_integer_injective'
  (i: integer_size)
  (b1: bytes { Seq.length b1 == i } )
  (b2: bytes { Seq.length b2 == i } )
: Lemma
  (decode_bounded_integer i b1 == decode_bounded_integer i b2 ==> Seq.equal b1 b2)
= if decode_bounded_integer i b1 = decode_bounded_integer i b2
  then begin
    E.lemma_be_to_n_is_bounded b1;
    E.lemma_be_to_n_is_bounded b2;
    assert (U32.v (U32.uint_to_t (E.be_to_n b1)) == E.be_to_n b1);
    assert (U32.v (U32.uint_to_t (E.be_to_n b2)) == E.be_to_n b2);
    assert (E.be_to_n b1 == E.be_to_n b2);
    E.be_to_n_inj b1 b2
  end else ()

let decode_bounded_integer_injective
  (i: integer_size)
: Lemma
  (make_total_constant_size_parser_precond i (bounded_integer i) (decode_bounded_integer i))
= Classical.forall_intro_2 (decode_bounded_integer_injective' i)

// unfold
let parse_bounded_integer_kind
  (i: integer_size)
: Tot parser_kind
= total_constant_size_parser_kind i

let parse_bounded_integer
  (#err: Type0)
  (i: integer_size)
  (e: err)
: Tot (parser (parse_bounded_integer_kind i) (bounded_integer i) err)
= decode_bounded_integer_injective i;
  make_total_constant_size_parser i (bounded_integer i) _ (decode_bounded_integer i) e

#reset-options "--z3rlimit 64 --max_fuel 64 --max_ifuel 64 --z3refresh --z3cliopt smt.arith.nl=false"

let parse_vldata_payload_size
  (sz: integer_size)
: Pure nat
  (requires True)
  (ensures (fun y -> y == pow2 (FStar.Mul.op_Star 8 sz) - 1 ))
= match sz with
  | 1 -> 255
  | 2 -> 65535
  | 3 -> 16777215
  | 4 -> 4294967295

#reset-options

// unfold
inline_for_extraction
let parse_vldata_payload_kind
  (sz: integer_size)
: parser_kind
= strong_parser_kind 0 (parse_vldata_payload_size sz) ({
    parser_kind_metadata_total = false;
  })

let parse_vldata_payload
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (e: err)
  (i: bounded_integer sz { f i == true } )
: Tot (parser (parse_vldata_payload_kind sz) t err)
= weaken (parse_vldata_payload_kind sz) (parse_fldata p (U32.v i) e)

#set-options "--z3rlimit 64"

let parse_fldata_and_then_cases_injective
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (e: err)
: Lemma
  (and_then_cases_injective (parse_vldata_payload sz f p e))
= let g
    (len1 len2: (len: bounded_integer sz { f len == true } ))
    (b1 b2: bytes)
  : Lemma
    (requires (and_then_cases_injective_precond (parse_vldata_payload sz f p e) len1 len2 b1 b2))
    (ensures (len1 == len2))
  = assert (injective_precond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (injective_postcond p (Seq.slice b1 0 (U32.v len1)) (Seq.slice b2 0 (U32.v len2)));
    assert (len1 == len2)
  in
  let g'
    (len1 len2: (len: bounded_integer sz { f len == true } ))
    (b1: bytes)
  : Lemma
    (forall (b2: bytes) . and_then_cases_injective_precond (parse_vldata_payload sz f p e) len1 len2 b1 b2 ==> len1 == len2)
  = Classical.forall_intro (Classical.move_requires (g len1 len2 b1))
  in
  Classical.forall_intro_3 g'

#reset-options

// unfold
inline_for_extraction
let parse_vldata_gen_kind
  (sz: integer_size)
: Tot parser_kind
= strong_parser_kind sz (sz + parse_vldata_payload_size sz) ({
    parser_kind_metadata_total = false;
  })

let parse_vldata_gen_kind_correct
  (sz: integer_size)
: Lemma
  ( (parse_vldata_gen_kind sz) == (and_then_kind (parse_filter_kind (parse_bounded_integer_kind sz)) (parse_vldata_payload_kind sz)))
= let kl = parse_vldata_gen_kind sz in
  let kr = and_then_kind (parse_filter_kind (parse_bounded_integer_kind sz)) (parse_vldata_payload_kind sz) in
  assert_norm (kl == kr)

let parse_vldata_gen
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (e_size_incomplete: err)
  (e_size_invalid: err)
  (e_payload: err)
: Tot (parser (parse_vldata_gen_kind sz) t err)
= parse_fldata_and_then_cases_injective sz f p e_payload;
  parse_vldata_gen_kind_correct sz;
  (parse_filter (parse_bounded_integer sz e_size_incomplete) f e_size_invalid)
  `and_then`
  parse_vldata_payload sz f p e_payload

let unconstrained_bounded_integer
  (sz: integer_size)
  (i: bounded_integer sz)
: GTot bool
= true

let parse_vldata
  (sz: integer_size)
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (e_size: err)
  (e_payload: err)
: Tot (parser _ t err)
= parse_vldata_gen sz (unconstrained_bounded_integer sz) p e_size e_size e_payload


(** Explicit bounds on size *)

inline_for_extraction
val log256'
  (n: nat)
: Pure integer_size
  (requires (n > 0 /\ n < 4294967296))
  (ensures (fun l ->
    pow2 (FStar.Mul.op_Star 8 (l - 1)) <= n /\
    n < pow2 (FStar.Mul.op_Star 8 l)
  ))

#reset-options "--z3rlimit 16 --z3cliopt smt.arith.nl=false"

let log256' n =
  [@inline_let]
  let _ = assert_norm (pow2 32 == 4294967296) in
  [@inline_let]
  let _ = assert (n < pow2 32) in
  [@inline_let]
  let z0 = 1 in
  [@inline_let]
  let z1 = 256 in
  [@inline_let]
  let _ = assert_norm (z1 == Prims.op_Multiply 256 z0) in
  [@inline_let]
  let l = 1 in
  [@inline_let]
  let _ = assert_norm (pow2 (Prims.op_Multiply 8 l) == z1) in
  [@inline_let]
  let _ = assert_norm (pow2 (Prims.op_Multiply 8 (l - 1)) == z0) in
  if n < z1
  then begin
    [@inline_let]
    let _ = assert (pow2 (Prims.op_Multiply 8 (l - 1)) <= n) in
    [@inline_let]
    let _ = assert (n < pow2 (Prims.op_Multiply 8 l)) in
    l
  end else begin
    [@inline_let]
    let z2 = 65536 in
    [@inline_let]
    let _ = assert_norm (z2 == Prims.op_Multiply 256 z1) in
    [@inline_let]
    let l = 2 in
    [@inline_let]
    let _ = assert_norm (pow2 (Prims.op_Multiply 8 l) == z2) in
    if n < z2
    then begin
      [@inline_let]
      let _ = assert (pow2 (Prims.op_Multiply 8 (l - 1)) <= n) in
      [@inline_let]
      let _ = assert (n < pow2 (Prims.op_Multiply 8 l)) in
      l
    end else begin
      [@inline_let]
      let z3 = 16777216 in
      [@inline_let]
      let _ = assert_norm (z3 == Prims.op_Multiply 256 z2) in
      [@inline_let]
      let l = 3 in
      [@inline_let]
      let _ = assert_norm (pow2 (Prims.op_Multiply 8 l) == z3) in
      if n < z3
      then begin
        [@inline_let]
	let _ = assert (pow2 (Prims.op_Multiply 8 (l - 1)) <= n) in
        [@inline_let]
	let _ = assert (n < pow2 (Prims.op_Multiply 8 l)) in
        l    
      end else begin
        [@inline_let]
        let l = 4 in
        [@inline_let]
        let _ = assert_norm (pow2 (Prims.op_Multiply 8 l) == Prims.op_Multiply 256 z3) in
        [@inline_let]
	let _ = assert (pow2 (Prims.op_Multiply 8 (l - 1)) <= n) in
        [@inline_let]
	let _ = assert (n < pow2 (Prims.op_Multiply 8 l)) in
        l
      end
    end
  end

#reset-options

let in_bounds
  (min: nat)
  (max: nat)
  (x: U32.t)
: GTot bool
= not (U32.v x < min || max < U32.v x)

// unfold
inline_for_extraction
let parse_bounded_vldata_kind
  (min: nat)
  (max: nat)
: Pure parser_kind
  (requires (min <= max /\ max > 0 /\ max < 4294967296 ))
  (ensures (fun _ -> True))
= strong_parser_kind (log256' max + min) (log256' max + max) ({
    parser_kind_metadata_total = false;
  })

#reset-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --z3refresh"

let parse_bounded_vldata_elim'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (e_size_incomplete e_size_invalid e_payload: err)
  (xbytes: bytes)
  (x: t)
  (consumed: consumed_length xbytes)
: Lemma
  (requires (parse (parse_vldata_gen (log256' max) (in_bounds min max) p e_size_incomplete e_size_invalid e_payload) xbytes == Correct (x, consumed)))
  (ensures (
    let sz : integer_size = log256' max in
    let plen = parse (parse_bounded_integer sz e_size_incomplete) xbytes in
    Correct? plen /\ (
    let (Correct (len, consumed_len)) = plen in
    (consumed_len <: nat) == (sz <: nat) /\
    in_bounds min max len /\
    U32.v len <= Seq.length xbytes - sz /\ (
    let input' = Seq.slice xbytes (sz <: nat) (sz + U32.v len) in
    let pp = parse p input' in
    Correct? pp /\ (
    let (Correct (x', consumed_p)) = pp in
    x' == x /\
    (consumed_p <: nat) == U32.v len /\
    (consumed <: nat) == sz + U32.v len
  )))))
=   let sz : integer_size = log256' max in
    let plen_ = parse (parse_filter (parse_bounded_integer sz e_size_incomplete) (in_bounds min max) e_size_invalid) xbytes in
    assert (Correct? plen_);
    let (Correct (len_, consumed_len_)) = plen_ in
    let plen = parse (parse_bounded_integer sz e_size_incomplete) xbytes in
    assert (Correct? plen);
    let (Correct (len, consumed_len)) = plen in
    assert ((len <: U32.t) == (len_ <: U32.t));
    assert (consumed_len_ == consumed_len);    
    assert ((consumed_len <: nat) == (sz <: nat));
    assert (in_bounds min max len);
    let input1 = Seq.slice xbytes sz (Seq.length xbytes) in
    let pp1 = parse (parse_vldata_payload sz (in_bounds min max) p e_payload len) input1 in
    assert (Correct? pp1);
    let (Correct (x1, consumed_p1)) = pp1 in
    assert (x == x1);
    let pp15 = parse (parse_fldata p (U32.v len) e_payload) input1 in
    assert (Correct? pp15);
    let (Correct (x15, consumed_p15)) = pp15 in
    assert (x == x15);
    assert (consumed_p1 == consumed_p15);
    assert (U32.v len <= Seq.length xbytes - sz);
    let input' = Seq.slice input1 0 (U32.v len) in
    assert (input' == Seq.slice xbytes (sz <: nat) (sz + U32.v len));
    let pp = parse p input' in
    assert (Correct? pp);
    let (Correct (x', consumed_p)) = pp in
    assert (x == x');
    assert ((consumed_p <: nat) == U32.v len);
    assert ((consumed <: nat) == sz + consumed_p);
    ()

let parse_bounded_vldata_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (e_size_incomplete e_size_invalid e_payload: err)
: Lemma
  (parser_kind_prop (parse_bounded_vldata_kind min max) (parse_vldata_gen (log256' max) (in_bounds min max) p e_size_incomplete e_size_invalid e_payload))
= let sz : integer_size = log256' max in
  let p' = parse_vldata_gen sz (in_bounds min max) p e_size_incomplete e_size_invalid e_payload in
  let prf
    (input: bytes)
  : Lemma
    (requires (Correct? (parse p' input)))
    (ensures (
      let pi = parse p' input in
      Correct? pi /\ (
      let (Correct (_, consumed)) = pi in
      sz + min <= (consumed <: nat) /\
      (consumed <: nat) <= sz + max
    )))
  = let (Correct (data, consumed)) = parse p' input in
    parse_bounded_vldata_elim' min max p e_size_incomplete e_size_invalid e_payload input data consumed 
  in
  Classical.forall_intro (Classical.move_requires prf)

#reset-options

let parse_bounded_vldata
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (e_size_incomplete e_size_invalid e_payload: err)
: Tot (parser (parse_bounded_vldata_kind min max) t err)
= parse_bounded_vldata_correct min max p e_size_incomplete e_size_invalid e_payload;
  strengthen (parse_bounded_vldata_kind min max) (parse_vldata_gen (log256' max) (in_bounds min max) p e_size_incomplete e_size_invalid e_payload)

let parse_bounded_vldata_elim
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (e_size_incomplete e_size_invalid e_payload: err)
  (xbytes: bytes)
  (x: t)
  (consumed: consumed_length xbytes)
: Lemma
  (requires (parse (parse_bounded_vldata min max p e_size_incomplete e_size_invalid e_payload) xbytes == Correct (x, consumed)))
  (ensures (
    let sz : integer_size = log256' max in
    let plen = parse (parse_bounded_integer sz e_size_incomplete) xbytes in
    Correct? plen /\ (
    let (Correct (len, consumed_len)) = plen in
    (consumed_len <: nat) == (sz <: nat) /\
    in_bounds min max len /\
    U32.v len <= Seq.length xbytes - sz /\ (
    let input' = Seq.slice xbytes (sz <: nat) (sz + U32.v len) in
    let pp = parse p input' in
    Correct? pp /\ (
    let (Correct (x', consumed_p)) = pp in
    x' == x /\
    (consumed_p <: nat) == U32.v len /\
    (consumed <: nat) == sz + U32.v len
  )))))
= parse_bounded_vldata_elim' min max p e_size_incomplete e_size_invalid e_payload xbytes x consumed

(* Serialization *)

let parse_bounded_vldata_strong_pred
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (x: t)
: GTot Type0
= let reslen = Seq.length (s x) in
  min <= reslen /\ reslen <= max

let parse_bounded_vldata_strong_t
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
: Tot Type0
= (x: t { parse_bounded_vldata_strong_pred min max s x } )

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --z3refresh"

let parse_bounded_vldata_strong_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (e_size_incomplete e_size_invalid e_payload: err)
  (xbytes: bytes)
  (consumed: consumed_length xbytes)
  (x: t)
: Lemma
  (requires (parse (parse_bounded_vldata min max p e_size_incomplete e_size_invalid e_payload) xbytes == Correct (x, consumed)))
  (ensures (parse_bounded_vldata_strong_pred min max s x))
= parse_bounded_vldata_elim min max p e_size_incomplete e_size_invalid e_payload xbytes x consumed;
  let sz : integer_size = log256' max in
  let plen = parse (parse_bounded_integer sz e_size_incomplete) xbytes in
  let f () : Lemma (Correct? plen) =
    parse_bounded_vldata_elim min max p e_size_incomplete e_size_invalid e_payload xbytes x consumed
  in
  f ();
  let (Correct (len, _)) = plen in
  let input' = Seq.slice xbytes (sz <: nat) (sz + U32.v len) in
  assert (Seq.equal input' (Seq.slice input' 0 (U32.v len)));
  serializer_correct_implies_complete p s;
  assert (s x == input');
  ()

#reset-options

let parse_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (e_size_incomplete e_size_invalid e_payload: err)
: Tot (parser (parse_bounded_vldata_kind min max) (parse_bounded_vldata_strong_t min max s) err) 
= coerce_parser
  (parse_bounded_vldata_strong_t min max s)
  (parse_strengthen (parse_bounded_vldata min max p e_size_incomplete e_size_invalid e_payload) (parse_bounded_vldata_strong_pred min max s) (parse_bounded_vldata_strong_correct min max s e_size_incomplete e_size_invalid e_payload))

let serialize_bounded_integer'
  (sz: integer_size)
: Tot (bare_serializer (bounded_integer sz))
= (fun (x: bounded_integer sz) ->
    let res = E.n_to_be (U32.uint_to_t sz) (U32.v x) in
    res
  )

#set-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8"

let serialize_bounded_integer_correct
  (#err: Type0)
  (sz: integer_size)
  (e: err)
: Lemma
  (serializer_correct (parse_bounded_integer sz e) (serialize_bounded_integer' sz))
= let prf
    (x: bounded_integer sz)
  : Lemma
    (
      let res = serialize_bounded_integer' sz x in
      Seq.length res == (sz <: nat) /\
      parse (parse_bounded_integer sz e) res == Correct (x, (sz <: nat))
    )
  = ()
  in
  Classical.forall_intro prf

#reset-options

let serialize_bounded_integer
  (#err: Type0)
  (sz: integer_size)
  (e: err)
: Tot (serializer (parse_bounded_integer sz e))
= serialize_bounded_integer_correct sz e;
  serialize_bounded_integer' sz

#set-options "--z3rlimit 64"

let serialize_bounded_vldata_strong'
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (e_size_incomplete: err)
: Tot (bare_serializer (parse_bounded_vldata_strong_t min max s))
= (fun (x: parse_bounded_vldata_strong_t min max s) ->
  let pl = s x in
  let sz = log256' max in
  let nlen = Seq.length pl in
  assert (min <= nlen /\ nlen <= max);
  let len = U32.uint_to_t nlen in
  let slen = serialize (serialize_bounded_integer sz e_size_incomplete) len in
  seq_slice_append_l slen pl;
  seq_slice_append_r slen pl;
  Seq.append slen pl
  )

val serialize_vldata_gen_correct_aux
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (e_size_incomplete e_size_invalid e_payload: err)
  (b b1 b2: bytes)
: Lemma
  (requires (
    Seq.length b1 == sz /\ (
    let vlen = parse (parse_bounded_integer sz e_size_incomplete) b1 in
    Correct? vlen /\ (
    let (Correct (len, _)) = vlen in
    f len == true /\
    Seq.length b2 == U32.v len /\ (
    let vv = parse p b2 in
    Correct? vv /\ (
    let (Correct (_, consumed)) = vv in
    consumed == Seq.length b2 /\
    Seq.length b1 <= Seq.length b /\
    Seq.slice b 0 (Seq.length b1) == b1 /\
    Seq.slice b (Seq.length b1) (Seq.length b) == b2
  ))))))
  (ensures (
    let vv = parse p b2 in
    Correct? vv /\ (
    let (Correct (v, consumed)) = vv in
    let vv' = parse (parse_vldata_gen sz f p e_size_incomplete e_size_invalid e_payload) b in
    Correct? vv' /\ (
    let (Correct (v', consumed')) = vv' in
    v == v' /\
    consumed == Seq.length b2 /\
    consumed' == Seq.length b
  ))))

#reset-options "--z3rlimit 128 --z3cliopt smt.arith.nl=false --z3refresh"

let serialize_vldata_gen_correct_aux sz f #k #t #err p e_size_incomplete e_size_invalid e_payload b b1 b2 =
  let (Correct (len, consumed1)) = parse (parse_bounded_integer sz e_size_incomplete) b1 in
  assert (consumed1 == sz);
  assert (no_lookahead_on (parse_bounded_integer sz e_size_incomplete) b1 b);
  let v1' = parse (parse_bounded_integer sz e_size_incomplete) b in
  assert (Correct? v1');
  let (Correct (len', consumed1')) = v1' in
  assert (consumed1' == sz);
  assert (injective_postcond (parse_bounded_integer sz e_size_incomplete) b1 b);
  assert (len' == len);
  let v1_ = parse (parse_filter (parse_bounded_integer sz e_size_incomplete) f e_size_invalid) b in
  assert (Correct? v1_);
  let (Correct (len_, consumed1_)) = v1_ in
  assert (consumed1_ == sz);
  assert ((len_ <: bounded_integer sz) == len);
  assert (Correct? (parse p b2));
  assert (b2 == Seq.slice b2 0 (U32.v len));
  assert (Correct? (parse (parse_fldata p (U32.v len) e_payload) b2));
  assert (Correct? (parse (parse_vldata_payload sz f p e_payload len) b2));
  assert (Correct? (parse (parse_vldata_gen sz f p e_size_incomplete e_size_invalid e_payload) b));
//  admit
  ()

#reset-options

val serialize_vldata_gen_correct
  (sz: integer_size)
  (f: (bounded_integer sz -> GTot bool))
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (e_size_incomplete e_size_invalid e_payload: err)
  (b1 b2: bytes)
: Lemma
  (requires (
    Seq.length b1 == sz /\ (
    let vlen = parse (parse_bounded_integer sz e_size_incomplete) b1 in
    Correct? vlen /\ (
    let (Correct (len, _)) = vlen in
    f len == true /\
    Seq.length b2 == U32.v len /\ (
    let vv = parse p b2 in
    Correct? vv /\ (
    let (Correct (_, consumed)) = vv in
    consumed == Seq.length b2
  ))))))
  (ensures (
    let vv = parse p b2 in
    Correct? vv /\ (
    let (Correct (v, consumed)) = vv in
    let vv' = parse (parse_vldata_gen sz f p e_size_incomplete e_size_invalid e_payload) (Seq.append b1 b2) in
    Correct? vv' /\ (
    let (Correct (v', consumed')) = vv' in
    v == v' /\
    consumed == Seq.length b2 /\
    consumed' == sz + Seq.length b2
  ))))

let serialize_vldata_gen_correct sz f #k #t #err p e_size_incomplete e_size_invalid e_payload b1 b2 =
  seq_slice_append_l b1 b2;
  seq_slice_append_r b1 b2;
  serialize_vldata_gen_correct_aux sz f p e_size_incomplete e_size_invalid e_payload (Seq.append b1 b2) b1 b2

#reset-options "--z3rlimit 32 --z3cliopt smt.arith.nl=false --z3refresh"

let serialize_bounded_vldata_strong_correct
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (e_size_incomplete e_size_invalid e_payload: err)
  (input: parse_bounded_vldata_strong_t min max s)
: Lemma
  (let formatted = serialize_bounded_vldata_strong' min max s e_size_incomplete input in
    parse (parse_bounded_vldata_strong min max s e_size_incomplete e_size_invalid e_payload) formatted == Correct (input, Seq.length formatted))
= let sz = log256' max in
  let sp = serialize s input in
  let nlen = Seq.length sp in
  assert (min <= nlen /\ nlen <= max);
  let len = U32.uint_to_t nlen in
  assert (U32.v len < pow2 (FStar.Mul.op_Star 8 sz));
  let (len: bounded_integer sz) = len in
  let slen = serialize (serialize_bounded_integer sz e_size_incomplete) len in
  assert (Seq.length slen == sz);
  let pslen = parse (parse_bounded_integer sz e_size_incomplete) slen in
  assert (Correct? pslen);
  let (Correct (len', consumed_len')) = pslen in
  assert (len == len');
  assert (in_bounds min max len' == true);
  assert (Seq.length sp == U32.v len);
  let psp = parse p sp in
  assert (Correct? psp);
  let (Correct (_, consumed_p)) = psp in
  assert ((consumed_p <: nat) == Seq.length sp);
  serialize_vldata_gen_correct sz (in_bounds min max) p
    e_size_incomplete e_size_invalid e_payload
    slen
    sp
  ;
  ()

let serialize_bounded_vldata_strong
  (min: nat)
  (max: nat { min <= max /\ max > 0 /\ max < 4294967296 } )
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (e_size_incomplete e_size_invalid e_payload: err)
: Tot (serializer (parse_bounded_vldata_strong min max s e_size_incomplete e_size_invalid e_payload))
= Classical.forall_intro (serialize_bounded_vldata_strong_correct min max s e_size_incomplete e_size_invalid e_payload);
  serialize_bounded_vldata_strong' min max s e_size_incomplete
