module LowParse.Spec.Combinators
include LowParse.Spec.Base

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

(** Constant-size parsers *)

let make_constant_size_parser_aux
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
: Tot (bare_parser t)
= fun (s: bytes) ->
  if Seq.length s < sz
  then None
  else begin
    let s' : bytes = Seq.slice s 0 sz in
    match f s' with
    | None -> None
    | Some v ->
      let (sz: consumed_length s) = sz in
      Some (v, sz)
  end

let make_constant_size_parser_precond_precond
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
  (s1: bytes { Seq.length s1 == sz } )
  (s2: bytes { Seq.length s2 == sz } )
: GTot Type0
= (Some? (f s1) \/ Some? (f s2)) /\ f s1 == f s2

let make_constant_size_parser_precond
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
: GTot Type0
= forall (s1: bytes {Seq.length s1 == sz}) (s2: bytes {Seq.length s2 == sz}) .
    make_constant_size_parser_precond_precond sz t f s1 s2 ==> Seq.equal s1 s2

let make_constant_size_parser_precond'
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
: GTot Type0
= forall (s1: bytes {Seq.length s1 == sz}) (s2: bytes {Seq.length s2 == sz}) .
    make_constant_size_parser_precond_precond sz t f s1 s2 ==> s1 == s2

let make_constant_size_parser_injective
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
: Lemma
  (requires (
    make_constant_size_parser_precond sz t f
  ))
  (ensures (
    injective (make_constant_size_parser_aux sz t f)
  ))
= let p : bare_parser t = make_constant_size_parser_aux sz t f in
  let prf1
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond p b1 b2))
    (ensures (injective_postcond p b1 b2))
  = assert (Some? (parse p b1));
    assert (Some? (parse p b2));
    let (Some (v1, len1)) = parse p b1 in
    let (Some (v2, len2)) = parse p b2 in
    assert ((len1 <: nat) == (len2 <: nat));
    assert ((len1 <: nat) == sz);
    assert ((len2 <: nat) == sz);
    assert (make_constant_size_parser_precond_precond sz t f (Seq.slice b1 0 len1) (Seq.slice b2 0 len2));
    assert (make_constant_size_parser_precond' sz t f)
  in
  Classical.forall_intro_2 (fun (b1: bytes) -> Classical.move_requires (prf1 b1))

let constant_size_parser_kind
  (sz: nat)
: Tot parser_kind
= strong_parser_kind sz sz ({
    parser_kind_metadata_total = false;
  })

let make_constant_size_parser
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
: Pure (
    parser
      (constant_size_parser_kind sz)
      t
  )
  (requires (
    make_constant_size_parser_precond sz t f
  ))
  (ensures (fun _ -> True))
= let p : bare_parser t = make_constant_size_parser_aux sz t f in
  make_constant_size_parser_injective sz t f;
  p

let make_total_constant_size_parser_precond
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot t))
: GTot Type0
= forall (s1: bytes {Seq.length s1 == sz}) (s2: bytes {Seq.length s2 == sz}) .
  f s1 == f s2 ==> Seq.equal s1 s2

inline_for_extraction
let total_constant_size_parser_kind
  (sz: nat)
: Tot parser_kind
= strong_parser_kind sz sz ({
    parser_kind_metadata_total = true;
  })

let make_total_constant_size_parser
  (sz: nat)
  (t: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot t))
: Pure (
    parser
      (total_constant_size_parser_kind sz)
      t
  )
  (requires (
    make_total_constant_size_parser_precond sz t f
  ))
  (ensures (fun _ -> True))
= let p : bare_parser t = make_constant_size_parser sz t (fun x -> Some (f x)) in
  p


(** Combinators *)

/// monadic return for the parser monad
unfold
let parse_ret' (#t:Type) (v:t) : Tot (bare_parser t) =
  fun (b: bytes) -> Some (v, (0 <: consumed_length b))

// unfold
let parse_ret_kind : parser_kind =
  strong_parser_kind 0 0 ({
    parser_kind_metadata_total = true;
  })

let parse_ret (#t:Type) (v:t) : Tot (parser parse_ret_kind t) =
  parse_ret' v

let parse_empty : parser parse_ret_kind unit =
  parse_ret ()

let serialize_empty' : serializer parse_empty =
  fun (x:unit) -> Seq.empty

let serialize_empty : serializer parse_empty = serialize_empty'

#set-options "--z3rlimit 16"

let fail_parser_kind_precond
  (k: parser_kind)
: GTot Type0
= k.parser_kind_metadata.parser_kind_metadata_total == false /\
  (Some? k.parser_kind_high ==> k.parser_kind_low <= Some?.v k.parser_kind_high)

let fail_parser'
  (t: Type0)
: Tot (bare_parser t)
= fun _ -> None

let fail_parser
  (k: parser_kind)
  (t: Type0)
: Pure (parser k t)
  (requires (fail_parser_kind_precond k))
  (ensures (fun _ -> True))
= let p = fail_parser' t in
  strengthen k p

inline_for_extraction
let parse_false_kind = strong_parser_kind 0 0 ({ parser_kind_metadata_total = false })

let parse_false : parser parse_false_kind (squash False) = fail_parser _ _

let serialize_false : serializer parse_false = fun input -> false_elim ()

/// monadic bind for the parser monad

val and_then_bare : #t:Type -> #t':Type ->
                p:bare_parser t ->
                p': (t -> Tot (bare_parser t')) ->
                Tot (bare_parser t')
let and_then_bare #t #t' p p' =
    fun (b: bytes) ->
    match parse p b with
    | Some (v, l) ->
      begin
	let p'v = p' v in
	let s' : bytes = Seq.slice b l (Seq.length b) in
	match parse p'v s' with
	| Some (v', l') ->
	  let res : consumed_length b = l + l' in
	  Some (v', res)
	| None -> None
      end
    | None -> None

let and_then_cases_injective_precond
  (#t:Type)
  (#t':Type)
  (p': (t -> Tot (bare_parser t')))
  (x1 x2: t)
  (b1 b2: bytes)
: GTot Type0
= Some? ((p' x1) b1) /\
  Some? ((p' x2) b2) /\ (
    let (Some (v1, _)) = (p' x1) b1 in
    let (Some (v2, _)) = (p' x2) b2 in
    v1 == v2
  )

let and_then_cases_injective
  (#t:Type)
  (#t':Type)
  (p': (t -> Tot (bare_parser t')))
: GTot Type0
= forall (x1 x2: t) (b1 b2: bytes) .
  and_then_cases_injective_precond p' x1 x2 b1 b2 ==>
  x1 == x2

val and_then_injective
  (#t:Type)
  (#t':Type)
  (p: bare_parser t)
  (p': (t -> Tot (bare_parser t')))
: Lemma
  (requires (
    injective p /\
    (forall (x: t) . injective (p' x)) /\
    and_then_cases_injective p'
  ))
  (ensures (
    injective (and_then_bare p p')
  ))

let and_then_injective #t #t' p p' =
  let ps = and_then_bare p p' in
  let f
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond ps b1 b2))
    (ensures (injective_postcond ps b1 b2))
  = let (Some (v1, len1)) = p b1 in
    let (Some (v2, len2)) = p b2 in
    let b1' : bytes = Seq.slice b1 len1 (Seq.length b1) in
    let b2' : bytes = Seq.slice b2 len2 (Seq.length b2) in
    assert (Some? ((p' v1) b1'));
    assert (Some? ((p' v2) b2'));
    assert (and_then_cases_injective_precond p' v1 v2 b1' b2');
    assert (v1 == v2);
    assert (injective_precond p b1 b2);
    assert ((len1 <: nat) == (len2 <: nat));
    assert (injective (p' v1));
    assert (injective_precond (p' v1) b1' b2');
    assert (injective_postcond (p' v1) b1' b2');
    let (Some (_, len1')) = (p' v1) b1' in
    let (Some (_, len2')) = (p' v2) b2' in
    assert ((len1' <: nat) == (len2' <: nat));
    Seq.lemma_split (Seq.slice b1 0 (len1 + len1')) len1;
    Seq.lemma_split (Seq.slice b2 0 (len2 + len2')) len1;
    assert (injective_postcond ps b1 b2)
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (f x))

val and_then_no_lookahead_on
    (#t:Type)
    (#t':Type)
    (p: bare_parser t)
    (p': (t -> Tot (bare_parser t')))
    (x: bytes) 
    (x' : bytes)
  : Lemma
    (requires (
      no_lookahead p /\
      injective p /\
      (forall (x: t) . no_lookahead (p' x))
    ))
    (ensures (no_lookahead_on (and_then_bare p p') x x'))

let and_then_no_lookahead_on #t #t' p p' x x' =
    let f = and_then_bare p p' in
    match f x with
    | Some v -> 
      let (y, off) = v in
      let off : nat = off in
      let (off_x : consumed_length x ) = off in
      if off <= Seq.length x'
      then
	let (off_x' : consumed_length x') = off in
	let g () : Lemma
	  (requires (Seq.slice x' 0 off_x' == Seq.slice x 0 off_x))
	  (ensures (
	    Some? (f x') /\ (
	    let (Some v') = f x' in
	    let (y', off') = v' in
	    y == y'
	  )))
	= assert (Some? (p x));
	  let (Some (y1, off1)) = p x in
	  assert (off1 <= off);
	  assert (off1 <= Seq.length x');
	  assert (Seq.slice x' 0 off1 == Seq.slice (Seq.slice x' 0 off_x') 0 off1);
	  assert (Seq.slice x' 0 off1 == Seq.slice x 0 off1);
	  assert (no_lookahead_on p x x');
	  assert (Some? (p x'));
	  let (Some v1') = p x' in
	  let (y1', off1') = v1' in
	  assert (y1 == y1');
	  assert (injective_precond p x x');
	  assert ((off1 <: nat) == (off1' <: nat));
	  let x2 : bytes = Seq.slice x off1 (Seq.length x) in
	  let x2' : bytes = Seq.slice x' off1 (Seq.length x') in
	  let p2 = p' y1 in
	  assert (Some? (p2 x2));
	  let (Some (y2, off2)) = p2 x2 in
	  assert (off == off1 + off2);
	  assert (off2 <= Seq.length x2);
	  assert (off2 <= Seq.length x2');
	  assert (Seq.slice x2' 0 off2 == Seq.slice (Seq.slice x' 0 off_x') off1 (off1 + off2));
	  assert (Seq.slice x2' 0 off2 == Seq.slice x2 0 off2);
	  assert (no_lookahead_on p2 x2 x2');
	  assert (Some? (p2 x2'));
	  let (Some v2') = p2 x2' in
	  let (y2', _) = v2' in
	  assert (y2 == y2')
	in
	Classical.move_requires g ()
      else ()
    | _ -> ()

let and_then_metadata
  (k1 k2: parser_kind_metadata_t)
: Tot parser_kind_metadata_t
= {
    parser_kind_metadata_total = k1.parser_kind_metadata_total && k2.parser_kind_metadata_total;
  }

// unfold
let and_then_kind
  (k1 k2: parser_kind)
: Tot parser_kind
= {
    parser_kind_low = k1.parser_kind_low + k2.parser_kind_low;
    parser_kind_high =
      begin
	if Some? k1.parser_kind_high && Some? k2.parser_kind_high
	then Some (Some?.v k1.parser_kind_high + Some?.v k2.parser_kind_high)
	else None
      end;
    parser_kind_metadata = and_then_metadata k1.parser_kind_metadata k2.parser_kind_metadata;
    parser_kind_subkind =
      begin
        if k2.parser_kind_subkind = Some ParserConsumesAll
	then Some ParserConsumesAll
	else if k1.parser_kind_subkind = Some ParserStrong && k2.parser_kind_subkind = Some ParserStrong
	then Some ParserStrong
	else if k2.parser_kind_high = Some 0 && k2.parser_kind_subkind = Some ParserStrong
	then k1.parser_kind_subkind
	else None
      end;
  }

let and_then_no_lookahead
  (#k: parser_kind)
  (#t:Type)
  (p:parser k t)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
: Lemma
  (requires (
    and_then_cases_injective p'
  ))
  (ensures ((k.parser_kind_subkind == Some ParserStrong /\ k'.parser_kind_subkind == Some ParserStrong) ==> no_lookahead (and_then_bare p p')))
= if k.parser_kind_subkind = Some ParserStrong && k.parser_kind_subkind = Some ParserStrong then
    Classical.forall_intro_2 (fun x -> Classical.move_requires (and_then_no_lookahead_on p p' x))
  else ()

#set-options "--max_fuel 8 --max_ifuel 8 --z3rlimit 64"

let and_then_correct
  (#k: parser_kind)
  (#t:Type)
  (p:parser k t)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
: Lemma
  (requires (
    and_then_cases_injective p'
  ))
  (ensures (
    injective (and_then_bare p p') /\
    parser_kind_prop (and_then_kind k k') (and_then_bare p p')
  ))
= and_then_injective p p';
  and_then_no_lookahead p p'

#reset-options

val and_then
  (#k: parser_kind)
  (#t:Type)
  (p:parser k t)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
: Pure (parser (and_then_kind k k') t')
  (requires (
    and_then_cases_injective p'
  ))
  (ensures (fun _ -> True))

let and_then #k #t p #k' #t' p' =
  let f : bare_parser t' = and_then_bare p p' in
  and_then_correct p p' ;
  f

(* Special case for non-dependent parsing *)

let nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
: Tot (parser (and_then_kind k1 k2) (t1 * t2))
= p1 `and_then` (fun v1 -> p2 `and_then` (fun v2 -> (parse_ret (v1, v2))))

#set-options "--z3rlimit 16"

let nondep_then_eq
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (b: bytes)
: Lemma
  (parse (nondep_then p1 p2) b == (match parse p1 b with
  | Some (x1, consumed1) ->
    let b' = Seq.slice b consumed1 (Seq.length b) in
    begin match parse p2 b' with
    | Some (x2, consumed2) ->
      Some ((x1, x2), consumed1 + consumed2)
    | _ -> None
    end
  | _ -> None
  ))
= ()

#set-options "--z3rlimit 32"

let bare_serialize_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s2: serializer p2)
: Tot (bare_serializer (t1 * t2))
= fun (x: t1 * t2) ->
  let (x1, x2) = x in
  Seq.append (s1 x1) (s2 x2)

let seq_slice_append_l
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) == s1)
= assert (Seq.equal (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1)) s1)

let seq_slice_append_r
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length (Seq.append s1 s2)) == s2)
= assert (Seq.equal (Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length (Seq.append s1 s2))) s2)

let bare_serialize_nondep_then_correct
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s2: serializer p2)
: Lemma
  (requires (k1.parser_kind_subkind == Some ParserStrong))
  (ensures (serializer_correct (nondep_then p1 p2) (bare_serialize_nondep_then p1 s1 p2 s2)))
= let prf
    (x: t1 * t2)
  : Lemma (parse (nondep_then p1 p2) (bare_serialize_nondep_then p1 s1 p2 s2 x) == Some (x, Seq.length (bare_serialize_nondep_then p1 s1 p2 s2 x)))
  = let v1' = parse p1 (bare_serialize_nondep_then p1 s1 p2 s2 x) in
    let v1 = parse p1 (s1 (fst x)) in
    assert (Some? v1);
    assert (no_lookahead_on p1 (s1 (fst x)) (bare_serialize_nondep_then p1 s1 p2 s2 x));
    let (Some (_, len')) = parse p1 (s1 (fst x)) in
    assert (len' == Seq.length (s1 (fst x)));
    assert (len' <= Seq.length (bare_serialize_nondep_then p1 s1 p2 s2 x));
    assert (Seq.slice (s1 (fst x)) 0 len' == s1 (fst x));
    seq_slice_append_l (s1 (fst x)) (s2 (snd x));
    assert (no_lookahead_on_precond p1 (s1 (fst x)) (bare_serialize_nondep_then p1 s1 p2 s2 x));
    assert (no_lookahead_on_postcond p1 (s1 (fst x)) (bare_serialize_nondep_then p1 s1 p2 s2 x));
    assert (Some? v1');
    assert (injective_precond p1 (s1 (fst x)) (bare_serialize_nondep_then p1 s1 p2 s2 x));
    assert (injective_postcond p1 (s1 (fst x)) (bare_serialize_nondep_then p1 s1 p2 s2 x));
    let (Some (x1, len1)) = v1 in
    let (Some (x1', len1')) = v1' in
    assert (x1 == x1');
    assert ((len1 <: nat) == (len1' <: nat));
    assert (x1 == fst x);
    assert (len1 == Seq.length (s1 (fst x)));
    assert (bare_serialize_nondep_then p1 s1 p2 s2 x == Seq.append (s1 (fst x)) (s2 (snd x)));
    let s = bare_serialize_nondep_then p1 s1 p2 s2 x in
    seq_slice_append_r (s1 (fst x)) (s2 (snd x));
    ()
  in
  Classical.forall_intro prf

let serialize_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s2: serializer p2)
: Tot (serializer (nondep_then p1 p2))
= bare_serialize_nondep_then_correct p1 s1 p2 s2;
  bare_serialize_nondep_then p1 s1 p2 s2

let serialize_nondep_then_upd_left
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t1)
: Lemma
  (requires (Seq.length (serialize s1 y) == Seq.length (serialize s1 (fst x))))
  (ensures (
    let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
    Seq.length (serialize s1 y) <= Seq.length s /\
    serialize (serialize_nondep_then p1 s1 u p2 s2) (y, snd x) == seq_upd_seq s 0 (serialize s1 y)
  ))
= let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
  seq_upd_seq_left s (serialize s1 y);
  let l1 = Seq.length (serialize s1 (fst x)) in
  Seq.lemma_split s l1;
  Seq.lemma_append_inj (Seq.slice s 0 l1) (Seq.slice s l1 (Seq.length s)) (serialize s1 (fst x)) (serialize s2 (snd x))

let serialize_nondep_then_upd_left_chain
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t1)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let s1' = serialize s1 (fst x) in
    i' + Seq.length s' <= Seq.length s1' /\
    serialize s1 y == seq_upd_seq s1' i' s'
  ))
  (ensures (
    let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
    i' + Seq.length s' <= Seq.length s /\
    serialize (serialize_nondep_then p1 s1 u p2 s2) (y, snd x) == seq_upd_seq s i' s'
  ))
= serialize_nondep_then_upd_left p1 s1 u p2 s2 x y;
  let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
  let s1' = serialize s1 (fst x) in
  let l1 = Seq.length s1' in
  Seq.lemma_split s l1;
  Seq.lemma_append_inj (Seq.slice s 0 l1) (Seq.slice s l1 (Seq.length s)) s1' (serialize s2 (snd x));
  seq_upd_seq_right_to_left s 0 s1' i' s';
  seq_upd_seq_slice_idem s 0 (Seq.length s1')

let serialize_nondep_then_upd_bw_left
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t1)
: Lemma
  (requires (Seq.length (serialize s1 y) == Seq.length (serialize s1 (fst x))))
  (ensures (
    let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
    let len2 = Seq.length (serialize s2 (snd x)) in
    len2 + Seq.length (serialize s1 y) <= Seq.length s /\
    serialize (serialize_nondep_then p1 s1 u p2 s2) (y, snd x) == seq_upd_bw_seq s len2 (serialize s1 y)
  ))
= serialize_nondep_then_upd_left p1 s1 u p2 s2 x y

#reset-options "--z3refresh --z3rlimit 64 --z3cliopt smt.arith.nl=false"

let serialize_nondep_then_upd_bw_left_chain
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t1)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let s1' = serialize s1 (fst x) in
    i' + Seq.length s' <= Seq.length s1' /\
    serialize s1 y == seq_upd_bw_seq s1' i' s'
  ))
  (ensures (
    let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
    let len2 = Seq.length (serialize s2 (snd x)) in
    len2 + i' + Seq.length s' <= Seq.length s /\
    serialize (serialize_nondep_then p1 s1 u p2 s2) (y, snd x) == seq_upd_bw_seq s (len2 + i') s'
  ))
= let j' = Seq.length (serialize s1 (fst x)) - i' - Seq.length s' in
  serialize_nondep_then_upd_left_chain p1 s1 u p2 s2 x y j' s';
  assert (j' == Seq.length (serialize (serialize_nondep_then p1 s1 u p2 s2) x) - (Seq.length (serialize s2 (snd x)) + i') - Seq.length s')

let serialize_nondep_then_upd_right
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t2)
: Lemma
  (requires (Seq.length (serialize s2 y) == Seq.length (serialize s2 (snd x))))
  (ensures (
    let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
    Seq.length (serialize s2 y) <= Seq.length s /\
    serialize (serialize_nondep_then p1 s1 u p2 s2) (fst x, y) == seq_upd_seq s (Seq.length s - Seq.length (serialize s2 y)) (serialize s2 y)
  ))
= let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
  seq_upd_seq_right s (serialize s2 y);
  let l2 = Seq.length s - Seq.length (serialize s2 (snd x)) in
  Seq.lemma_split s l2;
  Seq.lemma_append_inj (Seq.slice s 0 l2) (Seq.slice s l2 (Seq.length s)) (serialize s1 (fst x)) (serialize s2 (snd x))

let serialize_nondep_then_upd_right_chain
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t2)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let s2' = serialize s2 (snd x) in
    i' + Seq.length s' <= Seq.length s2' /\
    serialize s2 y == seq_upd_seq s2' i' s'
  ))
  (ensures (
    let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
    let l1 = Seq.length (serialize s1 (fst x)) in
    Seq.length s == l1 + Seq.length (serialize s2 (snd x)) /\
    l1 + i' + Seq.length s' <= Seq.length s /\
    serialize (serialize_nondep_then p1 s1 u p2 s2) (fst x, y) == seq_upd_seq s (l1 + i') s'
  ))
= serialize_nondep_then_upd_right p1 s1 u p2 s2 x y;
  let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
  let s2' = serialize s2 (snd x) in
  let l2 = Seq.length s - Seq.length s2' in
  Seq.lemma_split s l2;
  Seq.lemma_append_inj (Seq.slice s 0 l2) (Seq.slice s l2 (Seq.length s)) (serialize s1 (fst x)) s2';
  seq_upd_seq_right_to_left s l2 s2' i' s';
  seq_upd_seq_slice_idem s l2 (Seq.length s)

let serialize_nondep_then_upd_bw_right
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t2)
: Lemma
  (requires (Seq.length (serialize s2 y) == Seq.length (serialize s2 (snd x))))
  (ensures (
    let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
    Seq.length (serialize s2 y) <= Seq.length s /\
    serialize (serialize_nondep_then p1 s1 u p2 s2) (fst x, y) == seq_upd_bw_seq s 0 (serialize s2 y)
  ))
= serialize_nondep_then_upd_right p1 s1 u p2 s2 x y

let serialize_nondep_then_upd_bw_right_chain
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t2)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let s2' = serialize s2 (snd x) in
    i' + Seq.length s' <= Seq.length s2' /\
    serialize s2 y == seq_upd_bw_seq s2' i' s'
  ))
  (ensures (
    let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
    let l1 = Seq.length (serialize s1 (fst x)) in
    Seq.length s == l1 + Seq.length (serialize s2 (snd x)) /\
    i' + Seq.length s' <= Seq.length s /\
    serialize (serialize_nondep_then p1 s1 u p2 s2) (fst x, y) == seq_upd_bw_seq s i' s'
  ))
= let s2' = serialize s2 (snd x) in
  let j' = Seq.length s2' - i' - Seq.length s' in
  assert (j' + Seq.length s' <= Seq.length s2');
  assert (serialize s2 y == seq_upd_seq s2' j' s');
  let s = serialize (serialize_nondep_then p1 s1 u p2 s2) x in
  serialize_nondep_then_upd_right_chain p1 s1 u p2 s2 x y j' s';
  assert (Seq.length (serialize s1 (fst x)) + j' == Seq.length s - i' - Seq.length s');
  ()

#reset-options "--z3rlimit 32"

(** Apply a total transformation on parsed data *)

let parse_strengthen_prf
  (#k: parser_kind)
  (#t1: Type0)
  (p1: parser k t1)
  (p2: t1 -> GTot Type0)
: Tot Type0
= (xbytes: bytes) ->
  (consumed: consumed_length xbytes) ->
  (x: t1) ->
  Lemma
  (requires (parse p1 xbytes == Some (x, consumed)))
  (ensures (p2 x))

let bare_parse_strengthen
  (#k: parser_kind)
  (#t1: Type0)
  (p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Tot (bare_parser (x: t1 { p2 x } ))
= fun (xbytes: bytes) ->
  match parse p1 xbytes with
  | Some (x, consumed) ->
    prf xbytes consumed x;
    let (x' : t1 { p2 x' } ) = x in
    Some (x', consumed)
  | _ -> None

let bare_parse_strengthen_no_lookahead
  (#k: parser_kind)
  (#t1: Type0)
  (p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Lemma
  (no_lookahead p1 ==> no_lookahead (bare_parse_strengthen p1 p2 prf))
= let p' : bare_parser (x: t1 { p2 x } ) = bare_parse_strengthen p1 p2 prf in
  assert (forall (b1 b2: bytes) . no_lookahead_on p1 b1 b2 ==> no_lookahead_on p' b1 b2)

let bare_parse_strengthen_injective
  (#k: parser_kind)
  (#t1: Type0)
  (p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Lemma
  (injective (bare_parse_strengthen p1 p2 prf))
= let p' : bare_parser (x: t1 { p2 x } ) = bare_parse_strengthen p1 p2 prf in
  assert (forall (b1 b2: bytes) . injective_precond p' b1 b2 ==> injective_precond p1 b1 b2);
  assert (forall (b1 b2: bytes) . injective_postcond p1 b1 b2 ==> injective_postcond p' b1 b2)

let bare_parse_strengthen_correct
  (#k: parser_kind)
  (#t1: Type0)
  (p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Lemma
  (injective (bare_parse_strengthen p1 p2 prf) /\
  parser_kind_prop k (bare_parse_strengthen p1 p2 prf))
= bare_parse_strengthen_no_lookahead p1 p2 prf;
  bare_parse_strengthen_injective p1 p2 prf;
  ()

let parse_strengthen
  (#k: parser_kind)
  (#t1: Type0)
  (p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Tot (parser k (x: t1 { p2 x } ))
= bare_parse_strengthen_correct p1 p2 prf;
  bare_parse_strengthen p1 p2 prf

let serialize_strengthen'
  (#k: parser_kind)
  (#t1: Type0)
  (#p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
  (s: serializer p1)
  (input: t1 { p2 input } )
: GTot bytes
= serialize s input

let serialize_strengthen_correct
  (#k: parser_kind)
  (#t1: Type0)
  (#p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
  (s: serializer p1)
  (input: t1 { p2 input } )
: Lemma
  (let output = serialize_strengthen' p2 prf s input in
  parse (parse_strengthen p1 p2 prf) output == Some (input, Seq.length output))
= ()

let serialize_strengthen
  (#k: parser_kind)
  (#t1: Type0)
  (#p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
  (s: serializer p1)
: Tot (serializer (parse_strengthen p1 p2 prf))
= Classical.forall_intro (serialize_strengthen_correct p2 prf s);
  serialize_strengthen' p2 prf s

/// monadic return for the parser monad
unfold
let parse_fret' (#t #t':Type) (f: t -> GTot t') (v:t) : Tot (bare_parser t') =
  fun (b: bytes) -> Some (f v, (0 <: consumed_length b))

unfold
let parse_fret (#t #t':Type) (f: t -> GTot t') (v:t) : Tot (parser parse_ret_kind t') =
  parse_fret' f v

let synth_injective
  (#t1: Type0)
  (#t2: Type0)
  (f: (t1 -> GTot t2))
: GTot Type0
= forall (x x' : t1) . {:pattern f x ; f x'} f x == f x' ==> x == x'

let synth_injective_intro
  (#t1: Type0)
  (#t2: Type0)
  (f: (t1 -> GTot t2))
: Lemma
  (requires (forall (x x' : t1) . f x == f x' ==> x == x'))
  (ensures (synth_injective f))
= ()

let parse_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
: Pure (parser k t2)
  (requires (
    synth_injective f2
  ))
  (ensures (fun _ -> True))
= coerce (parser k t2) (and_then p1 (fun v1 -> parse_fret f2 v1))

let parse_synth_eq
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (b: bytes)
: Lemma
  (requires (synth_injective f2))
  (ensures (parse (parse_synth p1 f2) b == (match parse p1 b with
  | None -> None
  | Some (x1, consumed) -> Some (f2 x1, consumed))))
= ()

let compose (#t1 #t2 #t3: Type) (f1: t1 -> GTot t2) (f2: t2 -> GTot t3) (x: t1) : GTot t3 =
  let y1 = f1 x in
  f2 y1

let make_total_constant_size_parser_compose
  (sz: nat)
  (t1 t2: Type0)
  (f1: ((s: bytes {Seq.length s == sz}) -> GTot t1))
  (g2: t1 -> GTot t2)
: Lemma
  (requires (
    make_total_constant_size_parser_precond sz t1 f1 /\
    (forall x x' . g2 x == g2 x' ==> x == x')
  ))
  (ensures (
    make_total_constant_size_parser_precond sz t1 f1 /\
    make_total_constant_size_parser_precond sz t2 (f1 `compose` g2) /\
    (forall x x' . g2 x == g2 x' ==> x == x') /\
    (forall input . parse (make_total_constant_size_parser sz t2 (f1 `compose` g2)) input == parse (make_total_constant_size_parser sz t1 f1 `parse_synth` g2) input)
  ))
= ()

val bare_serialize_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
: Tot (bare_serializer t2)

let bare_serialize_synth #k #t1 #t2 p1 f2 s1 g1 =
  fun (x: t2) -> s1 (g1 x)

val bare_serialize_synth_correct
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
: Lemma
  (requires (
    (forall (x : t2) . f2 (g1 x) == x) /\
    (forall (x x' : t1) . f2 x == f2 x' ==> x == x')
  ))
  (ensures (serializer_correct (parse_synth p1 f2) (bare_serialize_synth p1 f2 s1 g1 )))

let bare_serialize_synth_correct #k #t1 #t2 p1 f2 s1 g1 =
  ()

let synth_inverse
  (#t1: Type0)
  (#t2: Type0)
  (f2: (t1 -> GTot t2))
  (g1: (t2 -> GTot t1))
: GTot Type0
= (forall (x : t2) . f2 (g1 x) == x)

let synth_inverse_intro
  (#t1: Type0)
  (#t2: Type0)
  (f2: (t1 -> GTot t2))
  (g1: (t2 -> GTot t1))
: Lemma
  (requires (forall (x : t2) . f2 (g1 x) == x))
  (ensures (synth_inverse f2 g1))
= ()

let synth_inverse_synth_injective
  (#t1: Type0)
  (#t2: Type0)
  (f: (t1 -> GTot t2))
  (g: (t2 -> GTot t1))
: Lemma
  (requires (synth_inverse g f))
  (ensures (synth_injective f))
= ()

let serialize_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
: Tot (serializer (parse_synth p1 f2))
= bare_serialize_synth_correct p1 f2 s1 g1;
  bare_serialize_synth p1 f2 s1 g1

let serialize_synth_eq
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
  (x: t2)
: Lemma
  (serialize (serialize_synth p1 f2 s1 g1 u) x == serialize s1 (g1 x))
= ()

let serialize_synth_upd_chain
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
  (x1: t1)
  (x2: t2)
  (y1: t1)
  (y2: t2)
  (i': nat)
  (s' : bytes)
: Lemma
  (requires (
    let s = serialize s1 x1 in
    i' + Seq.length s' <= Seq.length s /\
    serialize s1 y1 == seq_upd_seq s i' s' /\
    x2 == f2 x1 /\
    y2 == f2 y1
  ))
  (ensures (
    let s = serialize (serialize_synth p1 f2 s1 g1 u) x2 in
    i' + Seq.length s' <= Seq.length s /\
    Seq.length s == Seq.length (serialize s1 x1) /\
    serialize (serialize_synth p1 f2 s1 g1 u) y2 == seq_upd_seq s i' s'
  ))
= ()

let serialize_synth_upd_bw_chain
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
  (x1: t1)
  (x2: t2)
  (y1: t1)
  (y2: t2)
  (i': nat)
  (s' : bytes)
: Lemma
  (requires (
    let s = serialize s1 x1 in
    i' + Seq.length s' <= Seq.length s /\
    serialize s1 y1 == seq_upd_bw_seq s i' s' /\
    x2 == f2 x1 /\
    y2 == f2 y1
  ))
  (ensures (
    let s = serialize (serialize_synth p1 f2 s1 g1 u) x2 in
    i' + Seq.length s' <= Seq.length s /\
    Seq.length s == Seq.length (serialize s1 x1) /\
    serialize (serialize_synth p1 f2 s1 g1 u) y2 == seq_upd_bw_seq s i' s'
  ))
= ()

(** Tot vs. Ghost *)

unfold
let lift_parser'
  (#k: parser_kind)
  (#t: Type0)
  (f: unit -> GTot (parser k t))
: Tot (bare_parser t)
= fun (input: bytes) -> parse (f ()) input

let lift_parser_correct
  (#k: parser_kind)
  (#t: Type0)
  (f: unit -> GTot (parser k t))
: Lemma
  (parser_kind_prop k (lift_parser' f))
= parser_kind_prop_ext k (f ()) (lift_parser' f)

unfold
let lift_parser
  (#k: parser_kind)
  (#t: Type0)
  (f: unit -> GTot (parser k t))
: Tot (bare_parser t)
= lift_parser' f

(** Refinements *)

// unfold
let parse_filter_kind (k: parser_kind) : Tot parser_kind =
  {
    parser_kind_low = k.parser_kind_low;
    parser_kind_high = k.parser_kind_high;
    parser_kind_metadata = {
      parser_kind_metadata_total = false;
    };
    parser_kind_subkind = k.parser_kind_subkind;
  }

// unfold
let parse_filter_payload_kind : parser_kind =
  strong_parser_kind 0 0 ({
    parser_kind_metadata_total = false;
  })

let parse_filter_payload
  (#t: Type0)
  (f: (t -> GTot bool))
  (v: t)
: Tot (parser parse_filter_payload_kind (x: t { f x == true }))
= lift_parser (fun () ->
    if f v
    then
      let v' : (x: t { f x == true } ) = v in
      weaken parse_filter_payload_kind (parse_ret v')
    else fail_parser parse_filter_payload_kind (x: t {f x == true} )
  )

let parse_filter
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (f: (t -> GTot bool))
: Tot (parser (parse_filter_kind k) (x: t { f x == true }))
= p `and_then` (parse_filter_payload f)

let parse_filter_eq
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (f: (t -> GTot bool))
  (input: bytes)
: Lemma
  (parse (parse_filter p f) input == (match parse p input with
  | None -> None
  | Some (x, consumed) ->
    if f x
    then Some (x, consumed)
    else None
  ))
= ()

let serialize_filter'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot bool))
: Tot (bare_serializer (x: t { f x == true } ))
= fun (input: t { f input == true } ) -> s input

let serialize_filter_correct
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot bool))
: Lemma
  (serializer_correct (parse_filter p f) (serialize_filter' s f))
= ()

let serialize_filter
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot bool))
: Tot (serializer (parse_filter p f))
= serialize_filter_correct s f;
  serialize_filter' s f

(* Helpers to define `if` combinators *)

let cond_true (cond: bool) : Tot Type0 = (u: unit { cond == true } )

let cond_false (cond: bool) : Tot Type0 = (u: unit { cond == false } )
