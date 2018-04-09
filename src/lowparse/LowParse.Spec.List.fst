module LowParse.Spec.List
include LowParse.Spec.Combinators // for seq_slice_append_l

module Seq = FStar.Seq
module L = FStar.List.Tot
module U32 = FStar.UInt32
module Classical = FStar.Classical

(* Parse a list, until there is nothing left to read. This parser will mostly fail EXCEPT if the whole size is known and the slice has been suitably truncated beforehand, or if the elements of the list all have a known constant size. *)

val parse_list_aux
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (_: unit { k.parser_kind_low > 0 } )
  (b: bytes)
: GTot (result (list t * (consumed_length b)) err)
  (decreases (Seq.length b))

let rec parse_list_aux #k #t #err p u b =
  if Seq.length b = 0
  then 
    Correct ([], (0 <: consumed_length b))
  else
    match p b with
    | Error e -> Error e
    | Correct (v, n) ->
      begin
        match parse_list_aux p u (Seq.slice b n (Seq.length b)) with
	| Correct (l, n') -> Correct (v :: l, (n + n' <: consumed_length b))
	| Error e -> Error e
      end

val parse_list_bare
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (_: unit { k.parser_kind_low > 0 } )
: Tot (bare_parser (list t) err)

let parse_list_bare #k #t #err p u = (fun b -> parse_list_aux #k #t #err p u b) <: bare_parser (list t) err

let rec parse_list_bare_consumed
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
  (b: bytes)
: Lemma
  (requires (Correct? (parse_list_bare p u b)))
  (ensures (
    let pb = parse_list_bare p u b in (
    Correct? pb /\ (
    let (Correct (_, consumed)) = pb in
    consumed == Seq.length b
  ))))
  (decreases (Seq.length b))
= if Seq.length b = 0
  then ()
  else
    let (Correct (_, consumed1)) = p b in
    let b' = Seq.slice b consumed1 (Seq.length b) in
    parse_list_bare_consumed p u b'

let parse_list_bare_consumes_all
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
: Lemma
  (consumes_all (parse_list_bare p u))
= Classical.forall_intro (Classical.move_requires (parse_list_bare_consumed p u))

let no_lookahead_weak_on_parse_list_bare
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
  (x x' : bytes)
: Lemma
  (no_lookahead_weak_on (parse_list_bare p u) x x')
= match parse_list_bare p u x with
  | Correct _ -> parse_list_bare_consumed p u x
  | _ -> ()

#set-options "--z3rlimit 16"

let parse_list_bare_injective
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
: Lemma
  (ensures (injective (parse_list_bare p u)))
= let f () : Lemma
    (injective p)
  = ()
  in
  let rec aux
    (b1: bytes)
    (b2: bytes)
  : Lemma
    (requires (injective_precond (parse_list_bare p u) b1 b2))
    (ensures (injective_postcond (parse_list_bare p u) b1 b2))
    (decreases (Seq.length b1 + Seq.length b2))
  = if Seq.length b1 = 0
    then begin
      () // assert (Seq.equal b1 b2)
    end else begin
      assert (injective_precond p b1 b2);
      f ();
      assert (injective_postcond p b1 b2);
      let (Correct (_, len1)) = parse p b1 in
      let (Correct (_, len2)) = parse p b2 in
      assert ((len1 <: nat) == (len2 <: nat));
      let b1' : bytes = Seq.slice b1 len1 (Seq.length b1) in
      let b2' : bytes = Seq.slice b2 len2 (Seq.length b2) in
      aux b1' b2';
      let (Correct (_, len1')) = parse (parse_list_bare p u) b1' in
      let (Correct (_, len2')) = parse (parse_list_bare p u) b2' in
      Seq.lemma_split (Seq.slice b1 0 (len1 + len1')) len1;
      Seq.lemma_split (Seq.slice b2 0 (len2 + len2')) len2;
      assert (injective_postcond (parse_list_bare p u) b1 b2)
    end
  in
  Classical.forall_intro_2 (fun b -> Classical.move_requires (aux b))

#reset-options

inline_for_extraction
let parse_list_kind =
  {
    parser_kind_low = 0;
    parser_kind_high = None;
    parser_kind_metadata = {
      parser_kind_metadata_total = false;
    };
    parser_kind_subkind = Some ParserConsumesAll;
  }

inline_for_extraction
val parse_list
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
: Tot (parser parse_list_kind (list t) err)

let parse_list #k #t #err p u =
  Classical.forall_intro_2 (no_lookahead_weak_on_parse_list_bare p u);
  parse_list_bare_injective p u;
  parse_list_bare_consumes_all p u;
  parse_list_bare p u

let rec bare_serialize_list
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
  (s: serializer p)
  (x: list t)
: GTot bytes
= match x with
  | [] -> Seq.createEmpty
  | a :: q -> Seq.append (s a) (bare_serialize_list p u s q)

unfold
let serialize_list_precond
  (k: parser_kind)
: GTot bool
= k.parser_kind_subkind = Some ParserStrong &&
  k.parser_kind_low > 0

let bare_serialize_list_correct
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
  (s: serializer p)
: Lemma
  (requires (serialize_list_precond k))
  (ensures (serializer_correct (parse_list p u) (bare_serialize_list p u s)))
= let f () : Lemma (serialize_list_precond k) = () in
  let rec prf
    (l: list t)
  : Lemma
    (parse (parse_list p u) (bare_serialize_list p u s l) == Correct (l, Seq.length (bare_serialize_list p u s l)))
  = match l with
    | [] -> ()
    | a :: q ->
      let pa = parse p (bare_serialize_list p u s l) in
      f ();
      assert (no_lookahead_on p (s a) (bare_serialize_list p u s l));
      seq_slice_append_l (s a) (bare_serialize_list p u s q);
      assert (no_lookahead_on_precond p (s a) (bare_serialize_list p u s l));
      assert (no_lookahead_on_postcond p (s a) (bare_serialize_list p u s l));
      assert (Correct? pa);
      assert (injective_precond p (s a) (bare_serialize_list p u s l));
      assert (injective_postcond p (s a) (bare_serialize_list p u s l));
      let (Correct (a', lena)) = pa in
      assert (a == a');
      assert (lena == Seq.length (s a));
      assert (lena > 0);
      prf q;
      seq_slice_append_r (s a) (bare_serialize_list p u s q)
  in
  Classical.forall_intro prf

let serialize_list
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (u: unit { k.parser_kind_low > 0 } )
: Pure (serializer (parse_list p u))
  (requires (
    serialize_list_precond k
  ))
  (ensures (fun _ -> True))
= bare_serialize_list_correct p u s;
  bare_serialize_list p u s

let serialize_list_nil
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (u: unit { k.parser_kind_low > 0 } )
: Lemma
  (requires (
    serialize_list_precond k
  ))
  (ensures (serialize (serialize_list s u) [] == Seq.createEmpty))
= ()

let serialize_list_cons
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (u: unit { k.parser_kind_low > 0 } )
  (a: t)
  (q: list t)
: Lemma
  (requires (
    serialize_list_precond k
  ))
  (ensures (
    serialize (serialize_list s u) (a :: q) == Seq.append (serialize s a) (serialize (serialize_list s u) q)
  ))
= ()

let serialize_list_singleton
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (u: unit { k.parser_kind_low > 0 } )
  (a: t)
: Lemma
  (requires (serialize_list_precond k))
  (ensures (serialize (serialize_list s u) [a] == serialize s a))
= Seq.append_empty_r (serialize s a)

let rec serialize_list_append
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (u: unit { k.parser_kind_low > 0 } )
  (l1 l2: list t)
: Lemma
  (requires (serialize_list_precond k))
  (ensures (serialize (serialize_list s u) (L.append l1 l2) == Seq.append (serialize (serialize_list s u) l1) (serialize (serialize_list s u) l2)))
= match l1 with
  | a :: q ->
    serialize_list_append s u q l2;
    Seq.append_assoc (serialize s a) (serialize (serialize_list s u) q) (serialize (serialize_list s u) l2)
  | [] ->
    Seq.append_empty_l (serialize (serialize_list s u) l2)

val list_length_constant_size_parser_correct
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
  (b: bytes)
: Lemma
  (requires (
    k.parser_kind_high == Some k.parser_kind_low /\
    Correct? (parse (parse_list p u) b)
  ))
  (ensures (
    let pb = parse (parse_list p u) b in
    Correct? pb /\ (
    let (Correct (l, _)) = pb in
    FStar.Mul.op_Star (L.length l) k.parser_kind_low == Seq.length b
  )))
  (decreases (Seq.length b))

let rec list_length_constant_size_parser_correct #k #t #err p u b =
  let n = k.parser_kind_low in
  if Seq.length b = 0
  then ()
  else begin
    let (Correct (_, consumed)) = parse p b in
    assert ((consumed <: nat) == n);
    assert (n > 0);
    let b' : bytes = Seq.slice b n (Seq.length b) in
    list_length_constant_size_parser_correct p u b';
    let (Correct (l', _)) = parse (parse_list p u) b' in
    FStar.Math.Lemmas.distributivity_add_left 1 (L.length l') n
  end
