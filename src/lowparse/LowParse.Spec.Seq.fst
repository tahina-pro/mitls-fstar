module LowParse.Spec.Seq
include LowParse.Spec.Combinators

module Seq = FStar.Seq
module L = FStar.List.Tot
module PL = LowParse.Spec.List
module U32 = FStar.UInt32
module Classical = FStar.Classical

(* Parse a list, until there is nothing left to read. This parser will mostly fail EXCEPT if the whole size is known and the slice has been suitably truncated beforehand, or if the elements of the list all have a known constant size. *)

val parse_seq_aux
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
  (b: bytes)
: GTot (result (Seq.seq t * (consumed_length b)) err)
  (decreases (Seq.length b))

let rec parse_seq_aux #k #t #err p u b =
  if Seq.length b = 0
  then 
    Correct (Seq.createEmpty, (0 <: consumed_length b))
  else
    match p b with
    | Error e -> Error e
    | Correct (v, n) ->
      begin
        match parse_seq_aux p u (Seq.slice b n (Seq.length b)) with
	| Correct (l, n') -> Correct (Seq.cons v l, (n + n' <: consumed_length b))
	| Error e -> Error e
      end

let seq_of_list_inj
  (t: Type0)
: Lemma
  (forall (l1 l2 : list t) . Seq.seq_of_list l1 == Seq.seq_of_list l2 ==> l1 == l2)
= Classical.forall_intro (Seq.lemma_list_seq_bij #t)

let parse_seq'
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
: Tot (parser PL.parse_list_kind (Seq.seq t) err)
= seq_of_list_inj t;
  parse_synth (PL.parse_list p u) (Seq.seq_of_list)

val parse_seq_aux_correct
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
  (b: bytes)
: Lemma
  (ensures (
    parse (parse_seq_aux p u) b == parse (parse_seq' p u) b
  ))
  (decreases (Seq.length b))

#set-options "--z3rlimit 32"

let rec parse_seq_aux_correct #k #t #err p u b =
  if Seq.length b = 0
  then ()
  else
    match parse p b with
    | Correct (v, n) ->
	let b' = Seq.slice b n (Seq.length b) in
	parse_seq_aux_correct p u b'
    | _ -> ()

#reset-options

let parse_seq
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
: Tot (parser PL.parse_list_kind (Seq.seq t) err)
= Classical.forall_intro (parse_seq_aux_correct p u);
  no_lookahead_weak_ext (parse_seq' p u) (parse_seq_aux p u);
  injective_ext (parse_seq' p u) (parse_seq_aux p u);
  no_lookahead_ext (parse_seq' p u) (parse_seq_aux p u);
  parse_seq_aux p u

let parse_seq_correct
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
  (b: bytes)
: Lemma
  (parse (parse_seq p u) b == parse (parse_seq' p u) b)
= parse_seq_aux_correct p u b

val seq_length_constant_size_parser_correct
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (u: unit { k.parser_kind_low > 0 } )
  (b: bytes)
: Lemma
  (requires (
    k.parser_kind_high == Some k.parser_kind_low /\
    Correct? (parse (parse_seq p u) b)
  ))
  (ensures (
    let pb = parse (parse_seq p u) b in
    Correct? pb /\ (
    let (Correct (l, _)) = pb in
    FStar.Mul.op_Star (Seq.length l) k.parser_kind_low == Seq.length b
  )))

let seq_length_constant_size_parser_correct #k #t #err p u b =
  parse_seq_correct p u b;
  PL.list_length_constant_size_parser_correct p u b

let serialize_seq'
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (u: unit { k.parser_kind_low > 0 } )
: Pure (serializer (parse_seq' p u))
  (requires (PL.serialize_list_precond k))
  (ensures (fun _ -> True))
= Classical.forall_intro (Seq.lemma_seq_list_bij #t);
  Classical.forall_intro (Seq.lemma_list_seq_bij #t);
  serialize_synth (PL.parse_list p u) Seq.seq_of_list (PL.serialize_list s u) Seq.seq_to_list ()

let serialize_seq
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (u: unit { k.parser_kind_low > 0 } )
: Pure (serializer (parse_seq p u))
  (requires (PL.serialize_list_precond k))
  (ensures (fun _ -> True))
= Classical.forall_intro (parse_seq_correct p u);
  serialize_ext (parse_seq' p u) (serialize_seq' s u) (parse_seq p u)

