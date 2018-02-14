(* Parse data of some explicitly fixed length *)

module LowParse.Spec.FLData
include LowParse.Spec.Combinators

module Seq = FStar.Seq
module Classical = FStar.Classical

inline_for_extraction
val parse_fldata'
  (#t: Type0)
  (p: bare_parser t)
  (sz: nat)
: Tot (bare_parser t)

let parse_fldata' #t p sz =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes) ->
  if Seq.length s < sz
  then None
  else
    match p (Seq.slice s 0 sz) with
    | Some (v, consumed) ->
      if (consumed <: nat) = (sz <: nat)
      then Some (v, (sz <: consumed_length s))
      else None
    | _ -> None

let parse_fldata_injective
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
: Lemma
  (ensures (injective (parse_fldata' p sz)))
= let f
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond (parse_fldata' p sz) b1 b2))
    (ensures (injective_postcond (parse_fldata' p sz) b1 b2))
  = assert (injective_precond p (Seq.slice b1 0 sz) (Seq.slice b2 0 sz))
  in
  Classical.forall_intro_2 (fun b -> Classical.move_requires (f b))

// unfold
let parse_fldata_kind
  (sz: nat)
: Tot parser_kind
= {
    parser_kind_low = sz;
    parser_kind_high = Some sz;
    parser_kind_total = false;
    parser_kind_subkind = Some ParserStrong
  }

inline_for_extraction
val parse_fldata
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
: Tot (parser (parse_fldata_kind sz) t)

let parse_fldata #b #t p sz =
  parse_fldata_injective p sz;
  parse_fldata' p sz  

#set-options "--z3rlimit 16"

let parse_fldata_intro_none_parse
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat )
  (input: bytes)
: Lemma
  (requires (
    sz <= Seq.length input ==> (
    let (cl : nat { 0 <= cl && cl <= Seq.length input } ) = sz in
    None? (parse p (Seq.slice input 0 (cl)))
  )))
  (ensures (parse (parse_fldata p sz) input == None))
= ()

#set-options "--z3rlimit 32 --max_fuel 16"

let parse_fldata_intro_none_fldata
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat )
  (input: bytes)
  (d: t)
  (consumed: nat)
: Lemma
  (requires (
    sz <= Seq.length input /\
    consumed <= sz /\ (
    let (cl : nat { 0 <= cl && cl <= Seq.length input } ) = sz in
    parse p (Seq.slice input 0 (cl)) == Some (d, consumed) /\
    (consumed <: nat) <> (sz <: nat)
  )))
  (ensures (parse (parse_fldata p sz) input == None))
= ()

let parse_fldata_intro_some
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat )
  (input: bytes)
  (d: t)
: Lemma
  (requires (
    sz <= Seq.length input /\ (
    let (cl : nat { 0 <= cl && cl <= Seq.length input } ) = sz in
    parse p (Seq.slice input 0 (cl)) == Some (d, sz)
  )))
  (ensures (parse (parse_fldata p sz) input == Some (d, sz)))
= ()

val parse_fldata_consumes_all
  (#t: Type0)
  (p: bare_parser t)
  (sz: nat)
: Pure (bare_parser t)
  (requires (consumes_all p))
  (ensures (fun _ -> True))

let parse_fldata_consumes_all #t p sz =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes) ->
  if Seq.length s < sz
  then None
  else
    match p (Seq.slice s 0 sz) with
    | Some (v, _) ->
      Some (v, (sz <: consumed_length s))
    | _ -> None

let parse_fldata_consumes_all_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
: Lemma
  (requires (k.parser_kind_subkind == Some ParserConsumesAll))
  (ensures (forall b . parse (parse_fldata p sz) b == parse (parse_fldata_consumes_all p sz) b))
= ()

let parse_fldata_intro_some_consumes_all
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
  (input: bytes)
  (d: t)
  (consumed: nat)
: Lemma
  (requires (
    sz <= Seq.length input /\
    k.parser_kind_subkind == Some ParserConsumesAll /\
    consumed <= sz /\
    parse p input == Some (d, consumed)
  ))
  (ensures (
    parse (parse_fldata p sz) input == Some (d, sz) /\
    consumed == sz
  ))
= parse_fldata_consumes_all_correct p sz

let parse_fldata_strong_pred
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (x: t)
: GTot Type0
= Seq.length (serialize s x) == sz

let parse_fldata_strong_t
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
: Tot Type0
= (x: t { parse_fldata_strong_pred s sz x } )

let parse_fldata_strong_correct
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (xbytes: bytes)
  (consumed: consumed_length xbytes)
  (x: t)
: Lemma
  (requires (parse (parse_fldata p sz) xbytes == Some (x, consumed)))
  (ensures (parse_fldata_strong_pred s sz x))
= serializer_correct_implies_complete p s

inline_for_extraction
let parse_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
: Tot (parser (parse_fldata_kind sz) (parse_fldata_strong_t s sz))
= coerce_parser
  (parse_fldata_strong_t s sz)
  (parse_strengthen (parse_fldata p sz) (parse_fldata_strong_pred s sz) (parse_fldata_strong_correct s sz))

let parse_fldata_strong_intro_some
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (input: bytes)
  (d: t)
  (consumed: nat)
: Lemma
  (requires (
    consumed <= Seq.length input /\
    parse (parse_fldata p sz) input == Some (d, consumed)
  ))
  (ensures (
    parse_fldata_strong_pred s sz d /\
    parse (parse_fldata_strong s sz) input == Some (d, consumed)
  ))
= parse_fldata_strong_correct s sz input consumed d

let parse_fldata_strong_intro_none
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (input: bytes)
: Lemma
  (requires (
    None? (parse (parse_fldata p sz) input)
  ))
  (ensures (
    parse (parse_fldata_strong s sz) input == None
  ))
= ()

#set-options "--z3rlimit 16"

let serialize_fldata_strong'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
: Tot (bare_serializer (parse_fldata_strong_t s sz))
= (fun (x: parse_fldata_strong_t s sz) ->
  s x)

let serialize_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
: Tot (serializer (parse_fldata_strong s sz))
= serialize_fldata_strong' s sz
