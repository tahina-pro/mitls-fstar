(* Parse data of some explicitly fixed length *)

module LowParse.Spec.FLData
include LowParse.Spec.Combinators

module Seq = FStar.Seq
module Classical = FStar.Classical

inline_for_extraction
val parse_fldata'
  (#t: Type0)
  (#err: Type0)
  (p: bare_parser t err)
  (sz: nat)
  (e: err)
: Tot (bare_parser t err)

let parse_fldata' #t #err p sz e =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes) ->
  if Seq.length s < sz
  then Error e
  else
    match p (Seq.slice s 0 sz) with
    | Correct (v, consumed) ->
      if (consumed <: nat) = (sz <: nat)
      then Correct (v, (sz <: consumed_length s))
      else Error e
    | Error e' -> Error e'

let parse_fldata_injective
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (sz: nat)
  (e: err)
: Lemma
  (ensures (injective (parse_fldata' p sz e)))
= let f
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond (parse_fldata' p sz e) b1 b2))
    (ensures (injective_postcond (parse_fldata' p sz e) b1 b2))
  = assert (injective_precond p (Seq.slice b1 0 sz) (Seq.slice b2 0 sz))
  in
  Classical.forall_intro_2 (fun b -> Classical.move_requires (f b))

// unfold
inline_for_extraction
let parse_fldata_kind
  (sz: nat)
: Tot parser_kind
= strong_parser_kind sz sz ({
    parser_kind_metadata_total = false;
  })

inline_for_extraction
val parse_fldata
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (sz: nat)
  (e: err)
: Tot (parser (parse_fldata_kind sz) t err)

let parse_fldata #b #t #err p sz e =
  parse_fldata_injective p sz e;
  parse_fldata' p sz e

val parse_fldata_consumes_all
  (#t: Type0)
  (#err: Type0)
  (p: bare_parser t err)
  (sz: nat)
  (e: err)
: Pure (bare_parser t err)
  (requires (consumes_all p))
  (ensures (fun _ -> True))

let parse_fldata_consumes_all #t #err p sz e =
  let () = () in // Necessary to pass arity checking
  fun (s: bytes) ->
  if Seq.length s < sz
  then Error e
  else
    match p (Seq.slice s 0 sz) with
    | Correct (v, _) ->
      Correct (v, (sz <: consumed_length s))
    | Error e' -> Error e'

let parse_fldata_consumes_all_correct
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (sz: nat)
  (e: err)
: Lemma
  (requires (k.parser_kind_subkind == Some ParserConsumesAll))
  (ensures (forall b . parse (parse_fldata p sz e) b == parse (parse_fldata_consumes_all p sz e) b))
= ()

let parse_fldata_strong_pred
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (sz: nat)
  (x: t)
: GTot Type0
= Seq.length (serialize s x) == sz

let parse_fldata_strong_t
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (sz: nat)
: Tot Type0
= (x: t { parse_fldata_strong_pred s sz x } )

let parse_fldata_strong_correct
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (sz: nat)
  (e: err)
  (xbytes: bytes)
  (consumed: consumed_length xbytes)
  (x: t)
: Lemma
  (requires (parse (parse_fldata p sz e) xbytes == Correct (x, consumed)))
  (ensures (parse_fldata_strong_pred s sz x))
= serializer_correct_implies_complete p s

inline_for_extraction
let parse_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (sz: nat)
  (e: err)
: Tot (parser (parse_fldata_kind sz) (parse_fldata_strong_t s sz) err)
= coerce_parser
  (parse_fldata_strong_t s sz)
  (parse_strengthen (parse_fldata p sz e) (parse_fldata_strong_pred s sz) (parse_fldata_strong_correct s sz e))

#set-options "--z3rlimit 16"

let serialize_fldata_strong'
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (sz: nat)
: Tot (bare_serializer (parse_fldata_strong_t s sz))
= (fun (x: parse_fldata_strong_t s sz) ->
  s x)

let serialize_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (sz: nat)
  (e: err)
: Tot (serializer (parse_fldata_strong s sz e))
= serialize_fldata_strong' s sz
