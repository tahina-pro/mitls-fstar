module LowParse.Impl.Sum
include LowParse.Impl.Enum
include LowParse.Spec.Sum

module S = LowParse.Slice
module T = FStar.Tactics

let lift_cases
  (#key #repr: eqtype)
  (e: enum key repr)
  (cases: (enum_key e -> Tot Type0))
  (k: maybe_enum_key e)
: Tot Type0
= match k with
  | Known k' -> cases k'
  | _ -> False

let lift_parser_cases
  (#pk: parser_kind)
  (#key #repr: eqtype)
  (e: enum key repr)
  (cases: (enum_key e -> Tot Type0))
  (pc: ((x: enum_key e) -> Tot (parser pk (cases x))))
  (k: maybe_enum_key e)
: Tot (parser (parse_filter_kind pk) (lift_cases e cases k))
= match k with
  | Known k' -> weaken (parse_filter_kind pk) (pc k')
  | _ -> fail_parser (parse_filter_kind pk) (lift_cases e cases k)

let parse_sum_synth
  (t: sum)
  (v: sum_repr_type t)
  (v' : lift_cases (sum_enum t) (sum_cases t) (maybe_enum_key_of_repr (sum_enum t) v))
: Tot (sum_type t)
= match maybe_enum_key_of_repr (sum_enum t) v with
  | Known k -> (| k, v' |)
  | _ -> false_elim ()

let parse_sum_payload
  (#k: parser_kind)
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (v: sum_repr_type t)
: Tot (parser (parse_filter_kind k) (sum_type t))
= parse_synth
    #(parse_filter_kind k)
    #(lift_cases (sum_enum t) (sum_cases t) (maybe_enum_key_of_repr (sum_enum t) v))
    #(sum_type t)
    (lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_enum_key_of_repr (sum_enum t) v))
    (parse_sum_synth t v)

#set-options "--z3rlimit 16"

let parse_sum_payload_and_then_cases_injective
  (#k: parser_kind)
  (t: sum)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
: unit ->
  Lemma
  (and_then_cases_injective (parse_sum_payload t pc))
= fun _ -> ()

#reset-options

let parse_sum'
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
: Tot (parser (and_then_kind kt (parse_filter_kind k)) (sum_type t))
= parse_sum_payload_and_then_cases_injective t pc ();
  p `and_then` (parse_sum_payload t pc)

#set-options "--z3rlimit 256"

let parse_sum'_correct
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
: Lemma
  (forall (input: bytes) . parse (parse_sum' t p pc) input == parse (parse_sum t p pc) input)
= ()

#reset-options

inline_for_extraction
val gen_validate_sum_partial'
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (ps: parser_st p)
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (vs' : ((x: sum_repr_type t) -> Tot (stateful_validator (lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_enum_key_of_repr (sum_enum t) x)))))
: Tot (stateful_validator (parse_sum' t p pc))

#set-options "--z3rlimit 16"

let gen_validate_sum_partial' #kt t p ps #k pc vs' =
  let g' (v: sum_repr_type t) : Tot (stateful_validator (parse_sum_payload t pc v)) =
    validate_synth
      #(parse_filter_kind k)
      #(lift_cases (sum_enum t) (sum_cases t) (maybe_enum_key_of_repr (sum_enum t) v))
      #(sum_type t)
      #(lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_enum_key_of_repr (sum_enum t) v))
      (vs' v)
      (parse_sum_synth t v)
  in
  parse_then_check'
    #kt
    #(sum_repr_type t)
    #p
    ps
    #(parse_filter_kind k)
    #(sum_type t)
    #(parse_sum_payload t pc)
    (parse_sum_payload_and_then_cases_injective t pc)
    g'

#reset-options

inline_for_extraction
val gen_validate_sum_partial
  (#kt: parser_kind)
  (t: sum)
  (p: parser kt (sum_repr_type t))
  (ps: parser_st p)
  (#k: parser_kind)
  (pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (vs' : ((x: sum_repr_type t) -> Tot (stateful_validator (lift_parser_cases (sum_enum t) (sum_cases t) pc (maybe_enum_key_of_repr (sum_enum t) x)))))
: Tot (stateful_validator (parse_sum t p pc))

let gen_validate_sum_partial #kt t p ps #k pc vs' =
  fun (input: S.bslice) ->
  parse_sum'_correct #kt t p #k pc;
  gen_validate_sum_partial' t p ps pc vs' input

inline_for_extraction
let lift_validator_cases
  (#key #repr: eqtype)
  (e: enum key repr)
  (cases: (enum_key e -> Tot Type0))
  (#pk: parser_kind)
  (pc: ((x: enum_key e) -> Tot (parser pk (cases x))))
  (vs: ((x: enum_key e) -> Tot (stateful_validator (pc x))))
  (k: maybe_enum_key e)
: Tot (stateful_validator (lift_parser_cases e cases pc k))
= match k with
  | Known k' -> vs k'
  | _ -> validate_fail (parse_filter_kind pk) False

inline_for_extraction
let validate_sum_cases_type
  (s: sum)
  (#pk: parser_kind)
  (pc: ((x: sum_key s) -> Tot (parser pk (sum_cases s x))))
  (k: maybe_enum_key (sum_enum s))
: Tot Type0
= stateful_validator (lift_parser_cases (sum_enum s) (sum_cases s) pc k)

inline_for_extraction
val validate_sum
  (s: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type s))
  (ps: parser_st p)
  (#k: parser_kind)
  (pc: ((x: sum_key s) -> Tot (parser k (sum_cases s x))))
  (destr: (
    (f: ((k: maybe_enum_key (sum_enum s)) -> Tot (validate_sum_cases_type s pc k))) ->
    (combine_if: ((k: maybe_enum_key (sum_enum s)) -> Tot (if_combinator (validate_sum_cases_type s pc k)))) ->
    (k: sum_repr_type s) ->
    Tot (validate_sum_cases_type s pc (maybe_enum_key_of_repr (sum_enum s) k))
  ))
  (vs : ((x: sum_key s) -> Tot (stateful_validator (pc x))))
: Tot (stateful_validator (parse_sum s p pc))

let validate_sum s #kt #p ps #k pc destr vs =
  gen_validate_sum_partial
    s
    p
    ps
    pc
    (destr
      (lift_validator_cases (sum_enum s) (sum_cases s) pc vs)
      (fun k -> validate_if (lift_parser_cases (sum_enum s) (sum_cases s) pc k))
    )

(* With a default case *)

let parse_dsum_synth
  (t: dsum)
  (v: sum_repr_type (fst t))
  (v' : dsum_cases t (maybe_enum_key_of_repr (sum_enum (fst t)) v))
: Tot (dsum_type t)
= (| maybe_enum_key_of_repr (sum_enum (fst t)) v, v' |)

let parse_dsum_payload
  (#k: parser_kind)
  (t: dsum)
  (pc: ((x: sum_key (fst t)) -> Tot (parser k (sum_cases (fst t) x))))
  (pd: parser k (snd t))
  (v: sum_repr_type (fst t))
: Tot (parser k (dsum_type t))
= parse_synth
    #k
    #(dsum_cases t (maybe_enum_key_of_repr (sum_enum (fst t)) v))
    #(dsum_type t)
    (parse_dsum_cases t pc pd (maybe_enum_key_of_repr (sum_enum (fst t)) v))
    (parse_dsum_synth t v)

#set-options "--z3rlimit 16"

let parse_dsum_payload_and_then_cases_injective
  (#k: parser_kind)
  (t: dsum)
  (pc: ((x: sum_key (fst t)) -> Tot (parser k (sum_cases (fst t) x))))
  (pd: parser k (snd t))
: unit ->
  Lemma
  (and_then_cases_injective (parse_dsum_payload t pc pd))
= fun _ -> ()

#reset-options

let parse_dsum'
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (sum_repr_type (fst t)))
  (#k: parser_kind)
  (pc: ((x: sum_key (fst t)) -> Tot (parser k (sum_cases (fst t) x))))
  (pd: parser k (snd t))
: Tot (parser (and_then_kind kt k) (dsum_type t))
= parse_dsum_payload_and_then_cases_injective t pc pd ();
  p `and_then` (parse_dsum_payload t pc pd)

#set-options "--z3rlimit 256"

let parse_dsum'_correct
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (sum_repr_type (fst t)))
  (#k: parser_kind)
  (pc: ((x: sum_key (fst t)) -> Tot (parser k (sum_cases (fst t) x))))
  (pd: parser k (snd t))
: Lemma
  (forall (input: bytes) . parse (parse_dsum' t p pc pd) input == parse (parse_dsum t p pc pd) input)
= ()

#reset-options

inline_for_extraction
val gen_validate_dsum_partial'
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (sum_repr_type (fst t)))
  (ps: parser_st p)
  (#k: parser_kind)
  (pc: ((x: sum_key (fst t)) -> Tot (parser k (sum_cases (fst t) x))))
  (pd: parser k (snd t))
  (vs' : ((x: sum_repr_type (fst t)) -> Tot (stateful_validator (parse_dsum_cases t pc pd (maybe_enum_key_of_repr (sum_enum (fst t)) x)))))
: Tot (stateful_validator (parse_dsum' t p pc pd))

#set-options "--z3rlimit 16"

let gen_validate_dsum_partial' #kt t p ps #k pc pd vs' =
  let g' (v: sum_repr_type (fst t)) : Tot (stateful_validator (parse_dsum_payload t pc pd v)) =
    validate_synth
      #k
      #(dsum_cases t (maybe_enum_key_of_repr (sum_enum (fst t)) v))
      #(dsum_type t)
      #(parse_dsum_cases t pc pd (maybe_enum_key_of_repr (sum_enum (fst t)) v))
      (vs' v)
      (parse_dsum_synth t v)
  in
  parse_then_check'
    #kt
    #(sum_repr_type (fst t))
    #p
    ps
    #k
    #(dsum_type t)
    #(parse_dsum_payload t pc pd)
    (parse_dsum_payload_and_then_cases_injective t pc pd)
    g'

#reset-options

inline_for_extraction
val gen_validate_dsum_partial
  (#kt: parser_kind)
  (t: dsum)
  (p: parser kt (sum_repr_type (fst t)))
  (ps: parser_st p)
  (#k: parser_kind)
  (pc: ((x: sum_key (fst t)) -> Tot (parser k (sum_cases (fst t) x))))
  (pd: parser k (snd t))
  (vs' : ((x: sum_repr_type (fst t)) -> Tot (stateful_validator (parse_dsum_cases t pc pd (maybe_enum_key_of_repr (sum_enum (fst t)) x)))))
: Tot (stateful_validator (parse_dsum t p pc pd))

let gen_validate_dsum_partial #kt t p ps #k pc pd vs' =
  fun (input: S.bslice) ->
  parse_dsum'_correct #kt t p #k pc pd;
  gen_validate_dsum_partial' t p ps pc pd vs' input

inline_for_extraction
let validate_dsum_cases_type
  (s: dsum)
  (#pk: parser_kind)
  (pc: ((x: sum_key (fst s)) -> Tot (parser pk (sum_cases (fst s) x))))
  (pd: parser pk (snd s))
  (k: maybe_enum_key (sum_enum (fst s)))
: Tot Type0
= stateful_validator (parse_dsum_cases s pc pd k)

inline_for_extraction
let lift_validator_dcases
  (s: dsum)
  (#pk: parser_kind)
  (pc: ((x: sum_key (fst s)) -> Tot (parser pk (sum_cases (fst s) x))))
  (pd: parser pk (snd s))
  (vs: ((x: sum_key (fst s)) -> Tot (stateful_validator (pc x))))
  (vd: stateful_validator pd)
  (k: dsum_key s)
: Tot (stateful_validator (parse_dsum_cases s pc pd k))
= match k with
  | Known k' -> vs k'
  | _ -> vd

inline_for_extraction
val validate_dsum
  (s: dsum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type (fst s)))
  (ps: parser_st p)
  (#k: parser_kind)
  (pc: ((x: sum_key (fst s)) -> Tot (parser k (sum_cases (fst s) x))))
  (pd: parser k (snd s))
  (destr: (
    (f: ((k: maybe_enum_key (sum_enum (fst s))) -> Tot (validate_dsum_cases_type s pc pd k))) ->
    (combine_if: ((k: maybe_enum_key (sum_enum (fst s))) -> Tot (if_combinator (validate_dsum_cases_type s pc pd k)))) ->
    (k: sum_repr_type (fst s)) ->
    Tot (validate_dsum_cases_type s pc pd (maybe_enum_key_of_repr (sum_enum (fst s)) k))
  ))
  (vs : ((x: sum_key (fst s)) -> Tot (stateful_validator (pc x))))
  (vd : stateful_validator pd)
: Tot (stateful_validator (parse_dsum s p pc pd))

let validate_dsum s #kt #p ps #k pc pd destr vs vd =
  gen_validate_dsum_partial
    s
    p
    ps
    pc
    pd
    (destr
      (lift_validator_dcases s pc pd vs vd)
      (fun k -> validate_if (parse_dsum_cases s pc pd k))
    )


(*

inline_for_extraction
let validate_sum_cases
  (s: sum)
  (univ_destr_gen: (
    (t: ((k: maybe_unknown_key (sum_enum s)) -> Tot Type0)) ->
    (f: ((k: maybe_unknown_key (sum_enum s)) -> Tot (t k))) ->
    (combine_if: ((k: maybe_unknown_key (sum_enum s)) -> Tot (if_combinator (t k)))) ->
    (k: sum_repr_type s) ->
    Tot (t (maybe_unknown_key_of_repr (sum_enum s) k))
  ))
  (#k: parser_kind)
  (pc: ((x: sum_key s) -> Tot (parser k (sum_cases s x))))
  (vs : ((x: sum_key s) -> Tot (stateful_validator (pc x))))
: (r: sum_repr_type s) ->
  Tot (stateful_validator (lift_parser_cases (sum_enum s) (sum_cases s) pc (maybe_unknown_key_of_repr (sum_enum s) r)))
= let t (k: maybe_unknown_key (sum_enum s)) : Tot Type0 =
    stateful_validator (lift_parser_cases (sum_enum s) (sum_cases s) pc k)
  in
  univ_destr_gen
    t
    (lift_validator_cases (sum_enum s) (sum_cases s) pc vs)
    (fun k -> validate_if (lift_parser_cases (sum_enum s) (sum_cases s) pc k))
