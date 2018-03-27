module LowParse.Impl.Base
include LowParse.Spec.Base

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module S = LowParse.Slice
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

[@"substitute"]
inline_for_extraction
let consumed_slice_length (input: S.bslice) : Tot Type0 =
  (off:U32.t{U32.v off <= U32.v (S.length input)})

/// A stateful parser that implements the same behavior as a pure parser. This
/// includes both the output and offset. The specification parser is an erased
/// type index; erasure helps guide extraction. The type is inlined for
/// extraction to make it clear that parsers are first-order functions taking a
/// buffer as input (as opposed to higher-order implementations that return a
/// function).
inline_for_extraction
let parser_st #t (p: bare_parser t) : Tot Type0 =
  input:S.bslice -> HST.Stack (option (t * consumed_slice_length input))
  (requires (fun h0 -> S.live h0 input))
  (ensures (fun h0 r h1 -> S.live h1 input /\
            S.modifies_none h0 h1 /\
            (let bs = S.as_seq h1 input in
            match p bs with
            | Some (v, n) -> Some? r /\
              begin
                let (rv, off) = Some?.v r in
                  v == rv /\ n == U32.v off
              end
            | None -> r == None)))

/// A stateful parser much like parser_st, except that error cases are
/// precluded. The precondition includes that the specification parser succeeds
/// on the input, and under this assumption a parser_st_nochk does not fail and
/// has the same behavior as the specification parser. The implementation need
/// not make error checks since those cases are impossible.
inline_for_extraction
let parser_st_nochk #t (p: bare_parser t) : Tot Type0 =
  input: S.bslice -> HST.Stack (t * consumed_slice_length input)
  (requires (fun h0 -> S.live h0 input /\
                    (let bs = S.as_seq h0 input in
                     Some? (parse p bs))))
  (ensures (fun h0 r h1 -> S.live h1 input /\
                  S.modifies_none h0 h1 /\
                  (let bs = S.as_seq h1 input in
                    Some? (parse p bs) /\
                    (let (v, n) = Some?.v (parse p bs) in
                     let (rv, off) = r in
                       v == rv /\
                       n == U32.v off))))

(** Slices that exactly correspond to some parsed data *)

unfold
let parses
  (#t: Type0)
  (h: HS.mem)
  (p: bare_parser t)
  (s: S.bslice)
  (k: ((t * consumed_slice_length s) -> GTot Type0))
: GTot Type0
= S.live h s /\ (
  let sq : bytes = S.as_seq h s in
  let y = parse p sq in (
  Some? y /\ (
  let (Some (v', l)) = y in
  k (v', U32.uint_to_t l)
  )))

unfold
let exactly_parses
  (#t: Type0)
  (h: HS.mem)
  (p: bare_parser t)
  (s: S.bslice)
  (k: (t -> GTot Type0))
: GTot Type0
= parses h p s (fun (v, len) -> S.length s == len /\ k v)

let parses_consumes_all_exactly_parses
  (#t: Type0)
  (h: HS.mem)
  (p: bare_parser t)
  (s: S.bslice)
  (k: ((t * consumed_slice_length s) -> GTot Type0))
: Lemma
  (requires (parses h p s k /\ consumes_all p))
  (ensures (exactly_parses h p s (fun v -> k (v, S.length s))))
= ()


/// A validation is an [option U32.t], where [Some off] indicates success and
/// consumes [off] bytes. A validation checks a parse result if it returns [Some
/// off] only when the parser also succeeds and returns the same offset, with
/// any result. Note that a validation need not be complete (in particular,
/// [None] validates any parse).


/// A stateful validator is parametrized by a specification parser. A validator
/// does not produce a value but only checks that the data is valid. The
/// specification ensures that when a validator accepts the input the parser
/// would succeed on the same input.
inline_for_extraction
let stateful_validator (#t: Type0) (p: bare_parser t) : Tot Type0 =
  input: S.bslice ->
  HST.Stack (option (consumed_slice_length input))
    (requires (fun h0 -> S.live h0 input))
    (ensures (fun h0 r h1 -> S.modifies_none h0 h1 /\ (
      Some? r ==> (
      let (Some len) = r in
      parses h0 p input (fun (_, len') -> len == len')
    ))))


/// Same thing, but where we already know that the data is valid. (In other words, how many offsets are skipped by the data being parsed.)
inline_for_extraction
let stateful_validator_nochk (#t: Type0) (p: bare_parser t) : Tot Type0 =
  input: S.bslice ->
  HST.Stack (consumed_slice_length input)
  (requires (fun h0 ->
    parses h0 p input (fun _ -> True)
  ))
  (ensures (fun h0 r h1 ->
    S.modifies_none h0 h1 /\
    parses h0 p input (fun (_, len) ->
      len == r
  )))
