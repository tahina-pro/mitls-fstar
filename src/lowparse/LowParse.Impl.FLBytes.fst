module LowParse.Impl.FLBytes
include LowParse.Impl.Combinators
include LowParse.Spec.FLBytes

module U32 = FStar.UInt32
module S = LowParse.Slice

inline_for_extraction
let validate_flbytes_gen
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (ps: stateful_validator p)
  (len: U32.t)
: Tot (stateful_validator (parse_flbytes p (U32.v len)))
= fun (input: S.bslice) ->
  let blen = S.length input in
  if U32.lt blen len
  then begin
    None
  end else begin
    let input'  = S.truncate_slice input len in
    match ps input' with
    | Some consumed ->
      if consumed = len
      then Some (let x : U32.t = consumed in (x <: consumed_slice_length input))
      else None
    | _ -> None
  end

inline_for_extraction
let validate_flbytes_consumes_all
  (#t: Type0)
  (#p: parser ParserConsumesAll t)
  (ps: stateful_validator p)
  (len: U32.t)
: Tot (stateful_validator (parse_flbytes p (U32.v len)))
= fun (input: S.bslice) ->
  let blen = S.length input in
  if U32.lt blen len
  then begin
    None
  end else begin
    let input'  = S.truncate_slice input len in
    match ps input' with
    | Some _ -> Some (len <: consumed_slice_length input)
    | _ -> None
  end

inline_for_extraction
let validate_flbytes
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (ps: stateful_validator p)
  (len: U32.t)
: Tot (stateful_validator (parse_flbytes p (U32.v len)))
= match k with
  | ParserConsumesAll -> validate_flbytes_consumes_all #t #p ps len
  | _ -> validate_flbytes_gen ps len

inline_for_extraction
let validate_flbytes_nochk
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (len: U32.t)
: Tot (stateful_validator_nochk (parse_flbytes p (U32.v len)))
= validate_constant_size_nochk len (parse_flbytes p (U32.v len))

module HS = FStar.HyperStack

inline_for_extraction
let serialize_flbytes_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: S.bslice)
  (len: nat)
  (h: HS.mem)
: Lemma
  (requires (
    exactly_parses h p b (fun _ -> True) /\
    len == U32.v (S.length b)
  ))
  (ensures (
    exactly_parses h p b (fun v ->
    exactly_parses h (parse_flbytes p len) b (fun v' ->
    v == v'
  ))))
= ()
