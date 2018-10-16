module LowParse.SLow.Combinators
include LowParse.Low.Combinators
include LowParse.SLow.Base

module U32 = FStar.UInt32
module I32 = FStar.Int32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

inline_for_extraction
let parse32_ret
  (#t: Type)
  (x: t)
: Tot (LowParse.SLow.Base.parser32 (parse_ret x))
= (fun input len -> let _ = HST.get () in (x, 0l))
  
inline_for_extraction
let parse32_empty : parser32 parse_empty = parse32_ret ()

inline_for_extraction
let serialize32_empty : serializer32 #_ #_ #parse_empty serialize_empty
= fun b len lo v ->
  let h = HST.get () in
  contains_valid_serialized_data_or_fail_equiv h #parse_empty serialize_empty b lo v lo;
  lo

inline_for_extraction
let size32_empty : size32 #_ #_ #parse_empty serialize_empty
= size32_constant #_ #_ #parse_empty serialize_empty 0ul ()

inline_for_extraction
let parse32_and_then
  (#k: parser_kind)
  (#t:Type)
  (#p:parser k t)
  (p32: parser32 p)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
  (u: unit { and_then_cases_injective p' } )
  (p32' : ((x: t) -> Tot (parser32 (p' x))))
: Tot (parser32 (p `and_then` p'))
= fun input len ->
  match p32 input len with
  | (v, l) ->
    let len' = len `I32.sub` l in
    let input' = B.sub input (Cast.int32_to_uint32 l) (Cast.int32_to_uint32 len') in
    begin match p32' v input' len' with
    | (v', l') ->
      (v', I32.add l l')
    end

inline_for_extraction
let parse32_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (p1' : parser32 p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (p2' : parser32 p2)
: Tot (parser32 (nondep_then p1 p2))
= parse32_and_then
    p1'
    _
    ()
    (fun v1 -> parse32_and_then
      p2'
      _
      ()
      (fun v2 -> parse32_ret (v1, v2)))

inline_for_extraction
let serialize32_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (s1' : serializer32 s1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (#s2: serializer p2)
  (s2' : serializer32 s2)
  (u' : unit) // FIXME: remove this unit, comes from serialize32_kind_precond k1 k2; with the serializer now potentially failing, this precondition disappears
: Tot (serializer32 (serialize_nondep_then p1 s1 u p2 s2))
= fun output len lo input ->
  match input with
  | (fs, sn) ->
    let mi = s1' output len lo fs in
    s2' output len mi sn

inline_for_extraction
let parse32_strengthen
  (#k: parser_kind)
  (#t1: Type0)
  (#p1: parser k t1)
  (p1' : parser32 p1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Tot (parser32 (parse_strengthen p1 p2 prf))
= fun input len ->
  let h = HST.get () in
  match p1' input len with
  | (x, consumed) ->
    [@inline_let]
    let _ = prf (B.as_seq h input) (I32.v consumed) x in
    [@inline_let]
    let (x' : t1 { p2 x' } ) = x in
    (x', consumed)

inline_for_extraction
let parse32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (f2': (x: t1) -> Tot (y: t2 { y == f2 x } )) 
  (p1' : parser32 p1)
  (u: unit {
    synth_injective f2
  })
: Tot (parser32 (parse_synth p1 f2))
= fun input len ->
  match p1' input len with
  (v1, consumed) -> (f2' v1, consumed)

inline_for_extraction
let parse32_synth'
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> Tot t2)
  (p1' : parser32 p1)
  (u: unit {
    synth_injective f2
  })
: Tot (parser32 (parse_synth p1 f2))
= parse32_synth p1 f2 (fun x -> f2 x) p1' u

inline_for_extraction
let serialize32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (s1' : serializer32 s1)
  (g1: t2 -> GTot t1)
  (g1': (x: t2) -> Tot (y: t1 { y == g1 x } ) )
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
: Tot (serializer32 (serialize_synth p1 f2 s1 g1 u))
= fun output len lo input ->
    let x = g1' input in
    let hi = s1' output len lo x in
    let h = HST.get () in
    contains_valid_serialized_data_or_fail_synth s1 f2 g1 h output lo x hi;
    hi

inline_for_extraction
let serialize32_synth'
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (s1' : serializer32 s1)
  (g1: t2 -> Tot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
= serialize32_synth p1 f2 s1 s1' g1 (fun x -> g1 x) u

inline_for_extraction
let parse32_filter
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (f: (t -> GTot bool))
  (g: ((x: t) -> Tot (b: bool { b == f x } ))) // TODO: this is useless, since we already know that the input buffer succeeds
: Tot (parser32 (parse_filter p f))
= fun input len ->
  match p32 input len with
  (v, consumed) ->
  ((v <: (v' : t { f v' == true })), consumed)

inline_for_extraction
let serialize32_filter
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (f: (t -> GTot bool))
: Tot (serializer32 #_ #_ #(parse_filter p f) (serialize_filter s f))
= fun output len lo (input: t { f input == true } ) ->
  let hi = s32 output len lo input in
  let h = HST.get () in
  contains_valid_serialized_data_or_fail_equiv h s output lo input hi;
  contains_valid_serialized_data_or_fail_equiv h (serialize_filter s f) output lo input hi;
  hi

inline_for_extraction
let parser32_of_constant_low_parser32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: LowParse.Low.Base.parser32 p)
  (sz: I32.t)
  (u: squash (k.parser_kind_high == Some k.parser_kind_low /\ k.parser_kind_low == I32.v sz))
: Tot (parser32 p)
= fun input len ->
  let x = p32 input in
  (x, sz)
  
inline_for_extraction
let size32_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (s1' : size32 s1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (#s2: serializer p2)
  (s2' : size32 s2)
: Tot (size32 (serialize_nondep_then _ s1 u _ s2))
= fun x ->
  match x with
  | (x1, x2) ->
    let v1 = s1' x1 in
    let v2 = s2' x2 in
    let res = add_overflow v1 v2 in
    (res <: (z : U32.t { size32_postcond (serialize_nondep_then _ s1 u _ s2) x z } ))

inline_for_extraction
let size32_filter
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s)
  (f: (t -> GTot bool))
: Tot (size32 #_ #_ #(parse_filter p f) (serialize_filter s f))
= fun x -> s32 x

inline_for_extraction
let size32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (s1' : size32 s1)
  (g1: t2 -> GTot t1)
  (g1': (x: t2) -> Tot (y: t1 { y == g1 x } ) )
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
: Tot (size32 (serialize_synth p1 f2 s1 g1 u))
= fun (input: t2) ->
    let x = g1' input in
    let y = s1' x in
    (y <: (res: U32.t { size32_postcond (serialize_synth p1 f2 s1 g1 u) input res } ))

inline_for_extraction
let size32_synth'
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (s1' : size32 s1)
  (g1: t2 -> Tot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
: Tot (size32 (serialize_synth p1 f2 s1 g1 u))
= size32_synth p1 f2 s1 s1' g1 (fun x -> g1 x) u
