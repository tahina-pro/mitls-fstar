module LowParse.SLow.Base
include LowParse.Low.Base

module B = LowStar.Buffer
module M = LowStar.ModifiesPat
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32
module Cast = FStar.Int.Cast
module MA = LowParse.Math
module G = FStar.Ghost

[@unifier_hint_injective]
inline_for_extraction
let parser32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: buffer8) ->
  (len: I32.t) ->
  HST.Stack (t * I32.t) // NOTE: here we are using I32 because sometimes we need to call validators (see Option).
  (requires (fun h ->
    B.live h input /\
    B.length input == I32.v len /\
    Some? (parse p (B.as_seq h input))
  ))
  (ensures (fun h (res, consumed) h' ->
    M.modifies M.loc_none h h' /\
    B.live h' input /\ (
    let ps = parse p (B.as_seq h input) in
    let (Some (res', consumed')) = ps in
    res == res' /\
    I32.v consumed == consumed'
  )))

inline_for_extraction
let coerce_parser32
  (t2: Type0)
  (#k: parser_kind)
  (#t1: Type0)
  (#p: parser k t1)
  (p32: parser32 p)
  (u: unit { t2 == t1 } )
: Tot (parser32 (coerce_parser t2 p))
= p32

[@unifier_hint_injective]
inline_for_extraction
let serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= serializer32_fail #k #t #p s

inline_for_extraction
let serialize32_ext
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (s1': serializer32 s1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (u: squash (t1 == t2 /\ (forall (input: bytes) . parse p1 input == parse p2 input)))
: Tot (serializer32 (serialize_ext p1 s1 p2))
= fun b len lo v -> 
  let h = HST.get () in
  let res = s1' b len lo v in
  let h' = HST.get () in
  contains_valid_serialized_data_or_fail_equiv h' s1 b lo v res;
  contains_valid_serialized_data_or_fail_equiv h' (serialize_ext p1 s1 p2) b lo v res;
  res
  
inline_for_extraction
let u32_max : (y: U32.t { forall (x: U32.t) . U32.v x <= U32.v y } ) =
  4294967295ul

inline_for_extraction
let add_overflow
  (x y: U32.t)
: Pure U32.t
  (requires True)
  (ensures (fun z ->
    if U32.v x + U32.v y > U32.v u32_max then
    z == u32_max
    else U32.v z == U32.v x + U32.v y
  ))
= if U32.lt (U32.sub u32_max y) x
  then u32_max
  else U32.add x y

let size32_postcond
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (x: t)
  (y: U32.t)
: GTot Type0
= let sz = Seq.length (serialize s x) in
  if sz > U32.v u32_max
  then y == u32_max
  else U32.v y == sz

[@unifier_hint_injective]
inline_for_extraction
let size32
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
: Tot Type0
= (x: t) ->
  Tot (y: U32.t {
    size32_postcond s x y
  })

let size32_constant_precond
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (len32: U32.t)
: GTot Type0
= k.parser_kind_high == Some k.parser_kind_low /\
  U32.v len32 == k.parser_kind_low

inline_for_extraction
let size32_constant
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (len32: U32.t)
  (u: unit { size32_constant_precond s len32 } )
: Tot (size32 s)
= fun x -> 
  [@inline_let]
  let (z: U32.t { size32_postcond s x z } ) = len32 in
  z

inline_for_extraction
let size32_ext
  (#k1: parser_kind)
  (#t1: Type0)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (s1': size32 s1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (u: squash (t1 == t2 /\ (forall (input: bytes) . parse p1 input == parse p2 input)))
: Tot (size32 (serialize_ext p1 s1 p2))
= fun input -> s1' input
