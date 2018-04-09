module LowParse.SLow.Base
include LowParse.Spec.Base

module B32 = LowParse.Bytes32
module U32 = FStar.UInt32

let bytes32 = B32.bytes

let parser32_correct
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (input: bytes32)
  (res: result (t * U32.t) err)
: GTot Type0
= let gp = parse p (B32.reveal input) in
  match res with
  | Error e -> gp == Error e
  | Correct (hres, consumed) ->
    Correct? gp /\ (
      let (Correct (hres' , consumed')) = gp in
      hres == hres' /\
      U32.v consumed == (consumed' <: nat)
    )

let parser32
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
: Tot Type0
= (input: bytes32) -> Tot (res: result (t * U32.t) err { parser32_correct p input res } )

inline_for_extraction
let make_parser32
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (p32: (input: bytes32) -> Pure (result (t * U32.t) err) (requires True) (ensures (fun res -> parser32_correct p input res)))
: Tot (parser32 p)
= (fun (input: bytes32) -> (p32 input <: (res: result (t * U32.t) err { parser32_correct p input res } )))

inline_for_extraction
let coerce_parser32
  (t2: Type0)
  (#k: parser_kind)
  (#t1: Type0)
  (#err: Type0)
  (#p: parser k t1 err)
  (p32: parser32 p)
  (u: unit { t2 == t1 } )
: Tot (parser32 (coerce_parser t2 p))
= p32

let validator_correct
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
  (input: bytes32)
  (res: result U32.t err)
: GTot Type0
= let gp = parse p (B32.reveal input) in
  match res with
  | Error e -> gp == Error e
  | Correct (consumed) ->
    Correct? gp /\ (
      let (Correct (_ , consumed')) = gp in
      U32.v consumed == (consumed' <: nat)
    )

let validator
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (p: parser k t err)
: Tot Type0
= (input: bytes32) -> Tot (res: result U32.t err { validator_correct p input res } )

let serializer32_correct
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (input: t)
  (res: bytes32)
: GTot Type0
= B32.reveal res == s input

let serializer32
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
: Tot Type0
= (input: t) -> Tot (res: bytes32 { serializer32_correct s input res } )

let partial_serializer32
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
: Tot Type0
= (input: t { Seq.length (s input) < 4294967296 } ) -> Tot (res: bytes32 { serializer32_correct s input res } )

inline_for_extraction
let total_to_partial_serializer32
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: serializer32 s)
: Tot (partial_serializer32 s)
= s32

let serializer32_then_parser32
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (p32: parser32 p)
  (s32: serializer32 s)
  (input: t)
: Lemma
  (p32 (s32 input) == Correct (input, B32.len (s32 input)))
= ()

let parser32_then_serializer32
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (p32: parser32 p)
  (s32: serializer32 s)
  (input: bytes32)
: Lemma
  (requires (Correct? (p32 input)))
  (ensures (
    let (Correct (v, consumed)) = p32 input in
    U32.v consumed <= B32.length input /\
    s32 v == B32.b32slice input 0ul consumed
  ))
= serializer_correct_implies_complete p s

let parser32_then_serializer32'
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (p32: parser32 p)
  (s32: serializer32 s)
  (input: bytes32)
  (v: t)
  (consumed: U32.t)
: Lemma
  (requires (p32 input == Correct (v, consumed)))
  (ensures (
    B32.length (s32 v) == U32.v consumed /\
    U32.v consumed <= B32.length input /\
    B32.reveal (s32 v) == Seq.slice (B32.reveal input) 0 (U32.v consumed)
  ))
= parser32_then_serializer32 s p32 s32 input

let parser32_injective
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (p32: parser32 p)
  (input1 input2: bytes32)
: Lemma
  (requires (
    let p1 = p32 input1 in
    let p2 = p32 input2 in
    Correct? p1 /\
    Correct? p2 /\ (
    let (Correct (v1, _)) = p1 in
    let (Correct (v2, _)) = p2 in
    v1 == v2
  )))
  (ensures (
    let p1 = p32 input1 in
    let p2 = p32 input2 in
    Correct? p1 /\
    Correct? p2 /\ (
    let (Correct (v1, consumed1)) = p1 in
    let (Correct (v2, consumed2)) = p2 in
    v1 == v2 /\
    consumed1 == consumed2 /\
    U32.v consumed1 <= B32.length input1 /\
    U32.v consumed2 <= B32.length input2 /\
    B32.b32slice input1 0ul consumed1 == B32.b32slice input2 0ul consumed2
  )))
= assert (injective_precond p (B32.reveal input1) (B32.reveal input2));
  assert (injective_postcond p (B32.reveal input1) (B32.reveal input2))

let serializer32_injective
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (s32: serializer32 s)
  (input1 input2: t)
: Lemma
  (requires (s32 input1 == s32 input2))
  (ensures (input1 == input2))
= ()

let parse32_size
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (p32: parser32 p)
  (input: bytes32)
  (data: t)
  (consumed: U32.t)
: Lemma
  (requires (p32 input == Correct (data, consumed)))
  (ensures (
    k.parser_kind_low <= U32.v consumed /\ (
    Some? k.parser_kind_high ==> (
    let (Some hi) = k.parser_kind_high in
    U32.v consumed <= hi
  ))))
= ()

let parse32_total
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (p32: parser32 p)
  (input: bytes32)
: Lemma
  (requires (
    k.parser_kind_high == Some k.parser_kind_low /\
    k.parser_kind_metadata.parser_kind_metadata_total == true /\
    k.parser_kind_low <= B32.length input
  ))
  (ensures (
    Correct? (p32 input)
  ))
= ()
  

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
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (x: t)
  (y: U32.t)
: GTot Type0
= let sz = Seq.length (serialize s x) in
  if sz > U32.v u32_max
  then y == u32_max
  else U32.v y == sz

let size32
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
: Tot Type0
= (x: t) ->
  Tot (y: U32.t {
    size32_postcond s x y
  })

let size32_constant_precond
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (len32: U32.t)
: GTot Type0
= k.parser_kind_high == Some k.parser_kind_low /\
  U32.v len32 == k.parser_kind_low

inline_for_extraction
let size32_constant
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (len32: U32.t)
  (u: unit { size32_constant_precond s len32 } )
: Tot (size32 s)
= fun x -> 
  [@inline_let]
  let (z: U32.t { size32_postcond s x z } ) = len32 in
  z
