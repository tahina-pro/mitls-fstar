module LowParse.Low.Base
include LowParse.Spec.Base

module B = FStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

type buffer8 = B.buffer FStar.UInt8.t

type pointer (t: Type) = (b: Buffer.buffer t { B.length b == 1 } )

let is_slice (h: HS.mem) (#t: Type) (b: Buffer.buffer t) (len: U32.t) : GTot Type0 =
  B.live h b /\
  B.length b == U32.v len

let is_slice_ptr (h: HS.mem) (#t: Type) (b: pointer (B.buffer t)) (len: pointer U32.t) : GTot Type0 =
  B.live h b /\
  B.live h len /\
  B.disjoint b len /\ (
    let b' = B.get h b 0 in
    let len' = B.get h len 0 in
    B.disjoint b' b /\
    B.disjoint b' len /\
    is_slice h b' len'
  )

let slice_ptr_as_seq 
  (h: HS.mem) (#t: Type) (b: pointer (B.buffer t)) (len: pointer U32.t) : Ghost (Seq.seq t)
  (requires (is_slice_ptr h b len))
  (ensures (fun _ -> True))
= let b' = B.get h b 0 in
  B.as_seq h b'

let is_tail_of (#t: Type) (b' b : B.buffer t) : GTot Type0 =
  B.length b' <= B.length b /\
  b' == B.sub b (U32.uint_to_t (B.length b - B.length b')) (U32.uint_to_t (B.length b'))

let tail_ptr (h h' : HS.mem) (#t: Type) (p: pointer (B.buffer t)) =
  B.live h p /\
  B.live h' p /\ (
    let b = B.get h p 0 in
    let b' = B.get h' p 0 in
    B.live h b /\
    B.live h' b /\
    b' `is_tail_of` b
  )

let validator32_postcond
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: pointer buffer8)
  (sz: pointer U32.t)
  (h: HS.mem)
  (res: bool)
  (h' : HS.mem)
: GTot Type0
= is_slice_ptr h input sz /\
  B.modifies_2 input sz h h' /\ (
    let pv = parse p (B.as_seq h (B.get h input 0)) in
    if res
    then
      is_slice_ptr h' input sz /\
      Some? pv /\ (
        let Some (_, consumed) = pv in
        let len' = U32.uint_to_t (U32.v (B.get h sz 0) - consumed) in
        B.get h' input 0 == B.sub (B.get h input 0) (U32.uint_to_t consumed) len' /\
        B.get h' sz 0 == len'
      )
    else
      B.live h' input /\
      B.live h' sz /\
      None? pv
  )

let validator32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: pointer buffer8) ->
  (sz: pointer U32.t) ->
  HST.Stack bool
  (requires (fun h ->
    is_slice_ptr h input sz
  ))
  (ensures (fun h res h' ->
    validator32_postcond p input sz h res h'
  ))

let parser32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: pointer buffer8) ->
  (sz: pointer U32.t) ->
  HST.Stack t
  (requires (fun h ->
    is_slice_ptr h input sz /\
    Some? (parse p (B.as_seq h (B.get h input 0)))
  ))
  (ensures (fun h res h' ->
    let ps = parse p (B.as_seq h (B.get h input 0)) in
    let (Some (res', _)) = ps in
    res == res' /\
    validator32_postcond p input sz h true h'
  ))

let validator_nochk32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: pointer buffer8) ->
  (sz: pointer U32.t) ->
  HST.Stack unit
  (requires (fun h ->
    is_slice_ptr h input sz /\
    Some? (parse p (B.as_seq h (B.get h input 0)))
  ))
  (ensures (fun h res h' ->
    validator32_postcond p input sz h true h'
  ))

inline_for_extraction
let truncate_slice_ptr
  (b: pointer buffer8)
  (len: pointer U32.t)
  (len' : U32.t)
: HST.Stack unit
  (requires (fun h -> is_slice_ptr h b len /\ U32.v len' <= U32.v (B.get h len 0)))
  (ensures (fun h _ h' ->
    B.modifies_2 b len h h' /\
    is_slice_ptr h' b len /\
    B.get h' len 0 == len' /\
    B.get h' b 0 == B.sub (B.get h b 0) 0ul len'
  ))
= let b0 = B.index b 0ul in
  let b' = B.sub b0 0ul len' in
  B.upd b 0ul b';
  B.upd len 0ul len'

inline_for_extraction
let advance_slice_ptr
  (b: pointer buffer8)
  (len: pointer U32.t)
  (ofs: U32.t)
: HST.Stack unit
  (requires (fun h -> is_slice_ptr h b len /\ U32.v ofs <= U32.v (B.get h len 0)))
  (ensures (fun h _ h' ->
    B.modifies_2 b len h h' /\
    is_slice_ptr h' b len /\ (
    let len' = U32.sub (B.get h len 0) ofs in
    B.get h' len 0 == len' /\
    B.get h' b 0 == B.sub (B.get h b 0) ofs len'
  )))
= let b0 = B.index b 0ul in
  let len0 = B.index len 0ul in
  let len' = U32.sub len0 ofs in
  let b' = B.sub b0 ofs len' in
  B.upd b 0ul b' ;
  B.upd len 0ul len'
