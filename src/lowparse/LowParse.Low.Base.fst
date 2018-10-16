module LowParse.Low.Base
include LowParse.Spec.Base

module B = LowStar.Buffer
module M = LowStar.ModifiesPat
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module I32 = FStar.Int32
module Cast = FStar.Int.Cast
module MA = LowParse.Math
module G = FStar.Ghost

let int32_to_uint32_pos
  (x: I32.t)
: Lemma
  (requires (I32.v x >= 0))
  (ensures (U32.v (Cast.int32_to_uint32 x) == I32.v x))
  [SMTPat (U32.v (Cast.int32_to_uint32 x))]
= MA.modulo_lemma (I32.v x) (pow2 32)

let uint32_to_int32_bounded
  (x: U32.t)
: Lemma
  (requires (U32.v x < 2147483648))
  (ensures (I32.v (Cast.uint32_to_int32 x) == U32.v x))
  [SMTPat (I32.v (Cast.uint32_to_int32 x))]
= MA.modulo_lemma (U32.v x) (pow2 32)

inline_for_extraction
type buffer8 = B.buffer FStar.UInt8.t

inline_for_extraction
type pointer (t: Type) = (b: B.buffer t { B.length b == 1 } )

let is_slice (h: HS.mem) (#t: Type) (b: B.buffer t) (len: I32.t) : GTot Type0 =
  B.live h b /\
  B.length b == I32.v len

unfold
let gsub
  (#t: Type)
  (b: B.buffer t)
  (i: U32.t)
  (len: U32.t)
: Ghost (B.buffer t)
  (requires (U32.v i + U32.v len <= B.length b))
  (ensures (fun b' -> B.length b' == U32.v len))
= B.gsub b i len

let is_tail_of (#t: Type) (b' b : B.buffer t) : GTot Type0 =
  B.length b' <= B.length b /\
  b' == gsub b (U32.uint_to_t (B.length b - B.length b')) (U32.uint_to_t (B.length b'))

let tail_ptr (h h' : HS.mem) (#t: Type) (p: pointer (B.buffer t)) : GTot Type0 =
  B.live h p /\
  B.live h' p /\ (
    let b = B.get h p 0 in
    let b' = B.get h' p 0 in
    B.live h b /\
    B.live h' b /\
    b' `is_tail_of` b
  )

let parse_from_slice
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (h: HS.mem)
  (b: buffer8)
  (sz: I32.t)
: Ghost (option (t * nat))
  (requires (is_slice h b sz))
  (ensures (fun y ->
    match y with
    | None -> parse p (B.as_seq h b) == None
    | Some (x, len) -> len <= B.length b /\ parse p (B.as_seq h b) == Some (x, len)
  ))
= match parse p (B.as_seq h b) with
  | Some (x, len) -> Some (x, len)
  | _ -> None

(* A validator, if succeeds, returns the remaining length; otherwise returns a negative number. *)

class validator32_cls = {
  validator32_error_gloc: G.erased B.loc;
  validator32_error_inv: HS.mem -> GTot Type0;
  validator32_error_inv_loc_not_unused_in: (h: HS.mem) -> Lemma
    (requires (validator32_error_inv h))
    (ensures (M.loc_not_unused_in h `M.loc_includes` (G.reveal validator32_error_gloc)));
  validator32_error_inv_frame: (h: HS.mem) -> (h' : HS.mem) -> (l: M.loc) -> Lemma
    (requires (M.modifies_inert l h h' /\ M.loc_disjoint (G.reveal validator32_error_gloc) l /\ validator32_error_inv h))
    (ensures (validator32_error_inv h'))
}

let validator32_error_loc [| validator32_cls |] () : GTot B.loc = G.reveal validator32_error_gloc

let validator32_error_inv_loc_not_unused_in'
  [| validator32_cls |]
  (h: HS.mem)
: Lemma
  (requires (validator32_error_inv h))
  (ensures (M.loc_not_unused_in h `M.loc_includes` (validator32_error_loc ())))
  [SMTPat (validator32_error_inv h)]
= validator32_error_inv_loc_not_unused_in h

let validator32_error_inv_frame'
  [| validator32_cls |]
  (h: HS.mem)
  (h' : HS.mem)
  (l: M.loc)
: Lemma
  (requires (M.modifies_inert l h h' /\ M.loc_disjoint (validator32_error_loc ()) l /\ validator32_error_inv h))
  (ensures (validator32_error_inv h'))
  [SMTPatOr [
    [SMTPat (M.modifies l h h'); SMTPat (validator32_error_inv h)];
    [SMTPat (M.modifies l h h'); SMTPat (validator32_error_inv h')];
  ]]
= validator32_error_inv_frame h h' l

let loc_includes_union_l_validator32_error_loc [| validator32_cls |] (l1 l2: M.loc)  : Lemma
  (requires (M.loc_includes l1 (validator32_error_loc ()) \/ M.loc_includes l2 (validator32_error_loc ())))
  (ensures (M.loc_includes (M.loc_union l1 l2) (validator32_error_loc ())))
  [SMTPat (M.loc_includes (M.loc_union l1 l2) (validator32_error_loc()))]
= M.loc_includes_union_l l1 l2 (validator32_error_loc ())

unfold
let validator32_postcond' 
  [| validator32_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: buffer8)
  (sz: I32.t)
  (h: HS.mem)
  (res: Int32.t)
  (h' : HS.mem)
: GTot Type0
= is_slice h input sz /\
  M.modifies (validator32_error_loc ()) h h' /\
  validator32_error_inv h' /\ (
    let pv = parse_from_slice p h input sz in
    if I32.v res >= 0
    then
      Some? pv /\ (
        let Some (_, consumed) = pv in
        I32.v res == I32.v sz - consumed
      )
    else
      None? pv
  )

let validator32_postcond
  [| validator32_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: buffer8)
  (sz: I32.t)
  (h: HS.mem)
  (res: Int32.t)
  (h' : HS.mem)
: GTot Type0
= validator32_postcond'  p input sz h res h' 

[@unifier_hint_injective]
inline_for_extraction
let validator32
  [| validator32_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: buffer8) ->
  (sz: I32.t) ->
  HST.Stack I32.t
  (requires (fun h ->
    is_slice h input sz /\
    M.loc_disjoint (B.loc_buffer input) (validator32_error_loc ()) /\
    validator32_error_inv h
  ))
  (ensures (fun h res h' ->
    validator32_postcond p input sz h res h'
  ))

inline_for_extraction
let validate32
  [| validator32_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator32 p)
  (input: buffer8)
  (sz: I32.t)
: HST.Stack bool
  (requires (fun h ->
    is_slice h input sz /\
    M.loc_disjoint (B.loc_buffer input) (validator32_error_loc ()) /\
    validator32_error_inv h
  ))
  (ensures (fun h res h' ->
    is_slice h input sz /\
    M.modifies (validator32_error_loc ()) h h' /\
    validator32_error_inv h' /\ (
    let pv = parse_from_slice p h input sz in
    res == Some? pv
 )))
= let res = v input sz in
  not (res `I32.lt` 0l)

inline_for_extraction
let ghost_parse_from_validator32
  [| cls: validator32_cls |]
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator32 p)
  (input: buffer8)
  (sz: I32.t)
: HST.Stack (option (Ghost.erased t))
  (requires (fun h ->
    is_slice h input sz /\
    M.loc_disjoint (B.loc_buffer input) (validator32_error_loc ()) /\
    validator32_error_inv h
  ))
  (ensures (fun h res h' ->
    is_slice h input sz /\
    M.modifies (validator32_error_loc ()) h h' /\
    validator32_error_inv h' /\
    res == (match parse_from_slice p h input sz with
    | Some (x, _) -> Some (Ghost.hide x)
    | _ ->  None
  )))
= let h = HST.get () in
  // FIXME: WHY WHY WHY does tc instantiation fail here?
  if validate32 #cls v input sz
  then begin
    let f () : GTot t =
      let (Some (x, _)) = parse_from_slice p h input sz in
      x
    in
    Some (Ghost.elift1 f (Ghost.hide ()))
  end
  else None

inline_for_extraction
let ghost_parse32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: buffer8)
: HST.Stack (Ghost.erased t)
  (requires (fun h -> B.live h input /\ Some? (parse p (B.as_seq h input))))
  (ensures (fun h res h' -> h == h' /\ (let (Some (x, _)) = parse p (B.as_seq h input) in res == Ghost.hide x)))
= let h = HST.get () in
  let f () : GTot t =
    let (Some (x, _)) = parse p (B.as_seq h input) in
    x
  in
  Ghost.elift1 f (Ghost.hide ())

[@unifier_hint_injective]
inline_for_extraction
let parser32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: buffer8) ->
  HST.Stack t
  (requires (fun h ->
    B.live h input /\
    Some? (parse p (B.as_seq h input))
  ))
  (ensures (fun h res h' ->
    M.modifies M.loc_none h h' /\
    B.live h' input /\ (
    let ps = parse p (B.as_seq h input) in
    let (Some (res', _)) = ps in
    res == res'
  )))

[@unifier_hint_injective]
inline_for_extraction
let validator_nochk32
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
: Tot Type0
= (input: buffer8) ->
  HST.Stack U32.t
  (requires (fun h ->
    B.live h input /\
    Some? (parse p (B.as_seq h input))
  ))
  (ensures (fun h res h' ->
    M.modifies M.loc_none h h' /\
    B.live h' input /\
    U32.v res <= B.length input /\ (
    let (Some (x, res')) = parse p (B.as_seq h input) in
    U32.v res == res'
  )))

[@unifier_hint_injective]
inline_for_extraction
let accessor
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (rel: (t1 -> t2 -> GTot Type0))
: Tot Type
= (input: buffer8) ->
  HST.Stack buffer8
  (requires (fun h ->
    B.live h input /\
    Some? (parse p1 (B.as_seq h input))
  ))
  (ensures (fun h res h' ->
    M.modifies (M.loc_none) h h' /\
    B.live h' input /\
    B.includes input res /\ (
    let Some (x1, _) = parse p1 (B.as_seq h input) in
    let ps2 = parse p2 (B.as_seq h res) in
    Some? ps2 /\ (
    let Some (x2, _) = ps2 in
    rel x1 x2
  ))))

inline_for_extraction
let read_from_buffer
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#rel: (t1 -> t2 -> GTot Type0))
  (a12: accessor p1 p2 rel)
  (p2' : parser32 p2)
  (input: buffer8)
: HST.Stack t2
  (requires (fun h ->
    B.live h input /\
    Some? (parse p1 (B.as_seq h input))
  ))
  (ensures (fun h y h' ->
    M.modifies M.loc_none h h' /\ (
    let (Some (x, _)) = parse p1 (B.as_seq h input) in
    rel x y
  )))
= p2' (a12 input)

let exactly_contains_valid_data'
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (p: parser k t)
  (b: buffer8)
  (lo: U32.t)
  (x: t)
  (hi: U32.t)
: GTot Type0
= B.live h b /\
  U32.v lo <= U32.v hi /\
  U32.v hi <= B.length b /\
  parse p (B.as_seq h (B.gsub b lo (U32.sub hi lo))) == Some (x, U32.v hi - U32.v lo)

abstract
let exactly_contains_valid_data
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (p: parser k t)
  (b: buffer8)
  (lo: U32.t)
  (x: t)
  (hi: U32.t)
: GTot Type0
= exactly_contains_valid_data' h p b lo x hi

abstract
let exactly_contains_valid_data_equiv
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (p: parser k t)
  (b: buffer8)
  (lo: U32.t)
  (x: t)
  (hi: U32.t)
: Lemma
  (exactly_contains_valid_data h p b lo x hi <==> exactly_contains_valid_data' h p b lo x hi)
= ()

abstract
let exactly_contains_valid_data_elim
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (p: parser k t)
  (b: buffer8)
  (lo: U32.t)
  (x: t)
  (hi: U32.t)
: Lemma
  (requires (exactly_contains_valid_data h p b lo x hi))
  (ensures (
    B.live h b /\
    U32.v lo <= U32.v hi /\
    U32.v hi <= B.length b /\ (
    let hilo = U32.v hi - U32.v lo in
    k.parser_kind_low <= hilo /\ (
    match k.parser_kind_high with
    | Some l -> hilo <= l
    | _ -> True
  ))))
  [SMTPat (exactly_contains_valid_data h p b lo x hi)]
= ()

abstract
let exactly_contains_valid_data_injective
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (p: parser k t)
  (b: buffer8)
  (lo: U32.t)
  (x1: t)
  (hi: U32.t)
  (x2: t)
: Lemma
  (requires (
    exactly_contains_valid_data h p b lo x1 hi /\
    exactly_contains_valid_data h p b lo x2 hi
  ))
  (ensures (
    x1 == x2
  ))
  [SMTPat (exactly_contains_valid_data h p b lo x1 hi);
   SMTPat (exactly_contains_valid_data h p b lo x2 hi);]
= ()

abstract
let exactly_contains_valid_data_injective_strong'
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (p: parser k t)
  (b: buffer8)
  (lo: U32.t)
  (x1: t)
  (hi1: U32.t)
  (x2: t)
  (hi2: U32.t)
: Lemma
  (requires (
    exactly_contains_valid_data h p b lo x1 hi1 /\
    exactly_contains_valid_data h p b lo x2 hi2 /\
    k.parser_kind_subkind == Some ParserStrong /\
    U32.v hi1 <= U32.v hi2
  ))
  (ensures (
    x1 == x2 /\ hi1 == hi2
  ))
= assert (no_lookahead_on p (B.as_seq h (B.gsub b lo (U32.sub hi1 lo))) (B.as_seq h (B.gsub b lo (U32.sub hi2 lo))));
  assert (injective_precond p (B.as_seq h (B.gsub b lo (U32.sub hi2 lo))) (B.as_seq h (B.gsub b lo (U32.sub hi1 lo)))) 

abstract
let exactly_contains_valid_data_injective_strong
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (p: parser k t)
  (b: buffer8)
  (lo: U32.t)
  (x1: t)
  (hi1: U32.t)
  (x2: t)
  (hi2: U32.t)
: Lemma
  (requires (
    exactly_contains_valid_data h p b lo x1 hi1 /\
    exactly_contains_valid_data h p b lo x2 hi2 /\
    k.parser_kind_subkind == Some ParserStrong
  ))
  (ensures (
    x1 == x2 /\ hi1 == hi2
  ))
  [SMTPat (exactly_contains_valid_data h p b lo x1 hi1);
   SMTPat (exactly_contains_valid_data h p b lo x2 hi2);]
= if U32.v hi1 <= U32.v hi2
  then exactly_contains_valid_data_injective_strong' h p b lo x1 hi1 x2 hi2
  else exactly_contains_valid_data_injective_strong' h p b lo x2 hi2 x1 hi1

abstract
let loc_jbuffer
  (b: buffer8)
  (lo: U32.t)
  (hi: U32.t)
: GTot M.loc
= if U32.v lo <= U32.v hi && U32.v hi <= B.length b
  then M.loc_buffer (B.gsub b lo (U32.sub hi lo))
  else M.loc_none

abstract
let loc_jbuffer_eq
  (b: buffer8)
  (i j: U32.t)
: Lemma
  (requires (U32.v i <= U32.v j /\ U32.v j <= B.length b))
  (ensures (loc_jbuffer b i j == M.loc_buffer (B.gsub b i (U32.sub j i))))
//  [SMTPat (loc_jbuffer b i j)] // test by uncommenting this and commenting the following 3 lemmas
= ()

abstract
let loc_jbuffer_includes_r
  (b: buffer8)
  (lo hi: U32.t)
: Lemma
  (M.loc_buffer b `M.loc_includes` loc_jbuffer b lo hi)
  [SMTPat (loc_jbuffer b lo hi)]
= ()

abstract
let loc_includes_union_l_jbuffer
  (l1 l2: M.loc)
  (b: buffer8)
  (i j: U32.t)
: Lemma
  (requires (M.loc_includes l1 (loc_jbuffer b i j) \/ M.loc_includes l2 (loc_jbuffer b i j)))
  (ensures (M.loc_includes (l1 `M.loc_union` l2) (loc_jbuffer b i j)))
  [SMTPat (M.loc_includes (l1 `M.loc_union` l2) (loc_jbuffer b i j))]
= ()

abstract
let loc_disjoint_jbuffer
  (b: buffer8)
  (i j k: U32.t)
: Lemma
  (requires (U32.v i <= U32.v j /\ U32.v j <= U32.v k))
  (ensures (M.loc_disjoint (loc_jbuffer b i j) (loc_jbuffer b j k)))
  [SMTPat (loc_jbuffer b i j); SMTPat (loc_jbuffer b j k)]
= ()

abstract
let exactly_contains_valid_data_invariant
  (#k: parser_kind)
  (#t: Type)
  (l: M.loc)
  (h h' : HS.mem)
  (p: parser k t)
  (b: buffer8)
  (lo: U32.t)
  (x: t)
  (hi: U32.t)
: Lemma
  (requires (
    M.modifies_inert l h h' /\
    exactly_contains_valid_data h p b lo x hi /\
    M.loc_disjoint l (loc_jbuffer b lo hi)
  ))
  (ensures (
    exactly_contains_valid_data h' p b lo x hi
  ))
  [SMTPat (M.modifies l h h'); SMTPat (exactly_contains_valid_data h p b lo x hi)]
= ()

let contains_valid_serialized_data_or_fail'
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (#p: parser k t)
  (s: serializer p)
  (b: buffer8)
  (lo: I32.t)
  (x: t)
  (hi: I32.t)
: GTot Type0
= B.live h b /\
  I32.v lo <= B.length b /\ (
  if I32.v lo < 0
  then I32.v hi < 0
  else
    let sd = serialize s x in
    if I32.v lo + Seq.length sd > B.length b
    then I32.v hi < 0
    else
      I32.v lo <= I32.v hi /\
      I32.v hi <= B.length b /\
      Seq.slice (B.as_seq h b) (I32.v lo) (I32.v hi) == sd
  )

abstract
let contains_valid_serialized_data_or_fail
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (#p: parser k t)
  (s: serializer p)
  (b: buffer8)
  (lo: I32.t)
  (x: t)
  (hi: I32.t)
= contains_valid_serialized_data_or_fail' h s b lo x hi

abstract
let contains_valid_serialized_data_or_fail_equiv
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (#p: parser k t)
  (s: serializer p)
  (b: buffer8)
  (lo: I32.t)
  (x: t)
  (hi: I32.t)
: Lemma
  (contains_valid_serialized_data_or_fail h s b lo x hi <==> contains_valid_serialized_data_or_fail' h s b lo x hi)
= ()

abstract
let contains_valid_serialized_data_or_fail_elim
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (#p: parser k t)
  (s: serializer p)
  (b: buffer8)
  (lo: I32.t)
  (x: t)
  (hi: I32.t)
: Lemma
  (requires (contains_valid_serialized_data_or_fail h s b lo x hi))
  (ensures (
    B.live h b /\
    I32.v lo <= B.length b /\ (
    if I32.v lo < 0
    then I32.v hi < 0
    else if I32.v hi < 0
    then match k.parser_kind_high with
      | None -> True
      | Some sz' -> I32.v lo + sz' > B.length b
    else
      I32.v lo <= I32.v hi /\
      I32.v hi <= B.length b /\ (
      let sz = I32.v hi - I32.v lo in
      k.parser_kind_low <= sz /\ (
      match k.parser_kind_high with
      | None -> True
      | Some sz' -> sz <= sz'
  )))))
  [SMTPat (contains_valid_serialized_data_or_fail h s b lo x hi)]
= ()

abstract
let contains_valid_serialized_data_or_fail_neg_intro
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (#p: parser k t)
  (s: serializer p)
  (b: buffer8)
  (lo: I32.t)
  (x: t)
  (hi: I32.t)
: Lemma
  (requires (B.live h b /\ I32.v lo < 0 /\ I32.v hi < 0))
  (ensures (contains_valid_serialized_data_or_fail h s b lo x hi))
= ()

abstract
let contains_valid_serialized_data_or_fail_exactly_contains_valid_data
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (#p: parser k t)
  (s: serializer p)
  (b: buffer8)
  (lo: I32.t)
  (x: t)
  (hi: I32.t)
: Lemma
  (requires (
    contains_valid_serialized_data_or_fail h s b lo x hi /\
    I32.v lo >= 0 /\
    I32.v hi >= 0
  ))
  (ensures (
    exactly_contains_valid_data h p b (Cast.int32_to_uint32 lo) x (Cast.int32_to_uint32 hi)
  ))
= ()

abstract
let exactly_contains_valid_data_contains_valid_serialized_data_or_fail
  (#k: parser_kind)
  (#t: Type)
  (h: HS.mem)
  (#p: parser k t)
  (s: serializer p)
  (b: buffer8)
  (lo: U32.t)
  (x: t)
  (hi: U32.t)
: Lemma
  (requires (
    exactly_contains_valid_data h p b lo x hi /\
    U32.v hi <= 2147483647
  ))
  (ensures (
    contains_valid_serialized_data_or_fail h s b (Cast.uint32_to_int32 lo) x (Cast.uint32_to_int32 hi)
  ))
= serializer_correct_implies_complete p s


abstract
let loc_ibuffer
  (b: buffer8)
  (i: I32.t)
  (j: I32.t)
: GTot B.loc
= if I32.v i < 0 || I32.v i > B.length b || (I32.v j >= 0 && I32.v j < I32.v i)
  then M.loc_none
  else if I32.v j < 0 || I32.v j > B.length b
  then M.loc_buffer (B.gsub b (Cast.int32_to_uint32 i) (B.len b ` U32.sub` Cast.int32_to_uint32 i))
  else M.loc_buffer (B.gsub b (Cast.int32_to_uint32 i) (Cast.int32_to_uint32 (j `I32.sub` i)))

abstract
let loc_ibuffer_eq
  (b: buffer8)
  (i: I32.t)
  (j: I32.t)
: Lemma
  (requires (
    I32.v i <= B.length b /\ (
    if I32.v i < 0
    then I32.v j < 0
    else if I32.v j < 0
    then True
    else I32.v i <= I32.v j /\ I32.v j <= B.length b
  )))
  (ensures (
    loc_ibuffer b i j == (
      if I32.v i < 0
      then M.loc_none
      else if I32.v j < 0
      then M.loc_buffer (B.gsub b (Cast.int32_to_uint32 i) (B.len b ` U32.sub` Cast.int32_to_uint32 i))
      else M.loc_buffer (B.gsub b (Cast.int32_to_uint32 i) (Cast.int32_to_uint32 (j `I32.sub` i)))
  )))
= ()

abstract
let contains_valid_serialized_data_or_fail_loc_ibuffer_eq
  (#k: parser_kind)
  (#t: Type)
  (h : HS.mem)
  (#p: parser k t)
  (s: serializer p)
  (b: buffer8)
  (i: I32.t)
  (x: t)
  (j: I32.t)
: Lemma
  (requires (contains_valid_serialized_data_or_fail h s b i x j))
  (ensures (contains_valid_serialized_data_or_fail' h s b i x j /\
    loc_ibuffer b i j == (
      if I32.v i < 0
      then M.loc_none
      else if I32.v j < 0
      then M.loc_buffer (B.gsub b (Cast.int32_to_uint32 i) (B.len b ` U32.sub` Cast.int32_to_uint32 i))
      else M.loc_buffer (B.gsub b (Cast.int32_to_uint32 i) (Cast.int32_to_uint32 (j `I32.sub` i)))
  )))
= ()

abstract
let loc_buffer_includes_ibuffer
  (b: buffer8)
  (i: I32.t)
  (j: I32.t)
: Lemma
  (B.loc_buffer b `B.loc_includes` loc_ibuffer b i j)
  [SMTPat (loc_ibuffer b i j)]
= ()

abstract
let loc_includes_union_r_ibuffer
  (l1 l2: M.loc)
  (b: buffer8)
  (i j: I32.t)
: Lemma
  (requires (M.loc_includes l1 (loc_ibuffer b i j) \/ M.loc_includes l2 (loc_ibuffer b i j)))
  (ensures (M.loc_includes (l1 `M.loc_union` l2) (loc_ibuffer b i j)))
  [SMTPat (M.loc_includes (l1 `M.loc_union` l2) (loc_ibuffer b i j))]
= ()

abstract
let loc_disjoint_ibuffer
  (b: buffer8)
  (i j k: I32.t)
: Lemma
  (M.loc_disjoint (loc_ibuffer b i j) (loc_ibuffer b j k))
  [SMTPat (loc_ibuffer b i j); SMTPat (loc_ibuffer b j k)]
= ()

abstract
let contains_valid_serialized_data_or_fail_invariant
  (#k: parser_kind)
  (#t: Type)
  (l: M.loc)
  (h h' : HS.mem)
  (#p: parser k t)
  (s: serializer p)
  (b: buffer8)
  (lo: I32.t)
  (x: t)
  (hi: I32.t)
: Lemma
  (requires (
    M.modifies_inert l h h' /\
    contains_valid_serialized_data_or_fail h s b lo x hi /\
    B.live h' b /\
    M.loc_disjoint l (loc_ibuffer b lo hi)
  ))
  (ensures (
    contains_valid_serialized_data_or_fail h' s b lo x hi
  ))
  [SMTPat (M.modifies l h h'); SMTPat (contains_valid_serialized_data_or_fail h s b lo x hi)]
= ()

abstract
let contains_valid_serialized_data_or_fail_loc_includes_loc_ibuffer
  (#k1: parser_kind)
  (#t1: Type)
  (h1 : HS.mem)
  (#p1: parser k1 t1)
  (s1: serializer p1)
  (b: buffer8)
  (i0: I32.t)
  (x1: t1)
  (i1: I32.t)
  (#k2: parser_kind)
  (#t2: Type)
  (h2: HS.mem)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x2: t2)
  (i2: I32.t)
: Lemma
  (requires (contains_valid_serialized_data_or_fail h1 s1 b i0 x1 i1 /\ contains_valid_serialized_data_or_fail h2 s2 b i1 x2 i2))
  (ensures (M.loc_includes (loc_ibuffer b i0 i2) (loc_ibuffer b i0 i1) /\ M.loc_includes (loc_ibuffer b i0 i2) (loc_ibuffer b i1 i2)))
  [SMTPat (contains_valid_serialized_data_or_fail h1 s1 b i0 x1 i1); SMTPat (contains_valid_serialized_data_or_fail h2 s2 b i1 x2 i2)]
= ()

[@unifier_hint_injective]
inline_for_extraction
let serializer32'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (b: buffer8) ->
  (lo: U32.t) ->
  (v: t) ->
  HST.Stack unit
  (requires (fun h -> B.live h b /\ U32.v lo + Seq.length (serialize s v) <= B.length b))
  (ensures (fun h _ h' ->
    let len = U32.uint_to_t (Seq.length (serialize s v)) in
    M.modifies (M.loc_buffer (B.gsub b lo len)) h h' /\
    B.live h' b /\
    B.as_seq h' (B.gsub b lo len) `Seq.equal` serialize s v
  ))

[@unifier_hint_injective]
inline_for_extraction
let serializer32
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (b: buffer8) ->
  (lo: U32.t) ->
  (v: t) ->
  HST.Stack unit
  (requires (fun h -> B.live h b /\ U32.v lo + Seq.length (serialize s v) <= B.length b))
  (ensures (fun h _ h' ->
    let len = U32.uint_to_t (Seq.length (serialize s v)) in
    M.modifies (loc_jbuffer b lo (U32.add lo len)) h h' /\
    B.live h' b /\
    exactly_contains_valid_data h' p b lo v (U32.add lo len)
  ))

inline_for_extraction
let serializer32_of_serializer32'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32' s)
: Tot (serializer32 s)
= fun b lo v ->
  s32 b lo v;
  let ghi = FStar.Ghost.hide (U32.add lo (U32.uint_to_t (Seq.length (serialize s v)))) in
  loc_jbuffer_eq b lo (FStar.Ghost.reveal ghi);
  let h' = HST.get () in
  exactly_contains_valid_data_equiv h' p b lo v (FStar.Ghost.reveal ghi)

[@unifier_hint_injective]
inline_for_extraction
let serializer32_fail
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
: Tot Type
= (b: buffer8) ->
  (len: I32.t { I32.v len == B.length b } ) ->
  (lo: I32.t) ->
  (v: t) ->
  HST.Stack I32.t
  (requires (fun h -> B.live h b /\ I32.v lo <= I32.v len))
  (ensures (fun h hi h' ->
    B.live h' b /\
    contains_valid_serialized_data_or_fail h' s b lo v hi /\
    M.modifies (loc_ibuffer b lo hi) h h'
  ))


(* Stateful serializers for constant-size parsers *)

inline_for_extraction
let serializer32_fail_of_serializer
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (psz: I32.t { k.parser_kind_high == Some k.parser_kind_low /\ k.parser_kind_low == I32.v psz } ) 
: Tot (serializer32_fail s)
= fun out (len: I32.t { I32.v len == B.length out } ) lo v ->
  let h = HST.get () in
  if lo `I32.lt` 0l
  then begin
    let res = lo in
    let h' = HST.get () in
    assert (contains_valid_serialized_data_or_fail h' s out lo v res);
    res
  end
  else begin
    assert (I32.v lo >= 0);
    assert (I32.v len >= 0);
    assert (I32.v lo <= I32.v len);
    assert (Seq.length (serialize s v) == I32.v psz);
    if (len `I32.sub` lo) `I32.lt` psz
    then begin
      let res = I32.int_to_t (-1) in
      let h' = HST.get () in
      assert (contains_valid_serialized_data_or_fail h' s out lo v res);
      assert (B.modifies (B.loc_buffer (B.gsub out (Cast.int32_to_uint32 lo) (B.len out `U32.sub` Cast.int32_to_uint32 lo))) h h');
      res
    end else begin
      assert (Seq.length (serialize s v) == I32.v psz);
      assert (I32.v lo + Seq.length (serialize s v) <= I32.v len);
      assert (U32.v (Cast.int32_to_uint32 lo) == I32.v lo);
      assert (U32.v (Cast.int32_to_uint32 lo) + Seq.length (serialize s v) <= I32.v len);
      assert (U32.v (Cast.int32_to_uint32 lo) + Seq.length (serialize s v) <= B.length out);
      s32 out (Cast.int32_to_uint32 lo) v;
      let h = HST.get () in
      exactly_contains_valid_data_contains_valid_serialized_data_or_fail h s out (Cast.int32_to_uint32 lo) v (Cast.int32_to_uint32 (lo `I32.add` psz));
      lo `I32.add` psz
    end
  end
  
inline_for_extraction
let error_code = (x: I32.t { I32.v x < 0 } )

(* Some instances for validator32_cls *)

inline_for_extraction
let default_validator32_cls : validator32_cls = {
  validator32_error_gloc = G.hide M.loc_none;
  validator32_error_inv = (fun _ -> True);
  validator32_error_inv_loc_not_unused_in = (fun _ -> ());
  validator32_error_inv_frame = (fun _ _ _ -> ());
}

inline_for_extraction
let buffer_validator32_cls (#t: Type) (b: M.buffer t) : Tot validator32_cls = {
  validator32_error_gloc = G.hide (M.loc_buffer b);
  validator32_error_inv = (fun h -> M.live h b);
  validator32_error_inv_loc_not_unused_in = (fun _ -> ());
  validator32_error_inv_frame = (fun _ _ _ -> ());
}

inline_for_extraction
let report_validation_error_gen
  (#error_log_t: Type)
  (transform_error: (error_log_t -> Tot error_log_t))
  (b: M.pointer error_log_t)
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v: validator32 #(buffer_validator32_cls b) p)
: Tot (validator32 #(buffer_validator32_cls b) p)
= fun input len ->
  let res = v input len in
  begin if res `I32.lt` 0l
  then
    let r = B.index b 0ul in
    B.upd b 0ul (transform_error r)
  end;
  res

inline_for_extraction
let append_validation_error
  (#error_log_t: Type)
  (append: (error_log_t -> error_log_t -> Tot error_log_t))
  (x: error_log_t)
= report_validation_error_gen (fun x0 -> append x0 x)

inline_for_extraction
let report_first_validation_error
  (#error_log_t: Type)
  (x: error_log_t)
= report_validation_error_gen (fun x0 -> match x0 with None -> Some x | _ -> x0)

inline_for_extraction
let buffer_validator32_of_default
  (#et: Type) (b: M.buffer et)
  (#k: parser_kind) (#t: Type) (#p: parser k t)
  (v: validator32 #default_validator32_cls p)
: Tot (validator32 #(buffer_validator32_cls b) p)
= fun input len -> v input len
