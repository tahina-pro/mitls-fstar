module LowParse.Impl.Combinators
include LowParse.Spec.Combinators
include LowParse.Impl.Base

module S = LowParse.Slice
module Seq = FStar.Seq
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module B = FStar.Buffer

inline_for_extraction
let validate_empty : stateful_validator parse_empty =
  fun (s: S.bslice) ->
  let h = HST.get () in
  assert (let s' = S.as_seq h s in Some? (parse parse_empty s'));
  Some (0ul <: consumed_slice_length s)

inline_for_extraction
val validate_and_split
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (sv: stateful_validator p)
  (s: S.bslice)
: HST.Stack (option (S.bslice * S.bslice))
  (requires (fun h ->
    S.live h s
  ))
  (ensures (fun h r h' ->
    S.modifies_none h h' /\
    S.live h s /\
    (Some? r ==> (
    let (Some (sl, sr)) = r in
    S.is_concat s sl sr /\
    parses h p s (fun (v, l) ->
    exactly_parses h p sl (fun v' ->
    S.length sl == l /\
    v == v'
  ))))))

let validate_and_split #k #t #p sv s =
  match sv s with
  | Some consumed ->
    let sl = S.truncate_slice s consumed in
    let sr = S.advance_slice s consumed in
    let h = HST.get () in
    assert (no_lookahead_weak_on p (S.as_seq h s) (S.as_seq h sl));
    Some (sl, sr)
  | _ -> None

inline_for_extraction
val split
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (sv: stateful_validator_nochk p)
  (s: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.live h s /\
    parses h p s (fun _ -> True)
  ))
  (ensures (fun h r h' ->
    S.modifies_none h h' /\
    S.live h s /\ (
    let (sl, sr) = r in
    S.is_concat s sl sr /\
    parses h p s (fun (v, l) ->
    exactly_parses h p sl (fun v' ->
    S.length sl == l /\
    v == v'
  )))))

let split #k #t #p sv s =
  let consumed = sv s in
  let sl = S.truncate_slice s consumed in
  let sr = S.advance_slice s consumed in
  let h = HST.get () in
  assert (no_lookahead_weak_on p (S.as_seq h s) (S.as_seq h sl));
  (sl, sr)

[@"substitute"]
inline_for_extraction
val validate_fail
  (k: parser_kind { fail_parser_kind_precond k } )
  (t: Type0)
: Tot (stateful_validator (fail_parser k t))

let validate_fail k t =
  (fun (input: S.bslice) -> (
    let h = HST.get () in
    None #(consumed_slice_length input)
  )) <: stateful_validator (fail_parser k t)

[@"substitute"]
inline_for_extraction
val parse_then_check'
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (ps1: parser_st p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: t1 -> Tot (parser k2 t2))
  (prf: unit -> Lemma (and_then_cases_injective p2))
  (ps2: ((x1: t1) -> Tot (stateful_validator (p2 x1))))
: Tot (prf (); stateful_validator (and_then p1 p2))

let parse_then_check' #k1 #t1 #p1 ps1 #k2 #t2 #p2 prf ps2 =
  fun input ->
  match ps1 input with
  | Some (v1, off1) ->
    let input2 = S.advance_slice input off1 in
    begin match ps2 v1 input2 with
    | Some off2 ->
      let off : consumed_slice_length input = U32.add off1 off2 in
      Some off
    | _ -> None
    end
  | _ -> None

[@"substitute"]
inline_for_extraction
val parse_then_check
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (ps1: parser_st p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: t1 -> Tot (parser k2 t2) {
    and_then_cases_injective p2
  })
  (ps2: ((x1: t1) -> Tot (stateful_validator (p2 x1))))
: Tot (stateful_validator (and_then p1 p2))

let parse_then_check #k1 #t1 #p1 ps1 #k2 #t2 #p2 ps2 =
  parse_then_check' ps1 (fun _ -> ()) ps2

[@"substitute"]
inline_for_extraction
let parse_nochk_then_nochk
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (ps1: parser_st_nochk p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: (t1 -> Tot (parser k2 t2)) {
    and_then_cases_injective p2
  })
  (ps2: ((x1: t1) -> Tot (stateful_validator_nochk (p2 x1))))
: Tot (stateful_validator_nochk (and_then p1 p2))
= fun input ->
  let (v1, off1) = ps1 input in
  let input2 = S.advance_slice input off1 in
  let off2 = ps2 v1 input2 in
  (U32.add off1 off2 <: consumed_slice_length input)

#set-options "--z3rlimit 32"

[@"substitute"]
inline_for_extraction
let validate_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (v1: stateful_validator p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (v2: stateful_validator p2)
: Tot (stateful_validator (nondep_then p1 p2))
= fun input ->
  match v1 input with
  | Some off -> begin
	  let s2 = S.advance_slice input off in
          match v2 s2 with
          | Some off' ->
	    Some (U32.add off off' <: consumed_slice_length input)
          | None -> None
    end
  | None -> None

[@"substitute"]
inline_for_extraction
let validate_nondep_then_nochk
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (v1: stateful_validator_nochk p1)
  (#t2: Type0)
  (#k2: parser_kind)
  (#p2: parser k2 t2)
  (v2: stateful_validator_nochk p2)
: Tot (stateful_validator_nochk (nondep_then p1 p2))
= fun s1 ->
  let off1 = v1 s1 in
  let s2 = S.advance_slice s1 off1 in
  let off2 = v2 s2 in
  (U32.add off1 off2 <: consumed_slice_length s1)

[@"substitute"]
inline_for_extraction
let parse_nondep_then_nochk
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (v1: parser_st_nochk p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2)
  (v2: parser_st_nochk p2)
: Tot (parser_st_nochk (nondep_then p1 p2))
= fun s1 ->
  let (x1, off1) = v1 s1 in
  let s2 = S.advance_slice s1 off1 in
  let (x2, off2) = v2 s2 in
  ((x1, x2), (U32.add off1 off2 <: consumed_slice_length s1))

#reset-options

inline_for_extraction
val nondep_destruct
  (#k1: parser_kind)
  (#t1: Type0)
  (#p1: parser k1 t1)
  (st1: stateful_validator_nochk p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (input: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    exactly_parses h (nondep_then p1 p2) input (fun _ -> True)
  ))
  (ensures (fun h r h' ->
    S.modifies_none h h' /\ (
    let (b1, b2) = r in
    S.is_concat_gen input [b1; b2] /\
    exactly_parses h (nondep_then p1 p2) input (fun v ->
    exactly_parses h p1 b1 (fun v1 ->
    exactly_parses h p2 b2 (fun v2 ->
    v == (v1, v2)
  ))))))

#set-options "--z3rlimit 64"

let nondep_destruct #k1 #t1 #p1 st1 #k2 #t2 p2 input =
  split st1 input

#reset-options

inline_for_extraction
val serialize_copy
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (dest src: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.disjoint dest src /\
    S.live h dest /\
    U32.v (S.length dest) >= U32.v (S.length src) /\
    exactly_parses h p src (fun _ -> True)
  ))
  (ensures (fun h (destl, destr) h' ->
    U32.v (S.length dest) >= U32.v (S.length src) /\
    S.is_concat dest destl destr /\
    S.length destl == S.length src /\
    S.live h' destr /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    exactly_parses h p src (fun v ->
    exactly_parses h' p src (fun v' ->
    exactly_parses h' p destl (fun v'' ->
    v == v' /\ v' == v''
  )))))

let serialize_copy #k #t p dest src =
  let len = S.length src in
  let destl = S.truncate_slice dest len in
  let destr = S.advance_slice dest len in
  B.blit (S.as_buffer src) 0ul (S.as_buffer destl) 0ul len ;
  (destl, destr)

val serialize_nondep_then_correct
  (#k1: strong_parser_kind)
  (#t1: Type0)
  (p1: parser (ParserStrong k1) t1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (b b1 b2: S.bslice)
  (h: HS.mem)
: Lemma
  (requires (
    S.is_concat b b1 b2 /\
    exactly_parses h p1 b1 (fun _ -> True) /\
    exactly_parses h p2 b2 (fun _ -> True)
  ))
  (ensures (
    exactly_parses h p1 b1 (fun v1 ->
    exactly_parses h p2 b2 (fun v2 ->
    exactly_parses h (nondep_then p1 p2) b (fun v ->
    v == (v1, v2)
  )))))

#set-options "--z3rlimit 256"

let serialize_nondep_then_correct #k1 #t1 p1 #k2 #t2 p2 b b1 b2 h =
  assert (no_lookahead_on p1 (S.as_seq h b1) (S.as_seq h b));
  assert (injective_postcond p1 (S.as_seq h b1) (S.as_seq h b))

#reset-options

inline_for_extraction
val serialize_nondep_then
  (#k1: strong_parser_kind)
  (#t1: Type0)
  (p1: parser (ParserStrong k1) t1)
  (#k2: parser_kind)
  (#t2: Type0)
  (p2: parser k2 t2)
  (dest src1 src2: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    S.disjoint dest src1 /\
    S.disjoint dest src2 /\
    S.live h dest /\
    U32.v (S.length dest) >= U32.v (S.length src1) + U32.v (S.length src2) /\
    exactly_parses h p1 src1 (fun _ -> True) /\
    exactly_parses h p2 src2 (fun _ -> True)
  ))
  (ensures (fun h (destl, destr) h' ->
    U32.v (S.length dest) >= U32.v (S.length src1) + U32.v (S.length src2) /\
    S.is_concat dest destl destr /\
    S.length destl == U32.add (S.length src1) (S.length src2) /\
    S.live h' destr /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    exactly_parses h p1 src1 (fun v1 ->
    exactly_parses h p2 src2 (fun v2 ->
    exactly_parses h' p1 src1 (fun v1' ->
    exactly_parses h' p2 src2 (fun v2' ->
    exactly_parses h' (nondep_then p1 p2) destl (fun v ->
    v1 == v1' /\ v2 == v2' /\ v == (v1, v2)
  )))))))

#set-options "--z3rlimit 256 --smtencoding.elim_box true"

let serialize_nondep_then #k1 #t1 p1 #k2 #t2 p2 dest src1 src2 =
  let h = HST.get () in
  let len1 = S.length src1 in
  let len2 = S.length src2 in
  let len = U32.add len1 len2 in
  let destl = S.truncate_slice dest len in
  let destr = S.advance_slice dest len in
  let (dest1, dest2) = serialize_copy p1 destl src1 in
  let (d2, _) = serialize_copy p2 dest2 src2 in
  assert (d2 == dest2);
  let h' = HST.get () in
  serialize_nondep_then_correct p1 p2 destl dest1 dest2 h';
  (destl, destr)

#reset-options

#set-options "--z3rlimit 32"

[@"substitute"]
inline_for_extraction
let validate_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser k t1)
  (v1: stateful_validator p1)
  (f2: (t1 -> Tot t2) {
    forall (x x' : t1) . f2 x == f2 x' ==> x == x'  
  })
: Tot (stateful_validator (parse_synth p1 f2))
= fun (b: S.bslice) -> v1 b

#reset-options

[@"substitute"]
inline_for_extraction
let validate_synth_nochk
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser k t1)
  (v1: stateful_validator_nochk p1)
  (f2: (t1 -> Tot t2) {
    forall (x x' : t1) . f2 x == f2 x' ==> x == x'  
  })
: Tot (stateful_validator_nochk (parse_synth p1 f2))
= fun b -> v1 b

[@"substitute"]
inline_for_extraction
let parse_synth_st_nochk
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (#p1: parser k t1)
  (ps1: parser_st_nochk p1)
  (f2: (t1 -> Tot t2) { // Tot necessary here
    forall (x x' : t1) . f2 x == f2 x' ==> x == x'  
  } )
: Tot (parser_st_nochk (parse_synth p1 f2))
= fun b ->
  let (v1, len) = ps1 b in
  (f2 v1, len)

val serialize_synth_correct
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (p1: parser k t1)
  (f2: t1 -> Tot t2)
  (b: S.bslice)
  (h: HS.mem)
: Lemma
  (requires (
    (forall (x x' : t1) . f2 x == f2 x' ==> x == x') /\
    exactly_parses h p1 b (fun _ -> True)
  ))
  (ensures (
    (forall (x x' : t1) . f2 x == f2 x' ==> x == x') /\
    exactly_parses h p1 b (fun v1 ->
    exactly_parses h (parse_synth p1 f2) b (fun v2 ->
    v2 == f2 v1
  ))))

let serialize_synth_correct #k #t1 #t2 p1 f2 b h = ()

inline_for_extraction
let validate_constant_size_nochk
  (#k: constant_size_parser_kind)
  (sz: U32.t)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize (U32.v sz) k)) t)
: Tot (stateful_validator_nochk p)
= fun input -> 
    let h = HST.get () in
    assert (let s = S.as_seq h input in Some? (p s));
    (sz <: consumed_slice_length input)

inline_for_extraction
let validate_total_constant_size
  (sz: U32.t)
  (#t: Type0)
  (p: parser (ParserStrong (StrongConstantSize (U32.v sz) ConstantSizeTotal)) t)
: Tot (stateful_validator p)
= fun s ->
  if U32.lt (S.length s) sz
  then None
  else begin
    let h = HST.get () in
    assert (let s' = S.as_seq h s in Some? (parse p s'));
    Some (sz <: consumed_slice_length s)
  end

inline_for_extraction
let parse_total_constant_size_nochk
  (sz: U32.t)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize (U32.v sz) ConstantSizeTotal)) t)
  (ps: (
    (input: S.bslice) ->
    HST.Stack t
    (requires (fun h ->
      U32.v (S.length input) >= U32.v sz /\
      S.live h input
    ))
    (ensures (fun h0 v h1 ->
      U32.v (S.length input) >= U32.v sz /\
      S.live h1 input /\
      S.modifies_none h0 h1 /\ (
      let x = S.as_seq h1 input in
      let y = p x in
      Some? y /\ (
      let (Some (v', _)) = y in
      v == v'
  ))))))
: Tot (parser_st_nochk p)
= fun s ->
  let sz : consumed_slice_length s = sz in
  (ps s, sz)

inline_for_extraction
let parse_total_constant_size
  (sz: U32.t)
  (#t: Type0)
  (#p: parser (ParserStrong (StrongConstantSize (U32.v sz) ConstantSizeTotal)) t)
  (ps: (parser_st_nochk p))
: Tot (parser_st p)
= fun s ->
  if U32.lt (S.length s) sz
  then None
  else Some (ps s)

val parse_filter_implies
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (f1: (t -> Tot bool))
  (f2: (t -> Tot bool))
  (s: bytes)
: Lemma
  (requires (
    let v1 = parse (parse_filter p f1) s in
    Some? v1 /\ (
    let (Some (x1, _)) = v1 in
    f2 x1 == true
  )))
  (ensures (
    let v1 = parse (parse_filter p f1) s in
    let v2 = parse (parse_filter p f2) s in
    Some? v1 /\
    Some? v2 /\ (
    let (Some (x1, consumed1)) = v1 in
    let (Some (x2, consumed2)) = v2 in
    ((x1 <: t) == (x2 <: t)) /\
    consumed1 == consumed2
  )))

let parse_filter_implies #k #t p f1 f2 s =
  let (Some (x1, consumed1)) = parse (parse_filter p f1) s in
  let v = parse p s in
  assert (Some? v);
  let (Some (x, consumed)) = v in
  assert ((x1 <: t) == x);
  assert (consumed1 == consumed);
  assert (f2 x1 == true);
  let s' : bytes = Seq.slice s consumed (Seq.length s) in
  assert (Some? (parse (parse_filter_payload f2 x1) s'));
  assert (Some? (parse (parse_filter p f2) s));
  ()

#set-options "--z3rlimit 32"

let stateful_filter_validator
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (f: (t -> Tot bool))
: Tot Type0
= (v2: (
    (b: S.bslice) ->
    HST.Stack bool
    (requires (fun h ->
      S.live h b /\ (
      let s = S.as_seq h b in (
      Some? (p s)
    ))))
    (ensures (fun h0 r h1 ->
      S.live h0 b /\
      S.live h1 b /\
      S.modifies_none h0 h1 /\ (
      let s = S.as_seq h0 b in
      let v' = p s in (
      Some? v' /\ (
      let (Some (w, _)) = v' in (
      r == f w
  ))))))))

inline_for_extraction
let validate_filter
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v1: stateful_validator p)
  (#f: (t -> Tot bool))
  (v2: stateful_filter_validator p f)
: Tot (stateful_validator (parse_filter p f))
= fun b ->
    let r1 = v1 b in
    if Some? r1
    then
      let r2 = v2 b in
      if r2
      then r1
      else None
    else None

#reset-options

#set-options "--z3rlimit 16"

inline_for_extraction
let validate_filter_nochk
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v1: stateful_validator_nochk p)
  (f: (t -> Tot bool))
: Tot (stateful_validator_nochk (parse_filter p f))
= fun (b: S.bslice) -> v1 b

inline_for_extraction
let validate_filter_st
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (ps: parser_st p)
  (f: (t -> Tot bool))
  (f': ((x: t) -> Pure bool (requires True) (ensures (fun y -> y == f x)))) // checker MUST be total here (we do have a stateful parser)
: Tot (stateful_validator (parse_filter p f))
= fun input ->
  match ps input with
  | Some (v, off) ->
    if f' v
    then Some off
    else None
  | _ -> None

inline_for_extraction
let validate_filter_st'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (ps: parser_st p)
  (f: (t -> Tot bool))
: Tot (stateful_validator (parse_filter p f))
= validate_filter_st ps f (fun (x: t) -> f x)

inline_for_extraction
let parse_filter_st
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (ps: parser_st p)
  (f: (t -> Tot bool)) // checker MUST be total here (we do have a stateful parser)
: Tot (parser_st (parse_filter p f))
= fun input ->
  match ps input with
  | Some (v, off) ->
    if f v
    then
      let (v: t { f v == true } ) = v in
      Some (v, off)
    else None
  | _ -> None

inline_for_extraction
let parse_filter_st_nochk
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (ps: parser_st_nochk p)
  (f: (t -> Tot bool))
: Tot (parser_st_nochk (parse_filter p f))
= fun (input: S.bslice) ->
  let (x, off) = ps input in
  let (x: t { f x == true } ) = x in
  (x, off)

inline_for_extraction
let parse_filter_st'
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (ps: parser_st p)
  (f: (t -> Tot bool))
  (f' : ((x: t) -> Tot (y: bool { y == f x } )))
: Tot (parser_st (parse_filter p f))
= fun (input: S.bslice) ->
  match ps input with
  | Some (v, off) ->
    if f' v
    then
      let (v: t { f v == true } ) = v in
      Some (v, off)
    else None
  | _ -> None

#reset-options

inline_for_extraction
let validate_if
  (#t: Type0)
  (p: bare_parser t)
: Tot (if_combinator (stateful_validator p))
= fun
  (cond: bool)
  (sv_true: (cond_true cond -> Tot (stateful_validator p)))
  (sv_false: (cond_false cond -> Tot (stateful_validator p)))
  input ->
  if cond
  then sv_true () input
  else sv_false () input
