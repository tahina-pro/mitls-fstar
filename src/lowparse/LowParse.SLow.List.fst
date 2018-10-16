module LowParse.SLow.List
include LowParse.Low.List
include LowParse.SLow.Combinators

module U32 = FStar.UInt32
module CL = C.Loops

#set-options "--z3rlimit 16"

module L = FStar.List.Tot

let rec parse_list_tailrec'
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
  (aux: list t)
: GTot (option (list t))
  (decreases (Seq.length b))
= if Seq.length b = 0
  then 
    Some (L.rev aux)
  else
    match parse p b with
    | None -> None
    | Some (v, n) ->
      if n = 0
      then None (* elements cannot be empty *)
      else
	parse_list_tailrec' p (Seq.slice b n (Seq.length b)) (v :: aux)

let list_append_rev_cons
  (#t: Type)
  (v: t) 
  (aux l: list t)
: Lemma (L.append (L.rev (v ::aux)) l == L.append (L.rev aux) (v :: l))
= L.rev_rev' (v :: aux);
  L.rev_rev' aux;
  L.append_assoc (L.rev aux) [v] l

let rec parse_list_tailrec'_correct'
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
  (aux: list t)
: Lemma
  (requires True)
  (ensures (
    parse_list_tailrec' p b aux == (
    match parse (parse_list p) b with
    | Some (l, n) -> Some (L.append (L.rev aux) l)
    | None -> None
  )))
  (decreases (Seq.length b))
= if Seq.length b = 0
  then
    L.append_l_nil (L.rev aux)
  else
    match parse p b with
    | None -> ()
    | Some (v, n) ->
      if n = 0
      then ()
      else begin
	let s = Seq.slice b n (Seq.length b) in
	parse_list_tailrec'_correct' p s (v :: aux);
	match parse (parse_list p) (s) with
	| Some (l, n') ->
          list_append_rev_cons v aux l
        | None -> ()
      end

let parse_list_tailrec'_correct
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (b: bytes)
: Lemma
  begin match parse (parse_list p) (b) with
  | Some (l, n) -> parse_list_tailrec' p b [] == Some l
  | None -> parse_list_tailrec' p b [] == None
  end
= parse_list_tailrec'_correct' p b []

let list_rev_inv
  (#t: Type)
  (l: list t)
  (b: bool)
  (x: list t * list t)
: GTot Type0
= let (rem, acc) = x in
  L.rev l == L.rev_acc rem acc /\
  (b == false ==> rem == [])

inline_for_extraction
noextract
let list_rev
  (#t: Type)
  (l: list t)
: Tot (l' : list t { l' == L.rev l } )
= match l with
  | [] -> []
  | _ ->
    let (_, l') =
      CL.total_while
        (fun (rem, _) -> L.length rem)
        (list_rev_inv l)
        (fun (rem, acc) ->
          match rem with
          | [] -> (false, (rem, acc))
          | a :: q -> (true, (q, a :: acc))
        )
        (l, [])
    in
    l'

module B = LowStar.Buffer
module HS = FStar.HyperStack
module I32 = FStar.Int32
module U8 = FStar.UInt8
module G = FStar.Ghost

let parse_list_tailrec_inv
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (input: B.buffer U8.t)
  (len: I32.t)
  (aux: B.pointer (I32.t * list t))
  (h0: G.erased HS.mem)
  (h: HS.mem)
  (b: bool)
: GTot Type0
= B.disjoint aux input /\
  B.modifies (B.loc_buffer aux) (G.reveal h0) h /\
  B.live (G.reveal h0) aux /\
  B.live (G.reveal h0) input /\ (
  let sinput = B.as_seq (G.reveal h0) input in
  Some? (parse_list_tailrec' p sinput []) /\
  I32.v len == B.length input /\ (
    match Seq.index (B.as_seq h aux) 0 with
    | (idx', accu') ->
      I32.v idx' >= 0 /\
      I32.v idx' <= B.length input /\
      parse_list_tailrec' p sinput [] == parse_list_tailrec' p (Seq.slice sinput (I32.v idx') (B.length input)) accu' /\
      (b == true ==> I32.v idx' == B.length input)
  ))

module HST = FStar.HyperStack.ST
module Cast = FStar.Int.Cast

inline_for_extraction
let parse_list_tailrec_body
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (input: B.buffer U8.t)
  (len: I32.t)
  (aux: B.pointer (I32.t * list t))
  (h0: G.erased HS.mem)
: HST.Stack bool
  (requires (fun h -> parse_list_tailrec_inv p input len aux h0 h false))
  (ensures (fun h stop h' ->
    parse_list_tailrec_inv p input len aux h0 h false /\
    parse_list_tailrec_inv p input len aux h0 h' stop
  ))
= let x : (I32.t * list t) = B.index aux 0ul in
  let (idx', accu') = x in
  if idx' = len
  then true
  else
    let len' = I32.sub len idx' in 
    let input' = B.sub input (Cast.int32_to_uint32 idx') (Cast.int32_to_uint32 len') in
    begin match p32 input' len' with
    | (v, consumed) ->
      B.upd aux 0ul (idx' `I32.add` consumed, v :: accu'); 
      false
    end

inline_for_extraction
let parse_list_tailrec
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
  (input: B.buffer U8.t)
  (len: I32.t)
: HST.Stack (list t)
  (requires (fun h -> 
    B.live h input /\
    I32.v len == B.length input /\
    Some? (parse_list_tailrec' p (B.as_seq h input) [])
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    B.live h' input /\
    parse_list_tailrec' p (B.as_seq h input) [] == Some res
  ))
= HST.push_frame ();
  let aux : B.pointer (I32.t * list t) = B.alloca (0l, []) 1ul in
  let h0 = G.hide (HST.get ()) in
  C.Loops.do_while
    (parse_list_tailrec_inv p input len aux h0)
    (fun () -> parse_list_tailrec_body p32 input len aux h0)
    ;
  let (_, res) = B.index aux 0ul in
  HST.pop_frame ();
  list_rev res

inline_for_extraction
let parse32_list
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (p32: parser32 p)
: Tot (parser32 (parse_list p))
= fun input len ->
    let h = HST.get () in
    parse_list_tailrec'_correct p (B.as_seq h input);
    parse_list_bare_consumed p (B.as_seq h input);
    let res = parse_list_tailrec p32 input len in
    (res, len)

let serialize32_list_inv
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (s: serializer p)
  (input: list t)
  (output: buffer8)
  (len: I32.t)
  (lo: I32.t)
  (aux: B.pointer (I32.t * G.erased (list t) * list t))
  (h0 h1: G.erased HS.mem)
  (h: HS.mem)
  (stop: bool)
: GTot Type0
= serialize_list_precond k /\
  B.disjoint output aux /\
  B.live (G.reveal h0) output /\
  B.live (G.reveal h1) output /\
  B.live h output /\
  B.live (G.reveal h1) aux /\
  B.live h aux /\
  I32.v len == B.length output /\
  I32.v lo <= B.length output /\ (
  let (hi, hd, tl) = B.get h aux 0 in
  B.modifies B.loc_none (G.reveal h0) (G.reveal h1) /\
  B.modifies (B.loc_union (loc_ibuffer output lo hi) (B.loc_buffer aux)) (G.reveal h1) h /\
  input == G.reveal hd `L.append` tl /\
  contains_valid_serialized_data_or_fail h (serialize_list _ s) output lo (G.reveal hd) hi /\
  (stop == true ==> (
    contains_valid_serialized_data_or_fail h (serialize_list _ s) output lo input hi
  )))

inline_for_extraction
let serialize32_list_body
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (s: serializer p)
  (s32: serializer32 s)
  (input: list t)
  (output: buffer8)
  (len: I32.t)
  (lo: I32.t)
  (aux: B.pointer (I32.t * G.erased (list t) * list t))
  (h0 h1: G.erased HS.mem)
: HST.Stack bool
  (requires (fun h -> serialize32_list_inv p s input output len lo aux h0 h1 h false))
  (ensures (fun h stop h' ->
    serialize32_list_inv p s input output len lo aux h0 h1 h false /\
    serialize32_list_inv p s input output len lo aux h0 h1 h' stop
  ))
= let (mi, hd, tl) = B.index aux 0ul in
  match tl with
  | [] ->
    L.append_l_nil (G.reveal hd);
    true
  | x :: tl' ->
    let hi = s32 output len mi x in
    let hd' = G.hide (L.append (G.reveal hd) [x]) in
    B.upd aux 0ul (hi, hd', tl');
    let h = HST.get () in
    L.append_assoc (G.reveal hd) [x] tl' ;
    contains_valid_serialized_data_or_fail_nil h s output hi;
    contains_valid_serialized_data_or_fail_cons h s output mi x hi [] hi;
    contains_valid_serialized_data_or_fail_append h s output lo (G.reveal hd) mi [x] hi;
    if hi `I32.lt` 0l
    then begin
      contains_valid_serialized_data_or_fail_neg_intro h (serialize_list _ s) output hi tl' hi;
      contains_valid_serialized_data_or_fail_append h s output lo (G.reveal hd') hi tl' hi;
      true
    end else begin
      false
    end

inline_for_extraction
let serialize32_list
  (#t: Type0)
  (#k: parser_kind)
  (p: parser k t)
  (s: serializer p)
  (s32: serializer32 s)
  (u: unit {
    serialize_list_precond k
  })
: Tot (serializer32 (serialize_list p s))
= fun output (len: I32.t { I32.v len == B.length output } ) lo input ->
  if lo `I32.lt` 0l
  then begin
    let h = HST.get () in
    contains_valid_serialized_data_or_fail_neg_intro h (serialize_list _ s) output lo input lo;
    lo
  end else begin
    let h = HST.get () in
    contains_valid_serialized_data_or_fail_nil h s output lo;
    let h0 = G.hide h in
    HST.push_frame ();
    let h05 = HST.get () in
    B.fresh_frame_modifies h h05;
    let aux : B.pointer (I32.t * G.erased (list t) * list t) = B.alloca (lo, G.hide [], input) 1ul in
    let h1 = G.hide (HST.get ()) in
    C.Loops.do_while
      (serialize32_list_inv _ s input output len lo aux h0 h1)
      (fun () -> serialize32_list_body _ s s32 input output len lo aux h0 h1)
      ;
    let (hi, _, _) = B.index aux 0ul in
    let h2 = HST.get () in
    HST.pop_frame ();
    let h3 = HST.get () in
    B.popped_modifies h2 h3;
    hi
  end

let size32_list_inv
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s)
  (u: unit {
    serialize_list_precond k
  })
  (input: list t)
  (continue: bool)
  (accu: (U32.t * list t))
: GTot Type0
= let (len, rem) = accu in
  let sz = Seq.length (serialize (serialize_list p s) input) in
  if continue
  then
    U32.v len < U32.v u32_max /\
    sz == U32.v len + Seq.length (serialize (serialize_list p s) rem)
  else
    size32_postcond (serialize_list p s) input len

let size32_list_measure
  (#t: Type0)
  (accu: (U32.t * list t))
: GTot nat
= let (_, rem) = accu in
  L.length rem

inline_for_extraction
let size32_list_body
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s)
  (u: unit {
    serialize_list_precond k
  })
  (input: list t)
: (x: (U32.t * list t)) ->
  Pure (bool * (U32.t * list t))
  (requires (size32_list_inv s32 u input true x))
  (ensures (fun (continue, y) ->
    size32_list_inv s32 u input continue y /\
    (continue == true ==> size32_list_measure y < size32_list_measure x)
  ))
= fun accu ->
  let (len, rem) = accu in
  match rem with
    | [] -> (false, accu)
    | a :: q ->
      let sza = s32 a in
      let len' = add_overflow len sza in
      if len' = u32_max
      then (false, (u32_max, []))
      else (true, (len', q))

inline_for_extraction
let size32_list
  (#t: Type0)
  (#k: parser_kind)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s)
  (u: unit {
    serialize_list_precond k
  })
: Tot (size32 (serialize_list p s))
= fun input ->
  [@inline_let]
  let (len, _) =
    CL.total_while
      size32_list_measure
      (size32_list_inv s32 u input)
      (fun x -> size32_list_body s32 u input x)
      (0ul, input)
  in
  (len <: (len : U32.t { size32_postcond (serialize_list p s) input len } ))
