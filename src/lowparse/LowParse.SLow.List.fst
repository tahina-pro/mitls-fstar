module LowParse.SLow.List
include LowParse.Spec.List
include LowParse.SLow.Combinators

module B32 = FStar.Bytes
module U32 = FStar.UInt32
module CL = C.Loops

#set-options "--z3rlimit 16 --max_fuel 8 --max_ifuel 8"

module L = FStar.List.Tot

let rec parse_list_tailrec'
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (p32: parser32 p)
  (u: unit { k.parser_kind_low > 0 } )
  (b: bytes32)
  (aux: list t)
: GTot (result (list t) err)
  (decreases (B32.length b))
= if B32.len b = 0ul
  then 
    Correct (L.rev aux)
  else
    match p32 b with
    | Error e -> Error e
    | Correct (v, n) ->
	parse_list_tailrec' p32 u (B32.slice b n (B32.len b)) (v :: aux)

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
  (#err: Type0)
  (#p: parser k t err)
  (p32: parser32 p)
  (u: unit { k.parser_kind_low > 0 } )
  (b: bytes32)
  (aux: list t)
: Lemma
  (requires True)
  (ensures (
    parse_list_tailrec' p32 u b aux == (
    match parse (parse_list p u) (B32.reveal b) with
    | Correct (l, n) -> Correct (L.append (L.rev aux) l)
    | Error e -> Error e
  )))
  (decreases (B32.length b))
= if B32.len b = 0ul
  then
    L.append_l_nil (L.rev aux)
  else
    match p32 b with
    | Error e -> ()
    | Correct (v, n) ->
      begin
	let s = B32.slice b n (B32.len b) in
	parse_list_tailrec'_correct' p32 u s (v :: aux);
	match parse (parse_list p u) (B32.reveal s) with
	| Correct (l, n') ->
          list_append_rev_cons v aux l
        | Error e -> ()
      end

let parse_list_tailrec'_correct
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (p32: parser32 p)
  (u: unit { k.parser_kind_low > 0 } )
  (b: bytes32)
: Lemma
  begin match parse (parse_list p u) (B32.reveal b) with
  | Correct (l, n) -> parse_list_tailrec' p32 u b [] == Correct l
  | Error e -> parse_list_tailrec' p32 u b [] == Error e
  end
= parse_list_tailrec'_correct' p32 u b []

let list_rev_inv
  (#t: Type)
  (l: list t)
  (b: bool)
  (x: list t * list t)
: GTot Type0
= let (rem, acc) = x in
  L.rev l == L.rev_acc rem acc /\
  (b == false ==> rem == [])

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

let parse_list_tailrec_inv
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (p32: parser32 p)
  (u: unit { k.parser_kind_low > 0 } )
  (input: bytes32)
  (b: bool)
  (x: result (bytes32 * list t) err)
: GTot Type0
= match x with
  | Correct (input', accu') ->
    parse_list_tailrec' p32 u input [] == parse_list_tailrec' p32 u input' accu' /\
    (b == false ==> B32.length input' == 0)
  | Error e -> 
    b == false /\ parse_list_tailrec' p32 u input [] == Error e

let parse_list_tailrec_measure
  (#t: Type0)
  (#err: Type0)
  (x: result (bytes32 * list t) err)
: GTot nat
= match x with
  | Error _ -> 0
  | Correct (input', _) -> B32.length input'

inline_for_extraction
let parse_list_tailrec_body
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (p32: parser32 p)
  (u: unit { k.parser_kind_low > 0 } )
  (input: bytes32)
: (x: result (bytes32 * list t) err) ->
  Pure (bool * result (bytes32 * list t) err)
  (requires (parse_list_tailrec_inv p32 u input true x))
  (ensures (fun (continue, y) ->
    parse_list_tailrec_inv p32 u input continue y /\
    (if continue then parse_list_tailrec_measure y < parse_list_tailrec_measure x else True)
  ))
= fun (x: result (bytes32 * list t) err) ->
  let (Correct (input', accu')) = x in
  let len = B32.len input' in
  if len = 0ul
  then (false, x)
  else
    match p32 input' with
    | Correct (v, consumed) ->
        let input'' = B32.slice input' consumed len in
        (true, Correct (input'', v :: accu'))
    | Error e -> (false, Error e)

inline_for_extraction
let parse_list_tailrec
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (p32: parser32 p)
  (u: unit { k.parser_kind_low > 0 } )
  (input: bytes32)
: Tot (res: result (list t) err { res == parse_list_tailrec' p32 u input [] } )
= let accu =
    CL.total_while
      (parse_list_tailrec_measure #t #err)
      (parse_list_tailrec_inv p32 u input)
      (fun x -> parse_list_tailrec_body p32 u input x)
      (Correct (input, []))
  in
  match accu with
  | Error e -> Error e
  | Correct (_, accu') -> Correct (list_rev accu')

inline_for_extraction
let parse32_list
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (p32: parser32 p)
  (u: unit { k.parser_kind_low > 0 } )
: Tot (parser32 (parse_list p u))
= fun (input: bytes32) -> ((
    parse_list_tailrec'_correct p32 u input;
    match parse_list_tailrec p32 u input with
    | Error e -> Error e
    | Correct res ->
      parse_list_bare_consumed p u (B32.reveal input);
      Correct (res, B32.len input)
  ) <: (res: result (list t * U32.t) err { parser32_correct (parse_list p u) input res } ))

let rec partial_serialize32_list'
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (u: unit { k.parser_kind_low > 0 } )
  (input: list t)
: Ghost bytes32
  (requires (
    serialize_list_precond k /\ (
    Seq.length (serialize (serialize_list s u) input) < 4294967296
  )))
  (ensures (fun (res: bytes32) ->
    serialize_list_precond k /\
    serializer32_correct (serialize_list s u) input res
  ))
  (decreases input)
= match input with
  | [] ->
    let res = B32.empty_bytes in
    assert (Seq.equal (B32.reveal res) (Seq.createEmpty));
    res
  | a :: q ->
    serialize_list_cons s u a q;
    let sa = s32 a in
    let sq = partial_serialize32_list' s32 u q in
    let res = B32.append sa sq in
    res

let rec partial_serialize32_list_tailrec'
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (u: unit { k.parser_kind_low > 0 } )
  (accu: bytes32)
  (input: list t)
: Ghost bytes32
  (requires (
    serialize_list_precond k /\ (
    B32.length accu + Seq.length (serialize (serialize_list s u) input) < 4294967296
  )))
  (ensures (fun (res: bytes32) ->
    serialize_list_precond k /\
    Seq.length (serialize (serialize_list s u) input) < 4294967296 /\
    B32.reveal res == Seq.append (B32.reveal accu) (B32.reveal (partial_serialize32_list' s32 u input))
  ))
  (decreases input)
= match input with
  | [] ->
    Seq.append_empty_r (B32.reveal accu);
    accu
  | a :: q ->
    serialize_list_cons s u a q;
    let sa = s32 a in
    let accu' = B32.append accu sa in
    Seq.append_assoc (B32.reveal accu) (B32.reveal sa) (B32.reveal (partial_serialize32_list' s32 u q));
    partial_serialize32_list_tailrec' s32 u accu' q

let partial_serialize32_list'_inv
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (u: unit { k.parser_kind_low > 0 } )
  (input: list t)
  (continue: bool)
  (x: bytes32 * list t)
: GTot Type0
= serialize_list_precond k /\
  Seq.length (serialize (serialize_list s u) input) < 4294967296 /\ (
    let (accu, input') = x in
    B32.length accu + Seq.length (serialize (serialize_list s u) input') < 4294967296 /\
    serializer32_correct
      (serialize_list s u)
      input
      (partial_serialize32_list_tailrec' s32 u accu input') /\
    (continue == false ==> L.length input' == 0)
  )

let partial_serialize32_list'_measure
  (#t: Type0)
  (x: bytes32 * list t)
: GTot nat
= L.length (snd x)

inline_for_extraction
let partial_serialize32_list'_body
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (u: unit { k.parser_kind_low > 0 } )
  (input: list t)
: (x: (bytes32 * list t)) ->
  Pure (bool * (bytes32 * list t))
  (requires (partial_serialize32_list'_inv s32 u input true x))
  (ensures (fun (continue, y) ->
    partial_serialize32_list'_inv s32 u input continue y /\
    (continue == true ==> partial_serialize32_list'_measure y < partial_serialize32_list'_measure x)
  ))
= fun (x: bytes32 * list t) ->
  let (accu, input') = x in
  match input' with
  | [] -> (false, x)
  | a :: q ->
    let sa = s32 a in
    let accu' = B32.append accu sa in
    (true, (accu', q))

let partial_serialize32_list'_init
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (u: unit { k.parser_kind_low > 0 } )
  (input: list t)
: Lemma
  (requires (
    serialize_list_precond k /\
    Seq.length (serialize (serialize_list s u) input) < 4294967296
  ))
  (ensures (
    partial_serialize32_list'_inv s32 u input true (B32.empty_bytes, input)
  ))
= assert (Seq.equal (B32.reveal B32.empty_bytes) Seq.createEmpty);
  Seq.append_empty_l (B32.reveal (partial_serialize32_list' s32 u input));
  assert (B32.reveal (partial_serialize32_list' s32 u input) == B32.reveal (partial_serialize32_list_tailrec' s32 u B32.empty_bytes input));
  assert (serializer32_correct (serialize_list s u) input (partial_serialize32_list_tailrec' s32 u B32.empty_bytes input))

inline_for_extraction
let partial_serialize32_list
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (u: unit {
    serialize_list_precond k
  })
: Tot (partial_serializer32 (serialize_list s ()))
= fun (input: list t { Seq.length (serialize (serialize_list s ()) input) < 4294967296 } ) -> ((
    let (res, _) =
      partial_serialize32_list'_init s32 () input;
      CL.total_while
        partial_serialize32_list'_measure
        (partial_serialize32_list'_inv s32 () input)
        (fun x -> partial_serialize32_list'_body s32 () input x)
        (B32.empty_bytes, input)
    in
    res
  ) <: (res: bytes32 { serializer32_correct (serialize_list s ()) input res }))

let size32_list_inv
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (u: unit {
    serialize_list_precond k
  })
  (input: list t)
  (continue: bool)
  (accu: (U32.t * list t))
: GTot Type0
= let (len, rem) = accu in
  let sz = Seq.length (serialize (serialize_list s ()) input) in
  if continue
  then
    U32.v len < U32.v u32_max /\
    sz == U32.v len + Seq.length (serialize (serialize_list s ()) rem)
  else
    size32_postcond (serialize_list s ()) input len

let size32_list_measure
  (#t: Type0)
  (accu: (U32.t * list t))
: GTot nat
= let (_, rem) = accu in
  L.length rem

inline_for_extraction
let size32_list_body
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: size32 s)
  (u: unit {
    serialize_list_precond k
  })
  (input: list t)
: (x: (U32.t * list t)) ->
  Pure (bool * (U32.t * list t))
  (requires (size32_list_inv s u input true x))
  (ensures (fun (continue, y) ->
    size32_list_inv s u input continue y /\
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
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: size32 s)
  (u: unit {
    serialize_list_precond k
  })
: Tot (size32 (serialize_list s ()))
= fun input ->
  [@inline_let]
  let (len, _) =
    CL.total_while
      size32_list_measure
      (size32_list_inv s u input)
      (fun x -> size32_list_body s32 u input x)
      (0ul, input)
  in
  (len <: (len : U32.t { size32_postcond (serialize_list s ()) input len } ))
