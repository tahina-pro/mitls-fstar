module LowParse.SLow.Combinators
include LowParse.SLow.Base
include LowParse.Spec.Combinators

module B32 = FStar.Bytes
module U32 = FStar.UInt32

#reset-options "--z3rlimit 16 --max_fuel 8 --max_ifuel 8"

inline_for_extraction
let parse32_ret
  (#t: Type)
  (#err: Type0)
  (x: t)
: Tot (parser32 (parse_ret x))
= (fun input -> ((Correct (x, 0ul)) <: (res: result (t * U32.t) err { parser32_correct (parse_ret x) input res } )))

inline_for_extraction
let parse32_and_then
  (#k: parser_kind)
  (#t:Type)
  (#err: Type0)
  (#p:parser k t err)
  (p32: parser32 p)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t' err)))
  (u: unit { and_then_cases_injective p' } )
  (p32' : ((x: t) -> Tot (parser32 (p' x))))
: Tot (parser32 (p `and_then` p'))
= fun (input: bytes32) ->
  ((match p32 input with
  | Correct (v, l) ->
    let input' = B32.slice input l (B32.len input) in
    begin match p32' v input' with
    | Correct (v', l') ->
      Correct (v', U32.add l l')
    | Error e -> Error e
    end
  | Error e -> Error e
  ) <: (res: result (t' * U32.t) err { parser32_correct (p `and_then` p') input res } ))

inline_for_extraction
let parse32_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#err: Type0)
  (#p1: parser k1 t1 err)
  (p1' : parser32 p1)
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2 err)
  (p2' : parser32 p2)
: Tot (parser32 (nondep_then p1 p2))
= fun (input: bytes32) ->
  ((match p1' input with
  | Correct (v, l) ->
    let input' = B32.slice input l (B32.len input) in
    begin match p2' input' with
    | Correct (v', l') ->
      Correct ((v, v'), U32.add l l')
    | Error e -> Error e
    end
  | Error e -> Error e
  ) <: (res: result ((t1 * t2) * U32.t) err { parser32_correct (p1 `nondep_then` p2) input res } ))

let serialize32_kind_precond
  (k1 k2: parser_kind)
: GTot bool
= Some? k1.parser_kind_high &&
  Some? k2.parser_kind_high &&
  Some?.v k1.parser_kind_high + Some?.v k2.parser_kind_high < 4294967296

inline_for_extraction
let serialize32_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#err: Type0)
  (#p1: parser k1 t1 err)
  (#s1: serializer p1)
  (s1' : serializer32 s1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2 err)
  (#s2: serializer p2)
  (s2' : serializer32 s2)
  (u' : unit {
    serialize32_kind_precond k1 k2
  })
: Tot (serializer32 (serialize_nondep_then p1 s1 u p2 s2))
= fun (input: t1 * t2) ->
  match input with
  | (fs, sn) ->
    let output1 = s1' fs in
    let output2 = s2' sn in
  ((B32.append output1 output2) <:
    (res: bytes32 { serializer32_correct (serialize_nondep_then p1 s1 u p2 s2) input res } ))

inline_for_extraction
let parse32_strengthen
  (#k: parser_kind)
  (#t1: Type0)
  (#err: Type0)
  (#p1: parser k t1 err)
  (p1' : parser32 p1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Tot (parser32 (parse_strengthen p1 p2 prf))
= fun (xbytes: bytes32) -> ((
  match p1' xbytes with
  | Correct (x, consumed) ->
    [@inline_let]
    let _ = prf (B32.reveal xbytes) (U32.v consumed) x in
    [@inline_let]
    let (x' : t1 { p2 x' } ) = x in
    Correct (x', consumed)
  | Error e -> Error e
  ) <: (res: result ((x: t1 { p2 x}) * U32.t) err { parser32_correct (parse_strengthen p1 p2 prf) xbytes res } ))

inline_for_extraction
let parse32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (#err: Type0)
  (p1: parser k t1 err)
  (f2: t1 -> GTot t2)
  (f2': (x: t1) -> Tot (y: t2 { y == f2 x } )) 
  (p1' : parser32 p1)
  (u: unit {
    synth_injective f2
  })
: Tot (parser32 (parse_synth p1 f2))
= fun (input: bytes32) ->
  ((
    match p1' input with
    | Correct (v1, consumed) -> Correct (f2' v1, consumed)
    | Error e -> Error e
   ) <: (res: result (t2 * U32.t) err { parser32_correct (parse_synth p1 f2) input res } ))

inline_for_extraction
let serialize32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (#err: Type0)
  (p1: parser k t1 err)
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
= fun (input: t2) ->
    let x = g1' input in
    (s1' x <: (res: bytes32 { serializer32_correct (serialize_synth p1 f2 s1 g1 u) input res } ))

inline_for_extraction
let parse32_filter
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (p32: parser32 p)
  (f: (t -> GTot bool))
  (e: err)
  (g: ((x: t) -> Tot (b: bool { b == f x } )))
: Tot (parser32 (parse_filter p f e))
= fun (input: bytes32) ->
  ((
    match p32 input with
    | Correct (v, consumed) ->
      if g v
      then
        [@inline_let]
        let (v' : t { f v' == true } ) = v in
	Correct (v', consumed)
      else
        Error e
    | Error e' -> Error e'
  ) <: (res: result ((v': t { f v' == true } ) * U32.t) err { parser32_correct (parse_filter p f e) input res } ))

inline_for_extraction
let serialize32_filter
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: serializer32 s)
  (f: (t -> GTot bool))
  (e: err)
: Tot (serializer32 (serialize_filter s f e))
= fun (input: t { f input == true } ) -> s32 input

inline_for_extraction
let make_total_constant_size_parser32
  (sz: nat)
  (sz' : U32.t { U32.v sz' == sz } )
  (#t: Type0)
  (#err: Type0)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (t)))
  (e: err)
  (u: unit {
    make_total_constant_size_parser_precond sz t f
  })
  (f' : ((s: B32.lbytes sz) -> Tot (y: t { y == f (B32.reveal s) } )))
: Tot (parser32 (make_total_constant_size_parser sz t _ f e))
= fun (input: bytes32) -> ((
    if U32.lt (B32.len input) sz'
    then Error e
    else
      let s' = B32.slice input 0ul sz' in
      Correct (f' s', sz')
  ) <: (res: result (t * U32.t) err { parser32_correct (make_total_constant_size_parser sz t _ f e) input res } ))

inline_for_extraction
let size32_nondep_then
  (#k1: parser_kind)
  (#t1: Type0)
  (#err: Type0)
  (#p1: parser k1 t1 err)
  (#s1: serializer p1)
  (s1' : size32 s1)
  (u: unit { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type0)
  (#p2: parser k2 t2 err)
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
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: size32 s)
  (f: (t -> GTot bool))
  (e: err)
: Tot (size32 (serialize_filter s f e))
= fun x -> s32 x

inline_for_extraction
let size32_synth
  (#k: parser_kind)
  (#t1: Type0)
  (#t2: Type0)
  (#err: Type0)
  (p1: parser k t1 err)
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
