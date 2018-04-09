module LowParse.SLow.Enum
include LowParse.Spec.Enum
include LowParse.SLow.Combinators

module L = FStar.List.Tot
module U32 = FStar.UInt32

(* Parser for enums *)

let maybe_enum_key_of_repr'_t
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot Type0
= (x: repr) ->
  Tot (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } )

#set-options "--z3rlimit 32"

inline_for_extraction
let enum_tail'
  (#key #repr: eqtype)
  (e: enum key repr)
: Pure (enum key repr)
  (requires True)
  (ensures (fun y -> Cons? e ==> (let (_ :: y') = e in y == y')))
= match e with _ :: y -> y | _ -> []

inline_for_extraction
let maybe_enum_key_of_repr'_t_cons_nil
  (#key #repr: eqtype)
  (e: enum key repr)
: Pure (maybe_enum_key_of_repr'_t e)
  (requires (Cons? e /\ Nil? (enum_tail' e)))
  (ensures (fun _ -> True))
= (fun (e' : list (key * repr) { e' == e } ) -> match e' with
  | [(k, r)] ->
    (fun x -> ((
      if r = x
      then Known k
      else Unknown x
    ) <: (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } ))))
    e

inline_for_extraction
let maybe_enum_key_of_repr'_t_cons
  (#key #repr: eqtype)
  (e: enum key repr )
  (g : maybe_enum_key_of_repr'_t (enum_tail' e))
: Pure (maybe_enum_key_of_repr'_t e)
  (requires (Cons? e))
  (ensures (fun _ -> True))
= (fun (e' : list (key * repr) { e' == e } ) -> match e' with
     | (k, r) :: _ ->
     (fun x -> ((
        if r = x
        then Known k
        else
        let y : maybe_enum_key (enum_tail' e) = g x in
        match y with
        | Known k' -> Known (k' <: key)
        | Unknown x' -> Unknown x
      ) <: (k: maybe_enum_key e { k == maybe_enum_key_of_repr e x } ))))
      e

#reset-options

inline_for_extraction
let parse32_maybe_enum_key_gen
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#err: Type0)
  (#p: parser k repr err)
  (p32: parser32 p)
  (e: enum key repr)
  (#k' : parser_kind)
  (p' : parser k' (maybe_enum_key e) err)
  (u: unit {
    k' == k /\
    p' == parse_maybe_enum_key p e
  })
  (f: maybe_enum_key_of_repr'_t e)
: Tot (parser32 p')
= parse32_synth p (maybe_enum_key_of_repr e) f p32 ()

#set-options "--z3rlimit 64 --max_fuel 16 --max_ifuel 16"

inline_for_extraction
let parse32_enum_key_gen
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#err: Type0)
  (p: parser k repr err)
  (e: enum key repr)
  (e_key_invalid: err)
  (#k' : parser_kind)
  (p' : parser k' (enum_key e) err)
  (u: unit {
    k' == parse_filter_kind k /\
    p' == parse_enum_key p e e_key_invalid
  })
  (pe: parser32 (parse_maybe_enum_key p e))
: Tot (parser32 p')
= (fun (input: bytes32) -> ((
    match pe input with
    | Correct (k, consumed) ->
      begin match k with
      | Known k' -> Correct (k', consumed)
      | _ -> Error e_key_invalid
      end
    | Error e' -> Error e'
  ) <: (res: result (enum_key e * U32.t) err { parser32_correct (parse_enum_key p e e_key_invalid) input res } )))

#reset-options

let enum_repr_of_key'_t
  (#key #repr: eqtype)
  (e: enum key repr)
: Tot Type0
= (x: enum_key e) ->
  Tot (r: enum_repr e { r == enum_repr_of_key e x } )

inline_for_extraction
let serialize32_enum_key_gen
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#err: Type0)
  (#p: parser k repr err)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
  (e_key_invalid: err)
  (#k' : parser_kind)
  (#p' : parser k' (enum_key e) err)
  (s' : serializer p')
  (u: unit {
    k' == parse_filter_kind k /\
    p' == parse_enum_key p e e_key_invalid /\
    s' == serialize_enum_key p s e e_key_invalid
  })
  (f: enum_repr_of_key'_t e)
: Tot (serializer32 s')
= fun (input: enum_key e) -> ((s32 (f input)) <: (r: bytes32 { serializer32_correct (serialize_enum_key p s e e_key_invalid) input r } ))

inline_for_extraction
let enum_repr_of_key_cons
  (#key #repr: eqtype)
  (e: enum key repr)
  (f : enum_repr_of_key'_t (enum_tail' e))
: Pure (enum_repr_of_key'_t e)
  (requires (Cons? e))
  (ensures (fun _ -> True))
= (fun (e' : list (key * repr) { e' == e } ) -> match e' with
     | (k, r) :: _ ->
     (fun (x: enum_key e) -> (
      if k = x
      then (r <: repr)
      else (f (x <: key) <: repr)
     ) <: (r: enum_repr e { enum_repr_of_key e x == r } )))
     e

inline_for_extraction
let enum_repr_of_key_cons_nil
  (#key #repr: eqtype)
  (e: enum key repr)
: Pure (enum_repr_of_key'_t e)
  (requires (Cons? e /\ Nil? (enum_tail' e)))
  (ensures (fun _ -> True))
= (fun (e' : list (key * repr) { e' == e } ) -> match e' with
     | [(k, r)] ->
     (fun (x: enum_key e) ->
      (r <: (r: enum_repr e { enum_repr_of_key e x == r } ))))
     e

inline_for_extraction
let serialize32_maybe_enum_key_gen'
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#err: Type0)
  (#p: parser k repr err)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
  (e_key_invalid: err)
  (f: serializer32 (serialize_enum_key p s e e_key_invalid))
: Tot (serializer32 (serialize_maybe_enum_key p s e))
= fun (input: maybe_enum_key e) -> ((
    match input with
    | Known k -> f k
    | Unknown r -> s32 r
   ) <: (r: bytes32 { serializer32_correct (serialize_maybe_enum_key p s e) input r } ))

inline_for_extraction
let serialize32_maybe_enum_key_gen
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#err: Type0)
  (#p: parser k repr err)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
  (e_dummy: err)
  (#k' : parser_kind)
  (#p' : parser k' (maybe_enum_key e) err)
  (s' : serializer p')
  (u: unit {
    k == k' /\
    p' == parse_maybe_enum_key p e /\
    s' == serialize_maybe_enum_key p s e
  })
  (f: enum_repr_of_key'_t e)
: Tot (serializer32 s')
= serialize32_maybe_enum_key_gen' s32 e e_dummy
    (serialize32_enum_key_gen s32 e e_dummy (serialize_enum_key _ s e e_dummy) () f)
