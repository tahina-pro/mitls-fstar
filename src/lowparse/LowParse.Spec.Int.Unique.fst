module LowParse.Spec.Int.Unique

module Aux = LowParse.Spec.Int.Aux
module I = LowParse.Spec.Int
module Seq = FStar.Seq

open LowParse.Spec.Base

let le_refl (x y: int) : Lemma (requires (x <= y /\ y <= x)) (ensures (x == y)) = ()

let parse_u8_unique
  (#err: Type0)
  (e: err)
  (b: bytes)
: Lemma
  (parse (Aux.parse_u8 e) b == parse (I.parse_u8 e) b)
= if Seq.length b < 1
  then begin
    I.parse_u8_spec_error e b
  end
  else begin
    I.parse_u8_spec e b;
    Aux.parse_u8_spec e b;
    let (Correct (vI, consumedI)) = parse (I.parse_u8 e) b in
    let (Correct (vAux, consumedAux)) = parse (Aux.parse_u8 e) b in
    le_refl consumedI 1;
    le_refl consumedAux 1;
    ()
  end

module U8 = FStar.UInt8

let serialize_u8_unique
  (#err: Type0)
  (e: err)
  (x: U8.t)
: Lemma
  (serialize (Aux.serialize_u8 e) x == serialize (I.serialize_u8 e) x)
= Classical.forall_intro (parse_u8_unique e);
  let s : serializer (I.parse_u8 e) = serialize_ext (Aux.parse_u8 e) (Aux.serialize_u8 e) (I.parse_u8 e) in
  serializer_unique (I.parse_u8 e) (I.serialize_u8 e) s x

let parse_u16_unique
  (#err: Type0)
  (e: err)
  (b: bytes)
: Lemma
  (parse (Aux.parse_u16 e) b == parse (I.parse_u16 e) b)
= if Seq.length b < 2
  then begin
    I.parse_u16_spec_error e b
  end
  else begin
    I.parse_u16_spec e b;
    Aux.parse_u16_spec e b;
    let (Correct (vI, consumedI)) = parse (I.parse_u16 e) b in
    let (Correct (vAux, consumedAux)) = parse (Aux.parse_u16 e) b in
    le_refl consumedI 2;
    le_refl consumedAux 2;
    ()
  end

module U16 = FStar.UInt16

let serialize_u16_unique
  (#err: Type0)
  (e: err)
  (x: U16.t)
: Lemma
  (serialize (Aux.serialize_u16 e) x == serialize (I.serialize_u16 e) x)
= Classical.forall_intro (parse_u16_unique e);
  let s : serializer (I.parse_u16 e) = serialize_ext (Aux.parse_u16 e) (Aux.serialize_u16 e) (I.parse_u16 e) in
  serializer_unique (I.parse_u16 e) (I.serialize_u16 e) s x

let parse_u32_unique
  (#err: Type0)
  (e: err)
  (b: bytes)
: Lemma
  (parse (Aux.parse_u32 e) b == parse (I.parse_u32 e) b)
= if Seq.length b < 4
  then begin
    I.parse_u32_spec_error e b
  end
  else begin
    I.parse_u32_spec e b;
    Aux.parse_u32_spec e b;
    let (Correct (vI, consumedI)) = parse (I.parse_u32 e) b in
    let (Correct (vAux, consumedAux)) = parse (Aux.parse_u32 e) b in
    le_refl consumedI 4;
    le_refl consumedAux 4;
    ()
  end

module U32 = FStar.UInt32

let serialize_u32_unique
  (#err: Type0)
  (e: err)
  (x: U32.t)
: Lemma
  (serialize (Aux.serialize_u32 e) x == serialize (I.serialize_u32 e) x)
= Classical.forall_intro (parse_u32_unique e);
  let s : serializer (I.parse_u32 e) = serialize_ext (Aux.parse_u32 e) (Aux.serialize_u32 e) (I.parse_u32 e) in
  serializer_unique (I.parse_u32 e) (I.serialize_u32 e) s x
