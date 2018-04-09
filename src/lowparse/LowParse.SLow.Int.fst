module LowParse.SLow.Int

module Aux = LowParse.SLow.Int.Aux
module Unique = LowParse.Spec.Int.Unique
module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module B32 = FStar.Bytes

let parse32_u8 #err e =
  (fun input ->
    [@inline_let]
    let _ = Unique.parse_u8_unique e (B32.reveal input) in
    [@inline_let]
    let res : result (U8.t * U32.t) err = Aux.parse32_u8 e input in
    (res <: (res: result (U8.t * U32.t) err { parser32_correct (parse_u8 e) input res } ))
  )

let serialize32_u8 #err e =
  (fun (input: U8.t) ->
    [@inline_let]
    let _ = Unique.serialize_u8_unique e input in
    [@inline_let]
    let res : bytes32 = Aux.serialize32_u8 e input in
    (res <: (res: bytes32 { serializer32_correct (serialize_u8 e) input res } )))

let parse32_u16 #err e =
  (fun input ->
    [@inline_let]
    let _ = Unique.parse_u16_unique e (B32.reveal input) in
    [@inline_let]
    let res : result (U16.t * U32.t) err = Aux.parse32_u16 e input in
    (res <: (res: result (U16.t * U32.t) err { parser32_correct (parse_u16 e) input res } ))
  )

let serialize32_u16 #err e =
  (fun (input: U16.t) ->
    [@inline_let]
    let _ = Unique.serialize_u16_unique e input in
    [@inline_let]
    let res : bytes32 = Aux.serialize32_u16 e input in
    (res <: (res: bytes32 { serializer32_correct (serialize_u16 e) input res } )))

let parse32_u32 #err e =
  (fun input ->
    [@inline_let]
    let _ = Unique.parse_u32_unique e (B32.reveal input) in
    [@inline_let]
    let res : result (U32.t * U32.t) err = Aux.parse32_u32 e input in
    (res <: (res: result (U32.t * U32.t) err { parser32_correct (parse_u32 e) input res } ))
  )

let serialize32_u32 #err e =
  (fun (input: U32.t) ->
    [@inline_let]
    let _ = Unique.serialize_u32_unique e input in
    [@inline_let]
    let res : bytes32 = Aux.serialize32_u32 e input in
    (res <: (res: bytes32 { serializer32_correct (serialize_u32 e) input res } )))
