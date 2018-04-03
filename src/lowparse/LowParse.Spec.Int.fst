module LowParse.Spec.Int

module Aux = LowParse.Spec.Int.Aux
module Seq = FStar.Seq
module E = LowParse.BigEndian
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

let parse_u8 = Aux.parse_u8

let parse_u8_spec = Aux.parse_u8_spec

let parse_u8_spec_error #err e b = ()

let serialize_u8 = Aux.serialize_u8

let parse_u16 = Aux.parse_u16

let parse_u16_spec = Aux.parse_u16_spec

let parse_u16_spec_error #err e b = ()

let serialize_u16 = Aux.serialize_u16

let parse_u32 = Aux.parse_u32

let parse_u32_spec = Aux.parse_u32_spec

let parse_u32_spec_error #err e b = ()

let serialize_u32 = Aux.serialize_u32
