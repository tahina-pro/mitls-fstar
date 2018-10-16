module LowParse.SLow.Int

module SC = LowParse.SLow.Combinators
module L = LowParse.Low.Int
module Seq = FStar.Seq
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

let parse32_u8 = SC.parser32_of_constant_low_parser32 L.parse32_u8 1l () 

let serialize32_u8 = L.serialize32_u8_fail

let parse32_u16 = SC.parser32_of_constant_low_parser32 L.parse32_u16 2l ()

let serialize32_u16 = L.serialize32_u16_fail

let parse32_u32 = SC.parser32_of_constant_low_parser32 L.parse32_u32 4l ()

let serialize32_u32 = L.serialize32_u32_fail
