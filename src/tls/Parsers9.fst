module Parsers9
open Parsers.ProtocolVersion
open Parsers.CipherSuite
open Parsers.TicketContents9

module HS = FStar.HyperStack
module LP = LowParse.Low
module LPT = LowParse.SLow.Tac.Enum
module LPB = LowParse.Spec.Bytes
module U32 = FStar.UInt32
module LPI = LowParse.Spec.Int

friend Parsers.ProtocolVersion
friend Parsers.CipherSuite
friend Parsers.TicketContents9

val valid_ticketContents12_intro'
  (h: HS.mem)
  (input: LP.slice)
  (pos: U32.t)
: Lemma
  (requires (
    LP.valid protocolVersion_parser h input pos /\ (
    let pos1 = LP.get_valid_pos protocolVersion_parser h input pos in
    LP.valid cipherSuite_parser h input pos1 /\ (
    let pos2 = LP.get_valid_pos cipherSuite_parser h input pos1 in
    LP.valid LPI.parse_u32 h input pos2 /\ (
    let pos3 = LP.get_valid_pos LPI.parse_u32 h input pos2 in
    LP.valid (LPB.parse_flbytes 48) h input pos3
  )))))
  (ensures (
    let pos1 = LP.get_valid_pos protocolVersion_parser h input pos in
    let pos2 = LP.get_valid_pos cipherSuite_parser h input pos1 in
    let pos3 = LP.get_valid_pos LPI.parse_u32 h input pos2 in
    let pos4 = LP.get_valid_pos (LPB.parse_flbytes 48) h input pos3 in
    LP.valid_content_pos ticketContents9_parser h input pos
      ({
        pv = LP.contents protocolVersion_parser h input pos;
        Parsers.TicketContents9.cs = LP.contents cipherSuite_parser h input pos1;
        ems = LP.contents LPI.parse_u32 h input pos2;
        master_secret = LP.contents (LPB.parse_flbytes 48) h input pos3;
      })
      pos4
  ))

let allow_inversion_tuple2 (t1 t2: Type) : Lemma (inversion (tuple2 t1 t2)) [SMTPat (tuple2 t1 t2)] = allow_inversion (tuple2 t1 t2)

#reset-options "--z3rlimit 128 --z3refresh --log_queries --query_stats --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let valid_ticketContents12_intro' h input pos =
  LP.valid_synth h ticketContents9'_parser synth_ticketContents9 input pos;
  LP.valid_nondep_then h (protocolVersion_parser `LP.nondep_then` cipherSuite_parser `LP.nondep_then` LPI.parse_u32) ticketContents9_master_secret_parser input pos;
  LP.valid_nondep_then h (protocolVersion_parser `LP.nondep_then` cipherSuite_parser) LPI.parse_u32 input pos;
  LP.valid_nondep_then h protocolVersion_parser cipherSuite_parser input pos
