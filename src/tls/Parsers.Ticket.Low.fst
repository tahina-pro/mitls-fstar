module Parsers.Ticket.Low
open Parsers.ProtocolVersion
open Parsers.CipherSuite
open Parsers.Boolean
open Parsers.TicketContents12
open Parsers.TicketContents13
open Parsers.TicketContents

module HS = FStar.HyperStack
module LP = LowParse.Low
module LPT = LowParse.SLow.Tac.Enum
module LPB = LowParse.Spec.Bytes
module U32 = FStar.UInt32

friend Parsers.ProtocolVersion
friend Parsers.CipherSuite
friend Parsers.Boolean
friend Parsers.TicketContents12
friend Parsers.TicketContents13

let write_protocolVersion =
  lemma_synth_protocolVersion_inj ();
  lemma_synth_protocolVersion_inv ();
  LP.write_synth
    (LP.write_maybe_enum_key LP.write_u16 protocolVersion_enum (_ by (LPT.enum_repr_of_key_tac protocolVersion_enum)))
    synth_protocolVersion
    synth_protocolVersion_inv
    (fun x -> synth_protocolVersion_inv x)
    ()

let write_cipherSuite =
  lemma_synth_cipherSuite_inj ();
  lemma_synth_cipherSuite_inv ();
  LP.write_synth
    (LP.write_maybe_enum_key LP.write_u16 cipherSuite_enum (_ by (LPT.enum_repr_of_key_tac cipherSuite_enum)))
    synth_cipherSuite
    synth_cipherSuite_inv
    (fun x -> synth_cipherSuite_inv x)
    ()

let write_boolean =
  lemma_synth_boolean_inj ();
  lemma_synth_boolean_inv ();
  LP.write_synth
    (LP.write_enum_key LP.write_u8 boolean_enum (_ by (LPT.enum_repr_of_key_tac boolean_enum)))
    synth_boolean
    synth_boolean_inv
    (fun x -> synth_boolean_inv x)
    ()

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
    LP.valid boolean_parser h input pos2 /\ (
    let pos3 = LP.get_valid_pos boolean_parser h input pos2 in
    LP.valid (LPB.parse_flbytes 48) h input pos3 /\ (
    let pos4 = LP.get_valid_pos (LPB.parse_flbytes 48) h input pos3 in
    LP.valid LPI.parse_u32 h input pos4 /\ (
    let pos5 = LP.get_valid_pos LPI.parse_u32 h input pos4 in
    LP.valid LPI.parse_u32 h input pos5
  )))))))
  (ensures (
    let pos1 = LP.get_valid_pos protocolVersion_parser h input pos in
    let pos2 = LP.get_valid_pos cipherSuite_parser h input pos1 in
    let pos3 = LP.get_valid_pos boolean_parser h input pos2 in
    let pos4 = LP.get_valid_pos (LPB.parse_flbytes 48) h input pos3 in
    let pos5 = LP.get_valid_pos LPI.parse_u32 h input pos4 in
    let pos6 = LP.get_valid_pos LPI.parse_u32 h input pos5 in
    LP.valid_content_pos ticketContents12_parser h input pos
      ({
        pv = LP.contents protocolVersion_parser h input pos;
        Parsers.TicketContents12.cs = LP.contents cipherSuite_parser h input pos1;
        ems = LP.contents boolean_parser h input pos2;
        master_secret = LP.contents (LPB.parse_flbytes 48) h input pos3;
        foo1 = LP.contents LPI.parse_u32 h input pos4;
        foo2 = LP.contents LPI.parse_u32 h input pos5;
      })
      pos6
  ))

let allow_inversion_tuple2 (t1 t2: Type) : Lemma (inversion (tuple2 t1 t2)) [SMTPat (tuple2 t1 t2)] = allow_inversion (tuple2 t1 t2)

#reset-options "--z3rlimit 128 --z3refresh --log_queries --query_stats --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --using_facts_from '* -LowParse.Spec.Combinators.nondep_then'"

let valid_ticketContents12_intro' h input pos =
  synth_ticketContents12_injective ();
  LP.valid_synth h ticketContents12'_parser synth_ticketContents12 input pos;
  LP.valid_nondep_then h (protocolVersion_parser `LP.nondep_then` cipherSuite_parser `LP.nondep_then` boolean_parser `LP.nondep_then` ticketContents12_master_secret_parser `LP.nondep_then` LPI.parse_u32) LPI.parse_u32 input pos;
  LP.valid_nondep_then h (protocolVersion_parser `LP.nondep_then` cipherSuite_parser `LP.nondep_then` boolean_parser `LP.nondep_then` ticketContents12_master_secret_parser) LPI.parse_u32 input pos;
  LP.valid_nondep_then h (protocolVersion_parser `LP.nondep_then` cipherSuite_parser `LP.nondep_then` boolean_parser) ticketContents12_master_secret_parser input pos;
  LP.valid_nondep_then h (protocolVersion_parser `LP.nondep_then` cipherSuite_parser) boolean_parser input pos;
  LP.valid_nondep_then h protocolVersion_parser cipherSuite_parser input pos

// #reset-options "--z3rlimit 256 --max_ifuel 8 --initial_ifuel 8 --max_fuel 2 --z3cliopt smt.arith.nl=false --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let valid_ticketContents13_intro' h input pos =
  let cs = LP.contents cipherSuite_parser h input pos in
  let pos1 = LP.get_valid_pos cipherSuite_parser h input pos in
  let rms = LP.contents ticketContents13_rms_parser h input pos1 in
  let pos2 = LP.get_valid_pos ticketContents13_rms_parser h input pos1 in
  let nonce = LP.contents ticketContents13_nonce_parser h input pos2 in
  let pos3 = LP.get_valid_pos ticketContents13_nonce_parser h input pos2 in
  let creation_time = LP.contents LP.parse_u32 h input pos3 in
  let pos4 = LP.get_valid_pos LP.parse_u32 h input pos3 in
  let age_add = LP.contents LP.parse_u32 h input pos4 in
  let pos5 = LP.get_valid_pos LP.parse_u32 h input pos4 in
  let custom_data = LP.contents ticketContents13_custom_data_parser h input pos5 in
  let pos6 = LP.get_valid_pos ticketContents13_custom_data_parser h input pos5 in
  LP.valid_nondep_then_intro h cipherSuite_parser ticketContents13_rms_parser
  input pos;
  LP.valid_nondep_then_intro h (  cipherSuite_parser
  `LP.nondep_then` ticketContents13_rms_parser)
  ticketContents13_nonce_parser
  input pos;
  LP.valid_nondep_then_intro h (  cipherSuite_parser
  `LP.nondep_then` ticketContents13_rms_parser
  `LP.nondep_then` ticketContents13_nonce_parser
  ) LP.parse_u32
  input pos;
  LP.valid_nondep_then_intro h (  cipherSuite_parser
  `LP.nondep_then` ticketContents13_rms_parser
  `LP.nondep_then` ticketContents13_nonce_parser
  `LP.nondep_then` LP.parse_u32
  ) LP.parse_u32
  input pos;
  LP.valid_nondep_then_intro h (  cipherSuite_parser
  `LP.nondep_then` ticketContents13_rms_parser
  `LP.nondep_then` ticketContents13_nonce_parser
  `LP.nondep_then` LP.parse_u32
  `LP.nondep_then` LP.parse_u32
  ) ticketContents13_custom_data_parser input pos;
  synth_ticketContents13_injective ();
  LP.valid_synth_intro h ticketContents13'_parser synth_ticketContents13 input pos;
  assert_norm (synth_ticketContents13 (((((cs, rms), nonce), creation_time), age_add), custom_data) == ({
    cs = cs;
    rms = rms;
    nonce = nonce;
    creation_time = creation_time;
    age_add = age_add;
    custom_data = custom_data;
  }))
