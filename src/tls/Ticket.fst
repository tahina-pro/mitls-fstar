module Ticket

open FStar.Bytes
open FStar.Error

open Mem
open Parse
open TLSError
open TLSConstants
open TLSInfo

module AE = AEADProvider

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("TCK| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if DebugFlags.debug_NGO then print else (fun _ -> ())

// verification-only
type hostname = string
type tlabel (h:hostname) = t:bytes * tls13:bool

noextract
private let region:rgn = new_region tls_tables_region

noeq
type ticket_key =
  | Key: i:AE.id -> wr:AE.writer i -> rd:AE.reader i -> ticket_key

private let dummy_id (a:aeadAlg) : St AE.id =
  assume false;
  let h = Hashing.Spec.SHA256 in
  let li = LogInfo_CH0 ({
    li_ch0_cr = Bytes.create 32ul 0z;
    li_ch0_ed_psk = empty_bytes;
    li_ch0_ed_ae = a;
    li_ch0_ed_hash = h;
  }) in
  let log : hashed_log li = empty_bytes in
  ID13 (KeyID #li (ExpandedSecret (EarlySecretID (NoPSK h)) ApplicationTrafficSecret log))

// The ticket encryption key is a module global, but it must be lazily initialized
// because the RNG may not yet be seeded when kremlinit_globals is called
private let ticket_enc : reference (option ticket_key) = ralloc region None

// Sealing key (for client-side sealing, e.g. of session local state)
private let sealing_enc : reference (option ticket_key) = ralloc region None

private let keygen () : St ticket_key =
  let id0 = dummy_id EverCrypt.CHACHA20_POLY1305 in
  let salt : AE.salt id0 = Random.sample (AE.iv_length id0) in
  let key : AE.key id0 = Random.sample (AE.key_length id0) in
  let wr = AE.coerce id0 region key salt in
  let rd = AE.genReader region #id0 wr in
  Key id0 wr rd

let get_ticket_key () : St ticket_key =
  match !ticket_enc with
  | Some k -> k
  | None ->
    let k = keygen () in
    ticket_enc := Some k; k

let get_sealing_key () : St ticket_key =
  match !sealing_enc with
  | Some k -> k
  | None ->
    let k = keygen () in
    sealing_enc := Some k; k

private let set_internal_key (sealing:bool) (a:aeadAlg) (kv:bytes) : St bool =
  let tid = dummy_id a in
  if length kv = AE.key_length tid + AE.iv_length tid then
    let k, s = split_ kv (AE.key_length tid) in
    let wr = AE.coerce tid region k s in
    let rd = AE.genReader region wr in
    let _ =
      if sealing then
        sealing_enc := Some (Key tid wr rd)
      else
        ticket_enc := Some (Key tid wr rd)
      in
    true
  else false

let set_ticket_key (a:aeadAlg) (kv:bytes) : St bool =
  set_internal_key false a kv

let set_sealing_key (a:aeadAlg) (kv:bytes) : St bool =
  set_internal_key true a kv

// TODO absolute bare bone for functionality
// We should expand with certificates, mode, etc
type ticket =
  // 1.2 ticket
  | Ticket12:
    pv: protocolVersion ->
    cs: cipherSuite{CipherSuite? cs} ->
    ems: bool ->
    msId: msId ->
    ms: bytes ->
    ticket
  // 1.3 RMS PSK
  | Ticket13:
    cs: cipherSuite{CipherSuite13? cs} ->
    li: logInfo ->
    rmsId: pre_rmsId li ->
    rms: bytes ->
    nonce: bytes ->
    ticket_created: UInt32.t ->
    ticket_age_add: UInt32.t ->
    custom: bytes ->
    ticket

// Currently we use dummy indexes until we can serialize them properly
let dummy_rmsid (ae: aeadAlg) (h: hash_alg): (li: logInfo & rmsId li) =
  let li: logInfo_SH = {
    li_sh_cr = Bytes.create 32ul 0z;
    li_sh_sr = Bytes.create 32ul 0z;
    li_sh_ae = ae;
    li_sh_hash = h;
    li_sh_psk = None;
  } in
  let li_cf: logInfo_CF = {
    li_cf_sf = ({ li_sf_sh = li; li_sf_certificate = None; });
    li_cf_certificate = None;
  } in
  let li: logInfo = LogInfo_CF li_cf in
  let log : hashed_log li = empty_bytes in
  let i : rmsId li = RMSID (ASID (Salt (EarlySecretID (NoPSK h)))) log in
  (| li, i |)

// Dummy msId TODO serialize and encrypt them properly
let dummy_msId pv cs ems =
  StandardMS PMS.DummyPMS (Bytes.create 64ul 0z) (kefAlg pv cs ems)

// not pure because of trace, but should be
let parse (b:bytes) (nonce:bytes) : St (option ticket) =
  trace ("Parsing ticket "^(hex_of_bytes b));
  if length b < 8 then None
  else
    let (pvb, r) = split b 2ul in
    match parseVersion pvb with
    | Error _ -> None
    | Correct pv ->
      let (csb, r) = split r 2ul in
      let csn = parseCipherSuiteName csb in
      match cipherSuite_of_name csn with // FIXME: move to check_ticket. Needs to be disentangled with dummy_rmsid, dummy_msId
      | None -> None
      | Some cs ->
        match pv, cs with
        | TLS_1p3, CipherSuite13 ae h ->
         begin
          let created, r = split r 4ul in
          let age_add, r = split r 4ul in
          match vlsplit 2 r with
          | Error _ -> None
          | Correct (custom, rms) ->
            match vlparse 2 rms with
            | Error _ -> None
            | Correct rms ->
              let (| li, rmsId |) = dummy_rmsid ae h in
              let age_add = uint32_of_bytes age_add in
              let created = uint32_of_bytes created in
              Some (Ticket13 cs li rmsId rms nonce created age_add custom)
         end
        | _ , CipherSuite _ _ _ ->
         begin
          let (emsb, ms) = split r 1ul in
          match vlparse 2 ms with
          | Error _ -> None
          | Correct rms ->
            let ems = 0z <> emsb.[0ul] in
            let msId = dummy_msId pv cs ems in
            Some (Ticket12 pv cs ems msId ms)
         end
        | _ -> None

let ticket_decrypt (seal:bool) cipher : St (option bytes) =
  let Key tid _ rd = if seal then get_sealing_key () else get_ticket_key () in
  let salt = AE.salt_of_state rd in
  let (nb, b) = split_ cipher (AE.iv_length tid) in
  let plain_len = length b - AE.taglen tid in
  let iv = AE.coerce_iv tid (xor_ #(AE.iv_length tid) nb salt) in
  AE.decrypt #tid #plain_len rd iv empty_bytes b

let check_ticket (seal:bool) (b:bytes{length b <= 65551}) : St (option ticket) =
  trace ("Decrypting ticket "^(hex_of_bytes b));
  let Key tid _ rd = get_ticket_key () in
  if length b < AE.iv_length tid + AE.taglen tid + 8 (*was: 32*) 
  then None 
  else match ticket_decrypt seal b with
    | None -> trace ("Ticket decryption failed."); None
    | Some plain ->
      let nonce, _ = split b 12ul in
      parse plain nonce

(* BEGIN added by hand *)

module LL = LowParse.Low.Base

val ticketContents_validator32: LL.validator32 ticketContents_parser

val ticketContents_access_tag: LL.accessor ticketContents_parser ticketVersion_parser (fun x y -> y == tag_of_ticketContents x)

val ticketContents_access_contents12: LL.accessor ticketContents_parser ticketContents12_parser (fun x y -> match x with Case_ticket12 y' -> y == y' | _ -> True)

val ticketContents_access_contents13: LL.accessor ticketContents_parser ticketContents13_parser (fun x y -> match x with Case_ticket13 y' -> y == y' | _ -> True)

module HST = FStar.HyperStack.ST

val ticketContents_contents12 (base: LL.slice) (off: U32.t) : HST.Stack unit
  (requires (fun h ->
    U32.v off < 4294967295 /\
    LL.valid h base (U32.add off 1ul) ticketContents12_parser))
  (ensures (fun h _ h' ->
    B.modifies (B.gsub base off (U32.sub (B.len base) off)) h h' /\
    LL.valid h' base off ticketContents_parser /\
    LL.contents h' base off ticketContents_parser == Case_ticket12 (LL.contents h base (U32.add off 1ul) ticketContents12_parser)
  ))

(* END added by hand *)

val serialize
  (out: slice)
  (pos: U32.t { pos <= out.len })
  (t: ticketContents)
: HST.Stack (result pos)
  (requires (fun h -> live_slice h out))
  (ensures (fun h res h' ->
    B.modifies (loc_slice_from out pos) h h' /\
    live_slice h' out /\
    match res with
    | Correct pos' ->

      valid_contents_len h' out pos ticketContents_serializer t pos'
(* defined as unfold valid_contents_len = 
      valid h' out pos ticketContents_parser /\
      contents h' out pos ticketContents_parser == t /\
      U32.v pos + content_length h' out pos ticketContents_serializer == U32.v pos'
// length (serialize ticketContent_serializer (contents h' out pos ticketContents_parser))
*)
    | Error _ ->
      U32.v pos + size ticketContents_serializer t > U32.v out.len
// length (serialize ticketContents_serializer t)
  ))

let serialize (out: slice) pos = function
  | Case_ticket12 t12 ->
(*  
    (versionBytes pv) @| (cipherSuiteNameBytes (name_of_cipherSuite cs))
    @| abyte (if ems then 1z else 0z) @| (vlbytes 2 ms)
*)

    

    if out.len - pos < 1 + ticketContents12_len then
      Error "cannot serialize ticket12"
    else begin
      let pos1 = U32.add pos 1ul in
(* By hand *)
      let pos2 = protocolVersion_serializer32 out pos1 t12.pv in
      let pos3 = cipherSuite_serializer32 out pos2 t12.cs in
      let pos4 = bool_serializer32 out pos3 t12.ems in
      let pos5 = LP.serialize32_flbytes 48ul out pos4 t12.master_secret in
      ticketContents12_serialize_lemma out pos1;
(* Using default emitter *)
      push_frame();
      let tmp = alloca 0uy 48ul in
      store_bytes t12.ms tmp;
      let pos5 = emit_ticketContents12 out pos1 t12.pv t12.cs t12.ems tmp in
      pop_frame();
      
      ticketContents_contents12 out pos pos5
    end

  | Case_ticket13 t13 ->
    if out.len - pos < 1 then
      Error "cannot serialize ticket13 tag"
    else begin
      let pos1 = U32.add pos 1ul in
      push_frame ();
      let tmp_vl_rms = vlbuffer_of_bytes 32ul 255ul t13.rms in
      let tmp_vl_nonce = vlbuffer_of_bytes 0ul 255ul t13.nonce in
      let tmp_vl_custom_data = vlbuffer_of_bytes 0ul 65535ul t13.custom_data in
      let pos2 = emit_ticketContents13 out pos1 t13.cs tmp_vl_rms tmp_vl_nonce t13.creation_time t13.age_add tmp_vl_custom_data in
      pop_frame ();
      if pos2 = max_uint32
      then max_uint32
      else ticketContents_contents13 out pos pos2
    end
    

    (versionBytes TLS_1p3) @| (cipherSuiteNameBytes (name_of_cipherSuite cs))
    @| (bytes_of_int32 created) @| (bytes_of_int32 age)
    @| (vlbytes 2 custom) @| (vlbytes 2 rms)

let ticket_encrypt (seal:bool) plain : St bytes =
  let Key tid wr _ = if seal then get_sealing_key () else get_ticket_key () in
  let nb = Random.sample (AE.iv_length tid) in
  let salt = AE.salt_of_state wr in
  let iv = AE.coerce_iv tid (xor 12ul nb salt) in
  let ae = AE.encrypt #tid #(length plain) wr iv empty_bytes plain in
  nb @| ae

let create_ticket (seal:bool) t =
  let plain = serialize t in
  let len_t = ticketContents_size32 t in
  assert (len_t < max_int); // ticketContents_parser_kind
  push_frame ();
  let out = alloca 0uy len_t in
  let res = serialize ({ base = out; len = len_t; }) 0ul t in
  assert (res == len_t);
  let plain = FStar.Bytes.of_buffer len_t out in
  pop_frame ();
  ticket_encrypt seal plain


let create_cookie (hrr:HandshakeMessages.hrr) (digest:bytes) (extra:bytes) =
  let hrm = HandshakeMessages.HelloRetryRequest hrr in
  let hrb = vlbytes 3 (HandshakeMessages.handshakeMessageBytes None hrm) in
  let plain = hrb @| (vlbytes 1 digest) @| (vlbytes 2 extra) in
  let cipher = ticket_encrypt false plain in
  trace ("Encrypting cookie: "^(hex_of_bytes plain));
  trace ("Encrypted cookie:  "^(hex_of_bytes cipher));
  cipher

val check_cookie: b:bytes -> St (option (HandshakeMessages.hrr * bytes * bytes))
let check_cookie b =
  trace ("Decrypting cookie "^(hex_of_bytes b));
  if length b < 32 then None else
  match ticket_decrypt false b with
  | None -> trace ("Cookie decryption failed."); None
  | Some plain ->
    trace ("Plain cookie: "^(hex_of_bytes plain));
    match vlsplit 3 plain with
    | Error _ -> trace ("Cookie decode error: HRR"); None
    | Correct (hrb, b) ->
      let (_, hrb) = split hrb 4ul in // Skip handshake tag and vlbytes 3
      match HandshakeMessages.parseHelloRetryRequest hrb with
      | Error (_, m) -> trace ("Cookie decode error: parse HRR, "^m); None
      | Correct hrr ->
        match vlsplit 1 b with
        | Error _ -> trace ("Cookie decode error: digest"); None
        | Correct (digest, b) ->
          match vlparse 2 b with
          | Error _ -> trace ("Cookie decode error: application data"); None
          | Correct extra ->
            Some (hrr, digest, extra)

let ticket_pskinfo (t:ticket) =
  match t with
  | Ticket13 cs li _ _ nonce created age_add custom ->
    let CipherSuite13 ae h = cs in
    Some ({
      ticket_nonce = Some nonce;
      time_created = created;
      ticket_age_add = age_add;
      allow_early_data = true;
      allow_dhe_resumption = true;
      allow_psk_resumption = true;
      early_ae = ae;
      early_hash = h;
      identities = (empty_bytes, empty_bytes);
    })
  | _ -> None

let check_ticket13 b =
  match check_ticket false b with
  | Some t -> ticket_pskinfo t
  | _ -> None

let check_ticket12 b =
  match check_ticket false b with
  | Some (Ticket12 pv cs ems msId ms) -> Some (pv, cs, ems, msId, ms)
  | _ -> None
