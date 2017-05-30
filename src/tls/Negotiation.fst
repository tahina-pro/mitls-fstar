(*--build-config
options:--fstar_home ../../../FStar --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection --use_hints --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../hacl-star/secure_api/LowCProvider/fst --include ../../../kremlin/kremlib --include ../../../hacl-star/specs --include ../../../hacl-star/code/lib/kremlin --include ../../../hacl-star/code/bignum --include ../../../hacl-star/code/experimental/aesgcm --include ../../../hacl-star/code/poly1305 --include ../../../hacl-star/code/salsa-family --include ../../../hacl-star/secure_api/test --include ../../../hacl-star/secure_api/utils --include ../../../hacl-star/secure_api/vale --include ../../../hacl-star/secure_api/uf1cma --include ../../../hacl-star/secure_api/prf --include ../../../hacl-star/secure_api/aead --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ../../src/tls/ideal-flags;
--*)
module Negotiation

open Platform.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open HandshakeMessages

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MR = FStar.Monotonic.RRef

//16-05-31 these opens are implementation-only; overall we should open less
open Extensions
open CoreCrypto

(**
  Debugging flag.
  F* normalizer will erase debug prints at extraction when set to false.
*)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("NGO| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if Flags.debug_NGO then print else (fun _ -> ())


//17-05-01 relocate these printing functions?!
let string_of_option_extensions (o: option extensions) = match o with
  | None -> "None"
  | Some es -> "[ "^Extensions.string_of_extensions es^"]"

let string_of_ciphersuite (cs:cipherSuite) =
  match name_of_cipherSuite cs with
  | Correct TLS_NULL_WITH_NULL_NULL -> "TLS_NULL_WITH_NULL_NULL"

  | Correct TLS_AES_128_GCM_SHA256 -> "TLS_AES_128_GCM_SHA256"
  | Correct TLS_AES_256_GCM_SHA384 -> "TLS_AES_256_GCM_SHA384"
  | Correct TLS_CHACHA20_POLY1305_SHA256 -> "TLS_CHACHA20_POLY1305_SHA256"
  | Correct TLS_AES_128_CCM_SHA256 -> "TLS_AES_128_CCM_SHA256"
  | Correct TLS_AES_128_CCM_8_SHA256 -> "TLS_AES_128_CCM_8_SHA256"

  | Correct TLS_RSA_WITH_NULL_MD5 -> "TLS_RSA_WITH_NULL_MD5"
  | Correct TLS_RSA_WITH_NULL_SHA -> "TLS_RSA_WITH_NULL_SHA"
  | Correct TLS_RSA_WITH_NULL_SHA256 -> "TLS_RSA_WITH_NULL_SHA256"
  | Correct TLS_RSA_WITH_RC4_128_MD5 -> "TLS_RSA_WITH_RC4_128_MD5"
  | Correct TLS_RSA_WITH_RC4_128_SHA -> "TLS_RSA_WITH_RC4_128_SHA"
  | Correct TLS_RSA_WITH_3DES_EDE_CBC_SHA -> "TLS_RSA_WITH_3DES_EDE_CBC_SHA"
  | Correct TLS_RSA_WITH_AES_128_CBC_SHA -> "TLS_RSA_WITH_AES_128_CBC_SHA"
  | Correct TLS_RSA_WITH_AES_256_CBC_SHA -> "TLS_RSA_WITH_AES_256_CBC_SHA"
  | Correct TLS_RSA_WITH_AES_128_CBC_SHA256 -> "TLS_RSA_WITH_AES_128_CBC_SHA256"
  | Correct TLS_RSA_WITH_AES_256_CBC_SHA256 -> "TLS_RSA_WITH_AES_256_CBC_SHA256"

  | Correct TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA -> "TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA"
  | Correct TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA -> "TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA"
  | Correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA -> "TLS_DHE_DSS_WITH_AES_128_CBC_SHA"
  | Correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA -> "TLS_DHE_RSA_WITH_AES_128_CBC_SHA"
  | Correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA -> "TLS_DHE_DSS_WITH_AES_256_CBC_SHA"
  | Correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA -> "TLS_DHE_RSA_WITH_AES_256_CBC_SHA"
  | Correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA256 -> "TLS_DHE_DSS_WITH_AES_128_CBC_SHA256"
  | Correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA256 -> "TLS_DHE_RSA_WITH_AES_128_CBC_SHA256"
  | Correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA256 -> "TLS_DHE_DSS_WITH_AES_256_CBC_SHA256"
  | Correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA256 -> "TLS_DHE_RSA_WITH_AES_256_CBC_SHA256"

  | Correct TLS_ECDHE_RSA_WITH_RC4_128_SHA -> "TLS_ECDHE_RSA_WITH_RC4_128_SHA"
  | Correct TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA -> "TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA"
  | Correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA -> "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA"
  | Correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256 -> "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256"
  | Correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA -> "TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA"
  | Correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384 -> "TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384"

  | Correct TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 -> "TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256"
  | Correct TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 -> "TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256"
  | Correct TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 -> "TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384"
  | Correct TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 -> "TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384"

  | Correct TLS_DH_anon_WITH_RC4_128_MD5 -> "TLS_DH_anon_WITH_RC4_128_MD5"
  | Correct TLS_DH_anon_WITH_3DES_EDE_CBC_SHA -> "TLS_DH_anon_WITH_3DES_EDE_CBC_SHA"
  | Correct TLS_DH_anon_WITH_AES_128_CBC_SHA -> "TLS_DH_anon_WITH_AES_128_CBC_SHA"
  | Correct TLS_DH_anon_WITH_AES_256_CBC_SHA -> "TLS_DH_anon_WITH_AES_256_CBC_SHA"
  | Correct TLS_DH_anon_WITH_AES_128_CBC_SHA256 -> "TLS_DH_anon_WITH_AES_128_CBC_SHA256"
  | Correct TLS_DH_anon_WITH_AES_256_CBC_SHA256 -> "TLS_DH_anon_WITH_AES_256_CBC_SHA256"

  | Correct TLS_RSA_WITH_AES_128_GCM_SHA256 -> "TLS_RSA_WITH_AES_128_GCM_SHA256"
  | Correct TLS_RSA_WITH_AES_256_GCM_SHA384 -> "TLS_RSA_WITH_AES_256_GCM_SHA384"
  | Correct TLS_DHE_RSA_WITH_AES_128_GCM_SHA256 -> "TLS_DHE_RSA_WITH_AES_128_GCM_SHA256"
  | Correct TLS_DHE_RSA_WITH_AES_256_GCM_SHA384 -> "TLS_DHE_RSA_WITH_AES_256_GCM_SHA384"
  | Correct TLS_DH_RSA_WITH_AES_128_GCM_SHA256 -> "TLS_DH_RSA_WITH_AES_128_GCM_SHA256"
  | Correct TLS_DH_RSA_WITH_AES_256_GCM_SHA384 -> "TLS_DH_RSA_WITH_AES_256_GCM_SHA384"
  | Correct TLS_DHE_DSS_WITH_AES_128_GCM_SHA256 -> "TLS_DHE_DSS_WITH_AES_128_GCM_SHA256"
  | Correct TLS_DHE_DSS_WITH_AES_256_GCM_SHA384 -> "TLS_DHE_DSS_WITH_AES_256_GCM_SHA384"
  | Correct TLS_DH_DSS_WITH_AES_128_GCM_SHA256 -> "TLS_DH_DSS_WITH_AES_128_GCM_SHA256"
  | Correct TLS_DH_DSS_WITH_AES_256_GCM_SHA384 -> "TLS_DH_DSS_WITH_AES_256_GCM_SHA384"
  | Correct TLS_DH_anon_WITH_AES_128_GCM_SHA256 -> "TLS_DH_anon_WITH_AES_128_GCM_SHA256"
  | Correct TLS_DH_anon_WITH_AES_256_GCM_SHA384 -> "TLS_DH_anon_WITH_AES_256_GCM_SHA384"

  | Correct TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 -> "TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256"
  | Correct TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 -> "TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256"
  | Correct TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256 -> "TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256"
  | Correct TLS_PSK_WITH_CHACHA20_POLY1305_SHA256 -> "TLS_PSK_WITH_CHACHA20_POLY1305_SHA256"
  | Correct TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256 -> "TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256"
  | Correct TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256 -> "TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256" | Error z -> "Unknown ciphersuite"

let string_of_signatureScheme = function
  | RSA_PKCS1_SHA256       -> "RSA_PKCS1_SHA256"
  | RSA_PKCS1_SHA384       -> "RSA_PKCS1_SHA384"
  | RSA_PKCS1_SHA512       -> "RSA_PKCS1_SHA512"
  | ECDSA_SECP256R1_SHA256 -> "ECDSA_SECP256R1_SHA256"
  | ECDSA_SECP384R1_SHA384 -> "ECDSA_SECP384R1_SHA384"
  | ECDSA_SECP521R1_SHA512 -> "ECDSA_SECP521R1_SHA512"
  | RSA_PSS_SHA256         -> "RSA_PSS_SHA256"
  | RSA_PSS_SHA384         -> "RSA_PSS_SHA384"
  | RSA_PSS_SHA512         -> "RSA_PSS_SHA512"
  //| ED25519                -> "ED25519"
  //| ED448                  -> "ED448"
  | RSA_PKCS1_SHA1         -> "RSA_PKCS1_SHA1"
  | RSA_PKCS1_MD5SHA1         -> "RSA_PKCS1_MD5SHA1"
  | ECDSA_SHA1             -> "ECDSA_SHA1"
  | DSA_SHA1               -> "DSA_SHA1"
  | DSA_SHA256             -> "DSA_SHA256"
  | DSA_SHA384             -> "DSA_SHA384"
  | DSA_SHA512             -> "DSA_SHA512"
  | OBSOLETE codepoint     -> "OBSOLETE " ^ (print_bytes codepoint)
  | PRIVATE_USE codepoint  -> "PRIVATE_USE " ^ (print_bytes codepoint)


(* Negotiation: HELLO sub-module *)
type ri = cVerifyData * sVerifyData

type resumption_offer_12 = // part of resumeInfo
  | OfferNothing
  | OfferTicket of b:bytes{ length b <> 0 }
  | OfferSid of b:bytes { length b <> 0 }
// type resumption_mode_12 (o: resumption_offer_12) = b:bool { OfferNothing? o ==> b = false }

let valid_offer ch =
  True
// There is a pure function computing a ClientHello from an offer (minus the PSK binders)
type offer = ch:HandshakeMessages.ch { valid_offer ch }

let find_client_extension filter o =
  match o.ch_extensions with
  | None -> None
  | Some es -> List.Tot.find filter es

let find_supported_versions o =
  match find_client_extension Extensions.E_supported_versions? o with
  | None -> None
  | Some (Extensions.E_supported_versions vs) -> Some vs

let find_signature_algorithms o : option signatureSchemeList =
  match find_client_extension Extensions.E_signature_algorithms? o with
  | None -> None
  | Some (Extensions.E_signature_algorithms algs) -> Some algs

// finding the pre-shared keys in ClientHello
let find_pske o =
  match find_client_extension Extensions.E_pre_shared_key? o with
  | None -> None
  | Some (Extensions.E_pre_shared_key psks) -> Some psks

let find_clientPske o =
  match find_client_extension Extensions.E_pre_shared_key? o with
  | None -> None
  | Some (Extensions.E_pre_shared_key psk) ->
    match psk with
    | ServerPSK _ -> None
    | ClientPSK ids _ -> Some ids

let find_serverPske sh =
  match sh.sh_extensions with
  | None -> None
  | Some exts ->
    match List.Tot.find E_pre_shared_key? exts with
    | Some (E_pre_shared_key (ServerPSK idx)) -> Some (UInt16.v idx)
    | _ -> None

let find_serverKeyShare sh =
  match sh.sh_extensions with
  | None -> None
  | Some exts ->
    match List.Tot.find E_key_share? exts with
    | Some (E_key_share (CommonDH.ServerKeyShare ks)) -> Some ks
    | _ -> None

// index in the list of PSKs offered by the client
type pski (o:offer) = n:nat {
  o.ch_protocol_version = TLS_1p3 /\
  (match find_clientPske o with
  | Some ids -> n < List.length ids
  | _ -> False) }

let find_supported_groups o =
  match find_client_extension Extensions.E_supported_groups? o with
  | None -> None
  | Some (Extensions.E_supported_groups gns) -> Some gns

type share = g:CommonDH.group & CommonDH.share g
type pre_share = g:CommonDH.group & CommonDH.pre_share g

let find_key_shares (o:offer)
  : Tot (option (CommonDH.clientKeyShare))
  =
  match find_client_extension Extensions.E_key_share? o with
  | Some (Extensions.E_key_share (CommonDH.ClientKeyShare ks)) -> Some ks
  | _ -> None

private let rec list_of_ClientKeyShare (ks:CommonDH.clientKeyShare)
  : Tot (list pre_share)
  =
  match ks with
  | [] -> []
  | CommonDH.Share g s :: tl -> (|g, s|) :: list_of_ClientKeyShare tl
  | CommonDH.UnknownShare _ _  :: tl -> list_of_ClientKeyShare tl

let gs_of (o:offer) : Tot (list pre_share) =
  match find_key_shares o with
  | Some ksl -> list_of_ClientKeyShare ksl
  | _ -> []

let find_early_data o =
  match find_client_extension Extensions.E_early_data? o with
  | None -> None
  | Some (Extensions.E_early_data maxl) -> Some maxl

(**
  We keep both the server's HelloRetryRequest
  and the overwritten parts of the initial offer
*)
type retryInfo (offer:offer) =
  hrr *
  list share (* we should actually keep the raw client extension content *) *
  (list (PSK.pskid * Hashing.anyTag))

(**
  The final negotiated outcome, including key shares and long-term identities.
  mode is the name used in the resilience paper;
  session_info is the one from TLSInfo
*)
noeq type mode =
  | Mode:
    n_offer: offer -> // negotiated client offer
    n_hrr: option (retryInfo n_offer) ->  // optional HRR roundtrip

    // more from SH (both TLS 1.2 and TLS 1.3)
    n_protocol_version: protocolVersion ->
    n_server_random: TLSInfo.random ->
    n_sessionID: option sessionID {n_sessionID = None <==> n_protocol_version = TLS_1p3} ->
    n_cipher_suite: cipherSuite ->

    // redundant with the server extension response?
    n_pski: option (pski n_offer) -> // only for TLS 1.3, result of a tricky stateful computation

    // concatenating SH and EE extensions for 1.3, in wire order.
    n_server_extensions: option (se:list extension{List.Tot.length se < 256}) ->

    // more from SKE in ...ServerHelloDone (1.2) or SH (1.3)
    n_server_share: option share ->

    // more from either ...ServerHelloDone (1.2) or ServerFinished (1.3)
    n_client_cert_request: option HandshakeMessages.cr ->
    n_server_cert: option Cert.chain13 ->

    // more from either CH+SH (1.3) or CKE (1.2)
    n_client_share: option share ->
    // { both shares are in the same negotiated group }
    mode

let is_resumption12 m =
  m.n_protocol_version <> TLS_1p3  &&
  m.n_sessionID = Some (m.n_offer.ch_sessionID)

let is_cacheable12 m =
  m.n_protocol_version <> TLS_1p3  &&
  ( let Some sid = m.n_sessionID in
    sid <> m.n_offer.ch_sessionID &&
    sid <> empty_bytes)

noeq type negotiationState (r:role) (cfg:config) (resume:resumeInfo r) =
  // Have C_Offer_13 and C_Offer? Shares aren't available in C_Offer yet
  | C_Init:     n_client_random: TLSInfo.random ->
                negotiationState r cfg resume

  | C_Offer:    n_offer: offer ->
                negotiationState r cfg resume

  | C_HRR:      n_offer: offer ->
                n_hrr: retryInfo n_offer ->
                negotiationState r cfg resume

  | C_WaitFinished1:
                n_partialmode: mode ->
                negotiationState r cfg resume

  | C_Mode:     n_mode: mode -> // In 1.2, used for resumption and full handshakes
                negotiationState r cfg resume

  | C_WaitFinished2: // Only 1.2
                n_mode: mode ->
                n_client_certificate: option Cert.chain13 ->
                negotiationState r cfg resume

  | C_Complete: n_mode: mode ->
                n_client_certificate: option Cert.chain13 ->
                negotiationState r cfg resume

  | S_Init:     n_server_random: TLSInfo.random ->
                negotiationState r cfg resume

  // Waiting for ClientHello2
  | S_HRR:      n_offer: offer ->
                n_hrr: hrr ->
                negotiationState r cfg resume

  | S_ClientHello: // Transitional state to allow Handshake to call KS and generate a share
                n_mode: mode -> // n_server_share and n_server_extensions are None
                negotiationState r cfg resume

  // This state is used to wait for both Finished1 and Finished2
  | S_Mode:     n_mode: mode -> // If 1.2, then client_share is None
                negotiationState r cfg resume

  | S_Complete: n_mode: mode ->
                n_client_certificate: option Cert.chain13 ->
                negotiationState r cfg resume

let ns_step (#r:role) (#cfg:config) (#resume:resumeInfo r)
  (ns:negotiationState r cfg resume) (ns':negotiationState r cfg resume) =
  match ns, ns' with
  | C_Init nonce, C_Offer offer -> nonce == offer.ch_client_random
  | C_Offer offer, C_Mode mode -> mode.n_offer == offer
  | C_Offer _, C_Complete _ _ -> True
  | C_Mode _, C_WaitFinished2 _ _ -> True
  | C_Mode _, C_Complete _ _ -> True
  | S_Init _, S_ClientHello _ -> True
  | S_ClientHello _, S_Mode _ -> True
  | _, _ -> ns == ns'

let ns_rel (#r:role) (#cfg:config) (#resume:resumeInfo r)
  (ns:negotiationState r cfg resume) (ns':negotiationState r cfg resume) =
  ns_step ns ns' \/
  (exists ns0. ns_step ns ns0 /\ ns_step ns0 ns')

assume val ns_rel_monotonic: #r:role -> #cfg:config -> #resume:resumeInfo r ->
  Lemma (MR.monotonic (negotiationState r cfg resume) (ns_rel #r #cfg #resume))

noeq type t (region:rgn) (role:TLSConstants.role) =
  | NS:
    cfg: config -> // local configuration
    resume: TLSInfo.resumeInfo role ->
    nonce: TLSInfo.random ->
    state: MR.m_rref region (negotiationState role cfg resume) ns_rel ->
    t region role

val computeOffer: r:role -> cfg:config -> resume:TLSInfo.resumeInfo r -> nonce:TLSInfo.random
  -> ks:option CommonDH.keyShare -> list (PSK.pskid * PSK.pskInfo)
  -> Tot offer
let computeOffer r cfg resume nonce ks pskinfo =
  let sid =
    match resume with
    | Some sid, _ -> sid
    | None, _ -> empty_bytes
  in
  let extensions =
    Extensions.prepareExtensions
      cfg.minVer
      cfg.maxVer
      cfg.ciphersuites
      cfg.safe_resumption
      cfg.safe_renegotiation
      cfg.enable_early_data
      cfg.signatureAlgorithms
      cfg.namedGroups
      None // : option (cVerifyData * sVerifyData)
      ks
      pskinfo
  in
  let compressions =
    match cfg.compressions with
    | [] -> [NullCompression]
    | _  -> cfg.compressions
  in
  {
    ch_protocol_version = minPV TLS_1p2 cfg.maxVer; // legacy for 1.3
    ch_client_random = nonce;
    ch_sessionID = sid;
    ch_cipher_suites = cfg.ciphersuites;
    // This file is reconstructed from ch_cipher_suites in HandshakeMessages.clientHelloBytes;
    ch_compressions = cfg.compressions;
    ch_extensions = Some extensions
  }

val create:
  region:rgn -> r:role -> cfg:config -> resume:TLSInfo.resumeInfo r -> TLSInfo.random ->
  St (t region r)
let create region r cfg resume nonce =
  match r with
  | Client ->
    let state = MR.m_alloc region (C_Init nonce) in
    NS cfg resume nonce state
  | Server ->
    let state = MR.m_alloc region (S_Init nonce) in
    NS cfg resume nonce state

// a bit too restrictive: use a single Hash in any given offer
val hashAlg: mode -> Hashing.Spec.alg
let hashAlg m = //FIXME!
  Hashing.Spec.SHA256

val kexAlg: mode -> TLSConstants.kexAlg
let kexAlg m =
  if m.n_protocol_version = TLS_1p3 then
    Kex_ECDHE // FIXME: inspect extensions
  else
    let CipherSuite kex _ _ = m.n_cipher_suite in
    kex

val aeAlg:
  m:mode{CipherSuite? m.n_cipher_suite \/ CipherSuite13? m.n_cipher_suite} ->
  TLSConstants.aeAlg
let aeAlg m =
  TLSConstants.get_aeAlg m.n_cipher_suite

val emsFlag: mode -> bool
let emsFlag mode =
  if mode.n_protocol_version = TLS_1p3 then
    true
  else
    match mode.n_offer.ch_extensions with
    | None -> false
    | Some cexts ->
      List.Tot.mem Extensions.E_extended_ms cexts &&
      (match mode.n_server_extensions with
       // called from server_ClientHello
       | None -> true
       // called from client_ServerHelloDone
       | Some sexts -> List.Tot.mem Extensions.E_extended_ms sexts)

val chosenGroup: mode -> option CommonDH.group
let chosenGroup mode =
  match kexAlg mode with
  | Kex_PSK_DHE
  | Kex_DHE -> CommonDH.group_of_namedGroup (FFDHE FFDHE2048)
  | Kex_PSK_ECDHE
  | Kex_ECDHE -> CommonDH.group_of_namedGroup (SEC CoreCrypto.ECC_P256)

val zeroRTToffer: offer -> bool
let zeroRTToffer o = Some? (find_early_data o)

val zeroRTT: mode -> bool
let zeroRTT mode =
  zeroRTToffer mode.n_offer &&
  Some? mode.n_pski

val local_config: #region:rgn -> #role:TLSConstants.role -> t region role -> config
let local_config #region #role ns =
  ns.cfg

val nonce: #region:rgn -> #role:TLSConstants.role -> t region role -> Tot TLSInfo.random
let nonce #region #role ns =
  ns.nonce

val resume: #region:rgn -> #role:TLSConstants.role -> t region role -> TLSInfo.resumeInfo role
let resume #region #role ns =
  ns.resume

val getMode: #region:rgn -> #role:TLSConstants.role -> t region role ->
  ST mode
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let getMode #region #role ns =
  match MR.m_read ns.state with
  | C_Mode mode
  | C_WaitFinished2 mode _
  | C_Complete mode _
  | S_ClientHello mode
  | S_Mode mode
  | S_Complete mode _ ->
  mode

(** Returns cfg.maxVersion or the negotiated version, when known *)
val version: #region:rgn -> #role:TLSConstants.role -> t region role ->
  ST protocolVersion
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let version #region #role ns =
  match MR.m_read ns.state with
  | C_Init _ -> ns.cfg.maxVer
  | C_Offer _ -> ns.cfg.maxVer
  | C_HRR o _ -> ns.cfg.maxVer
  | C_WaitFinished1 _ -> ns.cfg.maxVer
  | C_Mode mode
  | C_WaitFinished2 mode _
  | C_Complete mode _ -> mode.n_protocol_version
  | S_Init _ -> ns.cfg.maxVer
  | S_HRR o _ -> ns.cfg.maxVer
  | S_ClientHello mode
  | S_Mode mode
  | S_Complete mode _ -> mode.n_protocol_version

// Signature agility, depending on the CS and an optional client extension
let signatureScheme_of_mode mode supported_algs =
  let ha0 = sessionHashAlg mode.n_protocol_version mode.n_cipher_suite in
  match mode.n_protocol_version with
  | TLS_1p3 -> // signature_algorithms extension MUST have been offered
    begin
    match find_signature_algorithms mode.n_offer with
    | None -> None
    | Some algs ->
      List.Tot.find
        (fun alg -> is_handshake13_signatureScheme alg && List.Tot.mem alg supported_algs) algs
    end
   | TLS_1p2 ->
     begin
     let sa = sigAlg_of_ciphersuite mode.n_cipher_suite in
     match find_signature_algorithms mode.n_offer with
     | None ->
       Some (signatureScheme_of_sigHashAlg sa ha0)
       // ({RSASIG, ECDSA, DSA}, {SHA1, SHA256, SHA384, SHA512})
       // TODO: check that this is correct
       // The RFC (https://tools.ietf.org/html/rfc5246#section-7.4.1.4.10)
       // says that one should always use SHA1
     | Some algs -> List.Tot.find (fun alg -> List.Tot.mem alg supported_algs) algs
     end
   | _ ->
     let sa = sigAlg_of_ciphersuite mode.n_cipher_suite in
     Some (signatureScheme_of_sigHashAlg sa ha0) // (RSASIG, MD5SHA1) \/ (DSA, Hash SHA1)

val getSigningKey: #a:Signature.alg -> #region:rgn -> #role:TLSConstants.role -> t region role ->
  ST (option (Signature.skey a))
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let getSigningKey #a #region #role ns =
  Signature.lookup_key #a ns.cfg.private_key_file

val sign: #region:rgn -> #role:TLSConstants.role -> t region role -> bytes ->
  ST (option bytes)
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let sign #region #role ns tbs =
  let mode = getMode ns in
  match signatureScheme_of_mode mode ns.cfg.signatureAlgorithms with
  | None -> None
  | Some scheme ->
    begin
    let sa, ha = sigHashAlg_of_signatureScheme scheme in
    let a = Signature.(Use (fun _ -> true) sa [ha] false false) in
    match getSigningKey #a ns with
    | None ->
      (trace "*WARNING* couldn't load signing key";
       None)
    | Some skey ->
      let sigv = Signature.sign #a ha skey tbs in
      lemma_repr_bytes_values (length sigv);
      if length sigv >= 2 && length sigv < 65536 then Some (signatureSchemeBytes scheme @| vlbytes 2 sigv)
      else None
    end

val verify: signatureScheme -> list Cert.cert -> bytes -> bytes ->
  ST bool
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> True))
let verify scheme chain tbs sigv =
  let (sa,ha) = sigHashAlg_of_signatureScheme scheme in
  let a = Signature.(Use (fun _ -> true) sa [ha] false false) in
  match Signature.get_chain_public_key #a chain with
  | None -> false
  | Some pk -> Signature.verify #a ha pk tbs sigv


(* CLIENT *)

val client_ClientHello: #region:rgn -> t region Client
  -> option CommonDH.clientKeyShare
  -> list (PSK.pskid * PSK.pskInfo)
  -> St offer
let client_ClientHello #region ns oks pskinfo =
  //17-04-22 fix this in the definition of offer?
  let oks' =
    match oks with
    | Some ks -> Some (CommonDH.ClientKeyShare ks)
    | None -> None
  in
  match MR.m_read ns.state with
  | C_Init _ ->
      let offer = computeOffer Client ns.cfg ns.resume ns.nonce oks' pskinfo in
      trace ("offering client extensions "^string_of_option_extensions offer.ch_extensions);
      MR.m_write ns.state (C_Offer offer);
      offer

(**
  Checks that the protocol version in ClientHello is
  within the range of versions supported by the server configuration
  and outputs the negotiated version if true
*)

// usable on both sides; following https://tlswg.github.io/tls13-spec/#rfc.section.4.2.1
let offered_versions min_pv (o: offer): result (l: list protocolVersion {l <> []}) =
  match find_supported_versions o with
  | Some []  -> Error(AD_protocol_version, "protocol version negotiation: empty proposal")
  | Some vs -> Correct vs  // might check no proposal is below min_pv
  | None -> // use legacy offer
      match o.ch_protocol_version, min_pv with
      | TLS_1p0, TLS_1p0 -> Correct [TLS_1p0]
      | TLS_1p1, TLS_1p0 -> Correct [TLS_1p2; TLS_1p1]
      | TLS_1p1, TLS_1p1 -> Correct [TLS_1p1]
      | TLS_1p2, TLS_1p0 -> Correct [TLS_1p2; TLS_1p1; TLS_1p0]
      | TLS_1p2, TLS_1p1 -> Correct [TLS_1p2; TLS_1p1]
      | TLS_1p2, TLS_1p2 -> Correct [TLS_1p2]
      | _, _ -> Error(AD_protocol_version, "protocol version negotation: bad legacy proposal")

let is_client13 (o:offer) =
  match offered_versions TLS_1p3 o with
  | Correct vs -> List.Tot.existsb (fun v -> v = TLS_1p3) vs
  | Error _ -> false

let negotiate_version cfg offer =
  //17-04-26 TODO pass outer packet PV instead of TLS_1p0
  match offered_versions TLS_1p0 offer with
  | Error z -> Error z
  | Correct vs ->
    match List.Tot.find (fun v -> geqPV cfg.maxVer v && geqPV v cfg.minVer) vs with
    | Some v -> Correct v
    | None -> Error(AD_protocol_version, "protocol version negotiation: mismatch")

(**
  For use in negotiating the ciphersuite, takes two lists and
  outputs the first ciphersuite in list2 that also is in list
  one and is a valid ciphersuite, or [None]
*)
val negotiate:l1:list valid_cipher_suite -> list valid_cipher_suite -> Tot (option (c:valid_cipher_suite{CipherSuite? c && List.Tot.mem c l1}))
let negotiate l1 l2 =
  List.Tot.find #valid_cipher_suite (fun s -> CipherSuite? s && List.Tot.mem s l1) l2

(**
  For use in ensuring the result from negotiate is a Correct
  ciphersuite with associated kex, sig and ae algorithms,
  and throws an error if No ciphersuites were supported in both lists
*)
val negotiateCipherSuite: cfg:config -> pv:protocolVersion -> ccs:valid_cipher_suites -> Tot (result (TLSConstants.kexAlg * option TLSConstants.sigAlg * TLSConstants.aeAlg * valid_cipher_suite))
let negotiateCipherSuite cfg pv ccs =
  match negotiate ccs cfg.ciphersuites with
  | Some(CipherSuite kex sa ae) -> Correct(kex,sa,ae,CipherSuite kex sa ae)
  | None -> Error(AD_internal_error, perror __SOURCE_FILE__ __LINE__ "Cipher suite negotiation failed")

(*
val negotiateGroupKeyShare13
  config ->
  list extension ->
  Tot (result (option (kexAlg * namedGroup * option share))
let rec negotiateGroupKeyShare cfg pv exts =
  // first fetch the two relevant extensions
  let supported, keyshares =
    match o.ch_extensions with
    | None -> None, None
    | Some es ->
      ( match List.Tot.find Extensions.E_supported_groups? es with
        | None -> None
        | Some (Extensions.E_supported_groups gs) -> Some gs)
      ( match List.Tot.find Extensions.E_key_share? es with
        | None -> None
        | Some (Extensions.E_key_share (CommonDH.ClientKeyShare gl)) ->
            let filter (g, gx) =
              List.Tot.mem g cfg.namedGroups &&
              ( (SEC? g && (kex = Kex_ECDHE || kex = Kex_PSK_ECDHE)) ||
                (FFDHE? g && (kex = Kex_DHE || kex = Kex_PSK_DHE)) ) in
            Some(match List.Tot.filter filter gl)) in

  if pv = TLS_1p3 then
    match keyshares with
    | None -> Error(AD_decode_error, "no supported group or key share extension found")
    | Some [] -> Error(AD_decode_error, "no shared group between client and server config")
    | Some (share::_) -> Correct (Some share)
    // todo support HRR depending on supported_groups

  else if kex = Kex_ECDHE && Some? supported then
    let filter g = SEC? g && List.Tot.mem g cfg.namedGroups in
    let gs = List.Tot.filter

    Correct(Some (match List.Tot.filter filter gs), None)

    match supported with

    | Some
  List.Tot.existsb E_supported_groups? exts


  | Some exts when (kex = Kex_ECDHE && List.Tot.existsb E_supported_groups? exts) ->
    let Some (E_supported_groups gl) = List.Tot.find E_supported_groups? exts in

    let filter g =
    (match List.Tot.filter filter gl with
    | gn :: _ -> Correct (Some gn, None)
    | [] -> Error(AD_decode_error, "no shared curve configured"))
  | _ ->
    let filter x =
      (match kex with | Kex_DHE -> FFDHE? x | Kex_ECDHE -> SEC? x | _ -> false) in
    if kex = Kex_DHE || kex = Kex_ECDHE then
      (match List.Tot.filter filter cfg.namedGroups with
      | gn :: _ -> Correct (Some gn, None)
      | [] -> Error(AD_decode_error, "no valid group is configured for the selected cipher suite"))
    else Correct(None, None)
*)

(**
  Determines if the server random value contains a downgrade flag
  AND if there has been a downgrade
  The downgrade flag is a random value set by RFC (6.3.1.1)
*)
val isSentinelRandomValue: protocolVersion -> protocolVersion -> TLSInfo.random -> Tot bool
let isSentinelRandomValue c_pv s_pv s_random =
  geqPV c_pv TLS_1p3 && geqPV TLS_1p2 s_pv && equalBytes (abytes "DOWNGRD\x01") s_random ||
  geqPV c_pv TLS_1p2 && geqPV TLS_1p1 s_pv && equalBytes (abytes "DOWNGRD\x00") s_random


(** Confirms that the version negotiated by the server was:
  - within the range specified by client config AND
  - is not an unnecessary downgrade AND
  - is not a newer version than offered by the client
*)
val acceptableVersion: config -> protocolVersion -> TLSInfo.random -> Tot bool
let acceptableVersion cfg pv sr =
  // we statically know that the offered versions are compatible with our config
  // (we may prove e.g. acceptableVersion pv ==> pv in offered_versions
  geqPV pv cfg.minVer &&
  geqPV cfg.maxVer pv &&
  not (isSentinelRandomValue cfg.maxVer pv sr)

(** Confirms that the ciphersuite negotiated by the server was:
  - consistent with the client config;
  - TODO: [s_cs] is supported by the protocol version (e.g. no GCM with
    TLS<1.2).
 BD: Removed that the ciphersuite is acceptable given CHELO
 given that the clientOffer is prepared with the entire list
 of valid cipher suites in the client config
*)
val acceptableCipherSuite: config -> protocolVersion -> valid_cipher_suite -> Tot bool
let acceptableCipherSuite cfg spv cs =
  List.Tot.existsb (fun x -> x = cs) cfg.ciphersuites &&
  not (isAnonCipherSuite cs) || cfg.allowAnonCipherSuite

let matching_share
  (cext:option (ce:list extension{List.Tot.length ce < 256})) (g:CommonDH.group) :
   option (g:CommonDH.group & CommonDH.share g) =
  match cext with
  | Some cext ->
    begin
    match List.Tot.find Extensions.E_key_share? cext with
    | Some (E_key_share (CommonDH.ClientKeyShare shares)) ->
      begin
      match List.Tot.find (fun share -> CommonDH.Share?.g share = g) shares with
      | Some (CommonDH.Share g gx) -> Some (|g, gx|)
      | _ -> None
      end
    | _ -> None
    end
  | None -> None

// for this kind of function, can we just rely on type inference?
val client_ServerHello: #region:rgn -> t region Client ->
  HandshakeMessages.sh ->
  St (result mode) // it needs to be computed, whether returned or not
let client_ServerHello #region ns sh =
  match MR.m_read ns.state with
  | C_Offer offer ->
    let spv  = sh.sh_protocol_version in
    let sr   = sh.sh_server_random in
    let cs   = sh.sh_cipher_suite in
    let sext = sh.sh_extensions in
    let ssid = sh.sh_sessionID in
    let cext = offer.ch_extensions in
    let sig  = CoreCrypto.RSASIG in
    let resume = false in
    trace ("processing server extensions "^string_of_option_extensions sext);
    if not (acceptableVersion ns.cfg spv sr) then
      Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Protocol version negotiation")
    else if not (acceptableCipherSuite ns.cfg spv cs) then
      Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation")
    else
     match Extensions.negotiateClientExtensions spv ns.cfg cext sext cs None resume with
      | Error z -> Error z
      | Correct () ->
        trace ("negotiated "^string_of_pv spv^" "^string_of_ciphersuite cs);
        match cs with
        | CipherSuite13 ae ha ->
          begin
          let pski =
            match find_clientPske offer, find_serverPske sh with
            | Some ids, Some idx ->
              if idx < List.Tot.length ids then
                Correct (Some idx) // REMARK: we can't check yet consistency with early_data in EE
              else
                Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "PSK out of bounds")
            | None, Some _ ->
              Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "PSK not offered")
            | _, _ -> Correct None
          in
          match pski with
          | Error z -> Error z
          | Correct pski ->
            begin
            match spv, find_serverKeyShare sh with
            | TLS_1p3, Some (CommonDH.Share g gy) ->
              let server_share = (|g, gy|) in
              let client_share = matching_share cext g in
              let mode = Mode
                offer
                None // n_hrr
                spv
                sr
                None // (Some ssid)
                cs
                pski
                sext
                (Some server_share)
                None // n_client_cert_request
                None // n_server_cert
                client_share
               in
               MR.m_write ns.state (C_Mode mode);
               Correct mode
            | _ -> // TODO: pure PSK mode
              Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Ciphersuite negotiation")
            end
          end
        | CipherSuite kex sa ae ->
          let mode = Mode
            offer
            None
            spv
            sr
            None // (Some ssid)
            cs
            None // pski
            sext
            None // n_server_share; unknwon before SKE is received
            None // n_client_cert_request
            None // n_server_cert
            None // n_client_share
          in
          MR.m_write ns.state (C_Mode mode);
          Correct mode
        | _ -> Error (AD_decode_error, "ServerHello ciphersuite is not a real ciphersuite")

(* ---------------- signature stuff, to be removed from Handshake -------------------- *)

// why an option?
val to_be_signed: pv:protocolVersion -> role -> csr:option bytes{None? csr <==> pv == TLS_1p3} -> bytes -> bytes
let to_be_signed pv role csr tbs =
  match pv, csr with
  | TLS_1p3, None ->
      let pad = abytes (String.make 64 (Char.char_of_int 32)) in
      let ctx =
        match role with
        | Server -> "TLS 1.3, server CertificateVerify"
        | Client -> "TLS 1.3, client CertificateVerify"  in
      pad @| abytes ctx @| abyte 0z @| tbs
  | _, Some csr -> csr @| tbs

(** Note that in TLS < 1.2 SKE doesn't include the signature scheme *)
val signatureScheme_of_ske: bytes -> option (signatureScheme * bytes)
let signatureScheme_of_ske signature =
  if length signature > 4 then
   let sa, sigv = split signature 2 in
   match vlsplit 2 sigv with
   | Correct (sigv, eof) ->
     begin
     match length eof, parseSignatureScheme sa with
     | 0, Correct sa -> Some (sa, sigv)
     | _, _ -> None
     end
   | Error _ -> None
  else None

val client_ServerKeyExchange: #region:rgn -> t region Client ->
  serverCert: HandshakeMessages.crt ->
  HandshakeMessages.ske ->
  ocr: option HandshakeMessages.cr ->
  St (result mode)
let client_ServerKeyExchange #region ns crt ske ocr =
  match MR.m_read ns.state with
  | C_Mode mode ->
    match ske.ske_kex_s with
    | KEX_S_RSA _ ->
      Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Illegal message")
    | KEX_S_DHE gy ->
      let scert = Cert.chain_up crt.crt_chain in
      if (not ns.cfg.check_peer_certificate) ||
         Cert.validate_chain crt.crt_chain true ns.cfg.peer_name ns.cfg.ca_file
      then
        let ske_tbs = kex_s_to_bytes ske.ske_kex_s in
        match signatureScheme_of_ske ske.ske_sig with
        | None ->
          Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse SKE message")
        | Some (sa', sigv) ->
          begin
          match signatureScheme_of_mode mode [sa'] with
          | None -> Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Signature algorithm negotiation failed")
          | Some sa ->
            if sa <> sa' then
              Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Signature algorithm in ServerKeyexchange message cannot be negotiated")
            else
              let csr = ns.nonce @| mode.n_server_random in
              let tbs = to_be_signed mode.n_protocol_version Server (Some csr) ske_tbs in
              let chain = Cert.chain_down scert in
              let valid = verify sa chain tbs sigv in
              trace ("ServerKeyExchange signature: " ^ (if valid then "Valid" else "Invalid"));
              if not valid then
                Error (AD_handshake_failure, perror __SOURCE_FILE__ __LINE__ "Failed to check SKE signature")
              else
                let Mode offer hrr pv sr sid cs pski sext _ _ _ gx = mode in
                let mode = Mode offer hrr pv sr sid cs pski sext (Some gy) ocr (Some scert) gx in
                let ccert = None in // TODO
                MR.m_write ns.state (C_WaitFinished2 mode ccert);
                Correct mode
          end
       else
         Error (AD_certificate_unknown_fatal, perror __SOURCE_FILE__ __LINE__ "Certificate validation failed")


val clientComplete_13: #region:rgn -> t region Client ->
  HandshakeMessages.ee ->
  ocr: option HandshakeMessages.cr13 ->
  serverCert: Cert.chain13 ->
  cv: HandshakeMessages.cv ->
  digest: bytes{length digest <= 32} ->
  St (result mode) // it needs to be computed, whether returned or not
let clientComplete_13 #region ns ee ocr serverChain cv digest =
  trace "Nego.clientComplete_13";
  match MR.m_read ns.state with
  | C_Mode mode ->
    let ccert = None in
    let scert = Some serverChain in
    let sexts = mode.n_server_extensions in // TODO: add extensions from EE
    let mode = Mode
      mode.n_offer
      mode.n_hrr
      mode.n_protocol_version
      mode.n_server_random
      mode.n_sessionID
      mode.n_cipher_suite
      mode.n_pski
      mode.n_server_extensions
      mode.n_server_share
      ocr
      scert
      mode.n_client_share
    in
    MR.m_write ns.state (C_Complete mode ccert);
    Correct mode


(* SERVER *)

type cs13 offer =
  | PSK_EDH: j:pski offer -> oks: option share -> cs: cipherSuite ->  cs13 offer
  | JUST_EDH: oks: share -> cs: cipherSuite -> cs13 offer
  // JUST_PSK: TODO

// Work around #1016
private let rec compute_cs13_aux (i:nat) (o:offer)
  (psks:list (PSK.pskid * PSK.pskInfo))
  (g_gx:option share)
  ncs psk_kex : list (cs13 o) =
  if i = List.length psks then
    match g_gx, ncs with
    | Some x, (cs :: _) -> [JUST_EDH x cs]
    | _ -> []
  else
    let choices =
      match List.Tot.index psks i, psk_kex with
      | (id, info), true ->
        // ADL: FIXME pure PSK
        [PSK_EDH i g_gx (CipherSuite13 info.PSK.early_ae info.PSK.early_hash)]
      | _ -> []
    in
    choices @ (compute_cs13_aux (i+1) o psks g_gx ncs psk_kex)

// returns a list of negotiable "core modes" for TLS 1.3
// the key exchange can be derived from cs13
// (we could stop after finding the first)
val compute_cs13:
  cfg: config ->
  o: offer ->
  psks: list (PSK.pskid * PSK.pskInfo) ->
  shares: list share (* pre-registered *) ->
  result (list (cs13 o))
let compute_cs13 cfg o psks shares =
  // pick the (potential) group to use for DHE/ECDHE
  let g_gx: option share =
    match find_supported_groups o with
    | None -> None
    | Some gs ->
      match List.Tot.filter (fun g -> List.Tot.mem g cfg.namedGroups) gs with
      | [] -> None
      | g::_ ->
        let Some g = CommonDH.group_of_namedGroup g in
        match List.Tot.filter (fun g_s -> dfst g_s = g) shares with
        | [] -> None
        | s :: _ -> Some s
    in

  // pick acceptable record ciphersuites
  let ncs = List.Tot.filter
    (fun cs -> CipherSuite13? cs && List.Tot.mem cs cfg.ciphersuites)
    o.ch_cipher_suites in

  let psk_kex = true in
  Correct (compute_cs13_aux 0 o psks g_gx ncs psk_kex)

// Registration and filtering of DH shares
let rec filter_psk (l:list Extensions.pskIdentity)
  : St (list (PSK.pskid * PSK.pskInfo))
  =
  match l with
  | [] -> []
  | (id, _) :: t ->
    let id = utf8 (iutf8 id) in // FIXME Platform.Bytes
    (match PSK.psk_lookup id with
    | Some info -> (id, info) :: (filter_psk t)
    | None -> filter_psk t)

// Registration of DH shares
let rec register_shares (l:list pre_share)
  : St (list share) =
  match l with
  | [] -> []
  | (| g, gx |) :: t -> (| g, CommonDH.register #g gx |) :: (register_shares t)

//17-03-30 still missing a few for servers.

// TODO ADL: incorrect as written; CS nego depends on ext nego
//   (e.g. in TLS 1.2 it's incorrect to select an EC cipher suite if
//         EC extensions are missing)
// FIXME ADL
// I have hacked nego to at least not pick a bad CS for the server's cert keytype
// but this REALLY needs to be rewritten properly from scratch by someone who has
// read all TLS RFCs
// FIXME ADL: grossly inefficient; we need to cache the server keytype at startup
(* TODO: why irreducible? *)
irreducible val computeServerMode:
  cfg: config ->
  co: offer ->
  serverRandom: TLSInfo.random ->
  serverID: option sessionID ->
  St (result mode)
let computeServerMode cfg co serverRandom serverID =
  // for now, we set the version before negotiating the rest; this may lead to mismatches e.g. on tickets or certificates
  match negotiate_version cfg co with
  | Error z -> Error z
  | Correct TLS_1p3 ->
    begin
    // Filter and register offered PSKs
    let pske =
      match find_clientPske co with
      | Some pske -> filter_psk pske
      | None -> [] in
    let shares = register_shares (gs_of co) in
    match compute_cs13 cfg co pske shares with
    | Error z -> Error z
    | Correct [] -> Error(AD_handshake_failure, "ciphersuite negotiation failed")
    | Correct (kex :: _) ->
      begin
      match find_signature_algorithms co with
      | None ->
        Error(AD_handshake_failure, "Client didn't send signature_algorithm extension")
      | Some algs ->
        begin
        match List.Tot.filter (fun alg -> List.Tot.mem alg cfg.signatureAlgorithms) algs with
        | [] -> Error(AD_handshake_failure, "signature algorithm negotiation failed")
        | alg :: _ ->
          begin
          trace ("negotiated " ^ (string_of_signatureScheme alg));
          let serverExtensions = None in // To be computed in Handshake and filled later
          let scert =
            match Cert.lookup_chain cfg.cert_chain_file with
            | Correct cert -> Some (Cert.chain_up cert)
            | Error z ->
              trace ("*WARNING* no server certificate found: " ^ string_of_error z);
              None
          in
          match kex with
          | PSK_EDH j ogx cs  ->
            (trace "PSK_EDH";
            Correct (Mode
              co
              None // TODO: no HRR
              TLS_1p3
              serverRandom
              serverID
              cs
              (Some j)
              serverExtensions
              None // no server key share yet
              None // TODO: n_client_cert_request
              scert
              ogx))
          | JUST_EDH gx cs ->
            Correct (Mode
              co
              None // TODO: no HRR
              TLS_1p3
              serverRandom
              serverID
              cs
              None // No PSKs, pure (EC)DHE
              serverExtensions
              None // no server key share yet
              None // TODO: n_client_cert_request
              scert
              (Some gx))
          end
        end
      end
    end
  | Correct pv ->
  // with TLS 1.2, we pick the first ciphersuite compatible with our credentials
  // we could be a bit stricter and record wether the client is TLS
  let nosa = fun (CipherSuite _ sa _) -> None? sa in
  let sigfilter =
    match Cert.lookup_chain cfg.cert_chain_file with
    | Correct c  -> (
      match Cert.endpoint_keytype c with
      | Some kt -> (fun cs ->
        match cs with
        | CipherSuite _ sa _ ->
          begin
          match sa with
          | Some sa ->
            (match sa, kt with
            | RSASIG, KeyRSA _ | RSAPSS, KeyRSA _
            | ECDSA, KeyECDSA _ | DSA, KeyDSA _ -> true
            | _ -> false)
          | _ -> false
          end
        | _ -> false)
      | _ -> trace "WARNING: loaded wrong server cert"; nosa)
    | _ -> trace "WARNING: cannot load server cert"; nosa in
  // From https://tools.ietf.org/html/rfc5246#section-7.4.2:
  // In order to negotiate correctly, the server MUST check any candidate
  // cipher suites against the "signature_algorithms" extension before selecting them
  // TODO: we're not doing this
  let ccs = List.Tot.filter sigfilter co.ch_cipher_suites in
  match negotiateCipherSuite cfg pv ccs with
  | Error z -> Error z
  | Correct (kex,sa,ae,cs) ->
  // compute server extensions
  match co.ch_extensions with
  | None -> Error(AD_illegal_parameter, "Missing mandatory ClientHello extensions")
  (* omitted details:
              | SSL_3p0 ->
                let cre =
                  if contains_TLS_EMPTY_RENEGOTIATION_INFO_SCSV (list_valid_cs_is_list_cs ccs) then
                     {ne_default with ne_secure_renegotiation = RI_Valid}
                  else ne_default
                in Correct (cre)
             | _ -> Error... )) *)
  | Some cexts ->
    let serverExtensions = None in // To be computed in Handshake and filled later
  // compression is null and non-negotiable; we just report client errors
  let correct_compression_offer =
    if is_client13 co
    then co.ch_compressions = [NullCompression]
    else List.Tot.existsb (fun c -> c = NullCompression) co.ch_compressions in
  if not correct_compression_offer
  then Error(AD_illegal_parameter, "Compression is deprecated") else
  let scert =
    match Cert.lookup_chain cfg.cert_chain_file with
    | Correct cert -> Some (Cert.chain_up cert)
    | Error z ->
      trace ("No cert found: "^string_of_error z);
      None
  in
  Correct (Mode
    co
    None // no HRR before TLS 1.3
    pv
    serverRandom
    serverID
    cs
    None
    serverExtensions
    None // no server key share yet
    None
    scert
    None // no client key share yet for 1.2
  )

val server_ClientHello: #region:rgn -> t region Server ->
  HandshakeMessages.ch ->
  option sessionID ->
  St (result mode)
let server_ClientHello #region ns offer sid =
  trace ("offered client extensions "^string_of_option_extensions offer.ch_extensions);
  trace (string_of_result (List.Tot.fold_left (fun s pv -> s^" "^string_of_pv pv) "offered versions")  (offered_versions TLS_1p0 offer));
  match MR.m_read ns.state with
  | S_Init _ ->
    match computeServerMode ns.cfg offer ns.nonce sid with
    | Error z ->
      trace ("negotiation failed: "^string_of_error z);
      Error z
    | Correct m ->
      trace ("negotiated "^string_of_pv m.n_protocol_version^" "^string_of_ciphersuite m.n_cipher_suite);
      MR.m_write ns.state (S_ClientHello m);
      Correct m


let share_of_serverKeyShare (ks:CommonDH.keyShare) : share =
  let CommonDH.ServerKeyShare (CommonDH.Share g gy) = ks in (| g, gy |)

val server_ServerShare: #region:rgn -> t region Server -> option CommonDH.keyShare ->
  St (result mode)
let server_ServerShare #region ns ks =
  match MR.m_read ns.state with
  | S_ClientHello mode ->
    let cexts = mode.n_offer.ch_extensions in
    trace ("processing client extensions " ^ string_of_option_extensions cexts);
    match Extensions.negotiateServerExtensions
      mode.n_protocol_version
      cexts
      mode.n_offer.ch_cipher_suites
      ns.cfg
      mode.n_cipher_suite
      None  // option (TI.cVerifyData*TI.sVerifyData)
      mode.n_pski
      ks
      false // resume?
    with
    | Error z -> Error z
    | Correct sexts ->
      begin
      trace ("including server extensions " ^ string_of_option_extensions sexts);
      let mode = Mode
        mode.n_offer
        mode.n_hrr
        mode.n_protocol_version
        mode.n_server_random
        mode.n_sessionID
        mode.n_cipher_suite
        mode.n_pski
        sexts
        (Option.map share_of_serverKeyShare ks)
        mode.n_client_cert_request
        mode.n_server_cert
        mode.n_client_share
      in
      MR.m_write ns.state (S_Mode mode);
      Correct mode
      end


//17-03-30 where is it used?
type hs_id = {
  id_cert: Cert.chain;
  id_sigalg: option signatureScheme;
}

//17-03-30 get rid of this wrapper?
type session = {
  session_nego: option mode;
}


// represents the outcome of a successful handshake,
// providing context for the derived epoch
type handshake =
  | Fresh of session // was sessionInfo
  | Resumed of session // was abbrInfo * sessionInfo
// We use SessionInfo as unique session indexes.
// We tried using instead hs, but this creates circularities
// We'll probably need a global log to reason about them.
// We should probably do the same in the session store.
