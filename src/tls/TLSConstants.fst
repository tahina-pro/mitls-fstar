(**
This file implements type representations and parsing functions
for the different values negotiated during the TLS
handshake. For instance protocol version, key exchange mechanism,
hash algorithm etc.

@summary Module for main constants
*)
module TLSConstants

/// 18-09-08 contents & triage (beware of scopes)
/// - crypto ==> EverCrypt
/// - datatypes ==> QD
///    7% for signatures
///   53% for ciphersuites!
///   10% for certificates
/// - prf details ==> KeySchedule
/// - parsed extension contents ==> Extensions
/// - split Config (defaults are defined much later); align to EverCrypt
/// - callbacks + ad hoc string conversions ==> FFI ?

//18-02-27 not a reasonable default?
//#set-options "--max_fuel 0 --initial_fuel 0 --max_ifuel 1 --initial_ifuel 1"

open FStar.Seq
open FStar.UInt32
open FStar.Bytes
open FStar.Error
open TLSError

open Mem
open Parse
//include Parse

(* Relocate? *)
let rec fold_string (#a:Type)
                    (f: a -> string)
                    (accum:string)
                    (sep:string)
                    (al:list a) : Tot string (decreases al) =
    match al with
    | [] -> accum
    | a::al -> let accum = accum ^ sep ^ f a in
             fold_string f accum sep al

/// HIGH-LEVEL DECLARATIONS

(** Role of the connection endpoints *)
type role =
  | Client
  | Server
let dualRole = function
  | Client -> Server
  | Server -> Client

(** Polarity for reading and writing on a connection *)
type rw =
  | Reader
  | Writer

/// 18-02-22 QD fodder?
///
(** Protocol version negotiated values *)

include Parsers.Parse_protocolVersion // for TLS_1p3, etc.

inline_for_extraction
type protocolVersion' = Parsers.Parse_protocolVersion.protocolVersion
inline_for_extraction
type protocolVersion = (p: protocolVersion' { not (Unknown_protocolVersion? p) } )

// aka TLS_1p3
let is_pv_13 = function
  | TLS_1p3 -> true
  | _       -> false

(** Serializing function for the protocol version *)
let versionBytes : protocolVersion' -> Tot (lbytes 2) =
  LowParseWrappers.wrap_serializer32_constant_length protocolVersion_serializer32 2 ()

inline_for_extraction
let parse_protocolVersion_error_msg : string =
  FStar.Error.perror __SOURCE_FILE__ __LINE__ ""

val parseVersion: pinverse_t versionBytes
let parseVersion x =
  LowParseWrappers.wrap_parser32_constant_length protocolVersion_serializer32 2 () protocolVersion_parser32 parse_protocolVersion_error_msg x

(** Determine the oldest protocol versions for TLS *)
let minPV (a:protocolVersion) (b:protocolVersion) =
  match a,b with
  | SSL_3p0, _  | _, SSL_3p0 -> SSL_3p0
  | TLS_1p0, _  | _, TLS_1p0 -> TLS_1p0
  | TLS_1p1, _  | _, TLS_1p1 -> TLS_1p1
  | TLS_1p2, _  | _, TLS_1p2 -> TLS_1p2
  | TLS_1p3, _  | _, TLS_1p3 -> TLS_1p3

let geqPV a b = (b = minPV a b)

let string_of_pv = function
  | SSL_3p0 -> "SSL3"
  | TLS_1p0 -> "1.0"
  | TLS_1p1 -> "1.1"
  | TLS_1p2 -> "1.2"
  | TLS_1p3 -> "1.3"
  | Unknown_protocolVersion x -> "Unknown protocol version: " ^ string_of_int (UInt16.v x)


/// Various elements used in ciphersuites

(** Key exchange algorithms **)
type kexAlg =
  | Kex_RSA
  | Kex_DH
  | Kex_PSK
  | Kex_PSK_DHE
  | Kex_PSK_ECDHE
  | Kex_DHE
  | Kex_ECDHE

(** Crypto algorithm names are defined in EverCrypt **)
type blockCipher = EverCrypt.block_cipher_alg
type streamCipher = EverCrypt.stream_cipher_alg
type aeadAlg = EverCrypt.aead_alg

(** Modes for the initialization vectors *)
type ivMode =
  | Fresh
  | Stale

(** Encryption types *)
type encAlg =
  | Block of blockCipher
  | Stream of streamCipher

(** TLS-specific hash and MAC algorithms *)

//18-09-08 eliminate once EverCrypt/Hashing are stable.

type hash_alg = Hashing.Spec.alg
type hashAlg = Hashing.Spec.tls_alg
type macAlg = Hashing.Spec.alg

let hashSize = Hashing.Spec.tls_tagLen
let macKeySize = Hashing.Spec.tagLen
let macSize = Hashing.Spec.tagLen

(** Authenticated Encryption modes *)
type aeAlg =
  | MACOnly: hash_alg -> aeAlg
  | MtE: encAlg -> hash_alg -> aeAlg
  | AEAD: aeadAlg -> hash_alg -> aeAlg // the hash algorithm is for the ciphersuite; it is not used by the record layer.

let aeAlg_hash = function
  | MACOnly ha -> ha
  | MtE _ ha -> ha
  | AEAD _ ha -> ha

(** Determine if this algorithm provide padding support with TLS 1.2 *)
let lhae = function
  | MtE (Block _) _                         -> true
  | MACOnly _ | AEAD _ _ | MtE (Stream _) _ -> false

(** Sequence numbers for StreamAE/StatefulLHAE *)
let is_seqn (n:nat) = repr_bytes n <= 8
type seqn_t = n:nat { is_seqn n }

(** Predicates for Strong Authentication *)
// MtE: ``The AE algorithms are CPA and INT-CTXT''
// MtE: ``The MAC algorithm of id is INT-CMA.''

assume val strongAuthAlg: protocolVersion -> aeAlg -> Tot bool
//  | MtE _ m | MACOnly m   -> int_cma (macAlg_of_id i)
//  | AEAD e m -> strongAEADalg

val strongAEAlg: protocolVersion -> aeAlg -> Tot bool
let strongAEAlg _ _ = false
// let strongAEAlg pv ae = match ae with
//    | AEAD e m -> true
//    | MtE _ -> false

assume val strongAuthAE: pv:protocolVersion -> ae:aeAlg -> Lemma(strongAEAlg pv ae ==> strongAuthAlg pv ae)

// we leave these functions abstract for verification purposes
// we may need to be more negative on weak algorithms (so that we don't try to verify their use)
// and more precise/positive on algorithms we implement (so that we reflect lower assumptions)

(** Encryption key sizes *)
let encKeySize = function
  | Stream EverCrypt.RC4_128 -> 16
  | Block a                  -> UInt32.v (EverCrypt.block_cipher_keyLen a)

(** AEAD salt sizes *)
let aeadSaltSize =
  let open EverCrypt in function // TLS 1.3 IV salt.
  | AES128_GCM       -> 4
  | AES256_GCM       -> 4
  | CHACHA20_POLY1305 -> 12
  | _                 -> 4 //recheck

(** AEAD *)
let aeadRecordIVSize =
  let open EverCrypt in function // TLS 1.2 explicit IVs
  | AES128_GCM       -> 8
  | AES256_GCM       -> 8
  | CHACHA20_POLY1305 -> 0
  | _                 -> 8 //recheck


// -----------------------------------------------------------------------
// record-layer length constants [5.2.1]
// note that TLS 1.3 lowers a bit the upper bound of cipher lengths (Ok in principle)
// but still enables padding beyond plausible plaintext lengths.

(** Constants for API and protocol-level fragments are in [0..2^14] *)
let max_TLSPlaintext_fragment_length     = 16384
let max_TLSCompressed_fragment_length    = max_TLSPlaintext_fragment_length + 1024
let max_TLSCiphertext_fragment_length    = max_TLSPlaintext_fragment_length + 2048
let max_TLSCiphertext_fragment_length_13 = max_TLSPlaintext_fragment_length + 256


/// SIGNATURE ALGORITHMS
/// 18-02-22 QD fodder

(** Signature algorithms *)
type sigAlg =
 | RSASIG
 | DSA
 | ECDSA
 | RSAPSS
 
(* This is the old version of the inverse predicate. According to CF,
   verification was harder with this style, so we moved to the new style with
   pinverse_t + lemmas. The type abbrevations lemma_inverse_* minimize the
   syntactic overhead.

  logic type pinverse (#a:Type) (#b:Type) (r:b -> b -> Type) (=f:a -> Tot b) =
    y:b -> Tot (xopt:result a{(forall (x:a). r (f x) y <==> (xopt = Correct x))})
*)

(** Payload of signature_algorithms extension, using format from TLS 1.3 spec
    https://tlswg.github.io/tls13-spec/#signature-algorithms
    https://tools.ietf.org/html/rfc5246#section-7.4.1.4.1
*)
type signatureScheme =
  | RSA_PKCS1_SHA256
  | RSA_PKCS1_SHA384
  | RSA_PKCS1_SHA512
  // ECDSA algorithms
  | ECDSA_SECP256R1_SHA256
  | ECDSA_SECP384R1_SHA384
  | ECDSA_SECP521R1_SHA512
  // RSASSA-PSS algorithms
  | RSA_PSS_SHA256
  | RSA_PSS_SHA384
  | RSA_PSS_SHA512
  // EdDSA algorithms
  //  | ED25519_SHA512
  //  | ED448_SHAKE256
  // Legacy algorithms
  | RSA_PKCS1_SHA1
  | RSA_PKCS1_MD5SHA1 // Only used internally, with codepoint 0xFFFF (PRIVATE_USE)
  | ECDSA_SHA1
  // Reserved Code Points
  | DSA_SHA1
  | DSA_SHA256
  | DSA_SHA384
  | DSA_SHA512
  | SIG_UNKNOWN of (codepoint: lbytes 2 {
      let v = int_of_bytes codepoint in
         v <> 0x0401 /\ v <> 0x0501 /\ v <> 0x0601 /\ v <> 0x0403
       /\ v <> 0x0503 /\ v <> 0x0603 /\ v <> 0x0804 /\ v <> 0x0805
       /\ v <> 0x0806
       // /\ v <> 0x0807 /\ v <> 0x0808
       /\ v <> 0x0201
       /\ v <> 0x0203 /\ v <> 0x0202 /\ v <> 0x0402 /\ v <> 0x0502
       /\ v <> 0x0602 /\ v <> 0xFFFF })

let is_handshake13_signatureScheme = function
  | ECDSA_SECP256R1_SHA256
  | ECDSA_SECP384R1_SHA384
  | ECDSA_SECP521R1_SHA512
  //| ED25519_SHA512
  //| ED448_SHAKE256
  | RSA_PSS_SHA256
  | RSA_PSS_SHA384
  | RSA_PSS_SHA512 -> true
  | _ -> false

val signatureSchemeBytes: s:signatureScheme -> lbytes 2
let signatureSchemeBytes = function
  | RSA_PKCS1_SHA256       -> twobytes (0x04z, 0x01z)
  | RSA_PKCS1_SHA384       -> twobytes (0x05z, 0x01z)
  | RSA_PKCS1_SHA512       -> twobytes (0x06z, 0x01z)
  | ECDSA_SECP256R1_SHA256 -> twobytes (0x04z, 0x03z)
  | ECDSA_SECP384R1_SHA384 -> twobytes (0x05z, 0x03z)
  | ECDSA_SECP521R1_SHA512 -> twobytes (0x06z, 0x03z)
  | RSA_PSS_SHA256         -> twobytes (0x08z, 0x04z)
  | RSA_PSS_SHA384         -> twobytes (0x08z, 0x05z)
  | RSA_PSS_SHA512         -> twobytes (0x08z, 0x06z)
  //| ED25519_SHA512         -> twobytes (0x08z, 0x07z)
  //| ED448_SHAKE256         -> twobytes (0x08z, 0x08z)
  | RSA_PKCS1_SHA1         -> twobytes (0x02z, 0x01z)
  | RSA_PKCS1_MD5SHA1      -> twobytes (0xFFz, 0xFFz)
  | ECDSA_SHA1             -> twobytes (0x02z, 0x03z)
  | DSA_SHA1               -> twobytes (0x02z, 0x02z)
  | DSA_SHA256             -> twobytes (0x04z, 0x02z)
  | DSA_SHA384             -> twobytes (0x05z, 0x02z)
  | DSA_SHA512             -> twobytes (0x06z, 0x02z)
  | SIG_UNKNOWN codepoint  -> codepoint

assume val signatureSchemeBytes_is_injective:
  s1: signatureScheme -> s2: signatureScheme ->
  Lemma
  (requires signatureSchemeBytes s1 == signatureSchemeBytes s2)
  (ensures s1 == s2)

val parseSignatureScheme: pinverse_t signatureSchemeBytes
let parseSignatureScheme b =
  match b.[0ul], b.[1ul] with
  | (0x04z, 0x01z) -> Correct RSA_PKCS1_SHA256
  | (0x05z, 0x01z) -> Correct RSA_PKCS1_SHA384
  | (0x06z, 0x01z) -> Correct RSA_PKCS1_SHA512
  | (0x04z, 0x03z) -> Correct ECDSA_SECP256R1_SHA256
  | (0x05z, 0x03z) -> Correct ECDSA_SECP384R1_SHA384
  | (0x06z, 0x03z) -> Correct ECDSA_SECP521R1_SHA512
  | (0x08z, 0x04z) -> Correct RSA_PSS_SHA256
  | (0x08z, 0x05z) -> Correct RSA_PSS_SHA384
  | (0x08z, 0x06z) -> Correct RSA_PSS_SHA512
  //| (0x08z, 0x07z) -> Correct ED25519_SHA512
  //| (0x08z, 0x08z) -> Correct ED448_SHAKE256
  | (0x02z, 0x01z) -> Correct RSA_PKCS1_SHA1
  | (0xFFz, 0xFFz) -> Correct RSA_PKCS1_MD5SHA1
  | (0x02z, 0x03z) -> Correct ECDSA_SHA1
  | (0x02z, 0x02z) -> Correct DSA_SHA1
  | (0x04z, 0x02z) -> Correct DSA_SHA256
  | (0x05z, 0x02z) -> Correct DSA_SHA384
  | (0x06z, 0x02z) -> Correct DSA_SHA512
  | (x, y) ->
    let v = int_of_bytes b in
    if v <> 0x0401 && v <> 0x0501 && v <> 0x0601 && v <> 0x0403
       && v <> 0x0503 && v <> 0x0603 && v <> 0x0804 && v <> 0x0805
       && v <> 0x0806 && v <> 0x0201 && v <> 0xFFFF && v <> 0x0203
       && v <> 0x0202 && v <> 0x0402 && v <> 0x0502 && v <> 0x0602
    then
      Correct (SIG_UNKNOWN b)
    else // Unreachable
      Error(AD_decode_error, "Parsed invalid SignatureScheme " ^ print_bytes b)

val sigHashAlg_of_signatureScheme:
  scheme:signatureScheme{~(SIG_UNKNOWN? scheme)} -> sigAlg * hashAlg
let sigHashAlg_of_signatureScheme =
  let open Hashing.Spec in
  function
  | RSA_PKCS1_SHA256       -> (RSASIG, Hash SHA256)
  | RSA_PKCS1_SHA384       -> (RSASIG, Hash SHA384)
  | RSA_PKCS1_SHA512       -> (RSASIG, Hash SHA512)
  | ECDSA_SECP256R1_SHA256 -> (ECDSA,  Hash SHA256)
  | ECDSA_SECP384R1_SHA384 -> (ECDSA,  Hash SHA384)
  | ECDSA_SECP521R1_SHA512 -> (ECDSA,  Hash SHA512)
  | RSA_PSS_SHA256         -> (RSAPSS, Hash SHA256)
  | RSA_PSS_SHA384         -> (RSAPSS, Hash SHA384)
  | RSA_PSS_SHA512         -> (RSAPSS, Hash SHA512)
//  | ED25519_SHA512         -> (EdDSA,  Hash SHA512)
//  | ED448_SHAKE256         -> (EdDSA,  Hash SHAKE256)
  | RSA_PKCS1_SHA1         -> (RSASIG, Hash SHA1)
  | RSA_PKCS1_MD5SHA1      -> (RSASIG, MD5SHA1)
  | ECDSA_SHA1             -> (ECDSA,  Hash SHA1)
  | DSA_SHA1               -> (DSA,    Hash SHA1)
  | DSA_SHA256             -> (DSA,    Hash SHA256)
  | DSA_SHA384             -> (DSA,    Hash SHA384)
  | DSA_SHA512             -> (DSA,    Hash SHA512)

val signatureScheme_of_sigHashAlg: sigAlg -> hashAlg -> signatureScheme
let signatureScheme_of_sigHashAlg sa ha =
  let open Hashing.Spec in
  match sa, ha with
  | (RSASIG, Hash SHA256) -> RSA_PKCS1_SHA256
  | (RSASIG, Hash SHA384) -> RSA_PKCS1_SHA384
  | (RSASIG, Hash SHA512) -> RSA_PKCS1_SHA512
  | (ECDSA,  Hash SHA256) -> ECDSA_SECP256R1_SHA256
  | (ECDSA,  Hash SHA384) -> ECDSA_SECP384R1_SHA384
  | (ECDSA,  Hash SHA512) -> ECDSA_SECP521R1_SHA512
  | (RSAPSS, Hash SHA256) -> RSA_PSS_SHA256
  | (RSAPSS, Hash SHA384) -> RSA_PSS_SHA384
  | (RSAPSS, Hash SHA512) -> RSA_PSS_SHA512
  //| (EdDSA,  Hash SHA512) -> ED25519_SHA512
  //| (EdDSA,  Hash SHAKE256) -> ED448_SHAKE256
  | (RSASIG, Hash SHA1)   -> RSA_PKCS1_SHA1
  | (ECDSA,  Hash SHA1)   -> ECDSA_SHA1
  | (DSA,    Hash SHA1)   -> DSA_SHA1
  | (DSA,    Hash SHA256) -> DSA_SHA256
  | (DSA,    Hash SHA384) -> DSA_SHA384
  | (DSA,    Hash SHA512) -> DSA_SHA512
  | (RSASIG, MD5SHA1)     -> RSA_PKCS1_MD5SHA1
  | _ -> // Map everything else to OBSOLETE 0x0000
    lemma_repr_bytes_values 0x0000;
    int_of_bytes_of_int #2 0x0000;
    SIG_UNKNOWN (bytes_of_int 2 0)



/// COMPRESSION (LARGELY DEPRECATED IN TLS 1.3)
/// QD fodder
///
(** Compression definition *)
type compression =
  | NullCompression
  | UnknownCompression of (b:byte{b <> 0z})

(** Serializing function for compression algorithms *)
val compressionBytes: compression -> Tot (lbytes 1)
let compressionBytes comp =
  match comp with
  | NullCompression      -> abyte 0z
  | UnknownCompression b -> abyte b

// Not pinverse_t compressionBytes, because it never fails

(** Parsing function for compression algorithm *)
val parseCompression: b:lbytes 1
  -> Tot (cm:compression{compressionBytes cm == b})
let parseCompression b =
  assume false; //18-02-23 to get the refinement above with FStar.Bytes
  match b.[0ul] with
  | 0z -> Seq.lemma_eq_intro (Bytes.reveal (abyte 0z)) (Bytes.reveal b);
         NullCompression
  | b  -> UnknownCompression b

// We ignore compression methods we don't understand. This is a departure
// from usual parsing, where we fail on unknown values, but that's how TLS
// handles compression method lists.

type compressions = cms: list compression {List.length cms <= 254}

(** Parsing function for compression algorithm lists *)
val parseCompressions:
  b:bytes {length b <= 254} ->
  Tot (cms: compressions {List.length cms = length b}) (decreases (length b))
let rec parseCompressions b =
  if length b = 0
  then
    let cms: list compression = [] in
    assert_norm (List.length cms = 0); //libraries?
    cms
  else (
    let cmB,b' = split b 1ul in
    let cm = parseCompression cmB in
    let cms' = parseCompressions b' in
    let cms = cm :: cms' in
    assert_norm(List.length cms = 1 + List.length cms'); //library?
    cms )

//#set-options "--max_fuel 1 --initial_fuel 1 --max_ifuel 1 --initial_ifuel 1"

(** Serializing function for lists of compression algorithms *)
val compressionMethodsBytes:
  cms: compressions -> Tot (lbytes (List.Tot.length cms))
let rec compressionMethodsBytes cms =
  match cms with
  | c::cs -> compressionBytes c @| compressionMethodsBytes cs
  | []   -> empty_bytes



/// CIPHERSUITES, with new structure for TLS 1.3
/// 18-02-22 QD fodder, will require a manual translation as we
/// primarily use this structured ADT --- see also cipherSuiteName
/// below, closer to the RFC.

include Parsers.Parse_cipherSuite // for TLS_ECDHE_PSK_WITH_AES_128_CCM_SHA256

(** Ciphersuite definition *)
type cipherSuite =
  | NullCipherSuite: cipherSuite
  | CipherSuite    : kexAlg -> option sigAlg -> aeAlg -> cipherSuite
  | CipherSuite13  : aeadAlg -> hash_alg -> cipherSuite
  | SCSV           : cipherSuite
  | UnknownCipherSuite: (r: cipherSuite_repr { not (known_cipherSuite_repr r) })  -> cipherSuite

(** Determine if a ciphersuite implies no peer authentication *)
let isAnonCipherSuite cs =
  match cs with
  | CipherSuite Kex_DHE None _ -> true
  | _ -> false

(** Determine if a ciphersuite implies using (EC)Diffie-Hellman KEX *)
let isDHECipherSuite cs =
  match cs with
  | CipherSuite Kex_DHE (Some DSA) _      -> true
  | CipherSuite Kex_DHE (Some RSASIG) _   -> true
  | CipherSuite Kex_ECDHE (Some ECDSA) _  -> true
  | CipherSuite Kex_ECDHE (Some RSASIG) _ -> true
  | _ -> false

(** Determine if a ciphersuite implies using Elliptic Curves Diffie-Hellman KEX *)
let isECDHECipherSuite cs =
  match cs with
  | CipherSuite Kex_ECDHE (Some ECDSA) _  -> true
  | CipherSuite Kex_ECDHE (Some RSASIG) _ -> true
  | _ -> false

(** Determine if a ciphersuite implies using plain Diffie-Hellman KEX *)
let isDHCipherSuite cs =
  match cs with
  | CipherSuite Kex_DH (Some DSA) _    -> true
  | CipherSuite Kex_DH (Some RSASIG) _ -> true
  | _ -> false

(** Determine if a ciphersuite implies using an RSA key exchange *)
let isRSACipherSuite cs =
  match cs with
  | CipherSuite Kex_RSA None _ -> true
  | _ -> false

(** Determine if a ciphersuite implies using MAC only and no encryption *)
let isOnlyMACCipherSuite cs =
  match cs with
  | CipherSuite _ _ (MACOnly _) -> true
  | _ -> false

(** Determine the signature algorithm associated to a ciphersuite *)
// 2018.05.14 SZ: TODO: turn this into a total function
val sigAlg_of_ciphersuite (cs:cipherSuite) : Dv sigAlg
let sigAlg_of_ciphersuite cs =
  match cs with
  | CipherSuite Kex_RSA None _
  | CipherSuite Kex_ECDHE (Some RSASIG) _
  | CipherSuite Kex_DHE (Some RSASIG) _
  | CipherSuite Kex_DH (Some RSASIG) _   -> RSASIG
  | CipherSuite Kex_DHE (Some DSA) _
  | CipherSuite Kex_DH (Some DSA) _      -> DSA
  | CipherSuite Kex_ECDHE (Some ECDSA) _ -> ECDSA
  | _ -> unexpected "[sigAlg_of_ciphersuite] invoked on a wrong ciphersuite"

(** Determine if a ciphersuite list contains the SCSV ciphersuite *)
let contains_SCSV (css: list cipherSuite) = List.Tot.mem SCSV css

inline_for_extraction
type cipherSuiteName = (x: Parsers.Parse_cipherSuite.cipherSuite {not (Parsers.Parse_cipherSuite.Unknown_cipherSuite? x) })

#reset-options "--z3rlimit 16 --max_fuel 1 --initial_fuel 1 --max_ifuel 2 --initial_ifuel 2 --using_facts_from '* -LowParse.Spec.Base'"

(** Determine the validity of a ciphersuite based on it's name *)
val cipherSuite_of_name: cipherSuiteName -> Tot cipherSuite
let cipherSuite_of_name =
  let open EverCrypt in 
  let open Hashing.Spec in function
  | TLS_NULL_WITH_NULL_NULL                -> NullCipherSuite

  | TLS_AES_128_GCM_SHA256                 -> CipherSuite13 AES128_GCM       SHA256
  | TLS_AES_256_GCM_SHA384                 -> CipherSuite13 AES256_GCM       SHA384
  | TLS_CHACHA20_POLY1305_SHA256           -> CipherSuite13 CHACHA20_POLY1305 SHA256
  | TLS_AES_128_CCM_SHA256                 -> CipherSuite13 AES128_CCM       SHA256
  | TLS_AES_128_CCM_8_SHA256               -> CipherSuite13 AES128_CCM8     SHA256

  | TLS_RSA_WITH_NULL_MD5                  -> CipherSuite Kex_RSA None (MACOnly MD5)
  | TLS_RSA_WITH_NULL_SHA                  -> CipherSuite Kex_RSA None (MACOnly SHA1)
  | TLS_RSA_WITH_NULL_SHA256               -> CipherSuite Kex_RSA None (MACOnly SHA256)
  | TLS_RSA_WITH_RC4_128_MD5               -> CipherSuite Kex_RSA None (MtE (Stream RC4_128) MD5)
  | TLS_RSA_WITH_RC4_128_SHA               -> CipherSuite Kex_RSA None (MtE (Stream RC4_128) SHA1)
  | TLS_RSA_WITH_3DES_EDE_CBC_SHA          -> CipherSuite Kex_RSA None (MtE (Block TDES_EDE_CBC) SHA1)
  | TLS_RSA_WITH_AES_128_CBC_SHA           -> CipherSuite Kex_RSA None (MtE (Block AES128_CBC) SHA1)
  | TLS_RSA_WITH_AES_256_CBC_SHA           -> CipherSuite Kex_RSA None (MtE (Block AES256_CBC) SHA1)
  | TLS_RSA_WITH_AES_128_CBC_SHA256        -> CipherSuite Kex_RSA None (MtE (Block AES128_CBC) SHA256)
  | TLS_RSA_WITH_AES_256_CBC_SHA256        -> CipherSuite Kex_RSA None (MtE (Block AES256_CBC) SHA256)

  | TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA      -> CipherSuite Kex_DHE (Some DSA) (MtE (Block TDES_EDE_CBC) SHA1)
  | TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA      -> CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)
  | TLS_DHE_DSS_WITH_AES_128_CBC_SHA       -> CipherSuite Kex_DHE (Some DSA) (MtE (Block AES128_CBC) SHA1)
  | TLS_DHE_RSA_WITH_AES_128_CBC_SHA       -> CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES128_CBC) SHA1)
  | TLS_DHE_DSS_WITH_AES_256_CBC_SHA       -> CipherSuite Kex_DHE (Some DSA) (MtE (Block AES256_CBC) SHA1)
  | TLS_DHE_RSA_WITH_AES_256_CBC_SHA       -> CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES256_CBC) SHA1)
  | TLS_DHE_DSS_WITH_AES_128_CBC_SHA256    -> CipherSuite Kex_DHE (Some DSA) (MtE (Block AES128_CBC) SHA256)
  | TLS_DHE_RSA_WITH_AES_128_CBC_SHA256    -> CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES128_CBC) SHA256)
  | TLS_DHE_DSS_WITH_AES_256_CBC_SHA256    -> CipherSuite Kex_DHE (Some DSA) (MtE (Block AES256_CBC) SHA256)
  | TLS_DHE_RSA_WITH_AES_256_CBC_SHA256    -> CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES256_CBC) SHA256)

  | TLS_ECDHE_RSA_WITH_RC4_128_SHA         -> CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1)
  | TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA    -> CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)
  | TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA     -> CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES128_CBC) SHA1)
  | TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256  -> CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES128_CBC) SHA256)
  | TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA     -> CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES256_CBC) SHA1)
  | TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384  -> CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES256_CBC) SHA384)

  | TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 -> CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES128_GCM SHA256)
  | TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256  -> CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES128_GCM SHA256)
  | TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 -> CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES256_GCM SHA384)
  | TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384  -> CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES256_GCM SHA384)

  | TLS_DH_anon_WITH_RC4_128_MD5           -> CipherSuite Kex_DHE None (MtE (Stream RC4_128) MD5)
  | TLS_DH_anon_WITH_3DES_EDE_CBC_SHA      -> CipherSuite Kex_DHE None (MtE (Block TDES_EDE_CBC) SHA1)
  | TLS_DH_anon_WITH_AES_128_CBC_SHA       -> CipherSuite Kex_DHE None (MtE (Block AES128_CBC) SHA1)
  | TLS_DH_anon_WITH_AES_256_CBC_SHA       -> CipherSuite Kex_DHE None (MtE (Block AES256_CBC) SHA1)
  | TLS_DH_anon_WITH_AES_128_CBC_SHA256    -> CipherSuite Kex_DHE None (MtE (Block AES128_CBC) SHA256)
  | TLS_DH_anon_WITH_AES_256_CBC_SHA256    -> CipherSuite Kex_DHE None (MtE (Block AES256_CBC) SHA256)

  | TLS_RSA_WITH_AES_128_GCM_SHA256        -> CipherSuite Kex_RSA None          (AEAD AES128_GCM SHA256)
  | TLS_RSA_WITH_AES_256_GCM_SHA384        -> CipherSuite Kex_RSA None          (AEAD AES256_GCM SHA384)
  | TLS_DHE_RSA_WITH_AES_128_GCM_SHA256    -> CipherSuite Kex_DHE (Some RSASIG) (AEAD AES128_GCM SHA256)
  | TLS_DHE_RSA_WITH_AES_256_GCM_SHA384    -> CipherSuite Kex_DHE (Some RSASIG) (AEAD AES256_GCM SHA384)
  | TLS_DH_RSA_WITH_AES_128_GCM_SHA256     -> CipherSuite Kex_DH  (Some RSASIG) (AEAD AES128_GCM SHA256)
  | TLS_DH_RSA_WITH_AES_256_GCM_SHA384     -> CipherSuite Kex_DH  (Some RSASIG) (AEAD AES256_GCM SHA384)
  | TLS_DHE_DSS_WITH_AES_128_GCM_SHA256    -> CipherSuite Kex_DHE (Some DSA)    (AEAD AES128_GCM SHA256)
  | TLS_DHE_DSS_WITH_AES_256_GCM_SHA384    -> CipherSuite Kex_DHE (Some DSA)    (AEAD AES256_GCM SHA384)
  | TLS_DH_DSS_WITH_AES_128_GCM_SHA256     -> CipherSuite Kex_DH  (Some DSA)    (AEAD AES128_GCM SHA256)
  | TLS_DH_DSS_WITH_AES_256_GCM_SHA384     -> CipherSuite Kex_DH  (Some DSA)    (AEAD AES256_GCM SHA384)
  | TLS_DH_anon_WITH_AES_128_GCM_SHA256    -> CipherSuite Kex_DHE None          (AEAD AES128_GCM SHA256)
  | TLS_DH_anon_WITH_AES_256_GCM_SHA384    -> CipherSuite Kex_DHE None          (AEAD AES256_GCM SHA384)
  | TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256    -> CipherSuite Kex_ECDHE (Some RSASIG) (AEAD CHACHA20_POLY1305 SHA256)
  | TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256  -> CipherSuite Kex_ECDHE (Some ECDSA) (AEAD CHACHA20_POLY1305 SHA256)
  | TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256      -> CipherSuite Kex_DHE (Some RSASIG) (AEAD CHACHA20_POLY1305 SHA256)
  | TLS_PSK_WITH_CHACHA20_POLY1305_SHA256          -> CipherSuite Kex_PSK None (AEAD CHACHA20_POLY1305 SHA256)
  | TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256    -> CipherSuite Kex_PSK_ECDHE None (AEAD CHACHA20_POLY1305 SHA256)
  | TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256      -> CipherSuite Kex_PSK_DHE None (AEAD CHACHA20_POLY1305 SHA256)


(** Determine the name of a ciphersuite based on its construction *)
let name_of_cipherSuite =
  let open EverCrypt in 
  let open Hashing.Spec in function
  | NullCipherSuite                                                      -> Correct TLS_NULL_WITH_NULL_NULL

  | CipherSuite13 AES128_GCM SHA256                                     -> Correct TLS_AES_128_GCM_SHA256
  | CipherSuite13 AES256_GCM SHA384                                     -> Correct TLS_AES_256_GCM_SHA384
  | CipherSuite13 CHACHA20_POLY1305 SHA256                               -> Correct TLS_CHACHA20_POLY1305_SHA256
  | CipherSuite13 AES128_CCM SHA256                                     -> Correct TLS_AES_128_CCM_SHA256
  | CipherSuite13 AES128_CCM8 SHA256                                   -> Correct TLS_AES_128_CCM_8_SHA256

  | CipherSuite Kex_RSA None (MACOnly MD5)                               -> Correct TLS_RSA_WITH_NULL_MD5
  | CipherSuite Kex_RSA None (MACOnly SHA1)                              -> Correct TLS_RSA_WITH_NULL_SHA
  | CipherSuite Kex_RSA None (MACOnly SHA256)                            -> Correct TLS_RSA_WITH_NULL_SHA256
  | CipherSuite Kex_RSA None (MtE (Stream RC4_128) MD5)                  -> Correct TLS_RSA_WITH_RC4_128_MD5
  | CipherSuite Kex_RSA None (MtE (Stream RC4_128) SHA1)                 -> Correct TLS_RSA_WITH_RC4_128_SHA
  | CipherSuite Kex_RSA None (MtE (Block TDES_EDE_CBC) SHA1)             -> Correct TLS_RSA_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_RSA None (MtE (Block AES128_CBC) SHA1)              -> Correct TLS_RSA_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_RSA None (MtE (Block AES256_CBC) SHA1)              -> Correct TLS_RSA_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_RSA None (MtE (Block AES128_CBC) SHA256)            -> Correct TLS_RSA_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_RSA None (MtE (Block AES256_CBC) SHA256)            -> Correct TLS_RSA_WITH_AES_256_CBC_SHA256

  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block TDES_EDE_CBC) SHA1)    -> Correct TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)    -> Correct TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES128_CBC) SHA1)     -> Correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES128_CBC) SHA1)     -> Correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES256_CBC) SHA1)     -> Correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES256_CBC) SHA1)     -> Correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES128_CBC) SHA256)   -> Correct TLS_DHE_DSS_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES128_CBC) SHA256)   -> Correct TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES256_CBC) SHA256)   -> Correct TLS_DHE_DSS_WITH_AES_256_CBC_SHA256
  | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES256_CBC) SHA256)   -> Correct TLS_DHE_RSA_WITH_AES_256_CBC_SHA256

  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1)      -> Correct TLS_ECDHE_RSA_WITH_RC4_128_SHA
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)  -> Correct TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES128_CBC) SHA1)   -> Correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES128_CBC) SHA256) -> Correct TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES256_CBC) SHA1)   -> Correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES256_CBC) SHA384) -> Correct TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384

  | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES128_GCM SHA256)        -> Correct TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES128_GCM SHA256)        -> Correct TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES256_GCM SHA384)        -> Correct TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES256_GCM SHA384)        -> Correct TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384

  | CipherSuite Kex_DHE None (MtE (Stream RC4_128) MD5)                  -> Correct TLS_DH_anon_WITH_RC4_128_MD5
  | CipherSuite Kex_DHE None (MtE (Block TDES_EDE_CBC) SHA1)             -> Correct TLS_DH_anon_WITH_3DES_EDE_CBC_SHA
  | CipherSuite Kex_DHE None (MtE (Block AES128_CBC) SHA1)              -> Correct TLS_DH_anon_WITH_AES_128_CBC_SHA
  | CipherSuite Kex_DHE None (MtE (Block AES256_CBC) SHA1)              -> Correct TLS_DH_anon_WITH_AES_256_CBC_SHA
  | CipherSuite Kex_DHE None (MtE (Block AES128_CBC) SHA256)            -> Correct TLS_DH_anon_WITH_AES_128_CBC_SHA256
  | CipherSuite Kex_DHE None (MtE (Block AES256_CBC) SHA256)            -> Correct TLS_DH_anon_WITH_AES_256_CBC_SHA256

  | CipherSuite Kex_RSA None          (AEAD AES128_GCM SHA256)          -> Correct TLS_RSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_RSA None          (AEAD AES256_GCM SHA384)          -> Correct TLS_RSA_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES128_GCM SHA256)          -> Correct TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES256_GCM SHA384)          -> Correct TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DH  (Some RSASIG) (AEAD AES128_GCM SHA256)          -> Correct TLS_DH_RSA_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DH  (Some RSASIG) (AEAD AES256_GCM SHA384)          -> Correct TLS_DH_RSA_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DHE (Some DSA)    (AEAD AES128_GCM SHA256)          -> Correct TLS_DHE_DSS_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DHE (Some DSA)    (AEAD AES256_GCM SHA384)          -> Correct TLS_DHE_DSS_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DH  (Some DSA)    (AEAD AES128_GCM SHA256)          -> Correct TLS_DH_DSS_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DH  (Some DSA)    (AEAD AES256_GCM SHA384)          -> Correct TLS_DH_DSS_WITH_AES_256_GCM_SHA384
  | CipherSuite Kex_DHE None          (AEAD AES128_GCM SHA256)          -> Correct TLS_DH_anon_WITH_AES_128_GCM_SHA256
  | CipherSuite Kex_DHE None          (AEAD AES256_GCM SHA384)          -> Correct TLS_DH_anon_WITH_AES_256_GCM_SHA384

  | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD CHACHA20_POLY1305 SHA256)  -> Correct TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256
  | CipherSuite Kex_ECDHE (Some ECDSA) (AEAD CHACHA20_POLY1305 SHA256)   -> Correct TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256
  | CipherSuite Kex_DHE (Some RSASIG) (AEAD CHACHA20_POLY1305 SHA256)    -> Correct TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256
  | CipherSuite Kex_PSK None (AEAD CHACHA20_POLY1305 SHA256)             -> Correct TLS_PSK_WITH_CHACHA20_POLY1305_SHA256
  | CipherSuite Kex_PSK_ECDHE None (AEAD CHACHA20_POLY1305 SHA256)       -> Correct TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256
  | CipherSuite Kex_PSK_DHE None (AEAD CHACHA20_POLY1305 SHA256)         -> Correct TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256

  | _ -> Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Invoked on a unknown ciphersuite")


/// 18-02-22 The parsers and formatters below are used only in
/// HandshakeMessages, should move there and disappear
/// (except for parseCipherSuite, also used in Ticket)

(* JK: injectivity proof requires extra specification for the
   UnknownCipherSuite objects as they have to be distinct from the
   'correct' ones *)

val cipherSuiteBytesOpt: cipherSuite -> Tot (option (lbytes 2))
let cipherSuiteBytesOpt cs =
  let open EverCrypt in
  let open Hashing.Spec in
  let twobytes b: option (FStar.Bytes.lbytes 2) = Some (FStar.Bytes.twobytes b) in
    match cs with
    | UnknownCipherSuite b1 b2 -> twobytes (b1,b2)
    | NullCipherSuite                                              -> twobytes ( 0x00z, 0x00z )

    | CipherSuite13 AES128_GCM        SHA256                       -> twobytes ( 0x13z, 0x01z )
    | CipherSuite13 AES256_GCM        SHA384                       -> twobytes ( 0x13z, 0x02z )
    | CipherSuite13 CHACHA20_POLY1305 SHA256                       -> twobytes ( 0x13z, 0x03z )
    | CipherSuite13 AES128_CCM        SHA256                       -> twobytes ( 0x13z, 0x04z )
    | CipherSuite13 AES128_CCM8       SHA256                       -> twobytes ( 0x13z, 0x05z )

    | CipherSuite Kex_RSA None (MACOnly MD5)                       -> twobytes ( 0x00z, 0x01z )
    | CipherSuite Kex_RSA None (MACOnly SHA1)                      -> twobytes ( 0x00z, 0x02z )
    | CipherSuite Kex_RSA None (MACOnly SHA256)                    -> twobytes ( 0x00z, 0x3Bz )
    | CipherSuite Kex_RSA None(MtE (Stream RC4_128) MD5)           -> twobytes ( 0x00z, 0x04z )
    | CipherSuite Kex_RSA None(MtE (Stream RC4_128) SHA1)          -> twobytes ( 0x00z, 0x05z )

    | CipherSuite Kex_RSA None(MtE (Block TDES_EDE_CBC) SHA1)      -> twobytes ( 0x00z, 0x0Az )
    | CipherSuite Kex_RSA None(MtE (Block AES128_CBC) SHA1)       -> twobytes ( 0x00z, 0x2Fz )
    | CipherSuite Kex_RSA None(MtE (Block AES256_CBC) SHA1)       -> twobytes ( 0x00z, 0x35z )
    | CipherSuite Kex_RSA None(MtE (Block AES128_CBC) SHA256)     -> twobytes ( 0x00z, 0x3Cz )
    | CipherSuite Kex_RSA None(MtE (Block AES256_CBC) SHA256)     -> twobytes ( 0x00z, 0x3Dz )

    (**************************************************************************)
    | CipherSuite Kex_DH (Some DSA)     (MtE (Block TDES_EDE_CBC) SHA1)   -> twobytes ( 0x00z, 0x0Dz )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block TDES_EDE_CBC) SHA1)   -> twobytes ( 0x00z, 0x10z )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block TDES_EDE_CBC) SHA1)   -> twobytes ( 0x00z, 0x13z )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)   -> twobytes ( 0x00z, 0x16z )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES128_CBC) SHA1)    -> twobytes ( 0x00z, 0x30z )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES128_CBC) SHA1)    -> twobytes ( 0x00z, 0x31z )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES128_CBC) SHA1)    -> twobytes ( 0x00z, 0x32z )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES128_CBC) SHA1)    -> twobytes ( 0x00z, 0x33z )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES256_CBC) SHA1)    -> twobytes ( 0x00z, 0x36z )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES256_CBC) SHA1)    -> twobytes ( 0x00z, 0x37z )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES256_CBC) SHA1)    -> twobytes ( 0x00z, 0x38z )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES256_CBC) SHA1)    -> twobytes ( 0x00z, 0x39z )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES128_CBC) SHA256)  -> twobytes ( 0x00z, 0x3Ez )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES128_CBC) SHA256)  -> twobytes ( 0x00z, 0x3Fz )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES128_CBC) SHA256)  -> twobytes ( 0x00z, 0x40z )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES128_CBC) SHA256)  -> twobytes ( 0x00z, 0x67z )

    | CipherSuite Kex_DH (Some DSA)     (MtE (Block AES256_CBC) SHA256)  -> twobytes ( 0x00z, 0x68z )
    | CipherSuite Kex_DH (Some RSASIG)  (MtE (Block AES256_CBC) SHA256)  -> twobytes ( 0x00z, 0x69z )
    | CipherSuite Kex_DHE (Some DSA)    (MtE (Block AES256_CBC) SHA256)  -> twobytes ( 0x00z, 0x6Az )
    | CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES256_CBC) SHA256)  -> twobytes ( 0x00z, 0x6Bz )

    (**************************************************************************)
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1)       -> twobytes ( 0xc0z, 0x11z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1)   -> twobytes ( 0xc0z, 0x12z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES128_CBC) SHA1)    -> twobytes ( 0xc0z, 0x13z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES256_CBC) SHA1)    -> twobytes ( 0xc0z, 0x14z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES128_CBC) SHA256)  -> twobytes ( 0xc0z, 0x27z )
    | CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES256_CBC) SHA384)  -> twobytes ( 0xc0z, 0x28z )

    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES128_GCM SHA256) -> twobytes ( 0xc0z, 0x2fz )
    | CipherSuite Kex_ECDHE (Some ECDSA)  (AEAD AES128_GCM SHA256) -> twobytes ( 0xc0z, 0x2bz )
    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES256_GCM SHA384) -> twobytes ( 0xc0z, 0x30z )
    | CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES256_GCM SHA384) -> twobytes ( 0xc0z, 0x2cz )

    (**************************************************************************)
    | CipherSuite Kex_PSK_DHE None (AEAD AES128_GCM SHA256) -> twobytes ( 0x00z, 0xaaz )
    | CipherSuite Kex_PSK_DHE None (AEAD AES256_GCM SHA384) -> twobytes ( 0x00z, 0xabz )
    | CipherSuite Kex_PSK_ECDHE None (AEAD AES128_GCM SHA256) -> twobytes ( 0xd0z, 0x01z )
    | CipherSuite Kex_PSK_ECDHE None (AEAD AES256_GCM SHA384) -> twobytes ( 0xd0z, 0x02z )

    (**************************************************************************)
    | CipherSuite Kex_DHE None   (MtE (Stream RC4_128) MD5)         -> twobytes ( 0x00z, 0x18z )
    | CipherSuite Kex_DHE None   (MtE (Block TDES_EDE_CBC) SHA1)    -> twobytes ( 0x00z, 0x1Bz )
    | CipherSuite Kex_DHE None   (MtE (Block AES128_CBC) SHA1)     -> twobytes ( 0x00z, 0x34z )
    | CipherSuite Kex_DHE None   (MtE (Block AES256_CBC) SHA1)     -> twobytes ( 0x00z, 0x3Az )
    | CipherSuite Kex_DHE None   (MtE (Block AES128_CBC) SHA256)   -> twobytes ( 0x00z, 0x6Cz )
    | CipherSuite Kex_DHE None   (MtE (Block AES256_CBC) SHA256)   -> twobytes ( 0x00z, 0x6Dz )

    (**************************************************************************)
    | CipherSuite Kex_RSA None     (AEAD AES128_GCM SHA256) -> twobytes( 0x00z, 0x9Cz )
    | CipherSuite Kex_RSA None     (AEAD AES256_GCM SHA384) -> twobytes( 0x00z, 0x9Dz )

    | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES128_GCM SHA256) -> twobytes( 0x00z, 0x9Ez )
    | CipherSuite Kex_DHE (Some RSASIG) (AEAD AES256_GCM SHA384) -> twobytes( 0x00z, 0x9Fz )
    | CipherSuite Kex_DH (Some RSASIG)  (AEAD AES128_GCM SHA256) -> twobytes( 0x00z, 0xA0z )
    | CipherSuite Kex_DH (Some RSASIG)  (AEAD AES256_GCM SHA384) -> twobytes( 0x00z, 0xA1z )

    | CipherSuite Kex_DHE (Some DSA) (AEAD AES128_GCM SHA256) -> twobytes( 0x00z, 0xA2z )
    | CipherSuite Kex_DHE (Some DSA) (AEAD AES256_GCM SHA384) -> twobytes( 0x00z, 0xA3z )
    | CipherSuite Kex_DH (Some DSA)  (AEAD AES128_GCM SHA256) -> twobytes( 0x00z, 0xA4z )
    | CipherSuite Kex_DH (Some DSA)  (AEAD AES256_GCM SHA384) -> twobytes( 0x00z, 0xA5z )

    | CipherSuite Kex_DHE None (AEAD AES128_GCM SHA256) -> twobytes( 0x00z, 0xA6z )
    | CipherSuite Kex_DHE None (AEAD AES256_GCM SHA384) -> twobytes( 0x00z, 0xA7z )

    (**************************************************************************)
    | CipherSuite Kex_ECDHE (Some RSASIG) (AEAD CHACHA20_POLY1305 SHA256) -> twobytes( 0xccz, 0xa8z )
    | CipherSuite Kex_ECDHE (Some ECDSA) (AEAD CHACHA20_POLY1305 SHA256)  -> twobytes( 0xccz, 0xa9z )
    | CipherSuite Kex_DHE (Some RSASIG) (AEAD CHACHA20_POLY1305 SHA256)   -> twobytes( 0xccz, 0xaaz )
    | CipherSuite Kex_PSK None (AEAD CHACHA20_POLY1305 SHA256)            -> twobytes( 0xccz, 0xabz )
    | CipherSuite Kex_PSK_ECDHE None (AEAD CHACHA20_POLY1305 SHA256)      -> twobytes( 0xccz, 0xacz )
    | CipherSuite Kex_PSK_DHE None (AEAD CHACHA20_POLY1305 SHA256)        -> twobytes( 0xccz, 0xadz )

    | SCSV -> twobytes ( 0x00z, 0xFFz )
    | _ -> None

let validCipherSuite (c:cipherSuite) = Some? (cipherSuiteBytesOpt c)
let valid_cipher_suite = c:cipherSuite{validCipherSuite c}

(** List of ciphersuite *)
type cipherSuites = cs: list valid_cipher_suite
  { let l = List.length cs in 0 <= l /\ l <= (65536/2 - 2)}

(** List of valid ciphersuite (redundant) *)
let valid_cipher_suites = cipherSuites

(** Serializing function for a valid ciphersuite *)
val cipherSuiteBytes: valid_cipher_suite -> Tot (lbytes 2)
let cipherSuiteBytes c = Some?.v (cipherSuiteBytesOpt c)


#reset-options "--z3rlimit 60 --max_fuel 1 --initial_fuel 1 --max_ifuel 2 --initial_ifuel 2"

(** Auxillary parsing function for ciphersuites *)
private
val parseCipherSuiteAux : lbytes 2 -> Tot (result (c:cipherSuite{validCipherSuite c}))
let parseCipherSuiteAux b =
  let open EverCrypt in 
  let open Hashing.Spec in
  match b.[0ul], b.[1ul] with
  | ( 0x00z, 0x00z ) -> Correct(NullCipherSuite)

  | ( 0x13z, 0x01z ) -> Correct (CipherSuite13 AES128_GCM SHA256)
  | ( 0x13z, 0x02z ) -> Correct (CipherSuite13 AES256_GCM SHA384)
  | ( 0x13z, 0x03z ) -> Correct (CipherSuite13 CHACHA20_POLY1305 SHA256)
  | ( 0x13z, 0x04z ) -> Correct (CipherSuite13 AES128_CCM SHA256)
  | ( 0x13z, 0x05z ) -> Correct (CipherSuite13 AES128_CCM8 SHA256)

  | ( 0x00z, 0x01z ) -> Correct(CipherSuite Kex_RSA None (MACOnly MD5))
  | ( 0x00z, 0x02z ) -> Correct(CipherSuite Kex_RSA None (MACOnly SHA1))
  | ( 0x00z, 0x3Bz ) -> Correct(CipherSuite Kex_RSA None (MACOnly SHA256))
  | ( 0x00z, 0x04z ) -> Correct(CipherSuite Kex_RSA None (MtE (Stream RC4_128) MD5))
  | ( 0x00z, 0x05z ) -> Correct(CipherSuite Kex_RSA None (MtE (Stream RC4_128) SHA1))

  | ( 0x00z, 0x0Az ) -> Correct(CipherSuite Kex_RSA None (MtE (Block TDES_EDE_CBC) SHA1))
  | ( 0x00z, 0x2Fz ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES128_CBC) SHA1))
  | ( 0x00z, 0x35z ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES256_CBC) SHA1))
  | ( 0x00z, 0x3Cz ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES128_CBC) SHA256))
  | ( 0x00z, 0x3Dz ) -> Correct(CipherSuite Kex_RSA None (MtE (Block AES256_CBC) SHA256))

  (**************************************************************************)
  | ( 0x00z, 0x0Dz ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block TDES_EDE_CBC) SHA1))
  | ( 0x00z, 0x10z ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))
  | ( 0x00z, 0x13z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block TDES_EDE_CBC) SHA1))
  | ( 0x00z, 0x16z ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))

  | ( 0x00z, 0x30z ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES128_CBC) SHA1))
  | ( 0x00z, 0x31z ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES128_CBC) SHA1))
  | ( 0x00z, 0x32z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES128_CBC) SHA1))
  | ( 0x00z, 0x33z ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES128_CBC) SHA1))

  | ( 0x00z, 0x36z ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES256_CBC) SHA1))
  | ( 0x00z, 0x37z ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES256_CBC) SHA1))
  | ( 0x00z, 0x38z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES256_CBC) SHA1))
  | ( 0x00z, 0x39z ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES256_CBC) SHA1))

  | ( 0x00z, 0x3Ez ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES128_CBC) SHA256))
  | ( 0x00z, 0x3Fz ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES128_CBC) SHA256))
  | ( 0x00z, 0x40z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES128_CBC) SHA256))
  | ( 0x00z, 0x67z ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES128_CBC) SHA256))

  | ( 0x00z, 0x68z ) -> Correct(CipherSuite Kex_DH (Some DSA) (MtE (Block AES256_CBC) SHA256))
  | ( 0x00z, 0x69z ) -> Correct(CipherSuite Kex_DH (Some RSASIG) (MtE (Block AES256_CBC) SHA256))
  | ( 0x00z, 0x6Az ) -> Correct(CipherSuite Kex_DHE (Some DSA) (MtE (Block AES256_CBC) SHA256))
  | ( 0x00z, 0x6Bz ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (MtE (Block AES256_CBC) SHA256))

  (**************************************************************************)
  | ( 0xc0z, 0x11z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Stream RC4_128) SHA1))
  | ( 0xc0z, 0x12z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block TDES_EDE_CBC) SHA1))
  | ( 0xc0z, 0x13z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES128_CBC) SHA1))
  | ( 0xc0z, 0x14z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES256_CBC) SHA1))
  | ( 0xc0z, 0x27z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES128_CBC) SHA256))
  | ( 0xc0z, 0x28z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (MtE (Block AES256_CBC) SHA384))

  (**************************************************************************)
  | ( 0xc0z, 0x2bz ) -> Correct(CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES128_GCM SHA256))
  | ( 0xc0z, 0x2fz ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES128_GCM SHA256))
  | ( 0xc0z, 0x2cz ) -> Correct(CipherSuite Kex_ECDHE (Some ECDSA) (AEAD AES256_GCM SHA384))
  | ( 0xc0z, 0x30z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (AEAD AES256_GCM SHA384))

  (**************************************************************************)
  | ( 0xd0z, 0x01z ) -> Correct(CipherSuite Kex_PSK_ECDHE None (AEAD AES128_GCM SHA256))
  | ( 0xd0z, 0x02z ) -> Correct(CipherSuite Kex_PSK_ECDHE None (AEAD AES256_GCM SHA384))

  (**************************************************************************)
  | ( 0x00z, 0x18z ) -> Correct(CipherSuite Kex_DHE None (MtE (Stream RC4_128) MD5))
  | ( 0x00z, 0x1Bz ) -> Correct(CipherSuite Kex_DHE None (MtE (Block TDES_EDE_CBC) SHA1))
  | ( 0x00z, 0x34z ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES128_CBC) SHA1))
  | ( 0x00z, 0x3Az ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES256_CBC) SHA1))
  | ( 0x00z, 0x6Cz ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES128_CBC) SHA256))
  | ( 0x00z, 0x6Dz ) -> Correct(CipherSuite Kex_DHE None (MtE (Block AES256_CBC) SHA256))

  (**************************************************************************)
  | ( 0x00z, 0x9Cz ) -> Correct(CipherSuite Kex_RSA None (AEAD AES128_GCM SHA256))
  | ( 0x00z, 0x9Dz ) -> Correct(CipherSuite Kex_RSA None (AEAD AES256_GCM SHA384))

  | ( 0x00z, 0x9Ez ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (AEAD AES128_GCM SHA256))
  | ( 0x00z, 0x9Fz ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (AEAD AES256_GCM SHA384))
  | ( 0x00z, 0xA0z ) -> Correct(CipherSuite Kex_DH (Some RSASIG)  (AEAD AES128_GCM SHA256))
  | ( 0x00z, 0xA1z ) -> Correct(CipherSuite Kex_DH (Some RSASIG)  (AEAD AES256_GCM SHA384))

  | ( 0x00z, 0xA2z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (AEAD AES128_GCM SHA256))
  | ( 0x00z, 0xA3z ) -> Correct(CipherSuite Kex_DHE (Some DSA) (AEAD AES256_GCM SHA384))
  | ( 0x00z, 0xA4z ) -> Correct(CipherSuite Kex_DH (Some DSA)  (AEAD AES128_GCM SHA256))
  | ( 0x00z, 0xA5z ) -> Correct(CipherSuite Kex_DH (Some DSA)  (AEAD AES256_GCM SHA384))

  | ( 0x00z, 0xA6z ) -> Correct(CipherSuite Kex_DHE None (AEAD AES128_GCM SHA256))
  | ( 0x00z, 0xA7z ) -> Correct(CipherSuite Kex_DHE None (AEAD AES256_GCM SHA384))

  (**************************************************************************)
  | ( 0x00z, 0xaaz ) -> Correct(CipherSuite Kex_PSK_DHE None (AEAD AES128_GCM SHA256))
  | ( 0x00z, 0xabz ) -> Correct(CipherSuite Kex_PSK_DHE None (AEAD AES256_GCM SHA384))

  (**************************************************************************)
  | ( 0xccz, 0xa8z ) -> Correct(CipherSuite Kex_ECDHE (Some RSASIG) (AEAD CHACHA20_POLY1305 SHA256))
  | ( 0xccz, 0xa9z ) -> Correct(CipherSuite Kex_ECDHE (Some ECDSA) (AEAD CHACHA20_POLY1305 SHA256))
  | ( 0xccz, 0xaaz ) -> Correct(CipherSuite Kex_DHE (Some RSASIG) (AEAD CHACHA20_POLY1305 SHA256))
  | ( 0xccz, 0xabz ) -> Correct(CipherSuite Kex_PSK None (AEAD CHACHA20_POLY1305 SHA256))
  | ( 0xccz, 0xacz ) -> Correct(CipherSuite Kex_PSK_ECDHE None (AEAD CHACHA20_POLY1305 SHA256))
  | ( 0xccz, 0xadz ) -> Correct(CipherSuite Kex_PSK_DHE None (AEAD CHACHA20_POLY1305 SHA256))

  (**************************************************************************)
  | ( 0x00z, 0xFFz ) -> Correct SCSV
  | (b1, b2) -> Correct(UnknownCipherSuite b1 b2)
// Was:  | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Parsed unknown cipher")

(** Parsing function for ciphersuites *)
val parseCipherSuite: pinverse_t cipherSuiteBytes
let parseCipherSuite b =
  match parseCipherSuiteAux b with
  | Correct c -> Correct c
  | Error z -> Error z

#reset-options "--z3rlimit 60 --max_ifuel 6 --initial_ifuel 6 --max_fuel 1 --initial_fuel 1"

(** Lemma for ciphersuite serializing/parsing inversions *)
val inverse_cipherSuite: x:cipherSuite -> Lemma
  (requires (~ (UnknownCipherSuite? x)))
  // parse (bytes (Unknown 0 0)) = NullCiphersuite
  // must exclude this case...
  (ensures (let y = cipherSuiteBytesOpt x in
    (Some? y ==> parseCipherSuiteAux (Some?.v y) = Correct x)))
  [SMTPat (parseCipherSuiteAux (Some?.v (cipherSuiteBytesOpt x)))]
let inverse_cipherSuite x = admit()

(** Lemma for ciphersuite serializing/parsing inversions *)
val pinverse_cipherSuite : x:lbytes 2 -> Lemma
  (requires True)
  (ensures (let y = parseCipherSuiteAux x in
    ( Correct? y ==>
      ( if UnknownCipherSuite? (Correct?._0 y) then true
        else Some? (cipherSuiteBytesOpt (Correct?._0 y))
               /\ Bytes.equal x (Some?.v (cipherSuiteBytesOpt (Correct?._0 y)))))))
  [SMTPat (cipherSuiteBytesOpt (Correct?._0 (parseCipherSuiteAux x)))]
let pinverse_cipherSuite x = admit()

#reset-options
#set-options "--max_ifuel 1 --initial_ifuel 1 --max_fuel 1 --initial_fuel 1"

(** Serializing function for a list of ciphersuite *)
val cipherSuitesBytes:
  cs: list valid_cipher_suite {List.length cs <= 65536} -> Tot (lbytes (op_Multiply 2 (List.length cs))) (decreases cs)
let rec cipherSuitesBytes cs =
  match cs with
  | [] -> empty_bytes
  | c::cs -> cipherSuiteBytes c @| cipherSuitesBytes cs

// Called by the server handshake;
// ciphersuites that we do not understand are parsed, but ignored

// type cipherSuites = cs: list valid_cipher_suite
//   { let l = List.length cs in 1 <= l /\ l <= (65536/2 - 2)}

#reset-options "--max_ifuel 2 --initial_ifuel 2 --max_fuel 2 --initial_fuel 2 --z3cliopt smt.arith.nl=false --z3rlimit 16 --using_facts_from '* -LowParse.Spec.Base'"

(** Parsing function for a list of ciphersuites *)
val parseCipherSuites: b:bytes -> Tot cipherSuites (decreases (length b))
let rec parseCipherSuites b =
  if length b > 1 then
    let (b0, b1) = split b 2ul in
    let rest = parseCipherSuites b1 in
    match parseCipherSuite b0 with
    | Correct cs ->
      if List.length rest < 65536/2 - 3
      then cs :: rest
      else rest
    | _ -> rest
  else
   []


#reset-options "--max_ifuel 2 --initial_ifuel 2 --max_fuel 2 --initial_fuel 2"

// (** Lemma for ciphersuite lists serializing/parsing inversions *)
// val inverse_cipherSuites: x:list (c:cipherSuite{validCipherSuite c}) -> Lemma
//   (requires (true))
//   (ensures (parseCipherSuites (cipherSuitesBytes x) = Correct x))
//   [SMTPat (parseCipherSuites (cipherSuitesBytes x))]
// let rec inverse_cipherSuites x =
//   match x with
//   | [] -> ()
//   | cs::css ->
//      assume (~ (UnknownCipherSuite? cs)); // TODO enforce it
//      let b = (cipherSuiteBytes cs) @| (cipherSuitesBytes css) in
//      let (b0,b1) = split b 2ul in
//      //lemma_append_inj b0 b1 (cipherSuiteBytes cs) (cipherSuitesBytes css); //TODO bytes NS 09/27
//      inverse_cipherSuite cs;
//      inverse_cipherSuites css

/// 18-02-22 QD fodder? An auxiliary (largely redundant) enum for
/// ciphersuites, closer to the RFC and used for configuration in the
/// TLS APIs.
///
(** Ciphersuite names definition *)
type cipherSuiteName =
  | TLS_NULL_WITH_NULL_NULL

  | TLS_AES_128_GCM_SHA256
  | TLS_AES_256_GCM_SHA384
  | TLS_CHACHA20_POLY1305_SHA256
  | TLS_AES_128_CCM_SHA256
  | TLS_AES_128_CCM_8_SHA256

  | TLS_RSA_WITH_NULL_MD5
  | TLS_RSA_WITH_NULL_SHA
  | TLS_RSA_WITH_NULL_SHA256
  | TLS_RSA_WITH_RC4_128_MD5
  | TLS_RSA_WITH_RC4_128_SHA
  | TLS_RSA_WITH_3DES_EDE_CBC_SHA
  | TLS_RSA_WITH_AES_128_CBC_SHA
  | TLS_RSA_WITH_AES_256_CBC_SHA
  | TLS_RSA_WITH_AES_128_CBC_SHA256
  | TLS_RSA_WITH_AES_256_CBC_SHA256

  | TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA
  | TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA
  | TLS_DHE_DSS_WITH_AES_128_CBC_SHA
  | TLS_DHE_RSA_WITH_AES_128_CBC_SHA
  | TLS_DHE_DSS_WITH_AES_256_CBC_SHA
  | TLS_DHE_RSA_WITH_AES_256_CBC_SHA
  | TLS_DHE_DSS_WITH_AES_128_CBC_SHA256
  | TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
  | TLS_DHE_DSS_WITH_AES_256_CBC_SHA256
  | TLS_DHE_RSA_WITH_AES_256_CBC_SHA256

  | TLS_ECDHE_RSA_WITH_RC4_128_SHA
  | TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
  | TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
  | TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
  | TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
  | TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384

  | TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
  | TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
  | TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
  | TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384

  | TLS_DH_anon_WITH_RC4_128_MD5
  | TLS_DH_anon_WITH_3DES_EDE_CBC_SHA
  | TLS_DH_anon_WITH_AES_128_CBC_SHA
  | TLS_DH_anon_WITH_AES_256_CBC_SHA
  | TLS_DH_anon_WITH_AES_128_CBC_SHA256
  | TLS_DH_anon_WITH_AES_256_CBC_SHA256

  | TLS_RSA_WITH_AES_128_GCM_SHA256
  | TLS_RSA_WITH_AES_256_GCM_SHA384
  | TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
  | TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
  | TLS_DH_RSA_WITH_AES_128_GCM_SHA256
  | TLS_DH_RSA_WITH_AES_256_GCM_SHA384
  | TLS_DHE_DSS_WITH_AES_128_GCM_SHA256
  | TLS_DHE_DSS_WITH_AES_256_GCM_SHA384
  | TLS_DH_DSS_WITH_AES_128_GCM_SHA256
  | TLS_DH_DSS_WITH_AES_256_GCM_SHA384
  | TLS_DH_anon_WITH_AES_128_GCM_SHA256
  | TLS_DH_anon_WITH_AES_256_GCM_SHA384

  | TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256
  | TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256
  | TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256
  | TLS_PSK_WITH_CHACHA20_POLY1305_SHA256
  | TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256
  | TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256

(** Definition of a list of ciphersuite *)
type cipherSuiteNames = list cipherSuiteName

#reset-options "--z3rlimit 60 --max_fuel 1 --initial_fuel 1 --max_ifuel 1 --initial_ifuel 1"

(** Return valid ciphersuites according to a list of ciphersuite names *)
val cipherSuites_of_nameList: l1:list cipherSuiteName
  -> Tot (l2: list valid_cipher_suite{List.Tot.length l2 = List.Tot.length l1})
let cipherSuites_of_nameList nameList =
  // REMARK: would trigger automatically if List.Tot.Properties is loaded
  List.Tot.map_lemma cipherSuite_of_name nameList;
  List.Tot.map cipherSuite_of_name nameList

#set-options "--max_ifuel 5 --initial_ifuel 5 --max_fuel 1 --initial_fuel 1"

(** Determine the names associated to a list of ciphersuite constructors *)
val names_of_cipherSuites : list valid_cipher_suite -> Tot (result cipherSuiteNames)
let rec names_of_cipherSuites css =
  match css with
  | [] -> Correct []
  | h::t ->
    begin
    match name_of_cipherSuite h with
    | Error(x,y) -> Error(x,y)
    | Correct n  ->
      begin
        match names_of_cipherSuites t with
        | Error(x,y)  -> Error(x,y)
        | Correct rem -> Correct (n::rem)
      end
    end


#reset-options "--admit_smt_queries true"

// Some of these could be hidden in Handshake.Secret

(** Definition for the PRF label type *)
type prflabel = bytes

(** Key schedule labels *)
let extract_label          = utf8_encode "master secret"
let extended_extract_label = utf8_encode "extended master secret"
let kdf_label              = utf8_encode "key expansion"

(** PRF definitions based on the protocol version *)
type prePrfAlg =
  | PRF_SSL3_nested         // MD5(SHA1(...)) for extraction and keygen
  | PRF_SSL3_concat         // MD5 @| SHA1    for VerifyData tags
  | PRF_TLS_1p01 of prflabel                       // MD5 xor SHA1
  | PRF_TLS_1p2 : prflabel -> macAlg -> prePrfAlg  // typically SHA256 but may depend on CS
  | PRF_TLS_1p3 // TBC

(** PRF associations *)
//BB.TODO: Documentation ?
type kefAlg_t = prePrfAlg
type kdfAlg_t = prePrfAlg
type vdAlg_t = protocolVersion * cipherSuite

// Only to be invoked with TLS 1.2 (hardcoded in previous versions)
// BB.TODO: Documentation ? Confirm that it is used with TLS 1.3 ! CF: no, for TLS 1.3 use tagLen a, e.g. 32 or 64
// let verifyDataLen_of_ciphersuite (cs:cipherSuite) = 12

// Only to be invoked with TLS 1.2 (hardcoded in previous versions)
val prfMacAlg_of_ciphersuite_aux: cipherSuite -> Tot (option macAlg)
let prfMacAlg_of_ciphersuite_aux =
  let open Hashing.Spec in function
  | CipherSuite  _ _  (MtE  _ _ )   -> Some SHA256
  | CipherSuite  _ _  (AEAD _ hAlg) -> Some hAlg
  | CipherSuite  _ _  (MACOnly _)   -> Some SHA256 //MK was (MACOnly hAlg) should it also be be (HMAC hAlg)?
  | _                               -> None

(** Determine if the tuple PV and CS is the correct association with PRF *)
let pvcs (pv:protocolVersion) (cs:cipherSuite) =
  match pv, cs with
  | TLS_1p3, CipherSuite13 _ _ -> true
  | TLS_1p3, CipherSuite _ _ _ -> false
  | pv, CipherSuite _ _ _ -> Some? (prfMacAlg_of_ciphersuite_aux cs)
  | _                 -> false

unfold type require_some (#a:Type) (#b:Type) ($f:(a -> Tot (option b))) =
  x:a{Some? (f x)} -> Tot b

let prfMacAlg_of_ciphersuite : require_some prfMacAlg_of_ciphersuite_aux =
  fun x -> Some?.v (prfMacAlg_of_ciphersuite_aux x)

// PRF and verifyData hash algorithms are potentially independent in TLS 1.2,
// so we use two distinct functions. However, all currently defined ciphersuites
// use the same hash algorithm, so the current implementation of the two functions
// is the same.

// Only to be invoked with TLS 1.2 (hardcoded in previous versions
// BB.TODO: Documentation ? Confirm that it is used with TLS 1.3 !
private
let verifyDataHashAlg_of_ciphersuite_aux =
  let open Hashing.Spec in function
  | CipherSuite _ _ (MtE  _ _) -> Some SHA256
  | CipherSuite _ _ (AEAD _ hAlg) -> Some hAlg
  | CipherSuite _ _ (MACOnly hAlg) -> Some SHA256
  | CipherSuite13 _ hAlg -> Some hAlg
  | _ -> None

// BB.TODO: Documentation ?
let verifyDataHashAlg_of_ciphersuite : require_some verifyDataHashAlg_of_ciphersuite_aux =
  fun x -> Some?.v (verifyDataHashAlg_of_ciphersuite_aux x)

(** Determine which session hash algorithm is to be used with the protocol version and ciphersuite *)
val sessionHashAlg: pv:protocolVersion -> cs:cipherSuite{pvcs pv cs} -> Tot hashAlg
let sessionHashAlg pv cs =
  let open Hashing.Spec in
  match pv with
  | TLS_1p3 -> let CipherSuite13 _ h = cs in Hash h
  | SSL_3p0 | TLS_1p0 | TLS_1p1 -> MD5SHA1 // FIXME: DSA uses only SHA1
  | TLS_1p2 -> Hash (verifyDataHashAlg_of_ciphersuite cs)

// TODO recheck this is the right hash for HKDF
// SZ: Right. The TLS 1.3 draft says "Where HMAC [RFC2104] uses
// the Hash algorithm for the handshake"

(** Determine the Authenticated Encryption algorithm associated with a ciphersuite *)
val get_aeAlg: cs:cipherSuite{ CipherSuite? cs \/ CipherSuite13? cs } -> Tot aeAlg
let get_aeAlg cs =
  match cs with
  | CipherSuite _ _ ae -> ae
  | CipherSuite13 a h -> AEAD a h

//(** Define the null authenticated encryption algorithm *)
// BB: Why does this default to MD5 ?
//let null_aeAlg = MACOnly MD5

(** Determine Encryption type to be used with a chosen PV and AE algorithm *)
val encAlg_of_aeAlg: (pv:protocolVersion) -> (a:aeAlg { MtE? a }) -> Tot (encAlg * ivMode)
let encAlg_of_aeAlg  pv ae =
  match pv,ae with
  | SSL_3p0, MtE (Block e) m -> (Block e),Stale
  | TLS_1p0, MtE (Block e) m -> (Block e),Stale
  | _, MtE e m -> e,Fresh

val macAlg_of_aeAlg: (pv:protocolVersion) -> (a:aeAlg { pv <> TLS_1p3 /\ ~(AEAD? a) }) -> Tot macAlg
let macAlg_of_aeAlg pv ae =
  match pv,ae with
  // 17-02-02 dropping support for weak ciphersuites. To be discussed!
  //  | SSL_3p0,MACOnly alg -> SSLKHash alg (* dropped pattern on the left to simplify refinements *)
  //  | SSL_3p0,MtE _ alg   -> SSLKHash alg
  //  | _      ,MACOnly alg -> SSLKHash alg
  | _      ,MACOnly alg
  | _      ,MtE _ alg   -> alg



/// 18-02-22 QD fodder
///
(** Certificate type definition *)
type certType =
  | RSA_sign
  | DSA_sign
  | RSA_fixed_dh
  | DSA_fixed_dh

(** Serializing function for the certificate type *)
val certTypeBytes: certType -> Tot (lbytes 1)
let certTypeBytes ct =
  match ct with
  | RSA_sign     -> abyte 1z
  | DSA_sign     -> abyte 2z
  | RSA_fixed_dh -> abyte 3z
  | DSA_fixed_dh -> abyte 4z

(** Parsing function for the certificate type *)
val parseCertType: pinverse_t certTypeBytes
let parseCertType b =
  match b.[0ul] with
  | 1z -> Correct RSA_sign
  | 2z -> Correct DSA_sign
  | 3z -> Correct RSA_fixed_dh
  | 4z -> Correct DSA_fixed_dh
  | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")

(** Lemmas associated to serializing/parsing of certificate types *)
val inverse_certType: x:_ -> Lemma
  (requires True)
  (ensures lemma_inverse_g_f certTypeBytes parseCertType x)
  [SMTPat (parseCertType (certTypeBytes x))]
let inverse_certType x = admit()

val pinverse_certType: x:_ -> Lemma
  (requires True)
  (ensures (lemma_pinverse_f_g Bytes.equal certTypeBytes parseCertType x))
  [SMTPat (certTypeBytes (Correct?._0 (parseCertType x)))]
let pinverse_certType x = admit()

#set-options "--max_fuel 1 --initial_fuel 1"

(** Serializing function for lists of certificate types *)
val certificateTypeListBytes: ctl:list certType {List.length ctl <= 256} -> Tot (lbytes (List.Tot.length ctl))
let rec certificateTypeListBytes ctl =
  match ctl with
  | [] -> empty_bytes
  | h::t ->
    let ct = certTypeBytes h in
    ct @| certificateTypeListBytes t

(** Parsing function for lists of certificate types *)
val parseCertificateTypeList: data:bytes -> Tot (list certType) (decreases (length data))
let rec parseCertificateTypeList data =
  if length data = 0 then []
  else
    let (thisByte,data) = split data 1ul in
    match parseCertType thisByte with
    | Error z -> // we skip this one
      parseCertificateTypeList data
    | Correct ct ->
      let rem = parseCertificateTypeList data in
      ct :: rem

#set-options "--max_ifuel 4 --initial_ifuel 1 --max_fuel 4 --initial_fuel 1"

(** Determine the certificate signature algorithms allowed according to the ciphersuite *)
val defaultCertTypes: bool -> cipherSuite -> HyperStack.All.ML (l:list certType{List.Tot.length l <= 1})

//17-12-26 TODO: get rid of this single use of ML
let defaultCertTypes sign cs =
  let alg = sigAlg_of_ciphersuite cs in
    if sign then
      match alg with
      | RSASIG -> [RSA_sign]
      | DSA -> [DSA_sign]
      | _ -> unexpected "[defaultCertTypes] invoked on an invalid ciphersuite"
    else
      match alg with
      | RSASIG -> [RSA_fixed_dh]
      | DSA -> [DSA_fixed_dh]
      | _ -> unexpected "[defaultCertTypes] invoked on an invalid ciphersuite"

#set-options "--max_ifuel 2 --initial_ifuel 2 --max_fuel 1 --initial_fuel 1"

(** Type definition of the Distinguished Name of a certificate *)
type dn = s:string{
  String.length s < 256 /\
  String.length s < pow2 30 /\ //18-02-23 improve precondition of [utf8_encode]?
  length(utf8_encode s) < 256}

(** Serializing function for a list of Distinguished Names of certificates *)
val distinguishedNameListBytes:
  names: list dn {List.length names <= 1024} -> // arbitrary bound
  b:bytes{length b <= op_Multiply 258 (List.Tot.length names)}
let rec distinguishedNameListBytes names =
  match names with
  | [] -> empty_bytes
  | h::t -> vlbytes2 (utf8_encode h) @| distinguishedNameListBytes t

(** Parsing function for a list of Distinguished Names of certificates *)
val parseDistinguishedNameList:
  data:bytes -> res:list dn -> Tot (result (list dn)) (decreases (length data))
//(* 18-02-24 I don't understand this error in pattern matching
let rec parseDistinguishedNameList data res =
  if length data = 0 then
    Correct res
  else
    if length data < 2 then
      Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
    else
      match vlsplit 2 data with
      | Error z -> Error z
      | Correct (nameBytes,data) ->
        begin
          match iutf8_opt nameBytes with
          | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
          | Some name ->
            if length (utf8_encode name) < 256 then
              let res = name :: res in
              parseDistinguishedNameList data res
            else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "")
        end

// TODO: move all the definitions below to a separate file / figure out whether
// they belong here ?
//
// TODO: all occurrences of [pinverse] from there on have been replaced by calls
// to [pinverse_t]; we should write corresponding inversion lemmas.



/// SIGNATURES
/// 18-02-22 QD fodder
///
let signatureSchemeList =
  algs:list signatureScheme{0 < List.Tot.length algs /\ op_Multiply 2 (List.Tot.length algs) < 65536}

// used in FFI
(** Serializing function for a SignatureScheme list *)

// FIXME(adl) this is serializing in reverse order (shb @| b)
let rec signatureSchemeListBytes_aux
  (algs: signatureSchemeList)
  (b:bytes)
  (algs':list signatureScheme{ length b + op_Multiply 2 (List.Tot.length algs') == op_Multiply 2 (List.Tot.length algs) })
: Tot (r:bytes{length r == op_Multiply 2 (List.Tot.length algs)})
  (decreases algs')
= match algs' with
  | [] -> b
  | alg::algs' ->
    let shb = signatureSchemeBytes alg in
    signatureSchemeListBytes_aux algs (shb @| b) algs'

private
let rec signatureSchemeListBytes_aux_is_injective
  (algs1: signatureSchemeList)
  (b1: bytes)
  (algs1': list signatureScheme{ length b1 + op_Multiply 2 (List.Tot.length algs1') == op_Multiply 2 (List.Tot.length algs1) })
  (algs2: signatureSchemeList { List.Tot.length algs1 == List.Tot.length algs2 } )
  (b2: bytes { length b1 == length b2 } )
  (algs2': list signatureScheme{ length b2 + op_Multiply 2 (List.Tot.length algs2') == op_Multiply 2 (List.Tot.length algs2) })
: Lemma
  (requires (Bytes.equal (signatureSchemeListBytes_aux algs1 b1 algs1') (signatureSchemeListBytes_aux algs2 b2 algs2')))
  (ensures (b1 == b2 /\ algs1' == algs2'))
  (decreases algs1')
= admit()
  // match algs1', algs2' with
  // | [], [] -> ()
  // | alg1::algs1_, alg2::algs2_ ->
  //   let shb1 = signatureSchemeBytes alg1 in
  //   let shb2 = signatureSchemeBytes alg2 in
  //   signatureSchemeListBytes_aux_is_injective algs1 (shb1 @| b1) algs1_ algs2 (shb2 @| b2) algs2_;
  //   //lemma_append_inj shb1 b1 shb2 b2; //TODO bytes NS 09/27
  //   signatureSchemeBytes_is_injective alg1 alg2

val signatureSchemeListBytes: algs:signatureSchemeList
  -> Tot (b:bytes{4 <= length b /\ length b < 65538})
let signatureSchemeListBytes algs =
  let pl = signatureSchemeListBytes_aux algs empty_bytes algs in
  lemma_repr_bytes_values (length pl);
  vlbytes 2 pl

/// 18-02-24 missing length bounds:
// let signatureSchemeListBytes_is_injective
//   (algs1: signatureSchemeList)
//   (s1: bytes)
//   (algs2: signatureSchemeList)
//   (s2: bytes)
// : Lemma
//   (requires (Bytes.equal (signatureSchemeListBytes algs1 @| s1) (signatureSchemeListBytes algs2 @| s2)))
//   (ensures (algs1 == algs2 /\ s1 == s2))
// = let pl1 = signatureSchemeListBytes_aux algs1 empty_bytes algs1 in
//   lemma_repr_bytes_values (length pl1);
//   let pl2 = signatureSchemeListBytes_aux algs2 empty_bytes algs2 in
//   lemma_repr_bytes_values (length pl2);
//   lemma_vlbytes_inj_strong 2 pl1 s1 pl2 s2;
//   signatureSchemeListBytes_aux_is_injective algs1 empty_bytes algs1 algs2 empty_bytes algs2

(** Parsing function for a SignatureScheme list *)
// FIXME(adl) this is parsing in reverse order (sha::algs)
val parseSignatureSchemeList: pinverse_t signatureSchemeListBytes
let rec parseSignatureSchemeList_aux: b:bytes -> algs:list signatureScheme -> b':bytes{length b' + op_Multiply 2 (List.Tot.length algs) == length b} ->
    Tot
      (result (algs:list signatureScheme{op_Multiply 2 (List.Tot.length algs) == length b}))
      (decreases (length b')) = fun b algs b' ->
    if length b' > 0 then
      if length b' >= 2 then
      let alg, bytes = split b' 2ul in
      match parseSignatureScheme alg with
      | Correct sha -> parseSignatureSchemeList_aux b (sha::algs) bytes
      | Error z     -> Error z
      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Too few bytes to parse sig hash algs")
    else Correct algs

let parseSignatureSchemeList b =
  match vlparse 2 b with
  | Correct b ->
    begin
    match parseSignatureSchemeList_aux b [] b with // Silly, but necessary for typechecking
    | Correct l -> Correct l
    | Error z -> Error z
    end
  | Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse sig hash algs")







// Moved here because it's used in both Extensions and TLSInfo and Extensions
// and Extensions cannot depend on TLSInfo
// -------------------------------------------------------------------
// Application configuration
// TODO Consider repackaging separate client and server options

(* discussion about IDs and configurations (Cedric, Antoine, Santiago)

Server Certificates?

- the client initial parameters...

- the server gets a CertSignQuery, picks its certificate chain from
  the ClientHello/ServerHello contents [new in miTLS 1.0]

- the client decides whether that's acceptable.

Certificate Request?

- in its ServerHello flight (or later) the server optionally requests a
  Cert/CertVerify (optionally with a list of CAs). This depends on
  what has been negotiated so far, including prior identities for
  both, and possibly on application data (e.g. ACL-based) [new in miTLS 1.0]

- the client optionally complies (for one of those CAs).
  [We always pass explicit requests to the client, as a CertSignQuery read result.]
  [We could have sign; read for solemnity; or read for simplicity.]

- the server decides whether that's acceptable.
  [We always pass inspection requests, as a CertVerifyQuery read result]
  [We have authorize; read for solemnity; could have read for simplicity.]

(forgetting about 0RTT for now)

type ServerCertificateRequest // something that determines this Handshake message

request_client_certificate: single_assign ServerCertificateRequest // uses this one, or asks the server; by default Some None.
*)





/// 18-02-22 QD fodder; their formatting is in Extensions.
///
type serverName =
  | SNI_DNS of b:bytes{repr_bytes (length b) <= 2}
  | SNI_UNKNOWN of (n:nat{repr_bytes n <= 1}) * (b:bytes{repr_bytes (length b) <= 2})

type alpn_entry = b:bytes{0 < length b /\ length b < 256}
type alpn = l:list alpn_entry{List.Tot.length l < 256}

type psk_identifier = identifier:bytes{length identifier < 65536}

type pskInfo = {
  ticket_nonce: option bytes;
  time_created: UInt32.t;
  ticket_age_add: UInt32.t;
  allow_early_data: bool;      // New draft 13 flag
  allow_dhe_resumption: bool;  // New draft 13 flag
  allow_psk_resumption: bool;  // New draft 13 flag
  early_ae: aeadAlg;
  early_hash: hash_alg;
  identities: bytes * bytes;
}

type ticketInfo =
  | TicketInfo_12 of protocolVersion * cipherSuite * ems:bool
  | TicketInfo_13 of pskInfo

type ticket_seal = b:bytes{length b < 65536}

// 2018.03.10 SZ: Allow it to modify [psk_region]?
// Missing refinements on arguments from types in PSK
type ticket_cb_fun =
  (FStar.Dyn.dyn -> sni:string -> ticket:bytes{length ticket < 65536} -> info:ticketInfo -> rawkey:bytes -> ST unit
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1))

noeq type ticket_cb = {
  ticket_context: FStar.Dyn.dyn;
  new_ticket: ticket_cb_fun;
}

type custom_extension = UInt16.t * b:bytes {length b < 65533}
type custom_extensions = l:list custom_extension{List.Tot.length l < 32}

(* Helper functions for the C API to construct the list from array *)
let empty_custom_extensions () : list custom_extension = []
let add_custom_extension (l:list custom_extension) (hd:UInt16.t) (b:bytes {length b < 65533}) =
  (hd, b) :: l

type nego_action =
  | Nego_abort: nego_action
  | Nego_retry: cookie_extra: bytes -> nego_action
  | Nego_accept: extra_ext: custom_extensions -> nego_action

type nego_cb_fun =
  (FStar.Dyn.dyn -> pv: protocolVersion -> client_ext: bytes -> cookie: option bytes -> ST nego_action
    (requires fun _ -> True)
    (ensures fun h0 r h1 -> Nego_retry? r ==> None? cookie /\ modifies_none h0 h1))

noeq type nego_cb = {
  nego_context: FStar.Dyn.dyn;
  negotiate: nego_cb_fun;
}

type cert_repr = b:bytes {length b < 16777216}
type cert_type = FFICallbacks.callbacks

noeq abstract
type cert_cb = {
  app_context : FStar.Dyn.dyn;
  (* Each callback takes an application context (app_context)
     and a function pointer to an application-provided functionality.

     The callback is actually performed in FFI.fst, which calls into ffi.c
     and takes care of marshalling miTLS parameters like signatureSchemeList
     to the types expected by the application.

     This explicit representation of closures is necessary for compiling this
     to C via KreMLin. The representation is hidden from callers and the wrappers
     are provided below to implement it.
   *)
  cert_select_ptr: FStar.Dyn.dyn;
  cert_select_cb:
    (FStar.Dyn.dyn -> FStar.Dyn.dyn -> pv:protocolVersion -> sni:bytes -> alpn:bytes -> sig:signatureSchemeList -> ST (option (cert_type * signatureScheme))
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1));

  cert_format_ptr: FStar.Dyn.dyn;
  cert_format_cb:
    (FStar.Dyn.dyn -> FStar.Dyn.dyn -> cert_type -> ST (list cert_repr)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1));

  cert_sign_ptr: FStar.Dyn.dyn;
  cert_sign_cb:
    (FStar.Dyn.dyn -> FStar.Dyn.dyn -> cert_type -> signatureScheme -> tbs:bytes -> ST (option bytes)
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1));

  cert_verify_ptr: FStar.Dyn.dyn;
  cert_verify_cb:
    (FStar.Dyn.dyn -> FStar.Dyn.dyn -> list cert_repr -> signatureScheme -> tbs:bytes -> sigv:bytes -> ST bool
    (requires fun _ -> True)
    (ensures fun h0 _ h1 -> modifies_none h0 h1));
}

abstract
let mk_cert_cb
    app_ctx
    cert_select_ptr
    cert_select_cb
    cert_format_ptr
    cert_format_cb
    cert_sign_ptr
    cert_sign_cb
    cert_verify_ptr
    cert_verify_cb = {
  app_context  = app_ctx;
  cert_select_ptr = cert_select_ptr;
  cert_select_cb = cert_select_cb;
  cert_format_ptr = cert_format_ptr;
  cert_format_cb = cert_format_cb;
  cert_sign_ptr = cert_sign_ptr;
  cert_sign_cb = cert_sign_cb;
  cert_verify_ptr = cert_verify_ptr;
  cert_verify_cb = cert_verify_cb
}

noeq type config : Type0 = {
    (* Supported versions, ciphersuites, groups, signature algorithms *)
    min_version: protocolVersion;
    max_version: protocolVersion;
    is_quic: bool; // Use QUIC labels for key derivations

    cipher_suites: x:valid_cipher_suites{List.Tot.length x < 256};
    named_groups: CommonDH.supportedNamedGroups;
    signature_algorithms: signatureSchemeList;

    (* Client side *)
    hello_retry: bool;          // honor hello retry requests from the server
    offer_shares: CommonDH.supportedNamedGroups;
    //18-02-20 should it be a subset of named_groups?
    custom_extensions: custom_extensions;
    use_tickets: list (psk_identifier * ticket_seal);

    (* Server side *)
    check_client_version_in_pms_for_old_tls: bool;
    request_client_certificate: bool; // TODO: generalize to CertificateRequest contents: a list of CAs.

    (* Common *)
    non_blocking_read: bool;
    max_early_data: option UInt32.t;   // 0-RTT offer (client) and support (server), and data limit
    safe_renegotiation: bool;     // demands this extension when renegotiating
    extended_master_secret: bool; // turn on RFC 7627 extended master secret support
    enable_tickets: bool;         // Client: offer ticket support; server: emit and accept tickets

    (* Callbacks *)
    ticket_callback: ticket_cb;   // Ticket callback, called when issuing or receiving a new ticket
    nego_callback: nego_cb;// Callback to decide stateless retry and negotiate extra extensions
    cert_callbacks: cert_cb;      // Certificate callbacks, called on all PKI-related operations

    alpn: option alpn;   // ALPN offers (for client) or preferences (for server)
    peer_name: option bytes;     // The expected name to match against the peer certificate
  }

let cert_select_cb (c:config) (pv:protocolVersion) (sni:bytes) (alpn:bytes) (sig:signatureSchemeList)
   : ST (option (cert_type * signatureScheme))
        (requires fun _ -> True)
        (ensures fun h0 _ h1 -> modifies_none h0 h1)
   = c.cert_callbacks.cert_select_cb
            c.cert_callbacks.app_context
            c.cert_callbacks.cert_select_ptr
            pv
            sni
            alpn
            sig

let cert_format_cb (c:config) (ct:cert_type)
   : ST (list cert_repr)
        (requires fun _ -> True)
        (ensures fun h0 _ h1 -> modifies_none h0 h1)
   = c.cert_callbacks.cert_format_cb
            c.cert_callbacks.app_context
            c.cert_callbacks.cert_format_ptr
            ct

let cert_sign_cb (c:config) (ct:cert_type) (ss:signatureScheme) (tbs:bytes)
   : ST (option bytes)
        (requires fun _ -> True)
        (ensures fun h0 _ h1 -> modifies_none h0 h1)
   = c.cert_callbacks.cert_sign_cb
            c.cert_callbacks.app_context
            c.cert_callbacks.cert_sign_ptr
            ct
            ss
            tbs

let cert_verify_cb (c:config) (cl:list cert_repr) (ss:signatureScheme) (tbs:bytes) (sigv:bytes)
   : ST bool
        (requires fun _ -> True)
        (ensures fun h0 _ h1 -> modifies_none h0 h1)
   = c.cert_callbacks.cert_verify_cb
            c.cert_callbacks.app_context
            c.cert_callbacks.cert_verify_ptr
            cl
            ss
            tbs
            sigv

type cVerifyData = b:bytes{length b <= 64} (* ClientFinished payload *)
type sVerifyData = b:bytes{length b <= 64} (* ServerFinished payload *)
