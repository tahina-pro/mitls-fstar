module QUIC

/// QUIC-specific interface on top of our main TLS API
/// * establishes session & exported keys: no application-data traffic!
/// * simplified configuration, with reasonable defaults
/// * TCP-like send/recv callbacks operate on caller-provided buffers
///   recv may yield (not enough input)
///   send is guaranteed to succeed (large enough output buffer expected)
///
/// Relying on FFI for accessing configs, callbacks, etc.
/// Testing both in OCaml (TCP-based, TestQUIC ~ TestFFI) and in C.

open Platform.Bytes
open Platform.Error
open TLSConstants
open TLSInfo
open Range
open DataStream
open TLS
open FFICallbacks

open FStar.HyperStack.All

#set-options "--lax"

(* A flag for runtime debugging of ffi data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("QIC| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if Flags.debug_QUIC then print else (fun _ -> ())


// an integer carrying the fatal alert descriptor
// we could also write txt into the application error log
type error = bytes 
private let errno description txt: ST error 
  (requires fun h0 -> True)
  (ensures fun h0 _ h1 -> h0 == h1) 
=
  trace ("returning error"^
    (match description with
    | Some ad -> " "^TLSError.string_of_ad ad
    | None    -> "")^": "^txt);
  Alert.alertBytes (match description with | Some a -> a | None -> TLSError.AD_internal_error)

/// TLS processing loop: we keep receiving and sending as long as we
/// can read.  Does not handle TLS termination (unused by QUIC?)
/// 
type result = 
  | TLS_would_block // requires more input to continue
  | TLS_error_local of error
  | TLS_error_alert of error  
  | TLS_secret0 // 0RTT exporter secret TODO
  | TLS_secret1 // 1RTT exporter secret TODO
  | TLS_ticket // server ticket TODO
  | TLS_complete // signalling handshake completion
  | TLS_refuse0 // TODO (still have to discard EOED)
 // do we ever need to return multiple signals?

val recv: Connection.connection -> St result
let rec recv c = 
  let i = currentId c Reader in 
  match read c i with 
  | Update false -> recv c // ignoring internal key changes
  | ReadWouldBlock -> TLS_would_block
  | Update true -> TLS_secret0 // TODO 0RTT, 0.5RTT, or 1RTT depending on c.
  | Complete -> TLS_complete
  | ReadError description txt -> TLS_error_local (errno description txt)
  | Read Close -> TLS_error_alert (errno (Some TLSError.AD_close_notify) "received close")
  | Read (Alert a) -> TLS_error_alert (errno (Some a) "received alert")
  | _ -> TLS_error_local (errno None "unexpected TLS read result")

/// Creation (no I/O yet)
/// 
let connect send recv client_config : ML Connection.connection =
  // we assume the configuration specifies the target SNI;
  // otherwise we should check after Complete that it matches the authenticated certificate chain.
  let tcp = Transport.callbacks send recv in
  let here = new_region HyperHeap.root in
  TLS.connect here tcp client_config

let accept send recv server_config : ML Connection.connection =
  let tcp = Transport.callbacks send recv in
  let here = new_region HyperHeap.root in
  TLS.accept_connected here tcp server_config

val ffiConnect: config:config -> callbacks:FFI.callbacks -> ML Connection.connection
let ffiConnect config cb =
  connect (FFI.sendTcpPacket cb) (FFI.recvTcpPacket cb) config

val ffiAcceptConnected: config:config -> callbacks:FFI.callbacks -> ML Connection.connection
let ffiAcceptConnected config cb =
  accept (FFI.sendTcpPacket cb) (FFI.recvTcpPacket cb) config

