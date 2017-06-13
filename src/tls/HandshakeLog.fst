(*--build-config
options:--fstar_home ../../../FStar --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection --use_hints --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../hacl-star/secure_api/LowCProvider/fst --include ../../../kremlin/kremlib --include ../../../hacl-star/specs --include ../../../hacl-star/code/lib/kremlin --include ../../../hacl-star/code/bignum --include ../../../hacl-star/code/experimental/aesgcm --include ../../../hacl-star/code/poly1305 --include ../../../hacl-star/code/salsa-family --include ../../../hacl-star/secure_api/test --include ../../../hacl-star/secure_api/utils --include ../../../hacl-star/secure_api/vale --include ../../../hacl-star/secure_api/uf1cma --include ../../../hacl-star/secure_api/prf --include ../../../hacl-star/secure_api/aead --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ../../src/tls/ideal-flags;
--*)
module HandshakeLog

open FStar.Heap
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Seq
 // for e.g. found
open FStar.Set
open Platform.Error
open Platform.Bytes
open TLSError
open TLSConstants
open TLSInfo
open HandshakeMessages
open Hashing
open Hashing.CRF // now using incremental, collision-resistant, agile Hashing.
module HH = FStar.HyperHeap
module HS = FStar.HyperStack


(* A flag for runtime debugging of handshakelog data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("HSL| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if Flags.debug_HSL then print else (fun _ -> ())


let erased_transcript : Type0 =
    if Flags.debug_HSL then hs_transcript
    else FStar.Ghost.erased hs_transcript

let reveal_log (l:erased_transcript) : GTot (hs_transcript) =
    if Flags.debug_HSL then l
    else FStar.Ghost.reveal l

let hide_log (l:hs_transcript) : Tot erased_transcript =
    if Flags.debug_HSL then l
    else FStar.Ghost.hide l

(** TODO: move to FStar.Ghost (breach of abstraction)  *)
let elift1_def (#a #b: Type) (f: (a -> GTot b)) (x: FStar.Ghost.erased a) : Lemma (FStar.Ghost.elift1 f x == FStar.Ghost.hide (f (FStar.Ghost.reveal x))) = ()

let ghost_bind
  (#a #b: Type)
  (x: erased a)
  (f: (
    (x': a) ->
    Pure (erased b)
    (requires (x' == FStar.Ghost.reveal x))
    (ensures (fun _ -> True))
  ))
: Tot (y: erased b { y == f (FStar.Ghost.reveal x) } )
= f (FStar.Ghost.reveal x)

let bind_log
  (l: erased_transcript)
  (f: (
    (x: hs_transcript) ->
    Pure erased_transcript
    (requires (x == reveal_log l))
    (ensures (fun _ -> True))
  ))
: Tot (y: erased_transcript { y == f (reveal_log l) } )
= if Flags.debug_HSL then f l
  else ghost_bind #hs_transcript #hs_transcript l f

let empty_hs_transcript : erased_transcript = hide_log []

let append_hs_transcript (l:erased_transcript) (ml:list msg { valid_transcript (reveal_log l @ ml) } ) : Tot erased_transcript =
    bind_log l (fun l' -> hide_log (append_transcript l' ml))

let extend_hs_transcript (l:erased_transcript) (m:msg { valid_transcript (reveal_log l @ [m]) } ) : Tot erased_transcript =
    append_hs_transcript l [m]

let print_hsl (hsl:erased_transcript) : Tot bool =
    if Flags.debug_HSL then
    let sl = List.Tot.map HandshakeMessages.string_of_handshakeMessage hsl in
    let s = List.Tot.fold_left (fun x y -> x^", "^y) "" sl in
    IO.debug_print_string ("Current log: " ^ s)
    else false

(* TODO: move to something like List.GTot *)
let rec gforall_list_to_list_refined
  (#a: Type)
  (f: (a -> GTot bool))
  (l: list a { gforall f l } )
: Tot (l': list (x: a {f x}))
= match l with
  | [] -> []
  | x :: q -> x :: gforall_list_to_list_refined f q

let transcript_bytes l =
  let v = transcript_version l in
  handshakeMessagesBytes v l

#set-options "--z3rlimit 64"

let transcript_format_version
  (ms ms': hs_transcript)
: Lemma
  (requires (Seq.equal (transcript_bytes ms) (transcript_bytes ms')))
  (ensures (transcript_version ms == transcript_version ms'))
= match ms with
  | [] -> assert (ms' == [])
  | ClientHello ch :: q0 ->
    let v = transcript_version ms in
    let v' = transcript_version ms' in
    let (ClientHello ch' :: q0') = ms' in
    clientHelloBytes_is_injective_strong ch (handshakeMessagesBytes v q0) ch' (handshakeMessagesBytes v' q0');
    begin match q0 with
    | [] -> assert (q0' == [])
    | Binders b :: q1 ->
      let (Binders b' :: q1') = q0' in
      lemma_append_inj (Extensions.bindersBytes b) (handshakeMessagesBytes v q1) (Extensions.bindersBytes b') (handshakeMessagesBytes v' q1');
      begin match q1 with
      | [] -> assert (q1' == [])
      | ServerHello sh :: q2 ->
        let (ServerHello sh' :: q2') = q1' in
        serverHelloBytes_is_injective_strong sh (handshakeMessagesBytes v q2) sh' (handshakeMessagesBytes v' q2')
      end
    | ServerHello sh :: q1 ->
      let (ServerHello sh' :: q1') = q0' in
      serverHelloBytes_is_injective_strong sh (handshakeMessagesBytes v q1) sh' (handshakeMessagesBytes v' q1')
    end

let transcript_format_injective ms0 ms1 =
  if transcript_bytes ms0 = transcript_bytes ms1
  then begin
    transcript_format_version ms0 ms1;
    handshakeMessagesBytes_is_injective (transcript_version ms0) ms0 ms1
  end else
    ()

//The type below includes buffers, the log, the hash, and the params needed to parse and hash the log.
//Note that a lot of this information is available in the log itself.
//In particular: pv+kex+hash_alg can be read from CH/SH, dh_group can be read from SKE
//TODO: decide whether to keep these parameters explicit or compute them from the log

private
let rec tags_append_aux
  (a: alg)
  (prior ms0 ms1: list msg)
  (hs0 hs1: list anyTag)
: Lemma
  (requires (tags a prior ms0 hs0 /\ tags a (prior @ ms0) ms1 hs1))
  (ensures (tags a prior (ms0 @ ms1) (hs0 @ hs1)))
  (decreases ms0)
= match ms0 with
  | [] ->
    List.Tot.append_l_nil prior
  | m :: ms ->
    let prior_before = prior in
    let prior = prior @ [m] in
    let _ : squash (tags a (prior @ ms) ms1 hs1) =
      List.Tot.append_assoc prior_before [m] ms
    in
    if tagged m
    then
      let (_::hs) = hs0 in
      tags_append_aux a prior ms ms1 hs hs1
    else
      tags_append_aux a prior ms ms1 hs0 hs1

let tags_append a prior ms0 ms1 hs0 hs1 =
  Classical.move_requires (tags_append_aux a prior ms0 ms1 hs0) hs1

noeq type hashState (prior: erased_transcript) (parsed: list msg) =
  | OpenHash: b:bytes { valid_transcript (reveal_log prior @ parsed) /\ b = transcript_bytes (reveal_log prior @ parsed) } -> hashState prior parsed
  | FixedHash:
      a: Hashing.alg ->
      state: accv a { valid_transcript (reveal_log prior @ parsed) /\ Hashing.content state = transcript_bytes (reveal_log prior @ parsed) } ->
      hashes: list anyTag { tags a (reveal_log prior) parsed hashes } ->
      hashState prior parsed

noeq type state =
  | State:
    transcript: erased_transcript ->

    outgoing: bytes -> // outgoing data, alrady formatted and hashed
    outgoing_next_keys: option (bool * option bytes * bool) -> // as next_keys_use, with next fragment after CCS
    outgoing_complete: bool ->
    
    incoming: bytes -> // received fragments; untrusted; not yet hashed or parsed
    parsed: list msg{valid_transcript (reveal_log transcript @ parsed)} ->
                       // partial incoming flight, hashed & parsed, with selected intermediate tags
    hashes: hashState transcript parsed  ->

    // memoized parameters
    pv: option protocolVersion { pv == transcript_version (reveal_log transcript @ parsed) } ->
    kex: option kexAlg ->                    // Used for the CKE and SKE
    dh_group: option CommonDH.group -> // Used for the CKE
    state
// TODO, not urgent, bound the lengths of the bytes and lists.

let log = HS.ref state

let get_reference l =
    HS.(Ref l)

// FIXME: what is this for?
val init: h:HS.mem -> log -> option TLSConstants.protocolVersion -> GTot bool
let init h (st:log) (pvo: option protocolVersion) =
   let s = HS.sel h st in
   OpenHash? s.hashes &&
   OpenHash?.b s.hashes = empty_bytes &&
   s.pv = pvo &&
   s.kex = None &&
   s.dh_group = None

// static precondition for HS writing messages & signals
let writing h st =
    let s = HS.sel h st in
    List.Tot.isEmpty s.parsed

// must be checked before incrementing the read epoch.
val notReading: state -> Tot bool
let notReading st = List.Tot.isEmpty st.parsed && st.incoming = empty_bytes

let hashAlg h st =
    let s = HS.sel h st in
    match s.hashes with
    | OpenHash _ -> None
    | FixedHash a _ _ -> Some a


//  specification-level transcript of all handshake messages logged so far
let transcript h t =
    reveal_log ((HS.sel h t).transcript)

let create reg =
    let l = State empty_hs_transcript empty_bytes None false
              empty_bytes [] (OpenHash empty_bytes) 
      None None None in
    let st = ralloc reg l in
    st

let setParams l ha kexo dho =
  let st = !l in
  match st.hashes with
  | OpenHash msgs ->
      let acc = Hashing.start ha in
      let acc = Hashing.extend #ha acc msgs in
      let _ : squash (Hashing.content acc == msgs) =
        append_empty_bytes_l msgs
      in
      assume (tags ha (reveal_log st.transcript) st.parsed []); // TODO: FIXME: should this be part of OpenHash?
      let hs = FixedHash ha acc [] in
      recall l;
      l := State st.transcript st.outgoing st.outgoing_next_keys st.outgoing_complete
              st.incoming st.parsed hs st.pv kexo dho

// TR: verifies up to this point
#set-options "--lax"

(*
val getHash: #ha:hash_alg -> t:log -> ST (tag ha)
    (requires (fun h -> hashAlg h t == Some ha))
    (ensures (fun h0 i h1 -> h0 == h1))
let getHash #ha (LOG #reg st) =
    let cst = !st in
    let b =
        if Flags.debug_HSL then
            print_hsl cst.transcript
        else false in
    Hashing.finalize #ha cst.hash
*)

(* SEND *)
let send l m =
  trace ("emit "^HandshakeMessages.string_of_handshakeMessage m);
  let st = !l in
  let mb = handshakeMessageBytes st.pv m in
  let h : hashState st.transcript (st.parsed @ [m]) =
    match st.hashes with
    | FixedHash a acc hl ->
      let acc = Hashing.extend #a acc mb in
      FixedHash a acc hl
    | OpenHash p ->
      OpenHash (p @| mb)
    in
  let o = st.outgoing @| mb in
  let t = extend_hs_transcript st.transcript m in
  l := State t o st.outgoing_next_keys st.outgoing_complete
                st.incoming st.parsed h st.pv st.kex st.dh_group

let hash_tag #a l =
  let st = !l in
  match st.hashes with
  | FixedHash a' acc hl ->
      if a <> a' then trace "BAD HASH (statically excluded)";
      Hashing.finalize #a acc
  | OpenHash b -> Hashing.compute a b

let hash_tag_truncated #a l len =
  let st = !l in
  match st.hashes with
  | FixedHash a' acc hl -> trace "BAD HASH (statically excluded)"; admit()
  | OpenHash b -> Hashing.compute a (fst (split b (length b - len)))

// maybe just compose the two functions above?
let send_tag #a l m =
  trace ("emit "^HandshakeMessages.string_of_handshakeMessage m^" and hash");
  let st = !l in
  let mb = handshakeMessageBytes st.pv m in
  let (h,tg) : (hashState st.transcript (st.parsed @ [m]) * anyTag) =
    match st.hashes with
    | FixedHash a' acc hl ->
      let acc = Hashing.extend #a acc mb in
      let tg = Hashing.finalize #a acc in
      (FixedHash a acc hl,tg)
    | OpenHash b ->
      let b = b @| mb in
      (OpenHash b, Hashing.compute a b)
    in
  let o = st.outgoing @| mb in
  let t = extend_hs_transcript st.transcript m in
  l := State t o st.outgoing_next_keys st.outgoing_complete
       st.incoming st.parsed h st.pv st.kex st.dh_group;
  tg

// An ad hoc variant for caching a message to be sent immediately after the CCS
// We always increment the writer, sometimes report handshake completion.

let send_CCS_tag #a l m cf =
  let st = !l in
  let mb = handshakeMessageBytes st.pv m in
  let (h,tg) : (hashState st.transcript (st.parsed @ [m]) * anyTag) =
    match st.hashes with
    | FixedHash a acc hl ->
      let acc = Hashing.extend #a acc mb in
      let tg = Hashing.finalize #a acc in
      (FixedHash a acc hl,tg)
    in
  let t = extend_hs_transcript st.transcript m in
  let nk =
    match st.outgoing_next_keys with
    | None -> Some (false, Some mb, false) in
  l := State t st.outgoing nk cf st.incoming st.parsed h st.pv st.kex st.dh_group;
  tg

// TODO require or check that both flags are clear before the call
let send_signals l next_keys1 complete1 =
  let State transcript outgoing outgoing_next_keys0 outgoing_complete0 incoming parsed hashes pv kex dh_group = !l in
  if outgoing_next_keys0 <> None then trace "WARNING: dirty next-key flag -- use send_CCS instead";
  if outgoing_complete0 then trace "WARNING: dirty complete flag";
  let outgoing_next_keys1 =
    match next_keys1 with
    | Some (enable_appdata,skip_0rtt) -> Some (enable_appdata, None, skip_0rtt)
    | None -> None in
  l := State transcript outgoing outgoing_next_keys1 complete1  incoming parsed hashes pv kex dh_group

let next_fragment l (i:id) =
  let st = !l in
  // do we have a fragment to send?
  let fragment, outgoing' =
    let o = st.outgoing in
    let lo = length o in
    if lo = 0 then // nothing to send
       (None, empty_bytes)
    else // at most one fragment
    if (lo <= max_TLSPlaintext_fragment_length) then
      let rg = (lo, lo) in
      (Some (| rg, o |), empty_bytes)
    else // at least two fragments
      let (x,y) = split o max_TLSPlaintext_fragment_length in
      let lx = length x in
      let rg = (lx, lx) in
      (Some (| rg, x |), y) in
    if length outgoing' = 0
    then (
      // send signals only after flushing the output buffer
      let next_keys1, outgoing1 = match st.outgoing_next_keys with
      | Some(a, Some finishedFragment, z) -> 
        (if a || z then trace "unexpected 1.2 signals");
        Some({
          out_appdata = a; 
          out_ccs_first = true; 
          out_skip_0RTT = z}), finishedFragment
      | Some(a, None, z) -> 
        Some({
          out_appdata = a; 
          out_ccs_first = false; 
          out_skip_0RTT = z}), outgoing'
      | None -> None, outgoing' in
      l := State 
              st.transcript outgoing1  None false
              st.incoming st.parsed st.hashes st.pv st.kex st.dh_group;
      Outgoing fragment next_keys1 st.outgoing_complete 
      )
    else (
      l := State 
              st.transcript outgoing' st.outgoing_next_keys st.outgoing_complete
              st.incoming st.parsed st.hashes st.pv st.kex st.dh_group;
      Outgoing fragment None false )

(* RECEIVE *)

//17-04-24 avoid parsing loop? may be simpler at the level of receive.
//17-05-09 but returning a list is convenient for handling truncated ClientHello
val parseMessages:
  pvo: option protocolVersion -> kexo: option kexAlg -> b: bytes ->
  ST (result (
    bool (* end of flight? *) *
    bytes (* remaining bytes *) *
    list msg (* parsed messages *) *
    list bytes (* ...and their unparsed bytes for hashes *)  ))
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies_none h0 h1))

let rec parseMessages pvo kexo buf =
  match HandshakeMessages.parseMessage buf with
  | Error z -> Error z
  | Correct None -> trace "more bytes required"; Correct (false, buf, [], [])
  | Correct (Some (| rem, hstype, pl, to_log |)) ->
    ( trace ("parsing " ^
        (if pvo = Some TLS_1p3 then "(1.3) " else if pvo = Some TLS_1p2 then  "(1.2) " else "(?) ") ^
        Platform.Bytes.print_bytes pl);
      if hstype = HT_client_hello
      then (
        match parseClientHello pl with // ad hoc case: we parse into one or two messages
        | Error z -> Error z
        | Correct (ch, None) -> (
          trace ("parsed [ClientHello] -- end of flight "^(if length rem > 0 then " (bytes waiting)" else ""));
          Correct(true, rem, [ClientHello ch], [to_log]))
        | Correct (ch, Some binders) -> (
          trace ("parsed [ClientHello; Binders] -- end of flight "^(if length rem > 0 then " (bytes waiting)" else ""));
          let chBytes, bindersBytes = split to_log (length to_log - HandshakeMessages.bindersLen_of_ch ch) in
          Correct(true, rem, [ClientHello ch; Binders binders], [chBytes; bindersBytes])))
      else (
        match parseHandshakeMessage pvo kexo hstype pl with
        | Error z -> Error z
        | Correct msg ->
          trace ("parsed "^HandshakeMessages.string_of_handshakeMessage msg);
          if eoflight msg
          then (
            trace ("end of flight"^(if length rem > 0 then " (bytes waiting)" else ""));
            Correct(true, rem, [msg], [to_log]) )
          else (
            match parseMessages pvo kexo rem with
            | Error z -> Error z
            | Correct (b,r,hl,bl) -> Correct (b,r,msg::hl,to_log::bl))))

val hashHandshakeMessages : t: erased_transcript ->
              p: list msg ->
          hashes: hashState t p ->
          next: (list msg) ->
          nextb: (list bytes) ->
          ST (hashState t (p @ next))
  (requires (fun h0 -> True))
  (ensures (fun h0 t h1 -> modifies_none h0 h1))
  
let rec hashHandshakeMessages t p hs n nb =
    match n,nb with
    | [],[] -> hs
    | m::mrest,mb::brest ->
         (match hs with
    | OpenHash b ->
      let hs = OpenHash (b @| mb) in
      hashHandshakeMessages t (p @ [m]) hs mrest brest
    | FixedHash a acc tl ->
      let acc = Hashing.extend #a acc mb in
      let tl = if tagged m then
             let t = Hashing.finalize #a acc in
         tl @ [t]
         else tl in
      let hs = FixedHash a acc tl in
      hashHandshakeMessages t (p @ [m]) hs mrest brest)

#reset-options

let rec transcript_version_weak
  (l: list hs_msg)
: Tot (option protocolVersion)
= match l with
  | [] -> None
  | ServerHello sh :: _ -> Some sh.sh_protocol_version
  | _ :: q -> transcript_version_weak q

let transcript_version_weak_weak_valid_transcript
  (l: list hs_msg { weak_valid_transcript l } )
: Lemma
  (transcript_version l == transcript_version_weak l)
= ()

let rec transcript_version_weak_append_some
  (l1 l2: list hs_msg)
: Lemma
  (requires (Some? (transcript_version_weak l1)))
  (ensures (transcript_version_weak (l1 @ l2) == transcript_version_weak l1))
= match l1 with
  | ServerHello _ :: _ -> ()
  | _ :: q -> transcript_version_weak_append_some q l2

let rec transcript_version_weak_append_none
  (l1 l2: list hs_msg)
: Lemma
  (requires (None? (transcript_version_weak l1)))
  (ensures (transcript_version_weak (l1 @ l2) == transcript_version_weak l2))
= match l1 with
  | [] -> ()
  | _ :: q -> transcript_version_weak_append_none q l2

assume val modifies_none_modifies_one
  (s: log)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_none h1 h2))
  (ensures (modifies_one s h1 h2))
  [SMTPat (modifies_none h1 h2); SMTPat (modifies_one s h1 h2)]

let receive l mb =
  let h = ST.get () in
  assume (h `HS.contains` l);
  assume (h `HS.weak_contains` l);
  let st = !l in
  let ib = st.incoming @| mb in
  match parseMessages st.pv st.kex ib with
  | Error z -> Error z
  | _ ->
    Error (AD_internal_error, "foobar")

(*
  | Correct (false,r,[],[]) -> (
       recall l;
       let st' : state = State
         st.transcript st.outgoing st.outgoing_next_keys st.outgoing_complete
         r st.parsed st.hashes st.pv st.kex st.dh_group
       in
       l := st' ;
       Correct None )
  | Correct(eof,r,ml,bl) ->
      let hs = hashHandshakeMessages st.transcript st.parsed st.hashes ml bl in
      let pv =
        if Some? st.pv
        then st.pv
        else transcript_version_weak ml          
      in
      let ml' = ml in
      let ml = st.parsed @ ml in
      List.Tot.append_assoc (reveal_log st.transcript) st.parsed ml';
      assume (valid_transcript (reveal_log st.transcript @ ml));
      assume (pv == transcript_version (reveal_log st.transcript @ ml));
      if eof then (
        let nt = append_hs_transcript st.transcript ml in
        List.Tot.append_nil_l (reveal_log nt);
        let (hs,tl) : hashState nt [] * list anyTag =
          match hs with
          | FixedHash a ac htl -> FixedHash a ac [], htl
          | OpenHash _ -> hs,[] in
        recall l;
        let st' : state = State
          nt st.outgoing st.outgoing_next_keys st.outgoing_complete
          r [] hs pv st.kex st.dh_group
        in
        l := st' ;
        let r = Correct (Some (ml,tl)) in
        assume False;
        r
      )
      else (
        recall l;
        let st' : state = State
          st.transcript st.outgoing st.outgoing_next_keys st.outgoing_complete
          r ml hs pv st.kex st.dh_group
        in
        l := st' ;
        Correct None )
*)

#set-options "--lax"

// We receive CCS as external end-of-flight signals;
// we return the messages processed so far, and their final tag;
// we still can't write.
// This should *fail* if there are pending input bytes.
let receive_CCS #a l =
  let st = !l in
  if length st.incoming > 0
  then (
    trace ("too many bytes: "^print_bytes st.incoming);
    Error (AD_unexpected_message, "unexpected fragment after CCS"))
  else
  match st.hashes with
  | OpenHash b -> Error (AD_internal_error, "the hash is open")
  | FixedHash a acc tl ->
    begin
      let nt = append_hs_transcript st.transcript st.parsed in
      let hs': hashState nt [] = FixedHash a acc [] in
      let h = Hashing.finalize #a acc in
      l := State
          nt st.outgoing st.outgoing_next_keys st.outgoing_complete
          st.incoming [] hs' st.pv st.kex st.dh_group;
      Correct (st.parsed, tl, h)
    end
