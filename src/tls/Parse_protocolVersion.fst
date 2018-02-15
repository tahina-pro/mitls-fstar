module Parse_protocolVersion

#reset-options "--using_facts_from '* -Parse -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

module LP = LowParse.SLow
module L = FStar.List.Tot

type protocolVersion' =
  | SSL_3p0
  | TLS_1p0
  | TLS_1p1
  | TLS_1p2
  | TLS_1p3
  | Unknown of (v:UInt16.t{v <> 768us /\ v <> 769us /\ v <> 770us /\ v <> 771us /\ v <> 772us})

type protocolVersion = v:protocolVersion'{~(Unknown? v)}

inline_for_extraction let protocolVersion_enum : LP.enum protocolVersion UInt16.t =
  [@inline_let] let e = [
    SSL_3p0, 768us;
    TLS_1p0, 769us;
    TLS_1p1, 770us;
    TLS_1p2, 771us;
    TLS_1p3, 772us;
  ] in
  [@inline_let] let no_dups =
    assert_norm (L.noRepeats (LP.list_map fst e));
    assert_norm (L.noRepeats (LP.list_map snd e))
  in 
  e

inline_for_extraction let synth_protocolVersion' (x:LP.maybe_enum_key protocolVersion_enum) : Tot protocolVersion' = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let]
    let v : UInt16.t = y in
    [@inline_let]
    let _ =
      Prims.norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd protocolVersion_enum))
    in
    Unknown v

let synth_protocolVersion'_inj () : Lemma
  (forall (x1 x2 : LP.maybe_enum_key protocolVersion_enum) . synth_protocolVersion' x1 == synth_protocolVersion' x2 ==> x1 == x2)
= ()

inline_for_extraction let synth_protocolVersion'_inv (x:protocolVersion') : Tot (LP.maybe_enum_key protocolVersion_enum) = 
  match x with
  | Unknown y ->
    [@inline_let]
    let v : UInt16.t = y in
    [@inline_let]
    let _ =
      Prims.norm_spec LP.norm_steps (LP.list_mem v (LP.list_map snd protocolVersion_enum))
    in
    LP.Unknown v
  | x ->
    [@inline_let]
    let x1 : protocolVersion = x in
    [@inline_let]
    let _ =
      Prims.norm_spec LP.norm_steps (LP.list_mem x1 (LP.list_map fst protocolVersion_enum))
    in
    LP.Known (x1 <: LP.enum_key protocolVersion_enum)

let synth_protocolVersion'_inv_recip () : Lemma
  (forall (x: protocolVersion') .
  synth_protocolVersion' (synth_protocolVersion'_inv x) == x)
= ()

let parse_maybe_protocolVersion_key : LP.parser _ (LP.maybe_enum_key protocolVersion_enum) =
  LP.parse_maybe_enum_key LP.parse_u16 protocolVersion_enum

let parse_protocolVersion' : LP.parser _ protocolVersion' =
  synth_protocolVersion'_inj ();
  parse_maybe_protocolVersion_key `LP.parse_synth` synth_protocolVersion'

let serialize_maybe_protocolVersion_key : LP.serializer parse_maybe_protocolVersion_key =
  LP.serialize_maybe_enum_key LP.parse_u16 LP.serialize_u16 protocolVersion_enum

let serialize_protocolVersion' : LP.serializer parse_protocolVersion' =
  synth_protocolVersion'_inj ();
  synth_protocolVersion'_inv_recip ();
  LP.serialize_synth _ synth_protocolVersion' serialize_maybe_protocolVersion_key synth_protocolVersion'_inv ()

inline_for_extraction let parse32_maybe_protocolVersion_key : LP.parser32 parse_maybe_protocolVersion_key =
  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_u16 protocolVersion_enum parse_maybe_protocolVersion_key ())

inline_for_extraction let parse32_protocolVersion' : LP.parser32 parse_protocolVersion' =
  synth_protocolVersion'_inj ();
  LP.parse32_synth _ synth_protocolVersion' (fun x->synth_protocolVersion' x) parse32_maybe_protocolVersion_key ()

inline_for_extraction let serialize32_maybe_protocolVersion_key : LP.serializer32 serialize_maybe_protocolVersion_key =
  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac
  #_ #_ #_ #LP.parse_u16 #LP.serialize_u16
    LP.serialize32_u16 protocolVersion_enum serialize_maybe_protocolVersion_key ())

inline_for_extraction let serialize32_protocolVersion' : LP.serializer32 serialize_protocolVersion' =
  synth_protocolVersion'_inj ();
  synth_protocolVersion'_inv_recip ();
  LP.serialize32_synth _ synth_protocolVersion' _ serialize32_maybe_protocolVersion_key synth_protocolVersion'_inv (fun x->synth_protocolVersion'_inv x) ()

(*
inline_for_extraction let protocolVersion_bytes (x:protocolVersion') : Tot (lbytes 2) =
  serialize32_protocolVersion' x <: LP.bytes32

inline_for_extraction let parse_protocolVersion : pinverse_t protocolVersion_bytes =
  fun x -> LP.parse32_total parse32_protocolVersion' v;
    let (Some (v, _)) = parse32_protocolVersion' x in Correct v
*)
