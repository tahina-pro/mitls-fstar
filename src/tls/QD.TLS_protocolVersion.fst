module QD.TLS_protocolVersion

module LP = LowParse.SLow
module L = FStar.List.Tot

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

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
  in e

inline_for_extraction let synth_protocolVersion' (x:LP.maybe_enum_key protocolVersion_enum) : Tot protocolVersion' = 
  match x with
  | LP.Known k -> k
  | LP.Unknown y ->
    [@inline_let] let v : UInt16.t = y in
    [@inline_let] let _ = LP.norm_spec (LP.list_mem v (LP.list_map snd protocolVersion_enum)) in
    Unknown_protocolVersion v

let lemma_synth_protocolVersion'_inj () : Lemma
  (LP.synth_injective synth_protocolVersion') = ()

inline_for_extraction let synth_protocolVersion'_inv (x:protocolVersion') : Tot (LP.maybe_enum_key protocolVersion_enum) = 
  match x with
  | Unknown_protocolVersion y ->
    [@inline_let] let v : UInt16.t = y in
    [@inline_let] let _ = LP.norm_spec (LP.list_mem v (LP.list_map snd protocolVersion_enum)) in
    LP.Unknown v
  | x ->
    [@inline_let] let x1 : protocolVersion = x in
    [@inline_let] let _ = LP.norm_spec (LP.list_mem x1 (LP.list_map fst protocolVersion_enum)) in
    LP.Known (x1 <: LP.enum_key protocolVersion_enum)

let lemma_synth_protocolVersion'_inv () : Lemma
  (LP.synth_inverse synth_protocolVersion' synth_protocolVersion'_inv) = ()

let parse_maybe_protocolVersion_key : LP.parser _ (LP.maybe_enum_key protocolVersion_enum) =
  LP.parse_maybe_enum_key LP.parse_u16 protocolVersion_enum

let serialize_maybe_protocolVersion_key : LP.serializer parse_maybe_protocolVersion_key =
  LP.serialize_maybe_enum_key LP.parse_u16 LP.serialize_u16 protocolVersion_enum

let parse_protocolVersion'_kind =
  LP.parse_u16_kind

let parse_protocolVersion'_spec' =
  lemma_synth_protocolVersion'_inj ();
  parse_maybe_protocolVersion_key `LP.parse_synth` synth_protocolVersion'

let parse_protocolVersion'_spec () = parse_protocolVersion'_spec'

inline_for_extraction let parse32_maybe_protocolVersion_key : LP.parser32 parse_maybe_protocolVersion_key =
  FStar.Tactics.synth_by_tactic (LP.parse32_maybe_enum_key_tac LP.parse32_u16 protocolVersion_enum parse_maybe_protocolVersion_key ())

inline_for_extraction
let parse_protocolVersion'_aux : LP.parser32 parse_protocolVersion'_spec' =
  lemma_synth_protocolVersion'_inj ();
  LP.parse32_synth _ synth_protocolVersion' (fun x->synth_protocolVersion' x) parse32_maybe_protocolVersion_key ()

let parse_protocolVersion' x = parse_protocolVersion'_aux x

let serialize_protocolVersion'_spec' : LP.serializer parse_protocolVersion'_spec' =
  lemma_synth_protocolVersion'_inj ();
  lemma_synth_protocolVersion'_inv ();
  LP.serialize_synth _ synth_protocolVersion' serialize_maybe_protocolVersion_key synth_protocolVersion'_inv ()

let serialize_protocolVersion'_spec () = serialize_protocolVersion'_spec'

inline_for_extraction let serialize32_maybe_protocolVersion_key : LP.serializer32 serialize_maybe_protocolVersion_key =
  FStar.Tactics.synth_by_tactic (LP.serialize32_maybe_enum_key_tac
    #_ #_ #_ #LP.parse_u16 #LP.serialize_u16 // FIXME(implicits for machine int parsers), see FStar #1384
    LP.serialize32_u16 protocolVersion_enum serialize_maybe_protocolVersion_key ())

inline_for_extraction
let serialize_protocolVersion'_aux : LP.serializer32 serialize_protocolVersion'_spec' =
  lemma_synth_protocolVersion'_inj ();
  lemma_synth_protocolVersion'_inv ();
  LP.serialize32_synth _ synth_protocolVersion' _ serialize32_maybe_protocolVersion_key synth_protocolVersion'_inv (fun x->synth_protocolVersion'_inv x) ()

let serialize_protocolVersion' x = serialize_protocolVersion'_aux x
