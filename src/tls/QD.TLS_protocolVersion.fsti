module QD.TLS_protocolVersion

open FStar.Bytes
open TLSError
open Parse

open LowParse.SLow.Base

type protocolVersion' =
  | SSL_3p0
  | TLS_1p0
  | TLS_1p1
  | TLS_1p2
  | TLS_1p3
  | Unknown_protocolVersion of (v:UInt16.t{v <> 768us /\ v <> 769us /\ v <> 770us /\ v <> 771us /\ v <> 772us})

type protocolVersion = v:protocolVersion'{~(Unknown_protocolVersion? v)}

inline_for_extraction
val parse_protocolVersion'_kind : (x: parser_kind {
  x.parser_kind_subkind == Some ParserStrong /\
  x.parser_kind_high == Some x.parser_kind_low /\
  x.parser_kind_low == 2
})

inline_for_extraction // should be: noextract
val parse_protocolVersion'_spec : unit -> Tot (parser parse_protocolVersion'_kind protocolVersion')

inline_for_extraction
val parse_protocolVersion' : parser32 (parse_protocolVersion'_spec ())

inline_for_extraction // should be: noextract
val serialize_protocolVersion'_spec : unit -> Tot (serializer (parse_protocolVersion'_spec ()))

inline_for_extraction
val serialize_protocolVersion' : serializer32 (serialize_protocolVersion'_spec ())
