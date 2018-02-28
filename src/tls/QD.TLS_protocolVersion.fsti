module QD.TLS_protocolVersion

module LP = LowParse.SLow.Base

type protocolVersion' =
  | SSL_3p0
  | TLS_1p0
  | TLS_1p1
  | TLS_1p2
  | TLS_1p3
  | Unknown_protocolVersion of (v:UInt16.t{v <> 768us /\ v <> 769us /\ v <> 770us /\ v <> 771us /\ v <> 772us})

type protocolVersion = v:protocolVersion'{~(Unknown_protocolVersion? v)}

inline_for_extraction
val parse_protocolVersion'_kind : (x: LP.parser_kind {
  x.LP.parser_kind_subkind == Some LP.ParserStrong /\
  x.LP.parser_kind_high == Some x.LP.parser_kind_low /\
  x.LP.parser_kind_low == 2
})

inline_for_extraction
val parse_protocolVersion'_spec : unit -> Tot (LP.parser parse_protocolVersion'_kind protocolVersion')

inline_for_extraction
val parse_protocolVersion' : LP.parser32 (parse_protocolVersion'_spec ())

inline_for_extraction
val serialize_protocolVersion'_spec : unit -> Tot (LP.serializer (parse_protocolVersion'_spec ()))

inline_for_extraction
val serialize_protocolVersion' : LP.serializer32 (serialize_protocolVersion'_spec ())
