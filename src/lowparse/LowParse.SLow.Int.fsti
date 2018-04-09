module LowParse.SLow.Int
include LowParse.Spec.Int
include LowParse.SLow.Base

inline_for_extraction
val parse32_u8 (#err: Type0) (e: err) : Tot (parser32 (parse_u8 e))

inline_for_extraction
val serialize32_u8 (#err: Type0) (e: err) : Tot (serializer32 (serialize_u8 e))

inline_for_extraction
val parse32_u16 (#err: Type0) (e: err) : Tot (parser32 (parse_u16 e))

inline_for_extraction
val serialize32_u16 (#err: Type0) (e: err) : Tot (serializer32 (serialize_u16 e))

inline_for_extraction
val parse32_u32 (#err: Type0) (e: err) : Tot (parser32 (parse_u32 e))

inline_for_extraction
val serialize32_u32 (#err: Type0) (e: err) : Tot (serializer32 (serialize_u32 e))
