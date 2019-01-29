module LowParseExample10

module LP = LowParse.SLow
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module BY = LowParse.Bytes32

inline_for_extraction
let t_tag_cond (x: msg_type) : Tot bool =
  x = msg_type_HelloRetryRequest

inline_for_extraction
let t_payload (b: bool) : Tot Type =
  if b then U32.t else U16.t

inline_for_extraction
let parse_t_payload (b: bool) : Tot (k: LP.parser_kind & LP.parser k (t_payload b)) =
  if b then (| _ , LP.parse_u32 |) else (| _, LP.parse_u16 |)

inline_for_extraction
let t_synth (x: msg_type) (y: t_payload (t_tag_cond x)) : Tot t =
  if t_tag_cond x
  then HelloRetryRequest y
  else Other ({ msg_type = x; contents = y })

inline_for_extraction
noextract
let parse_t_param = {
  LP.parse_ifthenelse_tag_kind = _;
  LP.parse_ifthenelse_tag_t = _;
  LP.parse_ifthenelse_tag_parser = LP.parse_flbytes 3;
  LP.parse_ifthenelse_tag_cond = t_tag_cond;
  LP.parse_ifthenelse_payload_t = t_payload;
  LP.parse_ifthenelse_payload_parser = parse_t_payload;
  LP.parse_ifthenelse_t = _;
  LP.parse_ifthenelse_synth = t_synth;
  LP.parse_ifthenelse_synth_injective = (fun t1 x1 t2 x2 -> ());
}

let parse_t = LP.parse_ifthenelse parse_t_param

inline_for_extraction
let serialize_t_payload (b: bool) : Tot (LP.serializer (dsnd (parse_t_param.LP.parse_ifthenelse_payload_parser b))) = // "(LP.serializer (dsnd (parse_t_payload b)))" makes serialize_t_param fail to typecheck
  if b then LP.serialize_u32 else LP.serialize_u16

inline_for_extraction
let t_synth_recip (x: t) : GTot (t: msg_type & (t_payload (t_tag_cond t))) =
  match x with
  | HelloRetryRequest y -> (| msg_type_HelloRetryRequest, y |)
  | Other m -> (| m.msg_type, m.contents |)

inline_for_extraction
noextract
let serialize_t_param : LP.serialize_ifthenelse_param parse_t_param = {
  LP.serialize_ifthenelse_tag_serializer = LP.serialize_flbytes 3;
  LP.serialize_ifthenelse_payload_serializer = serialize_t_payload;
  LP.serialize_ifthenelse_synth_recip = t_synth_recip;
  LP.serialize_ifthenelse_synth_inverse = (fun x -> ());
}

let serialize_t = LP.serialize_ifthenelse serialize_t_param

let parse32_t =
  LP.parse32_ifthenelse
    parse_t_param
    (LP.parse32_flbytes 3 3ul)
    (fun x -> t_tag_cond x)
    (fun b -> if b then LP.parse32_u32 else LP.parse32_u16)
    (fun b -> if b then (fun _ pl -> HelloRetryRequest pl) else (fun t pl -> Other ({ msg_type = t; contents = pl; })))

let serialize32_t =
  LP.serialize32_ifthenelse
    serialize_t_param
    (LP.serialize32_flbytes 3)
    (fun x -> match x with HelloRetryRequest _ -> msg_type_HelloRetryRequest | Other m -> m.msg_type)
    (fun x -> t_tag_cond x)
    (fun b -> if b then (fun (HelloRetryRequest y) -> y) else (fun (Other m) -> m.contents))
    (fun b -> if b then LP.serialize32_u32 else LP.serialize32_u16)

let size32_t =
  LP.size32_ifthenelse
    serialize_t_param
    (LP.size32_constant (LP.serialize_flbytes 3) 3ul ())
    (fun x -> match x with HelloRetryRequest _ -> msg_type_HelloRetryRequest | Other m -> m.msg_type)
    (fun x -> t_tag_cond x)
    (fun b -> if b then (fun (HelloRetryRequest y) -> y) else (fun (Other m) -> m.contents))
    (fun b -> if b then LP.size32_u32 else LP.size32_u16)

let main _ _ = C.EXIT_SUCCESS
