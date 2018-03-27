module LowParse.Impl.Int
include LowParse.Impl.Combinators
include LowParse.Spec.Int

module Seq = FStar.Seq
module S = LowParse.Slice
module E = FStar.Kremlin.Endianness
module C = C
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

[@"substitute"]
inline_for_extraction
val validate_u8_st : stateful_validator parse_u8
let validate_u8_st = validate_total_constant_size 1ul parse_u8

[@"substitute"]
inline_for_extraction
val validate_u16_st: stateful_validator parse_u16
let validate_u16_st = validate_total_constant_size 2ul parse_u16

[@"substitute"]
inline_for_extraction
val validate_u32_st: stateful_validator parse_u32
let validate_u32_st = validate_total_constant_size 4ul parse_u32

[@"substitute"]
inline_for_extraction
val validate_u8_st_nochk : stateful_validator_nochk parse_u8
let validate_u8_st_nochk = validate_constant_size_nochk 1ul parse_u8

[@"substitute"]
inline_for_extraction
val validate_u16_st_nochk: stateful_validator_nochk parse_u16
let validate_u16_st_nochk = validate_constant_size_nochk 2ul parse_u16

[@"substitute"]
inline_for_extraction
val validate_u32_st_nochk: stateful_validator_nochk parse_u32
let validate_u32_st_nochk = validate_constant_size_nochk 4ul parse_u32

[@"substitute"]
inline_for_extraction
let parse_u8_st_nochk :
    parser_st_nochk parse_u8 =
    parse_total_constant_size_nochk 1ul (fun (input: S.bslice) ->
      S.index input 0ul
    )

[@"substitute"]
inline_for_extraction
let parse_u8_st :
    parser_st parse_u8 =
    parse_total_constant_size 1ul parse_u8_st_nochk

#set-options "--z3rlimit 16"

[@"substitute"]
inline_for_extraction
let parse_u16_st_nochk :
  parser_st_nochk parse_u16 =
  parse_total_constant_size_nochk 2ul (fun (input: S.bslice) ->
    let s = S.truncate_slice input 2ul in
    C.load16_be (S.as_buffer s)
  )

#reset-options

[@"substitute"]
inline_for_extraction
let parse_u16_st : parser_st parse_u16 =
  parse_total_constant_size 2ul parse_u16_st_nochk

[@"substitute"]
inline_for_extraction
let parse_u32_st_nochk :
  parser_st_nochk (parse_u32) = 
  parse_total_constant_size_nochk 4ul (fun input ->
    let s = S.truncate_slice input 4ul in
    C.load32_be (S.as_buffer s)
  )

[@"substitute"]
inline_for_extraction
let parse_u32_st : parser_st (parse_u32) =
  parse_total_constant_size 4ul parse_u32_st_nochk

module HST = FStar.HyperStack.ST
module B = FStar.Buffer

inline_for_extraction
val serialize_u8
  (i: U8.t)
  (dest: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    U32.v (S.length dest) >= 1 /\
    S.live h dest
  ))
  (ensures (fun h (destl, destr) h' ->
    S.is_concat dest destl destr /\
    S.length destl == 1ul /\
    S.live h' destr /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    exactly_parses h' parse_u8 destl (fun v ->
    v == i
  )))

#set-options "--z3rlimit 64"

let serialize_u8 i dest =
  let destl = S.truncate_slice dest 1ul in
  let b = S.as_buffer destl in
  B.upd b 0ul i;
  let destr = S.advance_slice dest 1ul in
  (destl, destr)

#reset-options

module Cast = FStar.Int.Cast

inline_for_extraction
val serialize_u16
  (i: U16.t)
  (dest: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    U32.v (S.length dest) >= 2 /\
    S.live h dest
  ))
  (ensures (fun h (destl, destr) h' ->
    S.is_concat dest destl destr /\
    S.length destl == 2ul /\
    S.live h' destr /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    exactly_parses h' parse_u16 destl (fun v ->
    v == i
  )))

#set-options "--z3rlimit 64 --max_fuel 8 --max_ifuel 8"

let serialize_u16 i dest =
  let destl = S.truncate_slice dest 2ul in
  let b = S.as_buffer destl in
  let v256 = U16.uint_to_t 256 in
  B.upd b 1ul (Cast.uint16_to_uint8 (U16.rem i v256));
  B.upd b 0ul (Cast.uint16_to_uint8 (U16.div i v256));
  let destr = S.advance_slice dest 2ul in
  let h' = HST.get () in
  assert (Seq.equal (S.as_seq h' destl) (E.n_to_be 2ul (U16.v i)));
  Seq.lemma_eq_elim (S.as_seq h' destl) (E.n_to_be 2ul (U16.v i));
  assert (E.be_to_n (S.as_seq h' destl) == U16.v i);
  (destl, destr)

#reset-options

val serialize_u32_aux
  (i: U32.t)
  (s: bytes)
: Ghost bytes
  (requires (Seq.length s == 4))
  (ensures (fun s' ->
    Seq.length s' == 4 /\
    Seq.equal s' (E.n_to_be 4ul (U32.v i))
  ))

#set-options "--z3rlimit 128 --max_fuel 8 --max_ifuel 8"

let serialize_u32_aux i s =
  let v256 = U32.uint_to_t 256 in
  let j3 = Cast.uint32_to_uint8 (U32.rem i v256) in
  let s3 = Seq.upd s 3 j3 in
  let i2 = U32.div i v256 in
  let j2 = Cast.uint32_to_uint8 (U32.rem i2 v256) in
  let s2 = Seq.upd s3 2 j2 in
  let i1 = U32.div i2 v256 in
  let j1 = Cast.uint32_to_uint8 (U32.rem i1 v256) in
  let s1 = Seq.upd s2 1 j1 in
  let j0 = Cast.uint32_to_uint8 (U32.div i1 v256) in
  Seq.upd s1 0 j0

#reset-options

inline_for_extraction
val serialize_u32
  (i: U32.t)
  (dest: S.bslice)
: HST.Stack (S.bslice * S.bslice)
  (requires (fun h ->
    U32.v (S.length dest) >= 4 /\
    S.live h dest
  ))
  (ensures (fun h (destl, destr) h' ->
    S.is_concat dest destl destr /\
    S.length destl == 4ul /\
    S.live h' destr /\
    B.modifies_1 (S.as_buffer destl) h h' /\
    exactly_parses h' parse_u32 destl (fun v ->
    v == i
  )))

#set-options "--z3rlimit 64"

let serialize_u32 i dest =
  let destl = S.truncate_slice dest 4ul in
  let b = S.as_buffer destl in
  let h = HST.get () in
  let v256 = U32.uint_to_t 256 in
  let j3 = Cast.uint32_to_uint8 (U32.rem i v256) in
  B.upd b 3ul j3;
  let i2 = U32.div i v256 in
  let j2 = Cast.uint32_to_uint8 (U32.rem i2 v256) in
  B.upd b 2ul j2;
  let i1 = U32.div i2 v256 in
  let j1 = Cast.uint32_to_uint8 (U32.rem i1 v256) in
  B.upd b 1ul j1;
  let j0 = Cast.uint32_to_uint8 (U32.div i1 v256) in
  B.upd b 0ul j0;
  let destr = S.advance_slice dest 4ul in
  let h' = HST.get () in
  assert (S.as_seq h' destl == serialize_u32_aux i (S.as_seq h destl));
  assert (Seq.equal (S.as_seq h' destl) (E.n_to_be 4ul (U32.v i)));
  Seq.lemma_eq_elim (S.as_seq h' destl) (E.n_to_be 4ul (U32.v i));
  assert (E.be_to_n (S.as_seq h' destl) == U32.v i);
  (destl, destr)

#reset-options
