module LowParse.SLow.Array
include LowParse.SLow.FLData
include LowParse.SLow.VLData
include LowParse.SLow.List
include LowParse.Spec.Array

module U32 = FStar.UInt32

inline_for_extraction
let parse32_array
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (p32: parser32 p)
  (array_byte_size: nat)
  (array_byte_size32: U32.t { U32.v array_byte_size32 == array_byte_size } )
  (elem_count: nat)
  (e: err)
  (u : unit { fldata_array_precond p array_byte_size elem_count == true } )
: Tot (parser32 (parse_array s array_byte_size elem_count e))
= [@inline_let]
  let _ =
    fldata_to_array_inj s array_byte_size elem_count u
  in
  parse32_synth
    _
    (fldata_to_array s array_byte_size elem_count u)
    (fun x -> fldata_to_array s array_byte_size elem_count u x)
    (parse32_fldata_strong
      (serialize_list s ())
      (parse32_list p32 ())
      array_byte_size
      array_byte_size32
      e
    )
    ()

inline_for_extraction
let serialize32_array
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (array_byte_size: nat { array_byte_size < 4294967296 } )
  (elem_count: nat)
  (e: err)
  (u : unit { fldata_array_precond p array_byte_size elem_count == true } )
: Tot (serializer32 (serialize_array s array_byte_size elem_count e u))
= [@inline_let]
  let _ =
    fldata_to_array_inj s array_byte_size elem_count u
  in
  [@inline_let]
  let _ =
    array_to_fldata_to_array s array_byte_size elem_count u
  in
  serialize32_synth
    _
    (fldata_to_array s array_byte_size elem_count u)
    _
    (serialize32_fldata_strong
      (partial_serialize32_list s32 ())
      array_byte_size
      e
    )
    (array_to_fldata s array_byte_size elem_count u)
    (fun x -> array_to_fldata s array_byte_size elem_count u x)
    ()

inline_for_extraction
let parse32_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_min32: U32.t { U32.v array_byte_size_min32 == array_byte_size_min } )
  (array_byte_size_max: nat)
  (array_byte_size_max32: U32.t { U32.v array_byte_size_max32 == array_byte_size_max } )
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (p32: parser32 p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (e_size_incomplete e_size_invalid e_payload: err)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
: Tot (parser32 (parse_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max e_size_incomplete e_size_invalid e_payload u))
= [@inline_let]
  let _ =
    vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  parse32_synth
    _
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    (fun x -> vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x)
    (parse32_bounded_vldata_strong
      array_byte_size_min
      array_byte_size_min32
      array_byte_size_max
      array_byte_size_max32
      (serialize_list s ())
      (parse32_list p32 ())
      e_size_incomplete e_size_invalid e_payload
    )
    ()

inline_for_extraction
let serialize32_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat { array_byte_size_max < 4294967292 } ) // NOTE here: max must be less than 2^32 - 4 to account for the size of the length header
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (#s: serializer p)
  (s32: partial_serializer32 s)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (e_size_incomplete e_size_invalid e_payload: err)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
: Tot (serializer32 (serialize_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max e_size_incomplete e_size_invalid e_payload u))
= [@inline_let]
  let _ =
    vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  [@inline_let]
  let _ =
    vlarray_to_vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  serialize32_synth
    _
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    _
    (serialize32_bounded_vldata_strong
      array_byte_size_min
      array_byte_size_max
      (partial_serialize32_list s32 ())
      e_size_incomplete e_size_invalid e_payload
    )
    (vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    (fun x -> vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x)
    ()

inline_for_extraction
let size32_vlarray
  (array_byte_size_min: nat)
  (array_byte_size_max: nat { array_byte_size_max < 4294967292 } ) // NOTE here: max must be less than 2^32 - 4 to account for the size of the length header
  (#k: parser_kind)
  (#t: Type0)
  (#err: Type0)
  (#p: parser k t err)
  (s: serializer p)
  (elem_count_min: nat)
  (elem_count_max: nat)
  (e_size_incomplete e_size_invalid e_payload: err)
  (u: unit {
    vldata_vlarray_precond array_byte_size_min array_byte_size_max p elem_count_min elem_count_max == true  
  })
  (size_header_byte_size32: U32.t { U32.v size_header_byte_size32 == log256' array_byte_size_max } )
  (elem_byte_size32: U32.t { U32.v elem_byte_size32 == k.parser_kind_low } )
: Tot (size32 (serialize_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max e_size_incomplete e_size_invalid e_payload u))
= [@inline_let]
  let _ =
    vldata_to_vlarray_inj array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  [@inline_let]
  let _ =
    vlarray_to_vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u
  in
  size32_synth
    _
    (vldata_to_vlarray array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    _
    (size32_bounded_vldata_strong
      array_byte_size_min
      array_byte_size_max
      (size32_list (size32_constant s elem_byte_size32 ()) ())
      size_header_byte_size32
      e_size_incomplete e_size_invalid e_payload
    )
    (vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u)
    (fun x -> vlarray_to_vldata array_byte_size_min array_byte_size_max s elem_count_min elem_count_max u x)
    ()
