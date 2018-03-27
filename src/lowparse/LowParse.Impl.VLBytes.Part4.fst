module LowParse.Impl.VLBytes.Part4

module S = LowParse.Slice

#set-options "--z3rlimit 16"

let point_to_vlbytes_contents_correct sz f #k #t p b h len b1 b' =
  let s = S.as_seq h b in
  let (Some (v, _)) = parse (parse_vlbytes_gen sz f p) s in
  let (Some (len, consumedl)) = parse (parse_filter (parse_bounded_integer sz) f) s in
  let (Some (len', consumedl')) = parse (parse_bounded_integer sz) s in
  assert (consumedl == consumedl');
  assert ((len <: bounded_integer sz) == len');
  let sz' = U32.uint_to_t sz in
  let b0 = S.truncated_slice b sz' in
  let s0 = S.as_seq h b0 in
  assert (s0 == Seq.slice s 0 sz);
  assert (S.is_prefix_gen [b0; b'] b);
  ()

#reset-options
