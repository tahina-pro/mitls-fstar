module LowParse.Impl.VLBytes.Part2

let parse_bounded_integer'_correct i b =
  match i with
  | 1 -> LowParse.Impl.VLBytes.Part2.Subpart1.parse_bounded_integer'_1_correct b
  | 2 -> LowParse.Impl.VLBytes.Part2.Subpart2.parse_bounded_integer'_2_correct b
  | 3 -> LowParse.Impl.VLBytes.Part2.Subpart3.parse_bounded_integer'_3_correct b
  | 4 -> LowParse.Impl.VLBytes.Part2.Subpart4.parse_bounded_integer'_4_correct b
