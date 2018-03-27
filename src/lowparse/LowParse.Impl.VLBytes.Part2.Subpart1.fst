module LowParse.Impl.VLBytes.Part2.Subpart1
include LowParse.Impl.VLBytes.Part1

#set-options "--z3rlimit 32"

let parse_bounded_integer'_1_correct
  (b: bytes)
: Lemma
  (parse (parse_bounded_integer' 1) b == parse (parse_bounded_integer 1) b)
= ()

#reset-options
