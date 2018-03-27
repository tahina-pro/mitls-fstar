module LowParse.Impl.VLBytes.Part2
include LowParse.Impl.VLBytes.Part1

val parse_bounded_integer'_correct
  (i: integer_size)
  (b: bytes)
: Lemma
  (parse (parse_bounded_integer' i) b == parse (parse_bounded_integer i) b)
