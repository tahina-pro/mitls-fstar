module LowParse.Low.Int.Aux2

module Seq = FStar.Seq

let seq_equal_1
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (requires (Seq.length s1 == 1 /\ Seq.length s2 == 1 /\ Seq.index s1 0 == Seq.index s2 0))
  (ensures (s1 == s2))
= assert (s1 `Seq.equal` s2)
