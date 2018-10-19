module LowParse.ListLib
include FStar.List.Tot

let rec noRepeats_sorted
  (#t: eqtype)
  (ord: t -> t -> Tot bool)
  (l: list t)
: Tot bool
= match l with
  | a :: b :: q -> ord a b && noRepeats_sorted ord (b :: q)
  | _ -> true

let rec sorted_not_mem
  (#t: eqtype)
  (ord: t -> t -> Tot bool)
  (ord_irrefl: squash (forall x . ~ (ord x x)))
  (ord_trans: squash (forall x y z . (ord x y /\ ord y z) ==> ord x z))
  (a: t)
  (b: t)
  (q: list t)
: Lemma
  (requires (sorted ord (b :: q) /\ ord a b /\ mem a (b :: q)))
  (ensures False)
  (decreases (length q))
= match q with
  | [] -> ()
  | b' :: q' -> sorted_not_mem ord ord_irrefl ord_trans a b' q'

let rec noRepeats_sorted_noRepeats
  (#t: eqtype)
  (ord: t -> t -> Tot bool)
  (ord_irrefl: squash (forall x . ~ (ord x x)))
  (ord_trans: squash (forall x y z . (ord x y /\ ord y z) ==> ord x z))
  (ord' : t -> t -> Tot bool)
  (ord'_weaker: squash (forall x y . ord x y ==> ord' x y))
  (l: list t)
: Lemma
  (requires (noRepeats_sorted ord l /\ sorted ord' l))
  (ensures (sorted ord l /\ noRepeats l))
= match l with
  | a :: b :: q ->
    noRepeats_sorted_noRepeats ord ord_irrefl ord_trans ord' ord'_weaker (b :: q);
    Classical.move_requires (sorted_not_mem ord ord_irrefl ord_trans a b) q
  | _ -> ()

let clos_refl (#t: eqtype) (ord: t -> t -> Tot bool) (x1 x2: t) : Tot bool =
  if x1 = x2 then true else ord x1 x2

let clos_refl_weaker (#t: eqtype) (ord: t -> t -> Tot bool) (x1 x2: t) : Lemma
  (ord x1 x2 ==> clos_refl ord x1 x2)
= ()

let clos_refl_total (#t: eqtype) (ord: t -> t -> Tot bool) : Lemma
  (requires (forall x1 x2 . ord x1 x2 \/ ord x2 x1 \/ x1 == x2))
  (ensures (forall x1 x2 . clos_refl ord x1 x2 \/ clos_refl ord x2 x1))
= ()

let noRepeats_sort (#t: eqtype) (ord: t -> t -> Tot bool) (l: list t) : Tot bool =
  noRepeats_sorted ord (sortWith (compare_of_bool (clos_refl ord)) l) 

let feq2 (#a #b #c: Type) (f1 f2: (a -> b -> Tot c)) : GTot Type =
  (forall x y . f1 x y == f2 x y)

let rec sorted_feq2 (#t: Type) (ord1 ord2: (t -> t -> Tot bool)) (l: list t) : Lemma
  (requires (feq2 ord1 ord2 /\ sorted ord1 l))
  (ensures (sorted ord2 l))
= match l with
  | a :: b :: q -> sorted_feq2 ord1 ord2 (b :: q)
  | _ -> ()

let bool_of_compare_of_bool (#t: eqtype) (ord: t -> t -> Tot bool) : Lemma
  (feq2 (bool_of_compare (compare_of_bool ord)) ord)
= ()

let rec noRepeats_count
  (#t: eqtype)
  (l: list t)
  (x: t)
: Lemma
  (requires (noRepeats l))
  (ensures (count x l <= 1))
= match l with
  | [] -> ()
  | a :: q -> noRepeats_count q x; mem_count q x

let rec count_noRepeats
  (#t: eqtype)
  (l: list t)
: Lemma
  (requires (forall x . count x l <= 1))
  (ensures (noRepeats l))
= match l with
  | [] -> ()
  | a :: q -> mem_count q a; count_noRepeats q

let noRepeats_sort_noRepeats
  (#t: eqtype)
  (ord: t -> t -> Tot bool)
  (ord_irrefl: squash (forall (x: t) . ~ (ord x x)))
  (ord_trans: squash (forall (x1 x2 x3: t) . (ord x1 x2 /\ ord x2 x3) ==> ord x1 x3))
  (ord_total: squash (forall (x1 x2: t) . ord x1 x2 \/ ord x2 x1 \/ x1 == x2))
  (l: list t)
: Lemma
  (requires (noRepeats_sort ord l))
  (ensures (noRepeats l))
= sortWith_sorted (compare_of_bool (clos_refl ord)) l;
  bool_of_compare_of_bool (clos_refl ord);
  let l' = sortWith (compare_of_bool (clos_refl ord)) l in
  sorted_feq2 (bool_of_compare (compare_of_bool (clos_refl ord))) (clos_refl ord) l';
  noRepeats_sorted_noRepeats ord ord_irrefl ord_trans (clos_refl ord) (clos_refl_total ord) l';
  sortWith_permutation (compare_of_bool (clos_refl ord)) l;
  Classical.forall_intro (Classical.move_requires (noRepeats_count l'));
  count_noRepeats l

let noRepeats_sort8 (l: list FStar.UInt8.t) = noRepeats_sort FStar.UInt8.lt l

let noRepeats_sort_noRepeats8 (l: list FStar.UInt8.t) : Lemma
  (requires (noRepeats_sort8 l))
  (ensures (noRepeats l))
= noRepeats_sort_noRepeats FStar.UInt8.lt () () () l

let noRepeats_sort16 (l: list FStar.UInt16.t) = noRepeats_sort FStar.UInt16.lt l

let noRepeats_sort_noRepeats16 (l: list FStar.UInt16.t) : Lemma
  (requires (noRepeats_sort16 l))
  (ensures (noRepeats l))
= noRepeats_sort_noRepeats FStar.UInt16.lt () () () l

let noRepeats_sort32 (l: list FStar.UInt32.t) = noRepeats_sort FStar.UInt32.lt l

let noRepeats_sort_noRepeats32 (l: list FStar.UInt32.t) : Lemma
  (requires (noRepeats_sort32 l))
  (ensures (noRepeats l))
= noRepeats_sort_noRepeats FStar.UInt32.lt () () () l
