module Mem

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MR = FStar.Monotonic.RRef

abstract
noeq
type loc =
| LocRef: (
    (a: Type) ->
    (contents: HS.reference a) ->
    loc
 )
| LocMRef: (
    (r: MR.rid) ->
    (a: Type) ->
    (b: MR.reln a) ->
    (contents: MR.m_rref r a b) ->
    loc
  )

abstract
let is_ref (l: loc): GTot bool = LocRef? l

abstract
let loc_type (l: loc) : GTot Type =
  match l with
  | LocRef a _ -> a
  | LocMRef _ a _ _ -> a

abstract
let loc_ref (l: loc { is_ref l } ) : GTot (HS.reference (loc_type l)) = LocRef?.contents l

abstract
let is_mref (l: loc): GTot bool = LocMRef? l

// abstract // this is not possible, unification issues
let loc_region_type (l: loc) : GTot Type =
  if is_mref l then MR.rid else HH.rid

abstract
let loc_region (l: loc): GTot (loc_region_type l) =
  match l with
  | LocRef _ r -> HS.frameOf r
  | LocMRef r _ _ _ -> r

abstract
let loc_reln (l: loc { is_mref l }) : GTot (MR.reln (loc_type l)) =
  LocMRef?.b l

abstract
let loc_mref (l: loc { is_mref l }) : GTot (MR.m_rref (loc_region l) (loc_type l) (loc_reln l)) =
  LocMRef?.contents l

abstract
let loc_is_at_most_one
  (l: loc)
: Lemma
  ((if is_ref l then 1 else 0) + (if is_mref l then 1 else 0) <= 1)
= ()

abstract
let is_mref_inj
  (l1: loc {is_mref l1})
  (l2: loc {is_mref l2})
: Lemma
  (requires (loc_region l1 === loc_region l2 /\ loc_type l1 == loc_type l2 /\ loc_reln l1 === loc_reln l2 /\ loc_mref l1 === loc_mref l2))
  (ensures (l1 == l2))
= ()

let ref
  (a: Type)
: Tot Type
= (l: loc { is_ref l /\ loc_type l == a } )

let mref
  (r: MR.rid)
  (a: Type)
  (b: MR.reln a)
: Tot Type
= (l: loc { is_mref l /\ loc_type l == a /\ loc_region l == r /\ loc_reln l == b } )

abstract
let ref_of_reference
  (#a: Type)
  (r: HS.reference a)
: GTot (ref a)
= LocRef a r

abstract
let reference_of_ref
  (#a: Type)
  (r: ref a)
: GTot (HS.reference a)
= loc_ref r

abstract
let ref_of_reference_of_ref
  (#a: Type)
  (r: ref a)
: Lemma
  (ref_of_reference (reference_of_ref r) == r)
= ()

abstract
let reference_of_ref_of_reference
  (#a: Type)
  (r: HS.reference a)
: Lemma
  (reference_of_ref (ref_of_reference r) == r)
= ()

let mref_of_m_rref
  (#r: MR.rid)
  (#a: Type)
  (#b: MR.reln a)
  (mr: MR.m_rref r a b)
: GTot (mref r a b)
= LocMRef r a b mr

let m_rref_of_mref
  (#r: MR.rid)
  (#a: Type)
  (#b: MR.reln a)
  (mr: mref r a b)
: GTot (MR.m_rref r a b)
= loc_mref mr 

abstract
let sel
  (h: HS.mem)
  (l: loc)
: GTot (loc_type l)
= match l with
  | LocRef _ rr -> HS.sel h rr
  | LocMRef _ _ _ rr -> MR.m_sel h rr

abstract
let upd
  (h: HS.mem)
  (l: loc { HS.live_region h (loc_region l) } )
  (x: loc_type l)
: GTot HS.mem
= match l with
  | LocRef _ rr -> HS.upd h rr x
  | LocMRef _ _ _ rr -> HS.upd h (MR.as_hsref rr) x

abstract
let as_reference
  (l: loc)
: GTot (HS.reference (loc_type l))
= match l with
  | LocRef _ rr -> rr
  | LocMRef _ _ _ rr -> MR.as_hsref rr

assume val filter
  (r: HH.rid)
  (ls: TSet.set loc)
: GTot (TSet.set Heap.aref)

assume val mem_filter
  (r: HH.rid)
  (ls: TSet.set loc)
: Lemma
  (forall (a: Heap.aref) .
    TSet.mem a (filter r ls) <==> (
    exists (l: loc) . (
      TSet.mem l ls /\
      r == loc_region l /\
      a == HS.as_aref (as_reference l)
  )))
  [SMTPat (filter r ls)]

let filter_union
  (r: HH.rid)
  (ls1 ls2: TSet.set loc)
: Lemma
  (filter r (TSet.union ls1 ls2) == TSet.union (filter r ls1) (filter r ls2))
  [SMTPat (filter r (TSet.union ls1 ls2))]
= TSet.lemma_equal_elim (filter r (TSet.union ls1 ls2)) (TSet.union (filter r ls1) (filter r ls2))

let modifies
  (rs: Set.set HH.rid)
  (ls: TSet.set loc {forall (l: loc {TSet.mem l ls}) . Set.mem (loc_region l) rs})
  (h0 h1: HS.mem)
: GTot Type0
= HS.modifies rs h0 h1 /\ (
    forall (r: HH.rid { Map.contains h0.HS.h r } ) .
    HH.modifies_rref r (filter r ls) h0.HS.h h1.HS.h
  )

let modifies_refl
  (rs: Set.set HH.rid)
  (ls: TSet.set loc {forall (l: loc {TSet.mem l ls}) . Set.mem (loc_region l) rs})
  (h: HS.mem)
: Lemma
  (modifies rs ls h h)
= ()

let modifies_trans
  (rs12 rs23: Set.set HH.rid)
  (ls12: TSet.set loc {(forall (l: loc {TSet.mem l ls12}) . Set.mem (loc_region l) rs12)})
  (ls23: TSet.set loc {(forall (l: loc {TSet.mem l ls23}) . Set.mem (loc_region l) rs23)})
  (h1 h2 h3: HS.mem)
: Lemma
  (requires (
    modifies rs12 ls12 h1 h2 /\
    modifies rs23 ls23 h2 h3
  ))
  (ensures (
    modifies (Set.union rs12 rs23) (TSet.union ls12 ls23) h1 h3
  ))
= ()

let modifies_subset
  (rs rs': Set.set HH.rid)
  (ls: TSet.set loc {(forall (l: loc {TSet.mem l ls}) . Set.mem (loc_region l) rs)})
  (ls': TSet.set loc {(forall (l: loc {TSet.mem l ls'}) . Set.mem (loc_region l) rs')})
  (h h' : HS.mem)
: Lemma
  (requires (Set.subset rs rs' /\ TSet.subset ls ls' /\ modifies rs ls h h'))
  (ensures (modifies rs' ls' h h'))
= ()

