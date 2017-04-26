module Mem

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MR = FStar.Monotonic.RRef
module MS = FStar.Monotonic.Seq

let mem = HS.mem

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
| LocISeq: (
    (r: MS.rid) ->
    (a: Type) ->
    (p: (Seq.seq a -> Type)) ->
    (contents: MS.i_seq r a p) ->
    loc
  )

abstract
let is_ref (l: loc): GTot bool = LocRef? l

let guarded (t: Type) (p: (t -> Type)) : Tot Type = (x: t {p x})

abstract
let loc_type (l: loc) : GTot Type =
  match l with
  | LocRef a _ -> a
  | LocMRef _ a _ _ -> a
  | LocISeq _ a p _ -> guarded (Seq.seq a) p

abstract
let loc_ref (l: loc { is_ref l } ) : GTot (HS.reference (loc_type l)) = LocRef?.contents l

abstract
let is_mref (l: loc): GTot bool = LocMRef? l

abstract
let is_iseq (l: loc): GTot bool = LocISeq? l

let rid = HH.rid
let mr_rid = MR.rid
let ms_rid = MS.rid

// abstract // this is not possible, unification issues
let loc_region_type (l: loc) : GTot Type =
  if is_iseq l then ms_rid else
  if is_mref l then mr_rid else
  rid

abstract
let loc_region (l: loc): GTot (loc_region_type l) =
  match l with
  | LocRef _ r -> HS.frameOf r
  | LocMRef r _ _ _ -> r
  | LocISeq r _ _ _ -> r

let reln = MR.reln

let grows (#a: Type) (#p: (Seq.seq a -> Type)) (s1 s2: guarded (Seq.seq a) p) = MS.grows (s1 <: Seq.seq a) (s2 <: Seq.seq a)

let hetero_id
  (to: Type)
  (#from: Type)
  (x: from)
  (q: squash (from == to))
: Pure to
  (requires True)
  (ensures (fun y -> y == x /\ x == y))
= x

let hetero_id'
  (to: Type)
  (#from: Type)
  (x: from)
  (q: squash (to == from))
: Pure to
  (requires True)
  (ensures (fun y -> y == x /\ x == y))
= x

abstract
let loc_reln (l: loc { is_mref l \/ is_iseq l }) : GTot (reln (loc_type l)) =
  match l with
  | LocMRef _ _ b _ -> b
  | LocISeq _ a p _ -> grows #a #p

abstract
let loc_mref (l: loc { is_mref l }) : GTot (MR.m_rref (loc_region l) (loc_type l) (loc_reln l)) =
  LocMRef?.contents l

abstract
let loc_is_at_most_one
  (l: loc)
: Lemma
  (ensures (
    (if is_ref l then 1 else 0) +
    (if is_mref l then 1 else 0) +
    (if is_iseq l then 1 else 0) <=
    1
  ))
= ()

abstract
let is_mref_inj
  (l1: loc {is_mref l1})
  (l2: loc {is_mref l2})
: Lemma
  (requires (loc_region l1 === loc_region l2 /\ loc_type l1 == loc_type l2 /\ loc_reln l1 === loc_reln l2 /\ loc_mref l1 === loc_mref l2))
  (ensures (l1 == l2))
= ()

abstract
let loc_iseq_type
  (l: loc {is_iseq l})
: GTot Type
= LocISeq?.a l

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

let loc_invar
  (l: loc { is_iseq l } )
: GTot (Seq.seq (loc_iseq_type l) -> Type)
= LocISeq?.p l

let iseq
  (r: MS.rid)
  (a: Type)
  (p: (Seq.seq a -> Type))
: Tot Type
= (l: (l: loc { is_iseq l } ) { loc_iseq_type l == a /\ loc_region l == r /\ loc_invar l == p } )

let loc_type_iseq
  (#r: MS.rid)
  (#a: Type)
  (#p: (Seq.seq a -> Type))
  (x: iseq r a p)
: Lemma
  (loc_type x == guarded (Seq.seq a) p)
  [SMTPat (loc_type x)]
= ()

let loc_reln_iseq
  (#r: MS.rid)
  (#a: Type)
  (#p: (Seq.seq a -> Type))
  (x: iseq r a p)
: Lemma
  (loc_reln x == grows #a #p)
  [SMTPat (loc_reln x)]
= ()

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
let iseq_of_i_seq
  (#r: MS.rid)
  (#a: Type)
  (#p: (Seq.seq a -> Type))
  (ms: MS.i_seq r a p)
: GTot (iseq r a p)
= LocISeq r a p ms

abstract
let i_seq_of_iseq
  (#r: MS.rid)
  (#a: Type)
  (#p: (Seq.seq a -> Type))
  (ms: iseq r a p)
: GTot (MS.i_seq r a p)
= LocISeq?.contents ms

abstract
let sel
  (h: mem)
  (l: loc)
: GTot (loc_type l)
= match l with
  | LocRef _ rr -> HS.sel h rr
  | LocMRef _ _ _ rr -> MR.m_sel h rr
  | LocISeq r a p rr ->
    let x : guarded (Seq.seq a) p = MS.i_sel h rr in x

abstract
let as_reference
  (l: loc)
: GTot (HS.reference (loc_type l))
= match l with
  | LocRef _ rr -> rr
  | LocMRef _ _ _ rr -> MR.as_hsref rr
  | LocISeq r a p rr -> 
    let (x : HS.ref (s: Seq.seq a {p s}) { x.HS.id = r}) = MR.as_hsref rr in
    let (y: HS.reference (s: Seq.seq a {p s})) = x in
    assert_norm (guarded (Seq.seq a) p == (s: Seq.seq a {p s}));
    hetero_id (HS.reference (guarded (Seq.seq a) p)) y ()

private
let loc_region_iseq
  r a p x
: Lemma
  ((as_reference (LocISeq r a p x)).HS.id == loc_region (LocISeq r a p x))
  [SMTPatOr [
    [SMTPat (as_reference (LocISeq r a p x)).HS.id];
    [SMTPat (loc_region (LocISeq r a p x))];
  ]]
= assert ((MR.as_hsref x).HS.id == r) // TODO: WHY WHY WHY not automatic?

let live_region = HS.live_region

abstract
let upd
  (h: mem)
  (l: loc { live_region h (loc_region l) } )
  (x: loc_type l)
: GTot mem
= match l with
  | LocRef _ rr -> HS.upd h rr x
  | LocMRef _ _ _ rr -> HS.upd h (MR.as_hsref rr) x
  | LocISeq r a p rr ->
    let x : guarded (Seq.seq a) p = x in
    HS.upd h (MR.as_hsref rr) x

private
let upd_iseq
  (h: mem)
  (r: MS.rid) a p rr
  (x: guarded (Seq.seq a) p)
: Lemma
  (requires (live_region h r))
  (ensures (live_region h r /\ upd h (LocISeq r a p rr) x == HS.upd h (MR.as_hsref rr) x))
  [SMTPat (upd h (LocISeq r a p rr))]
= assert_norm (upd h (LocISeq r a p rr) x == HS.upd h (MR.as_hsref rr) x)

let sel_upd
  (h: mem)
  (l: loc { live_region h (loc_region l) })
  (x: loc_type l)
: Lemma
  (sel (upd h l x) l == x)
  [SMTPat (sel (upd h l x) l)]
= ()

let modifies_regions
  (rs: Set.set rid)
  (h0 h1: mem)
: GTot Type0
= HS.modifies rs h0 h1

let modifies_regions_refl
  (rs: Set.set rid)
  (h: mem)
: Lemma
  (modifies_regions rs h h)
= ()

let modifies_regions_trans
  (rs12 rs23: Set.set rid)
  (h1 h2 h3: mem)
: Lemma
  (requires (
    modifies_regions rs12 h1 h2 /\
    modifies_regions rs23 h2 h3
  ))
  (ensures (
    modifies_regions (Set.union rs12 rs23) h1 h3
  ))
= ()

let modifies_regions_subset
  (rs rs': Set.set rid)
  (h h' : mem)
: Lemma
  (requires (Set.subset rs rs' /\ modifies_regions rs h h'))
  (ensures (modifies_regions rs' h h'))
= ()

assume val filter
  (r: rid)
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

let filter_empty
  (r: HH.rid)
: Lemma
  (filter r TSet.empty == TSet.empty)
  [SMTPat (filter r TSet.empty)]
= TSet.lemma_equal_elim (filter r TSet.empty) TSet.empty

let filter_singleton_same
  (r: HH.rid)
  (l: loc)
: Lemma
  (requires (r = (loc_region l <: HH.rid)))
  (ensures (filter r (TSet.singleton l) == TSet.singleton (HS.as_aref (as_reference l))))
  [SMTPat (filter r (TSet.singleton l))]
= TSet.lemma_equal_elim (filter r (TSet.singleton l)) (TSet.singleton (HS.as_aref (as_reference l)))

let filter_singleton_other
  (r: HH.rid)
  (l: loc)
: Lemma
  (requires (r <> (loc_region l <: HH.rid)))
  (ensures (filter r (TSet.singleton l) == TSet.empty))
  [SMTPat (filter r (TSet.singleton l))]
= TSet.lemma_equal_elim (filter r (TSet.singleton l)) TSet.empty

let modifies_locs_in_region
  (r: HH.rid)
  (ls: TSet.set loc {forall (l: loc {TSet.mem l ls}) . r == loc_region l})
  (h0 h1: mem)
: GTot Type0
= HH.modifies_rref r (filter r ls) h0.HS.h h1.HS.h

let modifies_locs_in_region_refl
  (r: HH.rid)
  (ls: TSet.set loc {forall (l: loc {TSet.mem l ls}) . r == loc_region l})
  (h: mem)
: Lemma
  (modifies_locs_in_region r ls h h)
= ()

let modifies_locs_in_region_trans
  (r: HH.rid)
  (ls12: TSet.set loc {(forall (l: loc {TSet.mem l ls12}) . r == loc_region l)})
  (ls23: TSet.set loc {(forall (l: loc {TSet.mem l ls23}) . r == loc_region l)})
  (h1 h2 h3: mem)
: Lemma
  (requires (
    modifies_locs_in_region r ls12 h1 h2 /\
    modifies_locs_in_region r ls23 h2 h3
  ))
  (ensures (
    modifies_locs_in_region r (TSet.union ls12 ls23) h1 h3
  ))
= ()

let modifies_locs_in_region_subset
  (r: HH.rid)
  (ls: TSet.set loc {(forall (l: loc {TSet.mem l ls}) . r == loc_region l)})
  (ls': TSet.set loc {(forall (l: loc {TSet.mem l ls'}) . r == loc_region l)})
  (h h' : mem)
: Lemma
  (requires (TSet.subset ls ls' /\ modifies_locs_in_region r ls h h'))
  (ensures (modifies_locs_in_region r ls' h h'))
= ()

let modifies_regions_modifies_locs_in_region
  (r: HH.rid)
  (rs: Set.set HH.rid)
  (h h' : mem)
: Lemma
  (requires ((~ (Set.mem r rs)) /\ modifies_regions rs h h' /\ live_region h r))
  (ensures (modifies_locs_in_region r TSet.empty h h'))
= ()

abstract
let contains
  (m: mem)
  (l: loc)
: Tot Type0
= HS.contains m (as_reference l)

let contains_live_region
  (l: loc)
  h
: Lemma
  (requires (contains h l))
  (ensures (live_region h (loc_region l)))
  [SMTPatOr [
    [SMTPat (contains h l)];
    [SMTPat (live_region h (loc_region l))];
  ]]
= ()

let loc_diff
  (l1 l2: loc)
: GTot Type0
= ~ (HS.as_aref (as_reference l1) == HS.as_aref (as_reference l2))

let loc_diff_irrefl
  (l: loc)
: Lemma
  (~ (loc_diff l l))
= ()

let loc_diff_sym
  (l1 l2: loc)
: Lemma
  (requires (loc_diff l1 l2))
  (ensures (loc_diff l2 l1))
= ()

let modifies_locs_in_region_sel
  (r: HH.rid)
  (ls: TSet.set loc {(forall (l: loc {TSet.mem l ls}) . r == loc_region l)})
  (h h': mem)
  (l: loc)
: Lemma
  (requires (modifies_locs_in_region r ls h h' /\ contains h l /\ r == loc_region l /\ (
    forall (l' : loc { TSet.mem l' ls } ) .
    loc_diff l l'
  )))
  (ensures (sel h' l == sel h l))
= assert (forall
    (l': loc)
    . (
      TSet.mem l' ls /\
      r == loc_region l' /\
      HS.as_aref (as_reference l) == HS.as_aref (as_reference l')
    ) ==>
    loc_diff l l'
  ) // TODO: WHY WHY WHY not automatic?

unfold
let upd_post
  (h0: mem)
  (r: loc { live_region h0 (loc_region r) } )
  (v: loc_type r)
: GTot Type0
= modifies_regions (Set.singleton (loc_region r)) h0 (upd h0 r v) /\
  modifies_locs_in_region (loc_region r) (TSet.singleton r) h0 (upd h0 r v)

let upd_post_intro
  (h0: mem)
  (r: loc { live_region h0 (loc_region r) } )
  (v: loc_type r)
: Lemma (upd_post h0 r v)
  [SMTPat (upd h0 r v)]
= ()

abstract
let loc_mm
  (l: loc)
: GTot bool
= (as_reference l).HS.mm

let mref_not_mm
  (#r: MR.rid)
  (#a: Type)
  (#b: MR.reln a)
  (m: mref r a b)
: Lemma
  (~ (loc_mm m))
= ()

let is_eternal_region = HS.is_eternal_region

abstract
let recall
  (l: loc)
: Stack unit
  (requires (fun _ -> (is_eternal_region (loc_region l) /\ (~ (loc_mm l)))))
  (ensures (fun m0 _ m1 -> m0 == m1 /\ m1 `contains` l))
= match l with
  | LocRef a r -> ST.recall r
  | LocMRef _ _ _ r -> MR.m_recall r
  | LocISeq _ _ _ r -> MR.m_recall r

(* Accessors *)

abstract
let weak_contains
  (m: mem)
  (l: loc)
: GTot Type0
= HS.weak_contains m (as_reference l)

unfold let read_post (r: loc) (m0: mem) (x: loc_type r) (m1: mem) =
  m1==m0 /\ x==sel m0 r

let weak_live_region = HS.weak_live_region

let weak_live_region_not_mm_weak_contains
  (m: mem)
  (l: loc)
: Lemma
  (requires (weak_live_region m (loc_region l) /\ (~ (loc_mm l))))
  (ensures (weak_contains m l))
= ()

let weak_contains_mref
  (#r: MR.rid)
  (#a: Type)
  (#b: MR.reln a)
  (m: mref r a b)
  (h: mem)
: Lemma
  (weak_contains h m)
  [SMTPat (weak_contains h m)]
= ()

abstract
let read
  (l: loc)
: ST (loc_type l)
  (requires (fun h -> weak_contains h l))
  (ensures (fun m0 x m1 -> read_post l m0 x m1))
= match l with
  | LocRef a r -> !r
  | LocMRef _ _ _ r -> MR.m_read r
  | LocISeq i a p r ->
    let x : guarded (Seq.seq a) p = MS.i_read r in
    x

abstract
let write_pre
  (h0: mem)
  (l: loc)
  (v: loc_type l)
: GTot Type0
= match l with
  | LocRef _ _ -> True
  | LocMRef _ _ b r -> b (sel h0 l) v
  | LocISeq _ _ _ _ -> False

let ref_write_pre
  (#a: Type)
  (h0: mem)
  (r: ref a)
  (v: a)
: Lemma
  (write_pre h0 r v)
  [SMTPat (write_pre h0 r v)]
= ()

let mref_write_pre
  (#r: MR.rid)
  (#a: Type)
  (#b: MR.reln a)
  (h0: mem)
  (m: mref r a b)
  (v: a)
: Lemma
  (requires (b (sel h0 m) v))
  (ensures (write_pre h0 m v))
  [SMTPat (write_pre h0 m v)]
= ()

let contains_live_region
  (m0: mem)
  (l: loc)
: Lemma
  (requires (m0 `contains` l))
  (ensures (live_region m0 (loc_region l)))
  [SMTPat (live_region m0 (loc_region l))]
= ()

unfold let write_post (r:loc) (v:loc_type r) m0 (_u:unit) m1 =
  m0 `contains` r /\ m1 == upd m0 r v

abstract
let write
  (l: loc)
  (v: loc_type l)
: ST unit
  (requires (fun h0 -> h0 `contains` l /\ write_pre h0 l v))
  (ensures (write_post l v))
= match l with
  | LocRef _ r -> r := v
  | LocMRef _ _ _ r -> MR.m_write r v

let get = ST.get

unfold
let write_at_end_pre
  (#rgn: MS.rid)
  (#a: Type)
  (#p: (Seq.seq a -> Type))
  (r: iseq rgn a p)
  (x: a)
  (h: mem)
: Tot Type0
= let w : loc_type r = sel h r in
  let w = hetero_id (guarded (Seq.seq a) p) w () in
  p (Seq.snoc w x)

unfold
let write_at_end_post
  (#rgn: MS.rid)
  (#a: Type)
  (#p: (Seq.seq a -> Type))
  (r: iseq rgn a p)
  (x: a)
  (h0: mem)
  (_: unit)
  (h1: mem)
: Tot Type0
= h0 `contains` r /\ (
    let w : loc_type r = sel h0 r in
    let w = hetero_id (guarded (Seq.seq a) p) w () in
    p (Seq.snoc w x) /\ (
      let s : guarded (Seq.seq a) p = Seq.snoc w x in
      let s = hetero_id (loc_type r) s () in
      h1 == upd h0 r s
  ))

abstract
let write_at_end
  (#rgn: MS.rid)
  (#a: Type)
  (#p: (Seq.seq a -> Type))
  (r: iseq rgn a p)
  (x: a)
: ST unit
  (requires (write_at_end_pre r x))
  (ensures (write_at_end_post r x))
= recall r;
  let w : guarded (Seq.seq a) p = read r in
  let s : guarded (Seq.seq a) p = Seq.snoc w x in
  let rr = LocISeq?.contents r in
  let h0 = get () in
  assert (h0 `HS.contains` (MR.as_hsref rr));
  MR.m_write rr s

let int_at_most #r #a #p (x:int) (is:iseq r a p) (h:mem) : Type0 =
  let s : guarded (Seq.seq a) p = sel h is in
  let s : Seq.seq a = s in
  x < Seq.length s

private
let int_at_most_equiv #r #a #p (x:int) (is:iseq r a p) (h:mem)
: Lemma
  (int_at_most x is h <==> MS.int_at_most x (LocISeq?.contents is) h)
  [SMTPat (int_at_most x is h)]
= ()

unfold let stable_on_t
  (l: loc { is_mref l \/ is_iseq l } )
  (p: (mem -> GTot Type0))
= forall h0 h1 . p h0 /\ loc_reln l (sel h0 l) (sel h1 l) ==> p h1

#reset-options "--z3rlimit 32"

private
let i_sel_eq
  (#r: ms_rid) (#a: Type) (#p: (Seq.seq a -> Type)) (rr:MS.i_seq r a p)
  (h0: mem)
: Lemma
  (MS.i_sel h0 rr == MR.m_sel h0 rr)
= ()

private
let sel_iseq_i_sel
  (#r: ms_rid) (#a: Type) (#p: (Seq.seq a -> Type)) (is:iseq r a p)
  (h0: mem)
  : Lemma
  (((sel h0 is <: guarded (Seq.seq a) p) <: Seq.seq a) == MS.i_sel h0 (LocISeq?.contents is))
= ()

private
let sel_iseq_m_sel
  (#r: ms_rid) (#a: Type) (#p: (Seq.seq a -> Type)) (is:iseq r a p)
  (h0: mem)
  : Lemma
  (((sel h0 is <: guarded (Seq.seq a) p) <: Seq.seq a) == MR.m_sel h0 (LocISeq?.contents is))
= i_sel_eq (LocISeq?.contents is) h0; sel_iseq_i_sel is h0

private
let stable_on_t_iseq
  (#r: ms_rid) (#a: Type) (#p: (Seq.seq a -> Type)) (is:iseq r a p)
  (p': (mem -> GTot Type0))
: Lemma
  (stable_on_t is p' <==> MR.stable_on_t (LocISeq?.contents is) p')
= loc_type_iseq is;
  let f
    (h0 h1: mem)
  : Lemma
    (requires (stable_on_t is p' /\ p' h0 /\ MS.grows (MR.m_sel h0 (LocISeq?.contents is)) (MR.m_sel h1 (LocISeq?.contents is))))
    (ensures (p' h1))
  = 
    sel_iseq_m_sel is h0;
    sel_iseq_m_sel is h1;
    assert (grows #a #p (sel h0 is) (sel h1 is))
  in
  let g
    (h0 h1: mem)
  : Lemma
    (requires (MR.stable_on_t (LocISeq?.contents is) p' /\ p' h0 /\ grows #a #p (sel h0 is) (sel h1 is)))
    (ensures (p' h1))
  =
    sel_iseq_m_sel is h0;
    sel_iseq_m_sel is h1
  in
  Classical.forall_intro_2 (let f' (h0: mem) = Classical.move_requires (f h0) in f');
  Classical.forall_intro_2 (let g' (h0: mem) = Classical.move_requires (g h0) in g')

abstract
let int_at_most_is_stable (#r:ms_rid) (#a:Type) (#p: Seq.seq a -> Type) (is:iseq r a p) (k:int)
  : Lemma (ensures (stable_on_t is (int_at_most k is)))
  = stable_on_t_iseq is (int_at_most k is);
    MS.int_at_most_is_stable (LocISeq?.contents is) k
    
