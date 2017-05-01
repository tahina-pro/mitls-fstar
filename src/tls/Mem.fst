module Mem

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module MR = FStar.Monotonic.RRef
module MS = FStar.Monotonic.Seq

let mem = HS.mem

unfold
let grows (a: Type) (p: (Seq.seq a -> Type)) (s1 s2: (s: Seq.seq a {p s})) = MS.grows s1 s2

let is_eternal_region = HS.is_eternal_region

noeq
type class = | Class :
  (ref: Type) ->
  (value: Type) ->
  (as_reference: (ref -> GTot (HS.reference value))) ->
  (region_guard: (HH.rid -> GTot Type)) ->
  (region_guarded: (
    (r: ref) ->
    Lemma
    (region_guard (HS.frameOf (as_reference r)))
  )) ->
  (reln: MR.reln value) ->
  (recall: (
    (r: ref) ->
    Stack unit
    (requires (fun _ ->
      let rr = as_reference r in (
      is_eternal_region (HS.frameOf rr) /\
      (~ (HS.is_mm rr))
    )))
    (ensures (fun m0 _ m1 ->
      m0 == m1 /\ m1 `HS.contains` (as_reference r)
    ))
  )) ->
  (read: (
    (r: ref) ->
    ST value
    (requires (fun h -> HS.weak_contains h (as_reference r)))
    (ensures (fun m0 x m1 -> m1 == m0 /\ x == HS.sel m0 (as_reference r)))
  )) ->
  (write_pre: (
    (r: ref) ->
    (v: value) ->
    (h: mem) ->
    GTot Type
  )) ->
  (write: (
    (r: ref) ->
    (v: value) ->
    ST unit
    (requires (fun h0 -> h0 `HS.contains` (as_reference r) /\ write_pre r v h0))
    (ensures (fun m0 _ m1 ->
      m0 `HS.contains` (as_reference r) /\
      m1 == HS.upd m0 (as_reference r) v
  )))) ->
  class

noeq
type loc = | Loc :
  (cl: class) ->
  (obj: Class?.ref cl) ->
  loc

unfold
let ref_cl (a: Type): Tot class = Class
  (HS.reference a)
  a
  (fun x -> x)
  (fun _ -> True)
  (fun _ -> ())
  (fun _ _ -> False)
  (fun r -> ST.recall r)
  (fun r -> !r)
  (fun _ _ _ -> True)
  (fun r v -> r := v)

let ref (a: Type) : Tot Type = (l: loc { Loc?.cl l == ref_cl a } )

unfold
let mref_cl (r: MR.rid) (a: Type) (b: MR.reln a) : Tot class = Class
  (MR.m_rref r a b)
  a
  (MR.as_hsref #r #a #b)
  (fun r -> HS.is_eternal_region r)
  (fun _ -> ())
  b
  (fun r -> MR.m_recall r)
  (fun r -> MR.m_read r)
  (fun l v h0 -> b (MR.m_sel h0 l) v)
  (fun l v -> MR.m_write l v)

let mref (r: MR.rid) (a: Type) (b: MR.reln a) : Tot Type =
  (l: loc { Loc?.cl l == mref_cl r a b } )

unfold
let hetero_id
  (to: Type)
  (#from: Type)
  (x: from)
  (q: squash (from == to))
: Pure to
  (requires True)
  (ensures (fun y -> y == x /\ x == y))
= x

unfold
let i_as_hsref
  (r: MS.rid)
  (a: Type)
  (p: (Seq.seq a -> Type))
  (x: MS.i_seq r a p)
: GTot (HS.reference (s: (Seq.seq a) {p s}))
= let (x : HS.ref (s: Seq.seq a {p s}) { x.HS.id = r}) = MR.as_hsref x in
  let (y: HS.reference (s: Seq.seq a {p s})) = x in
  hetero_id (HS.reference (s: Seq.seq a {p s})) y ()

unfold
let iseq_cl (r: MS.rid) (a: Type) (p: (Seq.seq a -> Type)) : Tot class = Class
  (MS.i_seq r a p)
  (s: (Seq.seq a) {p s})
  (i_as_hsref r a p)
  (fun r -> HS.is_eternal_region r)
  (fun _ -> ())
  (grows a p)
  (fun r -> MR.m_recall r)
  (fun r -> MS.i_read r)
  (fun _ _ _ -> False)
  (fun _ _ -> ())

let iseq (r: MS.rid) (a: Type) (p: (Seq.seq a -> Type)) : Tot Type =
  (l: loc { Loc?.cl l == iseq_cl r a p } )

unfold
let loc_type (l: loc) : Tot Type = Class?.value (Loc?.cl l)

// unfold  // impossible, makes `loc_region` no longer typecheck
let loc_region_type (l: loc) : Tot Type =
  (r: HH.rid { Class?.region_guard (Loc?.cl l) r})

unfold
let loc_region (l: loc) : GTot (loc_region_type l) =
  let (Loc c r) = l in
  Class?.region_guarded c r;
  HS.frameOf (Class?.as_reference c r)

unfold
let as_reference
  (l: loc)
: GTot (HS.reference (loc_type l))
= Class?.as_reference (Loc?.cl l) (Loc?.obj l)

unfold
let sel
  (h: mem)
  (l: loc)
: GTot (loc_type l)
= HS.sel h (as_reference l)

let live_region = HS.live_region

unfold
let upd
  (h: mem)
  (l: loc { live_region h (loc_region l) } )
  (v: loc_type l)
: GTot (mem)
= HS.upd h (as_reference l) v

abstract
let sel_upd
  (h: mem)
  (l: loc { live_region h (loc_region l) })
  (x: loc_type l)
: Lemma
  (sel (upd h l x) l == x)
  [SMTPat (sel (upd h l x) l)]
= ()

unfold
let contains
  (h: mem)
  (l: loc)
= HS.contains h (as_reference l)

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

let reln = MR.reln

unfold
let stable_on_t
  (l: loc)
  (p: (mem -> GTot Type0))
= forall h0 h1 . p h0 /\ Class?.reln (Loc?.cl l) (sel h0 l) (sel h1 l) ==> p h1

let int_at_most #r #a #p (x:int) (is: iseq r a p) (h:mem) : Type0 =
  let s: Seq.seq a = sel h is in // TODO: WHY WHY WHY is this type cast needed?
  x < Seq.length s

abstract
let int_at_most_is_stable (#r:MS.rid) (#a:Type) (#p: Seq.seq a -> Type) (is:iseq r a p) (k:int)
  : Lemma (ensures (stable_on_t is (int_at_most k is)))
= assert (forall h . sel h is == MS.i_sel h (Loc?.obj is <: MS.i_seq r a p));
  MS.int_at_most_is_stable (Loc?.obj is <: MS.i_seq r a p) k

let rid = HH.rid

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
: GTot (Set.set nat)

assume val mem_filter
  (r: HH.rid)
  (ls: TSet.set loc)
: Lemma
  (forall (a:nat) .
    Set.mem a (filter r ls) <==> (
    exists (l: loc) . (
      TSet.mem l ls /\
      r == loc_region l /\
      a == HS.as_addr (as_reference l)
  )))
  [SMTPat (filter r ls)]

let filter_union
  (r: HH.rid)
  (ls1 ls2: TSet.set loc)
: Lemma
  (filter r (TSet.union ls1 ls2) == Set.union (filter r ls1) (filter r ls2))
  [SMTPat (filter r (TSet.union ls1 ls2))]
= Set.lemma_equal_elim (filter r (TSet.union ls1 ls2)) (Set.union (filter r ls1) (filter r ls2))

let filter_empty
  (r: HH.rid)
: Lemma
  (filter r TSet.empty == Set.empty)
  [SMTPat (filter r TSet.empty)]
= Set.lemma_equal_elim (filter r TSet.empty) Set.empty

let filter_singleton_same
  (r: HH.rid)
  (l: loc)
: Lemma
  (requires (r = (loc_region l <: HH.rid)))
  (ensures (filter r (TSet.singleton l) == Set.singleton (HS.as_addr (as_reference l))))
  [SMTPat (filter r (TSet.singleton l))]
= Set.lemma_equal_elim (filter r (TSet.singleton l)) (Set.singleton (HS.as_addr (as_reference l)))

let filter_singleton_other
  (r: HH.rid)
  (l: loc)
: Lemma
  (requires (r <> (loc_region l <: HH.rid)))
  (ensures (filter r (TSet.singleton l) == Set.empty))
  [SMTPat (filter r (TSet.singleton l))]
= Set.lemma_equal_elim (filter r (TSet.singleton l)) Set.empty

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

let loc_diff
  (l1 l2: loc)
: GTot Type0
= (HS.as_addr (as_reference l1) <> HS.as_addr (as_reference l2))

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
      HS.as_addr (as_reference l) = HS.as_addr (as_reference l')
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
= assume (contains h0 r)

abstract
let loc_mm
  (l: loc)
: GTot bool
= HS.is_mm (as_reference l)

let mref_not_mm
  (#r: MR.rid)
  (#a: Type)
  (#b: MR.reln a)
  (m: mref r a b)
: Lemma
  (~ (loc_mm m))
= ()

let recall
  (l: loc)
: Stack unit
  (requires (fun _ -> (is_eternal_region (loc_region l) /\ (~ (loc_mm l)))))
  (ensures (fun m0 _ m1 -> m0 == m1 /\ m1 `contains` l))
= Class?.recall (Loc?.cl l) (Loc?.obj l)

(* Accessors *)

let weak_contains
  (m: mem)
  (l: loc)
: GTot Type0
= HS.weak_contains m (as_reference l)

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

let weak_contains_iseq
  (#r: MS.rid)
  (#a: Type)
  (#p: (Seq.seq a -> Type)) 
  (m: iseq r a p)
  (h: mem)
: Lemma
  (weak_contains h m)
  [SMTPat (weak_contains h m)]
= ()

unfold
let read_post (r: loc) (m0: mem) (x: loc_type r) (m1: mem) =
  m1==m0 /\ x==sel m0 r

let read
  (l: loc)
: ST (loc_type l)
  (requires (fun h -> weak_contains h l))
  (ensures (fun m0 x m1 -> read_post l m0 x m1))
= Class?.read (Loc?.cl l) (Loc?.obj l)

unfold
let write_pre
  (l: loc)
  (v: loc_type l)
= Class?.write_pre (Loc?.cl l) (Loc?.obj l) v

unfold
let write_post (r:loc) (v:loc_type r) m0 (_u:unit) m1 =
  m0 `contains` r /\ m1 == upd m0 r v

(*
let ref_write_pre
  (#a: Type)
  (h0: mem)
  (r: ref a)
  (v: a)
: Lemma
  (write_pre r v h0)
  [SMTPat (write_pre r v h0)]
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
*)

let write
  (l: loc)
  (v: loc_type l)
: ST unit
  (requires (fun h0 -> h0 `contains` l /\ write_pre l v h0))
  (ensures (write_post l v))
= Class?.write (Loc?.cl l) (Loc?.obj l) v

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
= p (Seq.snoc (sel h r) x)

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
    let s = Seq.snoc (sel h0 r) x in
    p s /\
    h1 == upd h0 r s
  )

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
  let w = read r in
  let s = Seq.snoc w x in
  let rr : MS.i_seq rgn a p = Loc?.obj r in
  let h0 = get () in
  assert (h0 `HS.contains` (MR.as_hsref rr));
  MR.m_write rr s
