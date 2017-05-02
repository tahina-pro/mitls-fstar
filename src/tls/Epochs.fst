module Epochs

(* 
    This modules implements the mutable state for the successive StAE epochs allocated by KeySchedule and used by TLS. 
    Its separation from Handshake and coding is somewhat arbitrary.
    An elaboration would ensure that keys in old epochs are erased. 
    (i.e. we only keep old epoch AE logs for specifying authentication)
*)

open FStar.Seq // DO NOT move further below, it would shadow `FStar.HyperStack.mem`
open Platform.Error
open Platform.Bytes

open TLSError
open TLSInfo
open TLSConstants
open Range
//open HandshakeMessages
open StAE
//open Negotiation

type random = TLSInfo.random 

inline_for_extraction let epochs_debug = true
val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("EPO| "^s^"\n"))
unfold val trace: s:string -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
unfold let trace = if epochs_debug then print else (fun _ -> ())


type epoch_region_inv (#i:id) (hs_rgn:rgn) (r:reader (peerId i)) (w:writer i) =
  Mem.disjoint hs_rgn (region w) /\
  Mem.parent (region w) <> Mem.root /\
  Mem.parent (region r) <> Mem.root /\
  // grandparent of each writer is a sibling of the handshake
  Mem.parent hs_rgn = Mem.parent (Mem.parent (region w))  /\ 
  Mem.disjoint (region w) (region r) /\
  // they are all colored as epoch regions
  is_epoch_rgn (region w) /\ 
  is_epoch_rgn (region r) /\
  is_epoch_rgn (Mem.parent (region w)) /\
  is_epoch_rgn (Mem.parent (region r)) /\
  //except for the hs_rgn, of course
  is_hs_rgn hs_rgn

abstract type epoch_region_inv'
  (#i:id)
  (hs_rgn:rgn)
  (r:reader (peerId i))
  (w:writer i)
= epoch_region_inv hs_rgn r w

noeq type epoch (hs_rgn:rgn) (n:random) =
  | Epoch: #i:id{nonce_of_id i = n} ->
      h:Negotiation.handshake ->
      r: reader (peerId i) ->
      w: writer i {epoch_region_inv' hs_rgn r w} -> epoch hs_rgn n
// we would extend/adapt it for TLS 1.3,
// e.g. to notify 0RTT/forwad-privacy transitions
// for now epoch completion is a total function on handshake --- should be stateful

let epoch_id #r #n (e:epoch r n) : StAE.stae_id = Epoch?.i e

let reveal_epoch_region_inv_all (u:unit)
  : Lemma (forall i hs_rgn r w.{:pattern (epoch_region_inv' #i hs_rgn r w)}
       epoch_region_inv' #i hs_rgn r w   <==>
       epoch_region_inv #i hs_rgn r w)
=
  ()

let reveal_epoch_region_inv (#hs_rgn:rgn) (#n:random) (e:epoch hs_rgn n)
  : Lemma (let r = Epoch?.r e in
       let w = Epoch?.w e in
       epoch_region_inv hs_rgn r w)
= 
  ()

let writer_epoch (#hs_rgn:rgn) (#n:random) (e:epoch hs_rgn n)
  : Tot (w:writer (e.i) {epoch_region_inv hs_rgn (Epoch?.r e) w})
= 
  Epoch?.w e

let reader_epoch (#hs_rgn:rgn) (#n:random) (e:epoch hs_rgn n)
  : Tot (r:reader (peerId e.i) {epoch_region_inv hs_rgn r (Epoch?.w e)})
= 
  Epoch?.r e

(* The footprint just includes the writer regions *)
let epochs_inv (#r:rgn) (#n:random) (es: seq (epoch r n)) =
  forall (i:nat { i < Seq.length es })
    (j:nat { j < Seq.length es /\ i <> j}).{:pattern (Seq.index es i); (Seq.index es j)}
    let ei = Seq.index es i in
    let ej = Seq.index es j in
    // they all descend from a common epochs sub-region of the connection
    Mem.parent (region ei.w) = Mem.parent (region ej.w) /\
    // each epoch writer lives in a region disjoint from the others
    Mem.disjoint (region ei.w) (region ej.w)

abstract let epochs_inv' (#r:rgn) (#n:random) (es: seq (epoch r n)) = epochs_inv es

let reveal_epochs_inv' (u:unit)
  : Lemma (forall (r:rgn) (#n:random) (es:seq (epoch r n)). {:pattern (epochs_inv' es)}
         epochs_inv' es
         <==>
         epochs_inv es)
  = ()

// Epoch counters i must satisfy -1 <= i < length !es
type epoch_ctr_inv (#a:Type0) (#p:(seq a -> Type)) (r:Mem.eternal_rid) (es:Mem.iseq r a p) =
  x:int{-1 <= x /\ Mem.witnessed (Mem.int_at_most x es)}

type epoch_ctr (#a:Type0) (#p:(seq a -> Type)) (r:Mem.eternal_rid) (es:Mem.iseq r a p) =
  Mem.mref r (epoch_ctr_inv r es) Mem.increases

// As part of the handshake state, 
// we keep a sequence of allocated epochs, 
// together with counters for reading and writing
//NS: probably need some anti-aliasing invariant of these three references
//17-04-17 CF: consider switching to a single reference to a triple. 
noeq type epochs (r:rgn) (n:random) = | MkEpochs: 
  es: Mem.iseq r (epoch r n) (epochs_inv #r #n) ->
  read: epoch_ctr r es ->
  write: epoch_ctr r es -> epochs r n

let containsT (#r:rgn) (#n:random) (es:epochs r n) (h: Mem.mem) =
    Mem.contains h (MkEpochs?.es es) 

assume
val alloc_log_and_ctrs: #a:Type0 -> #p:(seq a -> Type0) -> r:rgn ->
  ST (is:Mem.iseq r a p & c1:epoch_ctr r is & c2:epoch_ctr r is)
    (requires (fun h -> p Seq.createEmpty))
    (ensures (fun h0 x h1 ->
      Mem.modifies_regions (Set.singleton r) h0 h1 /\
      Mem.modifies_locs_in_region r TSet.empty h0 h1 /\
      (let (| is, c1, c2 |) = x in
      Mem.contains h1 is /\
      Mem.contains h1 c1 /\
      Mem.contains h1 c2 /\ 
      Mem.sel h1 is == Seq.createEmpty)))
(*
let alloc_log_and_ctrs #a #p r =
  let init = Seq.createEmpty in
  let is = alloc_mref_iseq p r init in
  witness is (int_at_most (-1) is);
  let c1 : epoch_ctr #a #p r is = m_alloc r (-1) in
  let c2 : epoch_ctr #a #p r is = m_alloc r (-1) in
  (| is, c1, c2 |)
*)

#reset-options "--z3rlimit 16"
#reset-options "--z3rlimit 128"

val incr_epoch_ctr :
  #a:Type0 ->
  #p:(seq a -> Type0) ->
  #r:rgn ->
  #is:Mem.iseq r a p ->
  ctr:epoch_ctr r is ->
  ST unit
    (requires fun h -> 1 + Mem.sel h ctr < Seq.length (Mem.sel h is))
    (ensures (fun h0 _ h1 ->
      Mem.modifies_regions (Set.singleton r) h0 h1 /\ (
      Mem.loc_region_mref ctr; ( // FIXME: WHY WHY WHY does this become suddenly necessary? WHY WHY WHY does the pattern NOT trigger?
      Mem.modifies_locs_in_region r (TSet.singleton ctr) h0 h1 /\
      (Mem.sel h1 ctr = Mem.sel h0 ctr + 1 ) ))))
let incr_epoch_ctr #a #p #r #is ctr =
  Mem.recall ctr;
  let cur = Mem.read ctr in
  Mem.int_at_most_is_stable is (cur + 1);
  Mem.witness is (Mem.int_at_most (cur + 1) is);
  Mem.write ctr (cur + 1)
       
assume
val create: r:rgn -> n:random -> ST (epochs r n)
    (requires (fun h -> True))
    (ensures (fun h0 x h1 ->
      Mem.modifies_regions (Set.singleton r) h0 h1 /\ 
      Mem.modifies_locs_in_region r TSet.empty h0 h1
    ))
(*
let create (r:rgn) (n:random) =
  let (| esref, c1, c2 |) = alloc_log_and_ctrs #(epoch r n) #(epochs_inv #r #n) r in
  MkEpochs esref c1 c2
*)

unfold let incr_pre #r #n (es:epochs r n) (proj:(es:epochs r n -> Tot (epoch_ctr r (MkEpochs?.es es)))) h : GTot Type0 =
  let ctr = proj es in
  let cur = Mem.sel h ctr in
  cur + 1 < Seq.length (Mem.sel h (MkEpochs?.es es))

unfold let incr_post #r #n (es:epochs r n) (proj:(es:epochs r n -> Tot (epoch_ctr r (MkEpochs?.es es)))) h0 (_:unit) h1 : GTot Type0 =
  let ctr = proj es in
  let oldr = Mem.sel h0 ctr in
  let newr = Mem.sel h1 ctr in
  Mem.modifies_regions (Set.singleton r) h0 h1 /\
  Mem.modifies_locs_in_region r (TSet.singleton ctr) h0 h1 /\
  newr = oldr + 1

val add_epoch :
  #r:rgn -> #n:random -> es:epochs r n -> e:epoch r n ->
  ST unit
    (requires fun h -> let is = MkEpochs?.es es in epochs_inv #r #n (Seq.snoc (Mem.sel h is) e))
    (ensures fun h0 x h1 ->
        let es = MkEpochs?.es es in
        Mem.modifies_regions (Set.singleton r) h0 h1 /\ (
        Mem.loc_region_mref es; // FIXME: WHY WHY WHY does this become suddenly necessary? WHY WHY WHY does the pattern NOT trigger?
        Mem.modifies_locs_in_region r (TSet.singleton es) h0 h1 /\
        Mem.sel h1 es == Seq.snoc (Mem.sel h0 es) e
    ))
let add_epoch #r #n (MkEpochs es _ _) e = Mem.write_at_end es e

let incr_reader #r #n (es:epochs r n) : ST unit
    (requires (incr_pre es MkEpochs?.read))
    (ensures (incr_post es MkEpochs?.read))
= 
  trace "next reader";
  incr_epoch_ctr (MkEpochs?.read es)

let incr_writer #r #n (es:epochs r n) : ST unit
    (requires (incr_pre es MkEpochs?.write))
    (ensures (incr_post es MkEpochs?.write))
= 
  trace "next writer";
  incr_epoch_ctr (MkEpochs?.write es)

let get_epochs #r #n (es:epochs r n) = MkEpochs?.es es

let ctr (#r:_) (#n:_) (e:epochs r n) (rw:rw) = match rw with 
  | Reader -> e.read
  | Writer -> e.write
 
val readerT: #rid:rgn -> #n:random -> e:epochs rid n -> Mem.mem -> GTot (epoch_ctr_inv rid (get_epochs e))
let readerT #rid #n (MkEpochs es r w) (h:Mem.mem) = Mem.sel h r

val writerT: #rid:rgn -> #n:random -> e:epochs rid n -> Mem.mem -> GTot (epoch_ctr_inv rid (get_epochs e))
let writerT #rid #n (MkEpochs es r w) (h:Mem.mem) = Mem.sel h w

unfold let get_ctr_post (#r:rgn) (#n:random) (es:epochs r n) (rw:rw) h0 (i:int) h1 = 
  let epochs = MkEpochs?.es es in
  h0 == h1 /\ 
  i = (Mem.sel h1 (ctr es rw)) /\ 
  -1 <= i /\ 
  Mem.int_at_most i epochs h1

let get_ctr (#r:rgn) (#n:random) (es:epochs r n) (rw:rw)
  : ST int (requires (fun h -> True)) (ensures (get_ctr_post es rw))
= 
  let epochs = es.es in
  let n = Mem.read (ctr es rw) in
  Mem.testify (Mem.int_at_most n epochs);
  n      

let get_reader (#r:rgn) (#n:random) (es:epochs r n) = get_ctr es Reader
let get_writer (#r:rgn) (#n:random) (es:epochs r n) = get_ctr es Writer

let epochsT #r #n (es:epochs r n) (h:Mem.mem) = Mem.sel h (MkEpochs?.es es)

let get_current_epoch
  (#r:_)
  (#n:_)
  (e:epochs r n)
  (rw:rw)
  : ST (epoch r n)
       (requires (fun h -> 0 <= Mem.sel h (ctr e rw)))
       (ensures (fun h0 rd h1 -> 
           let j = Mem.sel h1 (ctr e rw) in
           let epochs = Mem.sel h1 e.es in
           h0==h1 /\
           Seq.indexable epochs j /\
           rd == Seq.index epochs j))
= 
  let j = get_ctr e rw in 
  let epochs = Mem.read e.es in
  Seq.index epochs j

// FIXME: WHY does the following not typecheck? Seems independent of Mem, isn't it?

#set-options "--lax"

val recordInstanceToEpoch: 
  #r:rgn -> #n:random -> hs:Negotiation.handshake -> 
  ks:KeySchedule.recordInstance -> Tot (epoch r n)
let recordInstanceToEpoch #hs_rgn #n hs (KeySchedule.StAEInstance #i rd wr) = Epoch hs rd wr
