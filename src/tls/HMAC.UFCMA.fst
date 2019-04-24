(**! Idealizing agile HMAC; independent of TLS, used for TLS 1.3 Finished message payloads and Binders. *)
module HMAC.UFCMA

open FStar.Bytes
open Mem

module MDM = FStar.Monotonic.DependentMap

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

type lbytes32 n = FStar.Bytes.lbytes (UInt32.v n)

let ipkg = Pkg.ipkg

let model = Flags.model
let ideal = Flags.ideal_HMAC // secret idealization flag for the UFCMA assumption

type safe (#ip:ipkg) (i:ip.Pkg.t) = b2t ideal /\ ip.Pkg.honest i

noextract
private let is_safe (#ip:ipkg) (i:ip.Pkg.t{ip.Pkg.registered i}): ST bool 
  (requires fun h0 -> True)
  (ensures fun h0 b h1 -> modifies_none h0 h1 /\ (b <==> safe i))
  =
  let b = ip.Pkg.get_honesty i in
  ideal && b

type ha = Hashing.alg

// initial parameters
noeq type info = | Info: 
  parent: rgn {~ (is_tls_rgn parent)} -> 
  alg: HMAC.ha -> 
  good: (Hashing.macable alg -> bool) ->  //TODO: should be Type0 instead of bool, and erased, but hard to propagate
  info

//18-02-25 should we index by i instead?
type text (u:info) = Hashing.macable u.alg
type tag (u:info) = lbytes32 (Hashing.tagLen u.alg)

let keylen (u:info): Pkg.keylen = Hashing.tagLen u.alg
type keyrepr (u:info) = Hashing.hkey u.alg

let goodish (#ip:ipkg) (i:ip.Pkg.t) (u:info) (msg:text u) =
  _: unit{~(safe i) \/ u.good msg}

[@unifier_hint_injective]
private type log_t (#ip:ipkg) (i:ip.Pkg.t) (u:info) (r:rgn) =
  MDM.t r (tag u * text u) (fun (t,v) -> goodish i u v) (fun _ -> True) // could constrain size

// runtime (concrete) type of MAC instances
noeq (* abstract *) type concrete_key =
  | MAC: u:info -> k:keyrepr u -> concrete_key

// The model type of instances - either ideal, or real
// The real and concrete version are related by the functional correctness of HMAC
noeq (* abstract *) type ir_key (ip:ipkg) (i:ip.Pkg.t) =
  | IdealKey:
    ck: concrete_key ->
    region: Mem.subrgn ck.u.parent {~(is_tls_rgn region)} ->  // intuitively, the writer's region
    log: log_t i ck.u region ->
    ir_key ip i
  | RealKey: ck:concrete_key -> ir_key ip i

type key (ip:ipkg) (i:ip.Pkg.t{ip.Pkg.registered i}) =
  (if model then
    k:ir_key ip i{IdealKey? k <==> safe i}
  else concrete_key)

// 18-02-25 we probably miss indexing by ha_of_i and good_of_i...
let usage (#ip:ipkg) (#i:ip.Pkg.t{ip.Pkg.registered i}) (k:key ip i): GTot info =
  if model then
    let k: ir_key ip i = k in
    match k with
    | IdealKey ck _ _ -> ck.u
    | RealKey ck      -> ck.u
  else k.u

let keyval (#ip:ipkg) (#i:ip.Pkg.t{ip.Pkg.registered i}) (k:key ip i): GTot (keyrepr (usage k)) =
  if model then
    let k: ir_key ip i = k in
    match k with
    | IdealKey ck _ _ -> ck.k
    | RealKey ck -> ck.k
  else k.k

let region (#ip:ipkg) (#i:ip.Pkg.t{ip.Pkg.registered i}) (k:key ip i): 
  Ghost (subrgn (usage k).parent)
  (requires safe i) 
  (ensures fun _ -> True)
  = let IdealKey _ r _ = k <: ir_key ip i in r

let shared_footprint: rset = rset_empty ()

let footprint (#ip:ipkg) (#i:ip.Pkg.t {ip.Pkg.registered i}) (k:key ip i): 
  GTot (s:rset{s `Set.disjoint` shared_footprint})
  =
  assume false; //TODO downwards closed set
  if model then
    let k: ir_key ip i = k in
    match k with
      | IdealKey _ r _ -> Set.singleton r
    | RealKey _ -> rset_empty ()
  else rset_empty ()

noextract
private let get_key (#ip:ipkg) (#i:ip.Pkg.t{ip.Pkg.registered i}) (k:key ip i)
  : concrete_key
  =
  if model then
    let k: ir_key ip i = k in
    match k with
    | IdealKey rk _ _ -> rk
    | RealKey rk -> rk
  else k

noextract
val create:
  ip:ipkg -> ha_of_i: (ip.Pkg.t -> ha) -> good_of_i: (i:ip.Pkg.t -> Hashing.macable (ha_of_i i) -> bool) ->
  i:ip.Pkg.t {ip.Pkg.registered i} ->
  u:info {u.alg = ha_of_i i /\ u.good == good_of_i i} -> ST (k:key ip i)
  (requires fun _ -> model)
  (ensures fun h0 k h1 ->
    modifies_none h0 h1 /\
    usage k == u /\
    Pkg.fresh_regions (footprint k) h0 h1)

#reset-options "--z3rlimit 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

noextract
let create ip _ _ i u =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert_norm(Spec.HMAC.keysized u.alg (EverCrypt.Hash.tagLength u.alg));
  let kv: keyrepr u = Random.sample32 (Hashing.tagLen u.alg) in
  let ck = MAC u kv in
  let k : ir_key ip i =
    if is_safe i then
      let region: Mem.subrgn u.parent = new_region u.parent in
      assert(~(is_tls_rgn u.parent));
      let log: log_t #ip i u region = MDM.alloc #_ #_ #_ #_ () in
      IdealKey ck region log
    else
      RealKey ck in
  k <: key ip i

noextract
let coerceT (ip: ipkg) (ha_of_i: ip.Pkg.t -> ha) (good_of_i: (i:ip.Pkg.t -> Hashing.macable (ha_of_i i) -> bool))
  (i: ip.Pkg.t {ip.Pkg.registered i /\ ~(safe i)})
  (u: info {u.alg = ha_of_i i /\ u.good == good_of_i i})
  (kv: lbytes32 (keylen u)) : GTot (key ip i)
  =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert_norm(Spec.HMAC.keysized u.alg (EverCrypt.Hash.tagLength u.alg));
  let ck = MAC u kv in
  if model then
    let k: ir_key ip i = RealKey ck in k
  else ck

(* 18-02-25 not sure what's wrong with this variant: 
val coerceT':
  ip:ipkg -> ha_of_i: (ip.Pkg.t -> ha) -> good_of_i: (i:ip.Pkg.t -> Hashing.macable (ha_of_i i) -> bool) ->
  i:ip.Pkg.t {ip.Pkg.registered i} ->
  u:info {u.alg = ha_of_i i /\ u.good == good_of_i i} ->
  kv: lbytes32 (keylen u) -> GTot (key ip i)
let coerceT' ip _ _ i u kv =  
  let ck = MAC u kv in
  if model then
    let k: ir_key ip i = RealKey ck in k
  else ck
*)

val coerce:
  ip: ipkg -> ha_of_i: (ip.Pkg.t -> ha) -> good_of_i: (i:ip.Pkg.t -> Hashing.macable (ha_of_i i) -> bool) ->
  i: ip.Pkg.t {ip.Pkg.registered i /\ ~(safe i)} ->
  u: info {u.alg = ha_of_i i /\ u.good == good_of_i i} ->
  kv: lbytes32 (keylen u) -> ST (k:key ip i)
  (requires fun _ -> True)
  (ensures fun h0 k h1 ->
    modifies_none h0 h1 /\
    k == coerceT ip ha_of_i good_of_i i u kv /\
    usage k == u /\
    Pkg.fresh_regions (footprint k) h0 h1)
let coerce ip _ _ i u kv =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert_norm(Spec.HMAC.keysized u.alg (EverCrypt.Hash.tagLength u.alg));
  let ck = MAC u kv in
  if model then
    let k: ir_key ip i = RealKey ck in k
  else ck

// not quite doable without reification?
// assert_norm(forall ip i u. (create #ip i u == coerce #ip i u (CoreCrypto.random (UInt32.v (keylen u)))))

val mac:
  ip: ipkg -> ha_of_i: (ip.Pkg.t -> ha) -> good_of_i: (i:ip.Pkg.t -> Hashing.macable (ha_of_i i) -> bool) ->
  #i:ip.Pkg.t{ip.Pkg.registered i} -> 
  k: key ip i ->
  p: Hashing.macable (ha_of_i i) { 
    let u = usage k in 
    u.alg = ha_of_i i /\ u.good == good_of_i i /\
    (u.good p \/ ~(safe i)) } ->
  ST (tag (usage k))
  (requires fun _ -> True)
  (ensures fun h0 t h1 -> modifies (footprint k) h0 h1)
  // we may be more precise to prove ideal functional correctness,
  // e,g,  /\ sel h1 k.log = snoc (sel h0 k.log) (Entry t p)
let mac ip ha_of_i good_of_i #i k p =
  admit() //18-02-25 TODO extra indexing?
  // let MAC u kv = get_key k in
  // let t = HMAC.hmac u.alg kv p in
  // if is_safe i then
  //   (let IdealKey _ _ log = k <: ir_key ip i in
  //   if None? (MDM.lookup log (t, p)) then MDM.extend log (t,p) ());
  // t

noextract
val verify:
  ip: ipkg -> ha_of_i: (ip.Pkg.t -> ha) -> good_of_i: (i:ip.Pkg.t -> Hashing.macable (ha_of_i i) -> bool) ->
  #i:ip.Pkg.t{ip.Pkg.registered i} -> 
  k: key ip i ->
  p: Hashing.macable (ha_of_i i) ->
  tag (usage k) -> 
  ST bool
  (requires fun _ -> let u = usage k in u.alg = ha_of_i i /\ u.good == good_of_i i)
  (ensures fun h0 b h1 -> 
    modifies_none h0 h1 /\
    ((b /\ safe i) ==> (usage k).good p))
 
#set-options "--initial_ifuel 1 --max_ifuel 1 --z3rlimit 20"
let verify ip ha_of_i good_of_i #i k p t =
  let MAC u kv = get_key k in
  let verified = HMAC.hmacVerify u.alg kv p t in
  if is_safe i then
    // We use the log to correct any verification errors
    let IdealKey _ _ log = k <: ir_key ip i in
    let tp : tag u * text u = (t,p) in
    let valid = Some? (MDM.lookup log tp) in
    verified && valid
  else
    verified

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

/// For TLS, we'll use something of the form
///
/// let good text =
///   exists digest.
///     hashed ha digest /\
///     text = hash ha digest /\
///     witnessed (fun h -> "this is the writer's state ...")
///
/// - how to deal with agility here?
/// - which level of abstraction?

type info1 
  (ip: ipkg) (ha_of_i: ip.Pkg.t -> ha)
  (good_of_i: (i:ip.Pkg.t -> Hashing.macable (ha_of_i i) -> bool)) 
  (i: ip.Pkg.t)
  =
  a:info{a.alg = ha_of_i i /\ a.good == good_of_i i}

noextract
unfold let localpkg 
  (ip: ipkg) (ha_of_i: ip.Pkg.t -> ha) 
  (good_of_i: (i:ip.Pkg.t -> Hashing.macable (ha_of_i i) -> bool)): 
  Pure (Pkg.local_pkg ip)
  (requires True) 
  (ensures fun p -> p.Pkg.key == key ip /\ p.Pkg.info == info1 ip ha_of_i good_of_i)
  =
  Pkg.LocalPkg
    (key ip)
    (info1 ip ha_of_i good_of_i)
    (fun #_ u -> keylen u )
    (b2t ideal)
    shared_footprint
    footprint // local footprint
    (fun #_ k h -> True) // local invariant
    (fun r i h0 k h1 -> ()) // Local invariant framing
    (fun #i u k h1 -> usage k == u) // create/coerce postcondition
    (fun #i u k h1 r h2 -> ())
    (create ip ha_of_i good_of_i)
    (coerceT ip ha_of_i good_of_i)
    (coerce ip ha_of_i good_of_i)

//TODO (later) support dynamic key compromise

// 18-01-07 only for debugging; how to reliably disable this function otherwise?
noextract 
let string_of_key (#ip:ipkg) (#i:ip.Pkg.t{ip.Pkg.registered i}) (k:key ip i): string = 
  let MAC u kv = get_key k in
//18-08-31 TODO string vs string
//"HMAC-"^Hashing.Spec.string_of_alg u.alg^" key="^print_bytes kv
"HMAC key="^print_bytes kv


(**! Unit test for the packaging of UFCMA *)

val coerce_eq2: a: (nat -> Type0) -> b: (nat -> Type0) -> v:a 0 -> Pure (b 0)
  (requires a == b) (ensures fun _ -> True)
let coerce_eq2 _ _ v = v // this works; many similar variants did not.

private type id = nat
private let ip : ipkg = Pkg.Idx id (fun _ -> True) (fun _ -> True) (fun _ -> true)

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 10"

noextract
private let test (a: HMAC.ha) (r: rgn{~(is_tls_rgn r)}) (v': Hashing.macable a) (t': Hashing.Spec.tag a)
  : ST bool
  (requires fun h0 -> model)
  (ensures fun h0 _ h1 -> True)
  =
  // testing usability of local packages
  let ha_of_i (i:ip.Pkg.t) = a in
  let good_of_i (i:ip.Pkg.t) (v:Hashing.macable  a) = length v = 0 in // a property worth MACing!

  let p = localpkg ip ha_of_i good_of_i in
  let table = mem_alloc (key ip) in

  let q = Pkg.memoization p table in

  assert(Pkg.Pkg?.key q == key ip);
  assert(Pkg.Pkg?.info q == info1 ip ha_of_i good_of_i);

  [@inline_let]
  let u1 : info1 ip ha_of_i good_of_i 0 = Info r a (good_of_i 0) in
  [@inline_let]
  let u = coerce_eq2 (info1 ip ha_of_i good_of_i) (Pkg.Pkg?.info q) u1 in

  let h0 = Mem.get() in
  // assert(
  //   let open Pkg in
  //   let log : i_mem_table p.key = itable q.define_table in
  //   let v = HS.sel h0 log in
  //   lemma_mm_forall_init v p.local_invariant h0;
  //   mm_forall v p.local_invariant h0);
  // assert_norm(q.Pkg.package_invariant h0);
  //if model then
  //  else True in

  //TODO call memoization_ST instead of memoization? We miss this postcondition.
  assume(q.Pkg.package_invariant h0);

  //TODO superficial but hard to prove...
  // assume(Monotonic.RRef.m_sel h0 (Pkg.itable table) == MDM.empty_map ip.Pkg.t (key ip));
  // assert(MDM.fresh (Pkg.itable table) 0 h0);
  // assert(q.Pkg.define_table == table);
  assert(mem_fresh q.Pkg.define_table 0 h0);

  //17-11-23  causing mysterious squash error
  // assert_by_tactic(u:info{u.alg = ha_of_i 0 /\ u.good == good_of_i 0} == Pkg.Pkg?.info q 0) FStar.Tactics.(norm "foo");
  // let u = u <: Pkg.Pkg?.info q 0 in
  let k: key ip 0 = Pkg.Pkg?.create q 0 u in

  // testing usability of logical payloads
  let v = empty_bytes in
  assert(good_of_i 0 v);
  let t = mac ip ha_of_i good_of_i #0 k v in

  let b0 = verify ip ha_of_i good_of_i #0 k v' t in
  assert(b0 /\ b2t ideal ==> length v' = 0);

  let b1 = verify ip ha_of_i good_of_i #0 k v' t' in
  assert(b1 /\ b2t ideal ==> length v' = 0);
  // assert false; // sanity check

  // expected: 
  let _ = IO.debug_print_string (string_of_key k^" tag="^print_bytes t^"\n") in
  b0 && not b1 

noextract
let unit_test(): St bool = 
  let _ = IO.debug_print_string "HMAC.UFCMA\n" in 
  assume(model); //18-01-07 avoid?
  let here = new_colored_region root hs_color in
  let b0 = 
    let a = Hashing.SHA1 in 
    assert_norm(Hashing.Spec.blockLength a <= Hashing.Spec.maxLength a);
    test a here empty_bytes (Bytes.create (Hashing.tagLen a) 42z) in
  let b1 = 
    let a = Hashing.SHA1 in 
    test a here empty_bytes (Bytes.create (Hashing.tagLen a) 42z) in
  let b2 = 
    let a = Hashing.SHA1 in 
    test a here empty_bytes (Bytes.create (Hashing.tagLen a) 42z) in
  b0 && b1 && b2
  // nothing bigger? 

(* --------- older, TLS-specific implementation. 18-01-07 to be deleted

//17-10-21 ADAPT: should depend only on agility parameter.

type id =
| HMAC_Finished of TLSInfo.finishedId
| HMAC_Binder of TLSInfo.binderId

let alg (i:id) = match i with
| HMAC_Finished i -> TLSInfo.finishedId_hash i
| HMAC_Binder i -> TLSInfo.binderId_hash i

//assume
val authId: id -> Tot bool
let authId id = false // TODO: move to Flags

type tag (i:id) = tag (alg i)



// We keep the tag in case we later want to enforce tag authentication
abstract type entry (i:id) (good: bytes -> Type) =
  | Entry: t:tag i -> p:bytes { authId i ==> good p } -> entry i good


val region: #i:id -> #good:(bytes -> Type) -> k:key i good -> GTot rid
val keyval: #i:id -> #good:(bytes -> Type) -> k:key i good -> GTot (keyrepr i)

let region #i #good (k:key i good) = k.region
let keyval #i #good (k:key i good) = k.kv

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 30"
// todo: mark it as private
private let gen0 i good (parent:rgn) kv : ST (key i good)
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->
    fresh_subregion (region #i #good k) parent h0 h1 /\
    modifies Set.empty h0 h1
  )) =
  let region = new_region parent in
  let log = ralloc region Seq.empty in
  Key #i #good #region kv log

val gen: i:id -> good: (bytes -> Type) -> parent: rgn -> ST(key i good)
  (requires (fun _ -> True))
  (ensures (fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion (region #i #good k) parent h0 h1 ))
let gen i good parent =
  gen0 i good parent (Random.sample (keysize i))

val coerce: i:id -> good: (bytes -> Type) -> parent: rgn -> kv:keyrepr i -> ST(key i good)
  (requires (fun _ -> ~(authId i)))
  (ensures (fun h0 k h1 ->
    modifies Set.empty h0 h1 /\
    fresh_subregion (region #i #good k) parent h0 h1 ))
let coerce i good parent kv =
  gen0 i good parent kv

val leak: #i:id -> #good: (bytes -> Type) -> k:key i good {~(authId i)} -> Tot (kv:keyrepr i { kv = keyval k })
let leak   #i #good k = k.kv

val mac: #i:id -> #good:(bytes -> Type) -> k:key i good -> p:bytes { authId i ==> good p } -> ST(tag i)
  (requires (fun _ -> True))
  (ensures (fun h0 t h1 -> modifies (Set.singleton (region k)) h0 h1
  //  /\
  //  sel h1 k.log = snoc (sel h0 k.log) (Entry t p)
  ))


// We log every authenticated texts, with their index and resulting tag
let mac #i #good k p =
  let p : p:bytes { authId i ==> good p } = p in
  let t = HMAC.hmac (alg i) k.kv p in
  let e : entry i good = Entry t p in
  recall k.log;
  k.log := snoc !k.log e;
  t

abstract val matches: #i:id -> #good:(bytes -> Type) -> p:text -> entry i good -> Tot bool
let matches #i #good p (Entry _ p') = p = p'

val verify: #i:id -> #good:(bytes -> Type) -> k:key i good -> p:bytes -> t:tag i -> ST bool
  (requires (fun _ -> True))
  (ensures (fun h0 b h1 -> modifies Set.empty h0 h1 /\ (b /\ authId i ==> good p)))

// We use the log to correct any verification errors
let verify #i #good k p t =
  let x = HMAC.hmacVerify (alg i) k.kv p t in
  let log = !k.log in
  x &&
  ( not(authId i) || Some? (seq_find (matches p) log))
*)
