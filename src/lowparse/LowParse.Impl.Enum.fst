module LowParse.Impl.Enum
include LowParse.Impl.Combinators
include LowParse.Spec.Enum

module L = FStar.List.Tot
module T = FStar.Tactics

let mk_if (test e_true e_false: T.term) : Tot T.term =
  let br_true = (T.Pat_Constant T.C_True, e_true) in
  let br_false = (T.Pat_Constant T.C_False, e_false) in
  let m = T.pack (T.Tv_Match test [ br_true; br_false ] ) in
  m

let discr_prop
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: enum_key e)
  (x: repr)
: Lemma
  (x == enum_repr_of_key e k <==> (L.mem x (L.map snd e) /\ enum_key_of_repr e x == k))
= enum_key_of_repr_of_key e k

inline_for_extraction
let discr
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: enum_key e)
: Tot (
    (x: repr) ->
    Tot (y: bool { y == true <==> (L.mem x (L.map snd e) /\ enum_key_of_repr e x == k) } )
  )
= let r = enum_repr_of_key e k in
  fun x ->
    discr_prop e k x;
    x = r

val enum_univ_destr_spec_gen
  (#key #repr: eqtype)
  (e: enum key repr)
  (t: (maybe_enum_key e -> Tot Type0))
  (f: ((k: maybe_enum_key e) -> Tot (t k)))
  (r: repr)
: Tot (t (maybe_enum_key_of_repr e r))

let enum_univ_destr_spec_gen #key #repr e t f r =
  f (maybe_enum_key_of_repr e r)

val enum_univ_destr_spec
  (#key #repr: eqtype)
  (e: enum key repr)
  (t: (enum_key e -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
  (r: enum_repr e)
: Tot (t (enum_key_of_repr e r))

let enum_univ_destr_spec #key #repr e t f r =
  f (enum_key_of_repr e r)

inline_for_extraction
let id
  (t: Type0)
  (x: t)
: Tot t
= x

inline_for_extraction
let enum_key_cons_coerce
  (#key #repr: eqtype)
  (e: enum key repr)
  (k' : key)
  (r' : repr)
  (e' : enum key repr)
  (k: enum_key e')
: Pure (enum_key e)
  (requires (e == (k', r') :: e'))
  (ensures (fun _ -> True))
= let k_ : key = k in
  k_ <: enum_key e

inline_for_extraction
let enum_repr_cons_coerce_recip
  (#key #repr: eqtype)
  (e: enum key repr)
  (k' : key)
  (r' : repr)
  (e' : enum key repr)
  (k: enum_repr e)
: Pure (enum_repr e')
  (requires (e == (k', r') :: e' /\ r' <> k))
  (ensures (fun _ -> True))
= let k_ : repr = k in
  k_ <: enum_repr e'

let mk_coercion
  (from_value: T.term)
  (to_typ: T.term)
: Tot (T.tactic T.term)
= T.bind (T.quote id) (fun id' ->
    let res = T.mk_app id' [to_typ, T.Q_Explicit; from_value, T.Q_Explicit] in
    T.return res
  )

let rec gen_enum_univ_destr_body
  (#key #repr: eqtype)
  (e: enum key repr)
  (t: ((k: enum_key e) -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
  (r: T.term)
: Pure (T.tactic T.term)
  (requires (Cons? e))
  (ensures (fun _ -> True))
  (decreases e)
= match e with
  | ((k', r') :: e') ->
    let e' : enum key repr = e' in
    let k' : enum_key e = k' in
    let fk' = f k' in
    T.bind (T.quote fk') (fun rt ->
      match e' with
      | [] -> T.return rt
      | _ ->
      T.bind (T.quote t) (fun t' ->
      T.bind (T.quote (enum_key_of_repr #key #repr e)) (fun myu ->
      let m_type = T.mk_app t' [T.mk_app myu [r, T.Q_Explicit], T.Q_Explicit] in
      T.bind (mk_coercion rt m_type) (fun rt_constr ->
      T.bind (T.quote (op_Equality #repr r')) (fun eq_repr_k' ->
        let test = T.mk_app eq_repr_k' [
          (r, T.Q_Explicit);
        ]
        in
	T.bind (T.quote (enum_repr_cons_coerce_recip #key #repr e k' r' e')) (fun q_r_false ->
        T.bind (
          gen_enum_univ_destr_body
            e'
            (fun (k: enum_key e') ->
              t (enum_key_cons_coerce #key #repr e k' r' e' k)
            )
            (fun (k: enum_key e') ->
              f (enum_key_cons_coerce #key #repr e k' r' e' k)
            )
            (T.mk_app q_r_false [r, T.Q_Explicit])
        ) (fun t' ->
          T.bind (mk_coercion t' m_type) (fun t'_constr ->
          let m = mk_if test rt_constr t'_constr in
          T.return m
  ))))))))

let rec gen_enum_univ_destr
  (#key #repr: eqtype)
  (e: enum key repr)
  (t: (enum_key e -> Tot Type0))
  (f: ((k: enum_key e) -> Tot (t k)))
: Tot (T.tactic unit)
= let open T in
  match e with
  | _ :: _ ->
    tk <-- quote (enum_repr #key #repr e) ;
    let x = fresh_binder tk in
    let r = T.pack (T.Tv_Var x) in
    body <-- gen_enum_univ_destr_body #key #repr e t f r ;
    let res = T.pack (T.Tv_Abs x body) in
    _ <-- print (term_to_string res) ;
    t_exact true false (return res)
  | _ ->
    let g (r: enum_repr #key #repr e) : Tot (t (enum_key_of_repr #key #repr e r)) =
      false_elim ()
    in
    exact_guard (quote g)

let maybe_enum_key_or_excluded
  (#key #repr: eqtype)
  (e: enum key repr)
  (excluded: list repr)
: Tot Type0
= (k: maybe_enum_key e {
    match k with
    | Known _ -> True
    | Unknown r -> L.mem r excluded == false
  })

#set-options "--use_two_phase_tc false"

inline_for_extraction
let maybe_enum_key_or_excluded_cons_coerce
  (#key #repr: eqtype)
  (e: enum key repr)
  (excluded: list repr)
  (k' : key)
  (r' : repr)
  (e' : enum key repr)
  (k: maybe_enum_key_or_excluded e' (r' :: excluded))
: Pure (maybe_enum_key_or_excluded e excluded)
  (requires (e == (k', r') :: e'))
  (ensures (fun _ -> True))
= match k with
  | Known r -> Known ((r <: key) <: enum_key e)
  | Unknown r -> Unknown ((r <: repr) <: unknown_enum_repr e)

#reset-options

let maybe_unknown_key_or_excluded_of_repr
  (#key #repr: eqtype)
  (e: enum key repr)
  (excluded: list repr)
  (r: repr { L.mem r excluded == false } )
: Tot (maybe_enum_key_or_excluded e excluded)
= maybe_enum_key_of_repr e r

let rec gen_enum_univ_destr_gen_body
  (#key #repr: eqtype)
  (e: enum key repr)
  (excluded: list repr)
  (t: ((k: maybe_enum_key_or_excluded e excluded) -> Tot Type0))
  (f: ((k: maybe_enum_key_or_excluded e excluded) -> Tot (t k)))
  (combine_if: ((k: maybe_enum_key_or_excluded e excluded) -> Tot (if_combinator (t k))))
  (r: T.term)
: Tot (T.tactic T.term)
  (decreases e)
= match e with
  | [] ->
    let g (r' : unknown_enum_repr e {L.mem r' excluded == false}) : Tot (t (Unknown r')) =
      f (Unknown r')
    in
    T.bind (T.quote g) (fun g' ->
      let res = T.mk_app g' [
        (r, T.Q_Explicit)
      ]
      in
      T.return res
    )
  | ((k', r') :: e') ->
    let k' : enum_key e = k' in
    let fk' = f (Known k') in
    T.bind (T.quote fk') (fun rt ->
      T.bind (T.quote t) (fun t' ->
      T.bind (T.quote (maybe_unknown_key_or_excluded_of_repr #key #repr e excluded)) (fun myu ->
      let m_key = T.mk_app myu [r, T.Q_Explicit] in
      let m_type = T.mk_app t' [m_key, T.Q_Explicit] in
      T.bind (T.quote (op_Equality #repr r')) (fun eq_repr_k' ->
        let test = T.mk_app eq_repr_k' [
          (r, T.Q_Explicit);
        ]
        in
        let excluded' = r' :: excluded in
        T.bind (
          gen_enum_univ_destr_gen_body
            e'
            excluded'
            (fun (k: maybe_enum_key_or_excluded e' excluded') ->
              t (maybe_enum_key_or_excluded_cons_coerce e excluded k' r' e' k)
            )
            (fun (k: maybe_enum_key_or_excluded e' excluded') ->
              f (maybe_enum_key_or_excluded_cons_coerce e excluded k' r' e' k)
            )
            (fun (k: maybe_enum_key_or_excluded e' excluded') ->
              combine_if (maybe_enum_key_or_excluded_cons_coerce e excluded k' r' e' k)
            )
            r
        ) (fun t' ->
          T.bind (T.quote cond_true) (fun cond_true_q ->
          T.bind (T.quote cond_false) (fun cond_false_q ->
          T.bind (T.quote combine_if) (fun combine_if_q ->
          T.bind (mk_coercion rt m_type) (fun rt_constr ->
          T.bind (mk_coercion t' m_type) (fun t'_constr ->
          let cond_true_type = T.mk_app cond_true_q [test, T.Q_Explicit] in
          let cond_true_var = T.fresh_binder cond_true_type in
          let cond_true_abs = T.pack (T.Tv_Abs cond_true_var rt_constr) in
          let cond_false_type = T.mk_app cond_false_q [test, T.Q_Explicit] in
          let cond_false_var = T.fresh_binder cond_false_type in
          let cond_false_abs = T.pack (T.Tv_Abs cond_false_var t'_constr) in
          let m = T.mk_app combine_if_q [
            m_key, T.Q_Explicit;
            test, T.Q_Explicit;
            cond_true_abs, T.Q_Explicit;
            cond_false_abs, T.Q_Explicit;
          ]
          in
          T.return m
  ))))))))))

let rec gen_enum_univ_destr_gen
  (#key #repr: eqtype)
  (e: enum key repr)
  (t: ((k: maybe_enum_key e) -> Tot Type0))
  (f: ((k: maybe_enum_key e) -> Tot (t k)))
  (combine_if: ((k: maybe_enum_key e) -> Tot (if_combinator (t k))))
: Tot (T.tactic unit)
= let open T in (
    tk <-- quote repr ;
    let x = fresh_binder tk in
    let r = T.pack (T.Tv_Var x) in
    body <-- gen_enum_univ_destr_gen_body #key #repr e [] t f combine_if r ;
    let res = T.pack (T.Tv_Abs x body) in
    _ <-- print (term_to_string res) ;
    t_exact true false (return res)
  )

inline_for_extraction
let is_known
  (#key #repr: eqtype)
  (e: enum key repr)
  (k: maybe_enum_key e)
: Tot bool
= match k with
  | Known _ -> true
  | _ -> false

module S = LowParse.Slice

#set-options "--z3rlimit 32"

inline_for_extraction
let validate_enum_key
  (#key #repr: eqtype)
  (e: enum key repr)
  (univ_destr_gen: (
    (t: ((k: maybe_enum_key e) -> Tot Type0)) ->
    (f: ((k: maybe_enum_key e) -> Tot (t k))) ->
    (combine_if: ((k: maybe_enum_key e) -> Tot (if_combinator (t k)))) ->
    (k: repr) ->
    Tot (t (maybe_enum_key_of_repr e k))
  ))
  (#k: parser_kind)
  (#p: parser k repr)
  (ps: parser_st p)
: Tot (stateful_validator (parse_enum_key p e))
= let f =
    univ_destr_gen
      (fun k -> (b: bool { b == Known? k } ))
      (fun k -> is_known e k)
      (fun k -> default_if _)
  in
  fun (s: S.bslice) ->
    validate_filter_st
      #_
      #repr
      #p
      ps
      (fun r -> Known? (maybe_enum_key_of_repr e r))
      (fun x -> f x)
      s

#reset-options

inline_for_extraction
let validate_total_enum_key
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (univ_destr_gen: (
    (t: ((k: maybe_enum_key e) -> Tot Type0)) ->
    (f: ((k: maybe_enum_key e) -> Tot (t k))) ->
    (combine_if: ((k: maybe_enum_key e) -> Tot (if_combinator (t k)))) ->
    (k: repr) ->
    Tot (t (maybe_enum_key_of_repr e k))
  ))
  (#k: parser_kind)
  (#p: parser k repr)
  (ps: parser_st p)
: Tot (stateful_validator (parse_total_enum_key p e))
= validate_enum_key e univ_destr_gen ps `validate_synth` (synth_total_enum_key e)

inline_for_extraction
let validate_maybe_enum_key
  (#key #repr: eqtype)
  (e: enum key repr)
  (#k: parser_kind)
  (#p: parser k repr)
  (vs: stateful_validator p)
: Tot (stateful_validator (parse_maybe_enum_key p e))
= vs `validate_synth` (maybe_enum_key_of_repr e)

inline_for_extraction
let validate_maybe_total_enum_key
  (#key #repr: eqtype)
  (e: total_enum key repr)
  (#k: parser_kind)
  (#p: parser k repr)
  (vs: stateful_validator p)
: Tot (stateful_validator (parse_maybe_total_enum_key p e))
= vs `validate_synth` (maybe_total_enum_key_of_repr e)
