module LowParse.SLow.Tac.Enum
include LowParse.SLow.Enum

module T = FStar.Tactics

private val split_lem : (#a:Type) -> (#b:Type) ->
                        squash a -> squash b -> Lemma (a /\ b)
let split_lem #a #b sa sb = ()

noextract
let rec resplit () : T.Tac unit =
  let g = T.cur_goal () in
  match T.term_as_formula g with
  | T.And _ _ -> T.apply_lemma (`split_lem); T.iseq [ resplit; resplit ]
  | _ -> T.first [
    (fun () -> T.trefl ());
    (fun () -> T.trivial ());
  ]

noextract
let conclude ()
: T.Tac unit
= T.norm [delta; iota; primops];
  T.dump "after norm";
  resplit ();
  T.dump "done?"

noextract
let rec maybe_enum_key_of_repr_tac
  (#key #repr: eqtype)
  (e: list (key * repr))
  ()
: T.Tac unit
  (decreases e)
= match e with
  | [] -> T.fail "e must be cons"
  | [_] ->
    let fu = quote (maybe_enum_key_of_repr'_t_cons_nil' #key #repr) in
    T.apply fu;
    T.iseq [
      (fun () -> T.exact_guard (quote ()); conclude ());
    ]
  |  _ :: e_ ->
    let fu = quote (maybe_enum_key_of_repr'_t_cons' #key #repr) in
    T.apply fu;
    T.iseq [
      (fun () -> maybe_enum_key_of_repr_tac e_ ());
      (fun () -> T.exact_guard (quote ()); conclude ());
    ]

noextract
let rec enum_repr_of_key_tac
  (#key #repr: eqtype)
  (e: enum key repr)
  (u: unit  { Cons? e } )
  ()
: T.Tac unit
= match e with
  | [_] ->
    let fu = quote (enum_repr_of_key_cons_nil' #key #repr) in
    T.apply fu;
    T.iseq [
      (fun () -> T.exact_guard (quote ()); conclude ());
    ]
  | _ :: e' ->
    let fu = quote (enum_repr_of_key_cons' #key #repr) in
    T.apply fu;
    T.iseq [
      (fun () -> enum_repr_of_key_tac e' () ());
      (fun () -> T.exact_guard (quote ()); conclude ());
    ]

noextract
let parse32_maybe_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr { Cons? e } )
  (#k' : parser_kind)
  (p' : parser k' (maybe_enum_key e))
  (u: unit {
    k' == k /\
    p' == parse_maybe_enum_key p e
  })
  ()
: T.Tac unit
= let fu = quote (parse32_maybe_enum_key_gen #k #key #repr #p p32 e #k' p') in
  T.apply fu;
  T.iseq [
    (fun () -> T.exact_guard (quote u); conclude ());
    (fun () -> maybe_enum_key_of_repr_tac #key #repr e ());
  ]

noextract
let parse32_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr { Cons? e } )
  (#k' : parser_kind)
  (p' : parser k' (enum_key e))
  (u: unit {
    k' == parse_filter_kind k /\
    p' == parse_enum_key p e
  })
  ()
: T.Tac unit
= let fu = quote (parse32_enum_key_gen #k #key #repr p e #k' p') in
  T.apply fu;
  T.iseq [
    (fun () -> T.exact_guard (quote u); conclude ());
    (fun () -> parse32_maybe_enum_key_tac p32 e (parse_maybe_enum_key p e) () ())
  ]

noextract
let serialize32_enum_key_gen_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr { Cons? e } )
  (#k' : parser_kind)
  (#p' : parser k' (enum_key e))
  (s' : serializer p')
  (u: unit {
    k' == parse_filter_kind k /\
    p' == parse_enum_key p e /\
    s' == serialize_enum_key p s e
  })
  ()
: T.Tac unit
= let fu = quote (serialize32_enum_key_gen #k #key #repr #p #s s32 e #k' #p' s') in
  T.apply fu;
  T.iseq [
    (fun () -> T.exact_guard (quote u); conclude ());
    (fun () -> enum_repr_of_key_tac e () ());
  ]

noextract
let serialize32_maybe_enum_key_tac
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr { Cons? e } )
  (#k' : parser_kind)
  (#p' : parser k' (maybe_enum_key e))
  (s' : serializer p')
  (u: unit {
    k == k' /\
    p' == parse_maybe_enum_key p e /\
    s' == serialize_maybe_enum_key p s e
  })
  ()
: T.Tac unit
= let fu = quote (serialize32_maybe_enum_key_gen #k #key #repr #p #s s32 e #k' #p' s') in
  T.apply fu;
  T.iseq [
    (fun () -> T.exact_guard (quote u); conclude ());
    (fun () -> enum_repr_of_key_tac e () ());
  ]
