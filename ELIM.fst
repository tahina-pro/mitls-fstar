module ELIM

open LowParse.TacLib

(* Non-recursive eliminator for non-parametric inductive types *)

let rec close_elim_arg (binders: list binder) (outtype: typ) : Tac typ =
  match binders with
  | [] -> outtype
  | b :: binders' -> close_elim_arg binders' (pack (Tv_Arrow b (pack_comp (C_Total outtype None))))

let rec make_elim_arg_type_aux (f: term) (intype: typ) (binders: list binder) (outtype: typ) : Tac term =
  match inspect intype with
  | Tv_Arrow binder intype' ->
    begin match inspect_comp intype' with
    | C_Total intype' _ ->
      let binder' = fresh_binder (type_of_binder binder) in
      make_elim_arg_type_aux f intype' (binder' :: binders) (mk_app outtype [binder_to_term binder', Q_Explicit])
    | _ -> fail "Non-total constructor type"
    end
  | _ -> close_elim_arg binders (mk_app f [outtype, Q_Explicit])

let make_elim_arg_type (f: term) (c: name) : Tac term =
  match lookup_typ (cur_env ()) c with
  | Some sg ->
    begin match inspect_sigelt sg with
    | Sg_Constructor _ intype -> make_elim_arg_type_aux f intype [] (pack (Tv_FVar (pack_fv c)))
    | _ -> fail "Not a constructor"
    end
  | _ -> fail "Definition not found"

let rec make_elim_type_aux (f: term) (l: list name) (accu: term) : Tac term =
  match l with
  | [] -> accu
  | c :: l' ->
    let b = fresh_binder (make_elim_arg_type f c) in
    make_elim_type_aux f l' (pack (Tv_Arrow b (pack_comp (C_Total accu None))))

let make_elim_type (t: term) (f: term) : Tac term =
  let env = cur_env () in
  match inspect t with
  | Tv_FVar v ->
    begin match lookup_typ env (inspect_fv v) with
    | Some sg ->
      begin match inspect_sigelt sg with
      | Sg_Inductive _ _ _ _ cts ->
        let x = fresh_binder t in
        let ret = pack (Tv_Arrow x (pack_comp (C_Total (mk_app f [binder_to_term x, Q_Explicit]) None))) in
        let res = make_elim_type_aux f (List.Tot.rev cts) ret in
        print (term_to_string res);
        res
      | _ -> fail "make_elim_type: Not an inductive type"
      end
    | _ -> fail "make_elim_type: Definition not found"
    end
  | _ -> fail "make_elim_type: Not an inductive type name"

let rec count_constr_args (t: typ) (accu: nat) : Tac nat =
  match inspect t with
  | Tv_Arrow _ t' -> 
    begin match inspect_comp t' with
    | C_Total t' _ -> count_constr_args t' (1 + accu)
    | _ -> fail "Not a total comp"
    end
  | _ -> accu

let rec intro_constr_binders (l: list name) (accu: list (nat * binder)) : Tac (list (nat * binder)) =
  match l with
  | [] -> List.Tot.rev accu
  | c :: q ->
    dump "intro_constr_binders";
    let b = intro () in
    begin match lookup_typ (cur_env ()) c with
    | Some sg ->
      begin match inspect_sigelt sg with
      | Sg_Constructor _ ty ->
        intro_constr_binders q ((count_constr_args ty 0, b) :: accu)
      | _ -> fail "Not a constructor"
      end
    | _ -> fail "Definition not found"
    end

let rec repeat_n (n: nat) (t: unit -> Tac unit) : Tac unit =
  if n = 0 then () else (t (); repeat_n (n - 1) t)

let rec apply_constr_binders (l: list (nat * binder)) : Tac unit =
  match l with
  | [] -> qed ()
  | (n, b) :: q ->
    iseq [fun () ->
      repeat_n n (fun () -> dump "intro"; let _ = intro () in ());
      let breq = intro () in
      rewrite breq;
      apply (binder_to_term b);
      qed ()
    ];
    apply_constr_binders q

let make_elim (t: term) (f: term) : Tac unit =
  match inspect t with
  | Tv_FVar v ->
    let env = cur_env () in
    begin match lookup_typ env (inspect_fv v) with
    | Some sg ->
      begin match inspect_sigelt sg with
      | Sg_Inductive _ _ _ _ cts -> 
        let binders = intro_constr_binders cts [] in
        let x = intro () in
        destruct (binder_to_term x);
        apply_constr_binders binders
      | _ -> fail "Not an inductive type"
      end
    | _ -> fail "Definition not found"
    end
  | _ -> fail "Not a fvar"

type t =
| A of int
| B

inline_for_extraction
let t_elim (f: t -> Type u#0) : Tot ((_ by (apply (make_elim_type (`t) (quote f)))) <: Type u#0) =
  _ by (make_elim (`t) (quote f))
