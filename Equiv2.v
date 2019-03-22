
(** Conversion from Named derivations to Locally Nameless derivations *)

Require Import RelationClasses Arith Omega Defs Proofs Equiv Alpha Alpha2.
Require Nam Mix.
Import ListNotations.
Import Nam Nam.Form.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.



(** Contexts *)

Definition nam2mix_ctx (c:Nam.context) : Mix.context :=
 List.map (nam2mix []) c.

Definition mix2nam_ctx (c:Mix.context) : Nam.context :=
 List.map (mix2nam []) c.

Lemma nam2mix_ctx_eqb (c c' : Nam.context) :
 (nam2mix_ctx c =? nam2mix_ctx c') = (c =? c').
Proof.
 revert c'.
 induction c; destruct c'; cbn; auto.
 rewrite nam2mix_eqb. case eqb; auto.
Qed.

Lemma nam2mix_ctx_fvars (c : Nam.context) :
 Vars.Equal (Mix.fvars (nam2mix_ctx c)) (Ctx.freevars c).
Proof.
 induction c as [|f c IH]; cbn; auto.
 - varsdec.
 - rewrite nam2mix_fvars, IH. simpl. varsdec.
Qed.

(** Sequents *)

Definition nam2mix_seq '(Nam.Seq c f) : Mix.sequent :=
  Mix.Seq (nam2mix_ctx c) (nam2mix [] f).

Definition mix2nam_seq '(Mix.Seq c f) : Nam.sequent :=
  Nam.Seq (mix2nam_ctx c) (mix2nam [] f).

Lemma nam2mix_seq_eqb (s s' : Nam.sequent) :
 (nam2mix_seq s =? nam2mix_seq s') = (s =? s').
Proof.
 destruct s as (c,f), s' as (c',f'); cbn.
 now rewrite nam2mix_ctx_eqb, nam2mix_eqb.
Qed.


(** Rule kinds *)

Definition nam2mix_rule r :=
  match r with
  | Nam.Ax => Mix.Ax
  | Nam.Tr_i => Mix.Tr_i
  | Nam.Fa_e => Mix.Fa_e
  | Nam.Not_i => Mix.Not_i
  | Nam.Not_e => Mix.Not_e
  | Nam.And_i => Mix.And_i
  | Nam.And_e1 => Mix.And_e1
  | Nam.And_e2 => Mix.And_e2
  | Nam.Or_i1 => Mix.Or_i1
  | Nam.Or_i2 => Mix.Or_i2
  | Nam.Or_e => Mix.Or_e
  | Nam.Imp_i => Mix.Imp_i
  | Nam.Imp_e => Mix.Imp_e
  | Nam.All_i v => Mix.All_i v
  | Nam.All_e t => Mix.All_e (nam2mix_term [] t)
  | Nam.Ex_i t => Mix.Ex_i (nam2mix_term [] t)
  | Nam.Ex_e v => Mix.Ex_e v
  | Nam.Absu => Mix.Absu
  end.

Definition mix2nam_rule r :=
  match r with
  | Mix.Ax => Nam.Ax
  | Mix.Tr_i => Nam.Tr_i
  | Mix.Fa_e => Nam.Fa_e
  | Mix.Not_i => Nam.Not_i
  | Mix.Not_e => Nam.Not_e
  | Mix.And_i => Nam.And_i
  | Mix.And_e1 => Nam.And_e1
  | Mix.And_e2 => Nam.And_e2
  | Mix.Or_i1 => Nam.Or_i1
  | Mix.Or_i2 => Nam.Or_i2
  | Mix.Or_e => Nam.Or_e
  | Mix.Imp_i => Nam.Imp_i
  | Mix.Imp_e => Nam.Imp_e
  | Mix.All_i v => Nam.All_i v
  | Mix.All_e t => Nam.All_e (mix2nam_term [] t)
  | Mix.Ex_i t => Nam.Ex_i (mix2nam_term [] t)
  | Mix.Ex_e v => Nam.Ex_e v
  | Mix.Absu => Nam.Absu
  end.

(** Derivations *)

Fixpoint nam2mix_deriv (d:Nam.derivation) :=
  let '(Nam.Rule r s ds) := d in
  Mix.Rule
    (nam2mix_rule r)
    (nam2mix_seq s)
    (List.map nam2mix_deriv ds).

Fixpoint mix2nam_deriv (d:Mix.derivation) :=
  let '(Mix.Rule r s ds) := d in
  Nam.Rule
    (mix2nam_rule r)
    (mix2nam_seq s)
    (List.map mix2nam_deriv ds).

Ltac break :=
 rewrite <- ?andb_lazy_alt;
 match goal with
 | |- _ = match ?f ?x with _ => _ end => destruct x
 | |- _ = match ?x with _ => _ end => destruct x
 | |- match ?f (?g ?x) with _ => _ end = _ => destruct x
 | |- match ?f ?x with _ => _ end = _ => destruct x
 | |- match ?x with _ => _ end = _ => destruct x
 end.

Lemma lazy_andb_false (a:bool) : a &&& false = false.
Proof.
 now destruct a.
Qed.


(*

Lemma nam2mix_term_substs_ext
 (vars:list variable)
 (subvar subvar' : list (variable*variable))
 (sub : Nam.Subst.st) t :
  (forall v, list_assoc_dft v subvar v = list_assoc_dft v subvar' v) ->
  nam2mix_term (List.map (fun v => list_assoc_dft v subvar v) vars)
          (Nam.term_substs (subvar2sub subvar ++ sub) t) =
  nam2mix_term (List.map (fun v => list_assoc_dft v subvar' v) vars)
          (Nam.term_substs (subvar2sub subvar' ++ sub) t).
Proof.
 induction t as [v|f l IH] using Nam.term_ind'; intros E.
 - cbn.


Lemma nam2mix_substs_ext
 (vars:list variable)
 (subvar subvar' : list (variable*variable))
 (sub : Nam.Subst.st) f :
  (forall v, subvar v = subvar') ->
  nam2mix (List.map (fun v => list_assoc_dft v subvar v) vars)
          (Nam.formula_substs (subvar2sub subvar ++ sub) f) =
  nam2mix (List.map (fun v => list_assoc_dft v subvar' v) vars)
          (Nam.formula_substs (subvar2sub subvar' ++ sub) f).
Proof.
 revert vars subvar subvar' sub.
 induction f; intros var subvar subvar' sub.
 - now cbn.
 - now cbn.
 - cbn. f_equal. rewrite !map_map. apply map_ext.


Definition InvSubVar v t f subvar :=
  ~In v (List.map fst subvar) /\ ~In v (List.map snd subvar) /\
   (forall w, In w (List.map snd subvar) ->
              ~Vars.In w (Vars.union (Nam.term_vars t) (Nam.allvars f))).

Lemma nam2mix_substs n (subvar: list (variable*variable)) v t f :
  InvSubVar v t f subvar ->
  n = List.length subvar ->
  let sub := List.map (fun '(v,w) => (v,Nam.Var w)) subvar
  in
  nam2mix (List.map snd subvar) (Nam.formula_substs (sub++[(v,t)]) f) =
  Mix.bsubst n (nam2mix_term [] t)
    (nam2mix ((List.map fst subvar) ++ [v]) f).
Proof.
 revert n subvar.
 induction f; cbn -[fresh_var Vars.union]; trivial.
 - intros.
   f_equal.
   rewrite !map_map.
   apply map_ext_in.
   admit.
 - intros. f_equal; auto.
 - intros. f_equal; auto. admit. admit.
 - intros.
   set (cond := negb _).
   destruct cond eqn:Hcond.
   + cbn. f_equal.
     set (sub := filter _ _) in *.
     specialize (IHf (S n) ((v0,v0)::subvar)).
     cbn in IHf. rewrite <- IHf; auto.
     case (eqbspec v v0).
     * intros <-.
       assert (sub = map (fun '(v, w) => (v, Nam.Var w)) subvar).
       { admit. }

     *

     admit.
   + set (sub := filter _ _) in *.
     set (z := fresh_var _).
     cbn -[z].
     f_equal.
     specialize (IHf (S n) ((v0,z)::subvar)).
     cbn in IHf. rewrite <- IHf; auto.
     admit.

Lemma nam2mix_subst v t f :
  nam2mix [] (Nam.formula_subst v t f) =
  Mix.bsubst 0 (nam2mix_term [] t) (nam2mix [v] f).
Proof.
Admitted. (* preuve ??? *)
*)

Lemma nam2mix_deriv_valid_step logic (d:Nam.derivation) :
  Mix.valid_deriv_step logic (nam2mix_deriv d) =
  Nam.valid_deriv_step logic d.
Proof.
 destruct d as [[ ] s ds]; cbn.
 - repeat (break; cbn; auto).
   unfold nam2mix_ctx.
   induction c as [|A c IH]; cbn; auto.
   rewrite <- nam2mix_eqb.
   case eqbspec; auto.
 - repeat (break; cbn; auto).
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   now rewrite nam2mix_eqb, !nam2mix_ctx_eqb.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d, d0.
 - repeat (break; cbn; auto).
   now rewrite <- !nam2mix_seq_eqb.
 - repeat (break; cbn; auto).
   now rewrite <- !nam2mix_seq_eqb.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   rewrite <- nam2mix_ctx_eqb, <- !nam2mix_seq_eqb.
   now destruct d, d0.
 - repeat (break; cbn; auto).
   rewrite <- nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn - [αeq]; auto);
    rewrite ?andb_false_r; auto.
   rewrite <- nam2mix_ctx_eqb.
   case eqbspec; auto. intro Ec. simpl.
   rewrite <- nam2mix_eqb. cbn.
   apply eq_true_iff_eq. simpl.
   rewrite !andb_true_iff.
   rewrite !negb_true_iff, <- !not_true_iff_false.
   rewrite !Vars.mem_spec.
   rewrite !eqb_eq.
   split; intros (U,V); split.
   + change (Mix.FVar x) with (nam2mix_term [] (Nam.Var x)) in U.
     simpl in U.
     rewrite <- nam2mix_rename_iff with (z:=x).
     rewrite <- partialsubst_bsubst0 in U.
     rewrite <- U.
     (* subst x par x donc idem. Mais quid des allvars au lieu de freevars :( ? *)
     admit.
     admit.
     admit.
   + (* faut montrer que c equiv c0 -> memes variables libres *)
     rewrite <- nam2mix_ctx_fvars. rewrite <- Ec. varsdec.
   + rewrite U.
     change (Mix.FVar x) with (nam2mix_term [] (Nam.Var x)).
     simpl.
     rewrite <- partialsubst_bsubst0.
     (* subst x par x donc idem. Mais quid des allvars au lieu de freevars :( ? *)
     admit.
     admit.
   + rewrite Ec, U, nam2mix_ctx_fvars.
     rewrite nam2mix_fvars. simpl. varsdec.

 - repeat (break; cbn; auto).
   rewrite !nam2mix_ctx_eqb. case eqb; simpl; auto.
   rewrite <- nam2mix_eqb.
   admit.
 - repeat (break; cbn; auto).
   rewrite !nam2mix_ctx_eqb. case eqb; simpl; auto.
   rewrite <- nam2mix_eqb.
   admit.
 - repeat (break; cbn - [αeq]; auto);
    rewrite ?andb_false_r; auto.
   rewrite <- nam2mix_seq_eqb, <- nam2mix_eqb. cbn.
   apply eq_true_iff_eq.
   rewrite !andb_true_iff.
   rewrite !negb_true_iff, <- !not_true_iff_false.
   rewrite !Vars.mem_spec.
   rewrite !eqb_eq.
   split.
   + intros (((U,V),W),X); repeat split.
     * rewrite <-V in U; exact U.
     * rewrite <- nam2mix_ctx_eqb. now apply eqb_eq.
     * admit. (* bsubst... *)
     * destruct s. cbn in *. injection U as U U'. admit.
   + intros ((U,(V,W)),Z); repeat split.
     * rewrite <- nam2mix_ctx_eqb in V. apply eqb_eq in V.
       rewrite U. f_equal; auto.
     * rewrite <- nam2mix_ctx_eqb in V. apply eqb_eq in V.
       rewrite V. auto.
     * rewrite W.
       change (Mix.FVar x) with (nam2mix_term [] (Nam.Var x)).
       admit.
     * destruct s. cbn in *. injection U as U U'. admit.
 - repeat (break; cbn; auto).
   case eqb; simpl; auto.
   now rewrite <- nam2mix_seq_eqb.
Admitted.
