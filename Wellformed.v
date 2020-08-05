
(** * Well-formed terms and formulas *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs Mix Toolbox.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

(** Well-formed terms and formulas over a particular signature :
    - use only the symbols of this signature
    - with the correct arity
    - and moreover with bounded variables that are indeed bounded.

   Thanks to class overloading, [WF] also works for contexts, sequents,
   derivations...

   Note that a derivation which is not well-formed may still be valid
   (in the sense of [Mix.Valid] or [Mix.Pr]). We'll see in [Restrict.v]
   how we can force the inners of a derivation to be well-formed.
*)

Definition WF {T}`{Check T}`{Level T} sign (t:T) :=
  check sign t = true /\ BClosed t.

Definition wf {T}`{Check T}`{Level T} sign (t:T) :=
  check sign t && (level t =? 0).

(** By default, the second arguments of [WF] are to be parsed as formula. *)
Arguments WF {T _ _} sign t%form.
Arguments wf {T _ _} sign t%form.

Lemma wf_spec {T}`{Check T}`{Level T} sign (t:T) :
  reflect (WF sign t) (wf sign t).
Proof.
 unfold WF, wf, BClosed.
 destruct check; cbn; [case eqbspec|]; now constructor.
Qed.

Lemma wf_iff {T}`{Check T}`{Level T} sign (t:T) :
  WF sign t <-> wf sign t = true.
Proof.
 apply reflect_iff, wf_spec.
Qed.

Lemma Op_WF sign o A B :
 WF sign (Op o A B) <-> WF sign A /\ WF sign B.
Proof.
 unfold WF, BClosed. cbn.
 rewrite lazy_andb_iff. rewrite max_0. intuition.
Qed.

Lemma Fun_WF sign f l :
  WF sign (Fun f l) <->
   sign.(funsymbs) f = Some (length l) /\ Forall (WF sign) l.
Proof.
 unfold WF, BClosed.
 rewrite Forall_forall. cbn.
 destruct funsymbs as [a|]; [|easy]. rewrite lazy_andb_iff.
 rewrite list_max_map_0, forallb_forall, eqb_eq.
 firstorder. congruence.
Qed.

Lemma Pred_WF sign p l :
  WF sign (Pred p l) <->
   sign.(predsymbs) p = Some (length l) /\ Forall (WF sign) l.
Proof.
 unfold WF, BClosed.
 rewrite Forall_forall. cbn.
 destruct predsymbs as [a|]; [|easy]. rewrite lazy_andb_iff.
 rewrite list_max_map_0, forallb_forall, eqb_eq.
 firstorder. congruence.
Qed.

Lemma bsubst_WF sign A t :
 WF sign (∀A) -> WF sign t -> WF sign (bsubst 0 t A).
Proof.
 intros (CK,BC) (CK',BC'). split.
 - apply check_bsubst; auto.
 - apply Nat.le_0_r. rewrite level_bsubst, BC'; auto.
   now rewrite <- pred_0.
Qed.

Lemma cons_WF sign f (c:context) :
 WF sign (f::c) <-> WF sign f /\ WF sign c.
Proof.
 unfold WF, BClosed. cbn.
 rewrite max_0, !andb_true_iff. intuition.
Qed.

Lemma ctx_WF sign (c:context) : WF sign c <-> Forall (WF sign) c.
Proof.
 induction c.
 - now unfold WF, BClosed.
 - rewrite cons_WF, IHc. split; auto.
   now constructor. inversion 1; subst; auto.
Qed.

Lemma seq_WF sign f (c:context) :
 WF sign (c ⊢ f) <-> WF sign c /\ WF sign f.
Proof.
 unfold WF, BClosed. cbn. rewrite max_0, lazy_andb_iff. intuition.
Qed.

(** WC : Well-formed Closed terms and formulas are moreover without
    free variables. See in particular axioms and theorems in [Theory.v],
    and points of the syntactic model in [Model.v]. *)

Definition WC {T}`{Check T}`{Level T}`{FVars T} sign (t:T) :=
  WF sign t /\ FClosed t.

Definition wc {T}`{Check T}`{Level T}`{IsFClosed T} sign (t:T) :=
  wf sign t && fclosed t.

Hint Unfold WF WC.
Arguments WC {T _ _ _} sign t%form.
Arguments wc {T _ _ _} sign t%form.
Implicit Types t : term.
Implicit Types A : formula.

Lemma term_wc_spec sign t : reflect (WC sign t) (wc sign t).
Proof.
 unfold WC, wc.
 case wf_spec; cbn; [ | now constructor].
 destruct (fclosed t) eqn:E.
 - rewrite term_fclosed_spec in E. now constructor.
 - constructor. rewrite <- term_fclosed_spec, E. easy.
Qed.

Lemma term_wc_iff sign t : WC sign t <-> wc sign t = true.
Proof.
 apply reflect_iff, term_wc_spec.
Qed.

Lemma wc_spec sign A : reflect (WC sign A) (wc sign A).
Proof.
 unfold WC, wc.
 case wf_spec; cbn; [ | now constructor].
 destruct (fclosed A) eqn:E.
 - rewrite form_fclosed_spec in E. now constructor.
 - constructor. rewrite <- form_fclosed_spec, E. easy.
Qed.

Lemma wc_iff sign A : WC sign A <-> wc sign A = true.
Proof.
 apply reflect_iff, wc_spec.
Qed.

Lemma WC_dec sign A : { WC sign A }+{ ~WC sign A }.
Proof.
 destruct (wc sign A) eqn:E; [left|right].
 - now apply wc_iff.
 - now rewrite wc_iff, E.
Qed.

Lemma True_WC sign : WC sign True.
Proof.
 now rewrite wc_iff.
Qed.

Lemma False_WC sign : WC sign False.
Proof.
 now rewrite wc_iff.
Qed.

Lemma Not_WC sign A : WC sign (Not A) <-> WC sign A.
Proof.
 now rewrite !wc_iff.
Qed.

Lemma Op_WC sign o A B :
 WC sign (Op o A B) <-> WC sign A /\ WC sign B.
Proof.
 unfold WC, FClosed. cbn. rewrite Op_WF; intuition.
Qed.

Lemma bsubst_cst_WC sign c A :
 sign.(funsymbs) c = Some 0 ->
 WC sign (∃A) -> WC sign (bsubst 0 (Cst c) A).
Proof.
 intros E ((CK,BC),FC).
 repeat split; unfold BClosed in *; cbn in *.
 - rewrite check_bsubst; auto. cbn. now rewrite E, eqb_refl.
 - apply Nat.le_0_r, level_bsubst; auto with *.
 - rewrite <- !form_fclosed_spec in *. now rewrite fclosed_bsubst.
Qed.

Lemma Fun_WC sign f l :
  WC sign (Fun f l) <->
   sign.(funsymbs) f = Some (length l) /\ Forall (WC sign) l.
Proof.
 unfold WC. rewrite Fun_WF.
 rewrite <- term_fclosed_spec. cbn.
 rewrite forallb_forall, !Forall_forall.
 setoid_rewrite term_fclosed_spec. intuition.
 now apply H1. now apply H1.
Qed.

Lemma Pred_WC sign p l :
  WC sign (Pred p l) <->
   sign.(predsymbs) p = Some (length l) /\ Forall (WC sign) l.
Proof.
 unfold WC. rewrite Pred_WF.
 rewrite <- form_fclosed_spec. cbn.
 rewrite forallb_forall, !Forall_forall.
 setoid_rewrite term_fclosed_spec. intuition.
 now apply H1. now apply H1.
Qed.

Lemma Cst_WC sign c :
  sign.(funsymbs) c = Some 0 -> WC sign (Cst c).
Proof.
 intros. now apply Fun_WC.
Qed.

Lemma Cst_wc sign c :
  sign.(funsymbs) c = Some 0 -> wc sign (Cst c) = true.
Proof.
 rewrite <- term_wc_iff. apply Cst_WC.
Qed.

Lemma bsubst_WC sign A t :
 WC sign (∀A) -> WC sign t -> WC sign (bsubst 0 t A).
Proof.
 intros (W,F) (W',F'). split.
 - now apply bsubst_WF.
 - rewrite <- form_fclosed_spec, fclosed_bsubst.
   now rewrite form_fclosed_spec.
   now rewrite term_fclosed_spec.
Qed.

Lemma WC_new_sign sign sign' A :
 check sign' A = true -> WC sign A -> WC sign' A.
Proof.
 now intros ? ((?,?),?).
Qed.

Lemma cons_WC sign f (c:context) :
 WC sign (f::c) <-> WC sign f /\ WC sign c.
Proof.
 unfold WC, FClosed. cbn -[Names.union].
 rewrite cons_WF. intuition.
Qed.

Lemma ctx_WC sign (c:context) : WC sign c <-> Forall (WC sign) c.
Proof.
 induction c.
 - now unfold WC, FClosed.
 - rewrite cons_WC, IHc. split; auto.
   now constructor. inversion 1; subst; auto.
Qed.

Lemma seq_WC sign f (c:context) :
 WC sign (c ⊢ f) <-> WC sign c /\ WC sign f.
Proof.
 unfold WC, FClosed. cbn. rewrite seq_WF. intuition.
Qed.
