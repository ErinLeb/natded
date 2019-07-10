
Require Import Defs NameProofs Mix Theories Meta.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

Definition Zero := Fun "O" [].
Definition Succ x := Fun "S" [x].

Notation "x = y" := (Pred "=" [x;y]) : formula_scope.
Notation "x + y" := (Fun "+" [x;y]) : formula_scope.
Notation "x * y" := (Fun "*" [x;y]) : formula_scope.

Module PeanoAx.
Local Open Scope formula_scope.

Definition ax1 := ∀ (#0 = #0).
Definition ax2 := ∀∀ (#1 = #0 -> #0 = #1).
Definition ax3 := ∀∀∀ (#2 = #1 /\ #1 = #0 -> #2 = #0).

Definition ax4 := ∀∀ (#1 = #0 -> Succ (#1) = Succ (#0)).
Definition ax5 := ∀∀∀ (#2 = #1 -> #2 + #0 = #1 + #0).
Definition ax6 := ∀∀∀ (#1 = #0 -> #2 + #1 = #2 + #0).
Definition ax7 := ∀∀∀ (#2 = #1 -> #2 * #0 = #1 * #0).
Definition ax8 := ∀∀∀ (#1 = #0 -> #2 * #1 = #2 * #0).

Definition ax9 := ∀ (Zero + #0 = #0).
Definition ax10 := ∀∀ (Succ(#1) + #0 = Succ(#1 + #0)).
Definition ax11 := ∀ (Zero * #0 = #0).
Definition ax12 := ∀∀ (Succ(#1) * #0 = (#1 * #0) + #0).

Definition ax13 := ∀∀ (Succ(#1) = Succ(#0) -> #1 = #0).
Definition ax14 := ∀ ~(Succ(#0) = Zero).

Definition axioms_list :=
  [ ax1; ax2; ax3; ax4; ax5; ax6; ax7; ax8;
    ax9; ax10; ax11; ax12; ax13; ax14 ].

Fixpoint nForall n A :=
  match n with
  | 0 => A
  | S n => (∀ (nForall n A))%form
  end.

Lemma nForall_check sign n A :
 check sign (nForall n A) = check sign A.
Proof.
 induction n; simpl; auto.
Qed.

Lemma nForall_fclosed n A :
 FClosed A -> FClosed (nForall n A).
Proof.
 induction n; simpl; auto.
Qed.

Lemma nForall_level n A :
 level (nForall n A) = level A - n.
Proof.
 induction n; cbn; auto with arith.
 rewrite IHn. omega.
Qed.

(** Change all bound vars [#n] into [h #n], with lifting
    under quantifiers *)

Fixpoint form_update n (h:term->term) f :=
 match f with
  | True | False => f
  | Pred p args => Pred p (List.map (bsubst n (h (BVar n))) args)
  | Not f => Not (form_update n h f)
  | Op o f f' => Op o (form_update n h f) (form_update n h f')
  | Quant q f' => Quant q (form_update (S n) h f')
 end.

Lemma form_update_check sign (h:term->term) :
 (forall n, check sign (h (BVar n)) = true) ->
 forall f n, check sign f = true ->
             check sign (form_update n h f) = true.
Proof.
 intros Hh. induction f; cbn; intros n; auto.
 - destruct predsymbs; auto.
   rewrite !lazy_andb_iff.
   rewrite map_length. intuition.
   rewrite forallb_forall in *. intros t Ht.
   rewrite in_map_iff in Ht. destruct Ht as (t' & <- & IN).
   apply check_bsubst_term; auto.
 - rewrite !lazy_andb_iff; intuition.
Qed.

Lemma bsubst_term_fvars' n (u t : term) :
  Names.Subset (fvars t) (fvars (bsubst n u t)).
Proof.
 revert t. fix IH 1. destruct t; cbn; auto with set.
 clear f.
 revert l. fix IH' 1. destruct l; cbn; auto with set.
 intro x. NamesF.set_iff. intros [IN|IN].
 - left; now apply IH.
 - right. now apply IH'.
Qed.

Lemma bsubst_fvars' n u (f:formula) :
  Names.Subset (fvars f) (fvars (bsubst n u f)).
Proof.
 revert n; induction f; cbn; intros n; auto with set.
 - apply (bsubst_term_fvars' n u (Fun "" l)).
 - intro x. NamesF.set_iff. intros [IN|IN].
   left; now apply IHf1.
   right; now apply IHf2.
Qed.

Lemma form_update_fvars (h:term->term) :
 (forall n, FClosed (h (BVar n))) ->
 forall f n, Names.Equal (fvars (form_update n h f)) (fvars f).
Proof.
 intros Hh. induction f; cbn; intros n; auto with set.
 - intro x. rewrite unionmap_map_in, unionmap_in.
   split.
   + intros (a & IN & IN'). exists a; split; auto.
     apply bsubst_term_fvars in IN.
     rewrite Names.union_spec in IN. destruct IN; auto.
     now apply Hh in H.
   + intros (a & IN & IN'). exists a; split; auto.
     now apply bsubst_term_fvars'.
 - intros x. NamesF.set_iff. now rewrite IHf1, IHf2.
Qed.

Lemma form_update_closed (h:term->term) :
 (forall n, FClosed (h (BVar n))) ->
 forall f n, FClosed f -> FClosed (form_update n h f).
Proof.
 intros. red. rewrite form_update_fvars; auto.
Qed.

Lemma level_bsubst_term' n (u t : term) :
  level u <= S n -> level (bsubst n u t) <= level t.
Proof.
 intro Hu. revert t. fix IH 1. destruct t; cbn; auto.
 - case eqbspec; intros; subst; auto.
 - revert l. fix IH' 1. destruct l; cbn; auto.
   apply Nat.max_le_compat; auto.
Qed.

Lemma level_bsubst' n u (f:formula) :
  level u <= S n -> level (bsubst n u f) <= level f.
Proof.
 revert n. induction f; cbn; intros n Hu; auto with arith.
 - now apply (level_bsubst_term' n u (Fun "" l)).
 - apply Nat.max_le_compat; auto.
 - apply Nat.pred_le_mono; auto with arith.
Qed.

Lemma form_update_level (h:term->term) :
 (forall n, level (h (BVar n)) <= S n) ->
 forall f n, level (form_update n h f) <= level f.
Proof.
 intros Hh. induction f; cbn; intros n; auto.
 - apply (level_bsubst_term' n (h (#n)) (Fun "" l)); auto.
 - apply Nat.max_le_compat; auto.
 - apply Nat.pred_le_mono; auto.
Qed.

(** Beware, bsubst would not be ok below for turning [#0] into [Succ #0]
    (no lift on substituted term inside quantifiers).
    And the unconventional [∀] before [A[0]] is to get the right
    bounded vars (Hack !). *)

Definition induction_schema A :=
  let n := level A in
  nForall
    (pred n)
    (∀ (bsubst 0 Zero A) /\ (∀ (A -> form_update 0 Succ A)) -> ∀ A).

Local Close Scope formula_scope.

Definition peano_sign' := Finite.to_infinite peano_sign.

Definition IsAx A :=
  List.In A axioms_list \/
  exists B, A = induction_schema B /\
            check peano_sign' B = true /\
            FClosed B.

Lemma WfAx A : IsAx A -> Wf peano_sign' A.
Proof.
 intros [ IN | (B & -> & HB & HB')].
 - apply Wf_iff.
   unfold axioms_list in IN.
   simpl in IN. intuition; subst; reflexivity.
 - repeat split; unfold induction_schema; cbn.
   + rewrite nForall_check. cbn.
     rewrite check_bsubst, HB; auto.
     rewrite form_update_check; auto.
   + red. rewrite nForall_level. cbn.
     assert (level (bsubst 0 Zero B) <= level B).
     { apply level_bsubst'. auto. }
     assert (level (form_update 0 Succ B) <= level B).
     { apply form_update_level. auto. }
     omega with *.
   + apply nForall_fclosed. red. cbn.
     rewrite form_update_fvars; auto.
     assert (FClosed (bsubst 0 Zero B)).
     { red. rewrite bsubst_fvars.
       intro x. rewrite Names.union_spec. cbn. red in HB'. intuition. }
     unfold FClosed in *. intuition.
Qed.

End PeanoAx.

Definition PeanoTheory :=
 {| sign := Finite.to_infinite peano_sign;
    IsAxiom := PeanoAx.IsAx;
    WfAxiom := PeanoAx.WfAx |}.

(** TODO : modele *)
