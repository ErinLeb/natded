(** * The Zermelo Fraenkel set theory and its Coq model *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Meta Theories PreModels Models.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

(** On the necessity of a non trivial set theory : Russell's paradox. *)

(*  The naive set theory consists of the non restricted comprehension axiom schema :
    ∀ x1, ..., ∀ xn, ∃ a, ∀ y (y ∈ a <-> A),
      forall formula A whose free variables are amongst x1, ..., xn, y. *)

Notation "x ∈ y" := (Pred "∈" [x;y]) (at level 70) : formula_scope.

Open Scope formula_scope.

(* So as to make the proof easier we Skolemise the instance of the comprehension axiom schema into
   ∀ y, (y ∈ a <-> A).
   It is easy to notice that ∀ (#0 ∈ A <-> ~(#0 ∈ #0)) is (almost) an instance of the comprehension
   axiom schema : it suffices to let A = ~ (a ∈ a). *)
Lemma Russell a : Pr Intuiti ([ ∀ (#0 ∈ (FVar a) <-> ~(#0 ∈ #0)) ] ⊢ False).
Proof.
  set (comp := ∀ _ <-> _).
  set (Γ := [comp]).
  set (A := FVar a).
  apply R_Not_e with (A := A ∈ A).
  + apply R_Imp_e with (A := ~ A ∈ A).
    - apply R_And_e2 with (A := (A ∈ A -> ~ A ∈ A)).
      assert (Pr Intuiti (Γ ⊢ comp)). { apply R_Ax. compute; intuition. }
      apply R_All_e with (t := FVar a) in H; auto.
    - apply R_Not_i.
      set (Γ' := (_ :: Γ)).
      apply R_Not_e with (A := A ∈ A).
      * apply R_Ax. compute; intuition.
      * apply R_Imp_e with (A := A ∈ A).
        ++ apply R_And_e1 with (B := (~ A ∈ A -> A ∈ A)).
           assert (Pr Intuiti (Γ' ⊢ comp)). { apply R_Ax. compute; intuition. }
           apply R_All_e with (t := FVar a) in H; auto.
        ++ apply R_Ax. compute; intuition.
  + apply R_Not_i.
      set (Γ' := (_ :: Γ)).
      apply R_Not_e with (A := A ∈ A).
      * apply R_Ax. compute; intuition.
      * apply R_Imp_e with (A := A ∈ A).
        ++ apply R_And_e1 with (B := (~ A ∈ A -> A ∈ A)).
           assert (Pr Intuiti (Γ' ⊢ comp)). { apply R_Ax. compute; intuition. }
           apply R_All_e with (t := FVar a) in H; auto.
        ++ apply R_Ax. compute; intuition.
Qed.

(* Russell's paradox therefore shows that the naive set theory is inconsistant.
   We are to try to fix it, using ZF(C) theory, which has not been proved inconstitant so far
   (neither has it been proved consistant though...). *)

(** The ZF axioms *)

Definition ZFSign := Finite.to_infinite zf_sign.

Notation "x = y" := (Pred "=" [x;y]) : formula_scope.
Notation "x ∈ y" := (Pred "∈" [x;y]) (at level 70) : formula_scope.

Module ZFAx.
Local Open Scope formula_scope.

Definition eq_refl := ∀ (#0 = #0).
Definition eq_sym := ∀∀ (#1 = #0 -> #0 = #1).
Definition eq_trans := ∀∀∀ (#2 = #1 /\ #1 = #0 -> #2 = #0).
Definition compat_left := ∀∀∀ (#0 = #1 /\ #0 ∈ #2 -> #1 ∈ #2).
Definition compat_right := ∀∀∀ (#0 ∈ #1 /\ #1 = #2 -> #0 ∈ #2).

Definition ext := ∀∀ (∀ (#0 ∈ #2 <-> #0 ∈ #1) -> #2 = #1).
Definition pairing := ∀∀∃∀ (#0 ∈ #1 <-> #0 = #3 \/ #0 = #2).
Definition union := ∀∃∀ (#0 ∈ #1 <-> ∃ (#0 ∈ #3 /\ #1 ∈ #0)).
Definition powerset := ∀∃∀ (#0 ∈ #1 <-> ∀ (#0 ∈ #1 -> #0 ∈ #3)).
Definition infinity := ∃ (∃ (#0 ∈ #1 /\ ∀ ~(#0 ∈ #1)) /\ ∀ (#0 ∈ #1 -> (∃ (#0 ∈ #2 /\ (∀ (#0 ∈ #1 <-> #0 = #2 \/ #0 ∈ #2)))))).

Definition axioms_list :=
 [ eq_refl; eq_sym; eq_trans; compat_left; compat_right; ext; pairing; union; powerset; infinity ].

(** Beware, [bsubst] is ok below for turning [#0] into [Succ #0], but
    only since it contains now a [lift] of substituted terms inside
    quantifiers. *)

Definition separation_schema A :=
  nForall
    (Nat.pred (level A)-2)
    (∀∃∀ (#0 ∈ #1 <-> #0 ∈ #2 /\ A)).

Definition replacement_schema A :=
  nForall
    (Nat.pred (level A)-2)
    (∀(∀ (#0 ∈ #1 -> (∃ (A /\ ∀ ((bsubst 1 (#0) A) -> #0 = #1)))) -> ∃∀ (#0 ∈ #2 -> ∃ (#0 ∈ #3 /\ A)))).

Local Close Scope formula_scope.

Definition IsAx A :=
  List.In A axioms_list \/
  (exists B, A = separation_schema B /\
            check ZFSign B = true /\
            FClosed B)
  \/
  (exists B, A = replacement_schema B /\
             check ZFSign B = true /\
             FClosed B).

Lemma WfAx A : IsAx A -> Wf ZFSign A.
Proof.
 intros [ IN | [ (B & -> & HB & HB') | (C & -> & HC & HC') ] ].
 - apply Wf_iff.
   unfold axioms_list in IN.
   simpl in IN. intuition; subst; reflexivity.
 - repeat split; unfold separation_schema; cbn.
   + rewrite nForall_check. cbn.
     apply andb_true_iff.
     split.
     * assumption.
     * apply orb_true_iff. left. assumption.
   + red. rewrite nForall_level. SearchAbout level.
     assert (level (bsubst 0 Zero B) <= level B).
     { apply level_bsubst'. auto. }
     assert (level (bsubst 0 (Succ(BVar 0)) B) <= level B).
     { apply level_bsubst'. auto. }
     omega with *.
   + apply nForall_fclosed. red. cbn.
     assert (FClosed (bsubst 0 Zero B)).
     { red. rewrite bsubst_fvars.
       intro x. rewrite Names.union_spec. cbn. red in HB'. intuition. }
     assert (FClosed (bsubst 0 (Succ(BVar 0)) B)).
     { red. rewrite bsubst_fvars.
       intro x. rewrite Names.union_spec. cbn - [Names.union].
       rewrite Names.union_spec.
       generalize (HB' x) (@Names.empty_spec x). intuition. }
     unfold FClosed in *. intuition.
- repeat split; unfold replacement_schema; cbn.
   + rewrite nForall_check. cbn.
     rewrite !check_bsubst, HB; auto.
   + red. rewrite nForall_level. cbn.
     assert (level (bsubst 0 Zero B) <= level B).
     { apply level_bsubst'. auto. }
     assert (level (bsubst 0 (Succ(BVar 0)) B) <= level B).
     { apply level_bsubst'. auto. }
     omega with *.
   + apply nForall_fclosed. red. cbn.
     assert (FClosed (bsubst 0 Zero B)).
     { red. rewrite bsubst_fvars.
       intro x. rewrite Names.union_spec. cbn. red in HB'. intuition. }
     assert (FClosed (bsubst 0 (Succ(BVar 0)) B)).
     { red. rewrite bsubst_fvars.
       intro x. rewrite Names.union_spec. cbn - [Names.union].
       rewrite Names.union_spec.
       generalize (HB' x) (@Names.empty_spec x). intuition. }
     unfold FClosed in *. intuition.
Qed.

End ZFAx.

Local Open Scope string.
Local Open Scope formula_scope.

Definition ZFTheory :=
 {| sign := PeanoSign;
    IsAxiom := PeanoAx.IsAx;
    WfAxiom := PeanoAx.WfAx |}.


Import ZFAx.
