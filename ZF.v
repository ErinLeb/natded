(** * The Zermelo Fraenkel set theory and its Coq model *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Meta Theories PreModels Models.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

(** The Peano axioms *)

Definition ZFSign := Finite.to_infinite zf_sign.

Notation "x = y" := (Pred "=" [x;y]) : formula_scope.
Notation "x ∈ y" := (Pred "∈" [x;y]) : formula_scope.

Module ZFAx.
Local Open Scope formula_scope.

Definition eq_refl := ∀ (#0 = #0).
Definition eq_sym := ∀∀ (#1 = #0 -> #0 = #1).
Definition eq_trans := ∀∀∀ (#2 = #1 /\ #1 = #0 -> #2 = #0).
Definition compat_left := ∀∀∀ (#0 = #1 /\ #0 ∈ #2 -> #1 ∈ #2).
Definition compat_right := ∀∀∀ (#0 ∈ #1 /\ #1 = #2 -> #0 ∈ #2).

Definition ext := ∀∀ (∀ (#2 ∈ #0 <-> #2 ∈ #1) -> #0 = #1).
Definition pairing := ∀∀∃∀ (#3 ∈ #2 <-> #3 = #0 \/ #3 = #1).
Definition union := ∀∃∀ (#2 ∈ #1 <-> ∃ (#3 ∈ #0 /\ #2 ∈ #3)).
Definition powerset := ∀∃∀ (#2 ∈ #1 <-> ∀ (#3 ∈ #2 -> #3 ∈ #0)).
Definition infinity := ∃ (∃ (#1 ∈ #0 /\ ∀ not #2 ∈ #1) /\ ∀ (#3 ∈ #0 -> (∃ (#4 ∈ #0 /\ (∀ (#5 ∈ #4 <-> #5 = #3 \/ #5 ∈ #3)))))).

Definition axioms_list :=
 [ eq_refl; eq_symp; eq_trans; compat_left; compat_right; ext; pairing; union; powerset; infinity ].

(** Beware, [bsubst] is ok below for turning [#0] into [Succ #0], but
    only since it contains now a [lift] of substituted terms inside
    quantifiers.
    And the unconventional [∀] before [A[0]] is to get the right
    bounded vars (Hack !). *)

Definition comprehension_schema A :=
  nForall
    (Nat.pred (level A))
    (

Definition induction_schema A_x :=
  let A_0 := bsubst 0 Zero A_x in
  let A_Sx := bsubst 0 (Succ(#0)) A_x in
  nForall
    (Nat.pred (level A_x))
    (((∀ A_0) /\ (∀ (A_x -> A_Sx))) -> ∀ A_x).

Local Close Scope formula_scope.

Definition IsAx A :=
  List.In A axioms_list \/
  exists B, A = induction_schema B /\
            check PeanoSign B = true /\
            FClosed B.

Lemma WfAx A : IsAx A -> Wf PeanoSign A.
Proof.
 intros [ IN | (B & -> & HB & HB')].
 - apply Wf_iff.
   unfold axioms_list in IN.
   simpl in IN. intuition; subst; reflexivity.
 - repeat split; unfold induction_schema; cbn.
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

End PeanoAx.

Local Open Scope string.
Local Open Scope formula_scope.

Definition PeanoTheory :=
 {| sign := PeanoSign;
    IsAxiom := PeanoAx.IsAx;
    WfAxiom := PeanoAx.WfAx |}.


Import PeanoAx.
