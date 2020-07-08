(** * The Zermelo Fraenkel set theory and its Coq model *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Meta Theories PreModels Models.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

(** On the necessity of a non trivial set theory : Russell's paradox. *)

(*  The naive set theory consists of the non restricted comprehension axiom schema :
    ∀ x1, ..., ∀ xn, ∃ E, ∀ y (y ∈ E <-> A),
      forall formula A whose free variable are x1, ..., xn. *)

Definition naive_sign :=
  (* So as to make the proof easier, we assume there is a constant E in the signature of the theory.
     This could be avoided by transforming the statement of the paradox into "∃∀ (#0 ∈ #1 <-> ~(#0 ∈ #0))". *)
  {| Finite.funsymbs := [("E",0)];
     Finite.predsymbs := [("∈",2)] |}.

Open Scope formula_scope.

(* It is easy to notice that ∀ (#0 ∈ A <-> ~(#0 ∈ #0)) is (almost) an instance of the comprehension axiom schema : it suffices to let A = . *)
Lemma Russell : Pr Intuiti ([ ∀ (#0 ∈ E <-> ~(#0 ∈ #0)) ] ⊢ False).
Proof.
  

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

Definition comprehension_schema A :=
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
  (exists B, A = comprehension_schema B /\
            check ZFSign B = true /\
            FClosed B).
  \/
  (exists B, A = replacement_schema B /\
             check ZFSign B = true /\
             FClosed B).

Lemma WfAx A : IsAx A -> Wf ZFSign A.
Proof.
 intros [ IN | (B & -> & HB & HB') ].
 - apply Wf_iff.
   unfold axioms_list in IN.
   simpl in IN. intuition; subst; reflexivity.
 - repeat split; unfold comprehension_schema; cbn.
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

End PeanoAx.

Local Open Scope string.
Local Open Scope formula_scope.

Definition PeanoTheory :=
 {| sign := PeanoSign;
    IsAxiom := PeanoAx.IsAx;
    WfAxiom := PeanoAx.WfAx |}.


Import PeanoAx.
