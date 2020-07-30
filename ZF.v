(** * The Zermelo Fraenkel set theory and its Coq model *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Meta Theories PreModels Models Peano.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

Ltac refold :=
 match goal with
 | x := _, H : _ |- _ => progress fold x in H; refold
 | x := _ |- _ => progress fold x; refold
 | _ => idtac
 end.

Ltac simp := cbn in *; reIff; refold.

(** On the necessity of a non trivial set theory : Russell's paradox. *)

(*  The naive set theory consists of the non restricted comprehension axiom schema :
    ∀ x1, ..., ∀ xn, ∃ a, ∀ y (y ∈ a <-> A),
      forall formula A whose free variables are amongst x1, ..., xn, y. *)

Notation "x ∈ y" := (Pred "∈" [x;y]) (at level 70) : formula_scope.

Open Scope string_scope.
Open Scope formula_scope.

(* It is easy to notice that ∃ a ∀ x (x ∈ a <-> ~(x ∈ x)) is (almost) an instance of the
   comprehension axiom schema : it suffices to let A = ~ (a ∈ a). *)
Lemma Russell : Pr Intuiti ([ ∃∀ (#0 ∈ #1 <-> ~(#0 ∈ #0)) ] ⊢ False).
Proof.
  apply R'_Ex_e with (x := "a"); auto.
  + cbn - [Names.union]. intro. inversion H.
  + cbn. set  (A := FVar "a"). fold (#0 ∈ A <-> ~ #0 ∈ #0)%form.
    set (comp := ∀ _ <-> _).
    set (Γ := [comp]).
    assert (Pr Intuiti (Γ ⊢ ~ A ∈ A)).
    {
      apply R_Not_i.
      set (Γ' := (_ :: Γ)).
      apply R_Not_e with (A := A ∈ A).
      * apply R_Ax. compute; intuition.
      * apply R_Imp_e with (A := A ∈ A).
        ++ apply R_And_e1 with (B := (~ A ∈ A -> A ∈ A)).
           assert (Pr Intuiti (Γ' ⊢ comp)). { apply R_Ax. compute; intuition. }
           apply R_All_e with (t := A) in H; auto.
        ++ apply R_Ax. compute; intuition.
    }     
    apply R_Not_e with (A := A ∈ A); auto.
    apply R_Imp_e with (A := ~ A ∈ A); auto.
    - apply R_And_e2 with (A := (A ∈ A -> ~ A ∈ A)).
      assert (Pr Intuiti (Γ ⊢ comp)). { apply R_Ax. compute; intuition. }
      apply R_All_e with (t := A) in H0; auto.
Qed.

(* Russell's paradox therefore shows that the naive set theory is inconsistent.
   We are to try to fix it, using ZF(C) theory, which has not been proved inconstitent so far
   (neither has it been proved consistent though).
   Actually, were we to intend to prove that ZF is consistent, Godel's second theorem tells us that
   we would have to do it in a stronger theory, which we would have to prove to be consitent too
   (in a stronger theory too), and so on... *)

(** The ZF axioms *)

Close Scope string_scope.
Definition ZFSign := Finite.to_infinite zf_sign.

Notation "x = y" := (Pred "=" [x;y]) : formula_scope.
Notation "x ∈ y" := (Pred "∈" [x;y]) (at level 70) : formula_scope.
Notation "x ∉ y" := (~ x ∈ y) (at level 70) : formula_scope.

Module ZFAx.
Local Open Scope formula_scope.

Definition zero s := ∀ #0 ∉ lift 0 s.
Definition succ x y := ∀ (#0 ∈ lift 0 y <-> #0 = lift 0 x \/ #0 ∈ lift 0 x).

Definition eq_refl := ∀ (#0 = #0).
Definition eq_sym := ∀∀ (#1 = #0 -> #0 = #1).
Definition eq_trans := ∀∀∀ (#2 = #1 /\ #1 = #0 -> #2 = #0).
Definition compat_left := ∀∀∀ (#0 = #1 /\ #0 ∈ #2 -> #1 ∈ #2).
Definition compat_right := ∀∀∀ (#0 ∈ #1 /\ #1 = #2 -> #0 ∈ #2).

Definition ext := ∀∀ (∀ (#0 ∈ #2 <-> #0 ∈ #1) -> #2 = #1).
Definition pairing := ∀∀∃∀ (#0 ∈ #1 <-> #0 = #3 \/ #0 = #2).
Definition union := ∀∃∀ (#0 ∈ #1 <-> ∃ (#0 ∈ #3 /\ #1 ∈ #0)).
Definition powerset := ∀∃∀ (#0 ∈ #1 <-> ∀ (#0 ∈ #1 -> #0 ∈ #3)).
Definition infinity := ∃ (∃ (#0 ∈ #1 /\ zero (#0)) /\ ∀ (#0 ∈ #1 -> (∃ (#0 ∈ #2 /\ succ (#1) (#0))))).

Definition axioms_list :=
 [ eq_refl; eq_sym; eq_trans; compat_left; compat_right; ext; pairing; union; powerset; infinity ].

(* POUR SEPARATION:
  dB dans A :  0=>x 1=>a n>=2:z_i
  dB dans (lift_above 1 A) 0=>x ... 2=>a (n>=3:z_i) *)
Definition separation_schema A :=
  nForall
    ((level A) - 2)
    (∀∃∀ (#0 ∈ #1 <-> (#0 ∈ #2 /\ lift 1 A))).

Definition exists_uniq A :=
∃ (A /\ ∀ (lift 1 A -> #0 = #1)).

(* POUR REPLACEMENT:
   dB dans A :  0=>y 1=>x 2=>a n>=3:z_i
   dB dans (lift_above 2 A) 0=>y 1=>x ... 3=>a (n>=4:z_i) *)
Definition replacement_schema A :=
  nForall
    ((level A) - 3)
    (∀ (∀ (#0 ∈ #1 -> exists_uniq A)) ->
       ∃∀ (#0 ∈ #2 -> ∃ (#0 ∈ #3 /\ lift 2 A))).

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

Lemma pred_max a b :
Nat.pred (Nat.max a b) = Nat.max (Nat.pred a) (Nat.pred b).
Proof.
symmetry. apply Nat.max_monotone. red. red. auto with *.
Qed.

Lemma WfAx A : IsAx A -> Wf ZFSign A.
Proof.
 intros [ IN | [ (B & -> & HB & HB') | (C & -> & HC & HC') ] ].
 - apply Wf_iff.
   unfold axioms_list in IN.
   simpl in IN. intuition; subst; reflexivity.
 - repeat split; unfold separation_schema; cbn.
   + rewrite nForall_check. cbn.
     rewrite !check_lift_form, HB.
     easy.
   + red. rewrite nForall_level.
     cbn -[Nat.max].
     rewrite !pred_max. simpl.
     assert (H := level_lift_form 1 B).
     apply Nat.sub_0_le.
     repeat apply Nat.max_lub; omega with *.
   + apply nForall_fclosed. rewrite <- form_fclosed_spec in *.
     cbn. now rewrite fclosed_lift_above, HB'.
 - repeat split; unfold replacement_schema; cbn.
   + rewrite nForall_check. cbn.
     rewrite !check_lift_form, HC.
     easy.
   + red. rewrite nForall_level.
     cbn -[Nat.max].
     rewrite !pred_max. simpl.
     assert (H := level_lift_form 1 C).
     assert (H' := level_lift_form 2 C).
     apply Nat.sub_0_le.
     repeat apply Nat.max_lub; omega with *.
   + apply nForall_fclosed. rewrite <- form_fclosed_spec in *.
     cbn. now rewrite !fclosed_lift_above, HC'.
Qed.

End ZFAx.

Local Open Scope string.
Local Open Scope formula_scope.

Definition ZF :=
 {| sign := ZFSign;
    IsAxiom := ZFAx.IsAx;
    WfAxiom := ZFAx.WfAx |}.

Import ZFAx.

Lemma emptyset : IsTheorem Intuiti ZF (∃∀ ~(#0 ∈ #1)). 
Proof.
  thm.
  exists [infinity].
  split; auto.
  - simpl. constructor; auto.
    unfold IsAx. left. calc.
  - apply R'_Ex_e with (x := "a").
    + calc.
    + cbn.
      apply R'_Ex_e with (x := "x").
      * calc.
      * cbn.
        apply R'_And_e.
        apply Pr_swap, Pr_pop.
        apply R'_And_e.
        apply Pr_pop.
        apply R_Ex_i with (t := FVar "x"). cbn.
        apply R'_Ax.
Qed.

Lemma singleton : IsTheorem Intuiti ZF (∀∃∀ (#0 ∈ #1 <-> #0 = #2)).
Proof.
  thm.
  exists [pairing].
  split; auto.
  - simpl. rewrite Forall_forall. intros. destruct H.
    + rewrite<- H. unfold IsAx. left. compute; intuition.
    + inversion H.
  - app_R_All_i "x" x.
    inst_axiom pairing [x; x]. simp.
    eapply R_Ex_e with (x := "y"); [ | exact H | ].
    + calc.
    + cbn. fold x.
      set (y := FVar "y"). reIff.
      apply R_Ex_i with (t := y); simp.
      apply R_All_i with (x := "z"); [ calc | ].
      set (z := FVar "z"). apply R'_All_e with (t := z); auto.
      simp.
      apply R_And_i; apply R'_And_e.
      * apply R_Imp_i.
        apply R_Or_e with (A := z = x) (B := z = x); [ | apply R_Ax; calc | apply R_Ax; calc ].
        apply R_Imp_e with (A := z ∈ y); apply R_Ax; calc.
      * apply R_Imp_i.
        apply R_Imp_e with (A := z = x \/ z = x); [ apply R_Ax; calc | ].
        apply R_Or_i1; apply R_Ax; calc.
Qed.

Lemma unionset : IsTheorem Intuiti ZF (∀∀∃∀ (#0 ∈ #1 <-> #0 ∈ #3 \/ #0 ∈ #2)).
Proof.
  thm.
  exists [ pairing; union; compat_right; eq_refl ].
  split; auto.
  - simpl. constructor.
    + left. calc.
    + constructor. left. calc.
      constructor. left. calc.
      constructor; [ left; calc | auto ].
  - set (Γ := [ _ ; _ ; _ ]).
    app_R_All_i "A" A.
    app_R_All_i "B" B.
    inst_axiom pairing [A; B]; simp.
    eapply R_Ex_e with (x := "C"); [ | exact H | ]; calc.
    set (C := FVar "C"). simp. clear H.
    inst_axiom union [C]; simp.
    eapply R_Ex_e with (x := "U"); [ | exact H | ]; calc.
    set (U := FVar "U"). simp. clear H.
    apply R_Ex_i with (t := U). simp.
    app_R_All_i "x" x. simp.
    apply R_And_i.
    + apply R_Imp_i.
      apply R_Ex_e with (A := #0 ∈ C /\ x ∈ #0) (x := "y"); set (y := FVar "y").
      * calc.
      * apply R_Imp_e with (A := x ∈ U).
        -- eapply R_And_e1.
           set (Ax := ∀ _). inst_axiom Ax [ x ].
           exact H.
        -- apply R'_Ax.
      * simp.
        apply R'_And_e.
        apply R_Or_e with (A := y = A) (B := y = B).
        -- apply R_Imp_e with (A := y ∈ C); [ | apply R'_Ax ].
           eapply R_And_e1.
           set (Ax := ∀ _ <-> _ \/ _). inst_axiom Ax [ y ].
           exact H.
        -- apply R_Or_i1.
           apply R_Imp_e with (A := x ∈ y /\ y = A).
           ++ inst_axiom compat_right [ A; y; x ].
           ++ apply R_And_i; apply R_Ax; calc.
        -- apply R_Or_i2.
           apply R_Imp_e with (A := x ∈ y /\ y = B).
           ++ inst_axiom compat_right [ B; y; x ].
           ++ apply R_And_i; apply R_Ax; calc.
    + apply R_Imp_i.
      apply R'_Or_e.
      * set (Ax := ∀ _ ∈ U <-> _). inst_axiom Ax [ x ].
        simp.
        apply R_And_e2 in H.
        apply R_Imp_e with (A := (∃ #0 ∈ C /\ x ∈ #0)); [ assumption | ].
        apply R_Ex_i with (t := A). simp.
        apply R_And_i.
        -- set (Ax2 := ∀ _ <-> _). inst_axiom Ax2 [ A ].
           simp.
           apply R_And_e2 in H0.
           apply R_Imp_e with (A := A = A \/ A = B); [ assumption | ].
           apply R_Or_i1.
           inst_axiom eq_refl [ A ].
        -- apply R'_Ax.
      * set (Ax := ∀ _ ∈ U <-> _). inst_axiom Ax [ x ].
        simp.
        apply R_And_e2 in H.
        apply R_Imp_e with (A := (∃ #0 ∈ C /\ x ∈ #0)); [ assumption | ].
        apply R_Ex_i with (t := B). simp.
        apply R_And_i.
        -- set (Ax2 := ∀ _ <-> _). inst_axiom Ax2 [ B ].
           simp.
           apply R_And_e2 in H0.
           apply R_Imp_e with (A := B = A \/ B = B); [ assumption | ].
           apply R_Or_i2.
           inst_axiom eq_refl [ B ].
        -- apply R'_Ax.
Qed.

Lemma Succ : IsTheorem Intuiti ZF
                       ((∀∃∀ (#0 ∈ #1 <-> #0 = #2))
                        -> (∀∀∃∀ (#0 ∈ #1 <-> #0 ∈ #3 \/ #0 ∈ #2))
                        -> ∀∃ succ (#1) (#0)).
Proof.
  thm.
  exists [ ].
  split; auto.
  repeat apply R_Imp_i.
  set (Un := ∀ ∀ _). set (Sing := ∀ ∃ _). set (Γ := Un :: Sing :: []).
  app_R_All_i "x" x. simp.
  inst_axiom Sing [x]; simp.
  eapply R_Ex_e with (x := "A"); [ | exact H | ]; calc.
  set (A := FVar "A"). simp. clear H.
  inst_axiom Un [ A; x ]. simp.
  eapply R_Ex_e with (x := "U"); [ | exact H | ]; calc.
  set (U := FVar "U"). simp. clear H.
  apply R_Ex_i with (t := U). simp.
  app_R_All_i "y" y. simp.
  apply R_And_i.
  - apply R_Imp_i.
    apply R_Or_e with (A := y ∈ A) (B := y ∈ x).
    + set (Ax := ∀ _ ∈ U <-> _).
      inst_axiom Ax [ y ]. simp.
      apply R_And_e1 in H.
      apply R_Imp_e with (A := y ∈ U) in H; [ intuition | apply R'_Ax ].
    + apply R_Or_i1.
      set (Ax := ∀ _ ∈ A <-> _).
      inst_axiom Ax [ y ]. simp.
      apply R_And_e1 in H.
      apply R_Imp_e with (A := y ∈ A) in H; [ intuition | apply R'_Ax ].
    + apply R_Or_i2. apply R'_Ax.
  - apply R_Imp_i.
    apply R_Imp_e with (A := y ∈ A \/ y ∈ x).
    + set (Ax := ∀ _ ∈ U <-> _).
      inst_axiom Ax [ y ]. simp.
      apply R_And_e2 in H.
      assumption.
    + apply R'_Or_e.
      * apply R_Or_i1.
        set (Ax := ∀ _ ∈ A <-> _).
        inst_axiom Ax [ y ]. simp.
        apply R_And_e2 in H.
        apply R_Imp_e with (A := y = x) in H; [ intuition | apply R'_Ax ].
      * apply R_Or_i2. apply R'_Ax.
Qed.
  
Lemma Successor : IsTheorem Intuiti ZF (∀∃ succ (#1) (#0)).
Proof.
  apply ModusPonens with (A := ∀∀∃∀ #0 ∈ #1 <-> #0 ∈ #3 \/ #0 ∈ #2); [ | apply unionset ].
  apply ModusPonens with (A := ∀∃∀ #0 ∈ #1 <-> #0 = #2); [ apply Succ | apply singleton ].
Qed.
