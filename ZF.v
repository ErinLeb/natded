(** * The Zermelo Fraenkel set theory and its Coq model *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Meta.
Require Import Wellformed Theories Nary PreModels Models Peano.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.
Local Open Scope formula_scope.

Notation "x = y" := (Pred "=" [x;y]) : formula_scope.
Notation "x ∈ y" := (Pred "∈" [x;y]) (at level 70) : formula_scope.
Notation "x ∉ y" := (~ x ∈ y) (at level 70) : formula_scope.

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

(* It is easy to notice that ∃ a ∀ x (x ∈ a <-> ~(x ∈ x)) is (almost) an instance of the
   comprehension axiom schema : it suffices to let A = ~ (a ∈ a). *)
Lemma Russell : Pr J ([ ∃∀ (#0 ∈ #1 <-> ~(#0 ∈ #0)) ] ⊢ False).
Proof.
  apply R'_Ex_e with (x := "a"); auto.
  + cbn - [Names.union]. intro. inversion H.
  + cbn. set  (A := FVar "a"). fold (#0 ∈ A <-> ~ #0 ∈ #0)%form.
    set (comp := ∀ _ <-> _).
    set (Γ := [comp]).
    assert (Pr J (Γ ⊢ ~ A ∈ A)).
    {
      apply R_Not_i.
      set (Γ' := (_ :: Γ)).
      apply R_Not_e with (A := A ∈ A).
      * apply R_Ax. compute; intuition.
      * apply R_Imp_e with (A := A ∈ A).
        ++ apply R_And_e1 with (B := (~ A ∈ A -> A ∈ A)).
           assert (Pr J (Γ' ⊢ comp)). { apply R_Ax. compute; intuition. }
           apply R_All_e with (t := A) in H; auto.
        ++ apply R_Ax. compute; intuition.
    }     
    apply R_Not_e with (A := A ∈ A); auto.
    apply R_Imp_e with (A := ~ A ∈ A); auto.
    - apply R_And_e2 with (A := (A ∈ A -> ~ A ∈ A)).
      assert (Pr J (Γ ⊢ comp)). { apply R_Ax. compute; intuition. }
      apply R_All_e with (t := A) in H0; auto.
Qed.

(* Russell's paradox therefore shows that the naive set theory is inconsistent.
   We are to try to fix it, using ZF(C) theory, which has not been proved inconstitent so far
   (neither has it been proved consistent though).
   Actually, were we to intend to prove that ZF is consistent, Godel's second theorem tells us that
   we would have to do it in a stronger theory, which we would have to prove to be consitent too
   (in a stronger theory too), and so on... *)

(** The ZF axioms *)

Definition ZFSign := Finite.to_infinite zf_sign.

Module ZFAx.

Definition zero s := ∀ #0 ∉ lift 0 s.
Definition succ x y := ∀ (#0 ∈ lift 0 y <-> #0 = lift 0 x \/ #0 ∈ lift 0 x).

Definition eq_refl := ∀ (#0 = #0).
Definition eq_sym := ∀∀ (#1 = #0 -> #0 = #1).
Definition eq_trans := ∀∀∀ (#2 = #1 /\ #1 = #0 -> #2 = #0).
Definition compat_left := ∀∀∀ (#2 = #1 /\ #2 ∈ #0 -> #1 ∈ #0).
Definition compat_right := ∀∀∀ (#2 ∈ #1 /\ #1 = #0 -> #2 ∈ #0).

Definition ext := ∀∀ ((∀ #0 ∈ #2 <-> #0 ∈ #1) -> #1 = #0).
Definition pairing := ∀∀∃∀ (#0 ∈ #1 <-> #0 = #3 \/ #0 = #2).
Definition union := ∀∃∀ (#0 ∈ #1 <-> ∃ (#0 ∈ #3 /\ #1 ∈ #0)).
Definition powerset := ∀∃∀ (#0 ∈ #1 <-> ∀ (#0 ∈ #1 -> #0 ∈ #3)).
Definition infinity := ∃ ((∃ (#0 ∈ #1 /\ zero (#0)))
                         /\ ∀ (#0 ∈ #1 -> (∃ (#0 ∈ #2 /\ succ (#1) (#0))))).

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
       ∃∀ (#0 ∈ #2 -> ∃ (#0 ∈ #2 /\ lift 2 A))).

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

Lemma WCAx A : IsAx A -> WC ZFSign A.
Proof.
 intros [ IN | [ (B & -> & HB & HB') | (C & -> & HC & HC') ] ].
 - apply wc_iff. revert A IN. now apply forallb_forall.
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
     cbn. now rewrite fclosed_lift, HB'.
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
     cbn. now rewrite !fclosed_lift, HC'.
Qed.

End ZFAx.

Definition ZF :=
 {| sign := ZFSign;
    IsAxiom := ZFAx.IsAx;
    WCAxiom := ZFAx.WCAx |}.

Import ZFAx.

Local Open Scope formula_scope.

Lemma emptyset : IsTheorem J ZF (∃∀ ~(#0 ∈ #1)).
Proof.
  thm.
  exists [infinity].
  split; auto.
  - simpl. constructor; auto.
    unfold IsAx. left. calc.
  - apply R'_Ex_e with (x := "a").
    + calc.
    + cbn.
      apply R'_And_e.
      apply Pr_swap, Pr_pop.
      apply R'_Ex_e with (x := "x").
      * calc.
      * cbn.
        apply R'_And_e.
        apply Pr_pop.
        apply R_Ex_i with (t := FVar "x"). cbn.
        apply R'_Ax.
Qed.

Lemma singleton : IsTheorem J ZF (∀∃∀ (#0 ∈ #1 <-> #0 = #2)).
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

Lemma unionset : IsTheorem J ZF (∀∀∃∀ (#0 ∈ #1 <-> #0 ∈ #3 \/ #0 ∈ #2)).
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
           ++ inst_axiom compat_right [ x; y; A ]. 
           ++ apply R_And_i; apply R_Ax; calc.
        -- apply R_Or_i2.
           apply R_Imp_e with (A := x ∈ y /\ y = B).
           ++ inst_axiom compat_right [ x; y; B ].
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

Lemma Succ : IsTheorem J ZF
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
  
Lemma Successor : IsTheorem J ZF (∀∃ succ (#1) (#0)).
Proof.
  apply ModusPonens with (A := ∀∀∃∀ #0 ∈ #1 <-> #0 ∈ #3 \/ #0 ∈ #2); [ | apply unionset ].
  apply ModusPonens with (A := ∀∃∀ #0 ∈ #1 <-> #0 = #2); [ apply Succ | apply singleton ].
Qed.


Close Scope formula_scope.

(** A "model" for ZF, using Benjamin Werner's ZFC contrib *)

Require Import ChoiceFacts.
Require Import zfc.

(* Some complements about ZFC, in a more modern way *)

Lemma EXType_exists {X:Type}(P : X -> Prop) :
 EXType X P <-> exists x, P x.
Proof.
 split; intros (x,p); exists x; trivial.
Qed.

Instance EQ_equiv : Equivalence EQ.
Proof.
 split. exact EQ_refl. exact EQ_sym. exact EQ_tran.
Qed.

Instance IN_m : Proper (EQ ==> EQ ==> iff) IN.
Proof.
 assert (forall x x' y y', EQ x x' -> EQ y y' -> IN x y -> IN x' y').
 { intros.
   apply IN_sound_left with x. easy.
   apply IN_sound_right with y; easy. }
 intros x x' Hx y y' Hy. split; now apply H.
Qed.

Instance Paire_m : Proper (EQ ==> EQ ==> EQ) Paire.
Proof.
 intros x x' Hx y y' Hy.
 transitivity (Paire x y').
 now apply Paire_sound_right.
 now apply Paire_sound_left.
Qed.

Instance Sing_m : Proper (EQ ==> EQ) Sing.
Proof.
 exact Sing_sound.
Qed.

Instance Union_m : Proper (EQ ==> EQ) Union.
Proof.
 exact Union_sound.
Qed.

Instance Succ_m : Proper (EQ ==> EQ) Succ.
Proof.
 unfold Succ. intros x x' H. now rewrite H.
Qed.

Lemma Vide_spec x : ~IN x Vide.
Proof.
 intro H. destruct (Vide_est_vide _ H).
Qed.

Lemma Paire_spec a b x :
 IN x (Paire a b) <-> EQ x a \/ EQ x b.
Proof.
 split.
 - apply Paire_IN.
 - intros [<-|<-]. apply IN_Paire_left. apply IN_Paire_right.
Qed.

Lemma Sing_spec a x : IN x (Sing a) <-> EQ x a.
Proof.
 unfold Sing. rewrite Paire_spec. intuition.
Qed.

Lemma Union_spec a x : IN x (Union a) <-> exists y, IN y a /\ IN x y.
Proof.
 split.
 - intros H. apply Union_IN in H. destruct H as (y & H & H').
   now exists y.
 - intros (y & H & H'). eapply IN_Union; eauto.
Qed.

Lemma Power_spec a x : IN x (Power a) <-> INC x a.
Proof.
 split. apply IN_Power_INC. apply INC_IN_Power.
Qed.

Lemma Succ_spec a x : IN x (Succ a) <-> EQ x a \/ IN x a.
Proof.
 split.
 - intros H. destruct (IN_Succ_or _ _ H). now left. now right.
 - intros [->|H]. apply IN_Succ. now apply INC_Succ.
Qed.

Lemma Omega_spec :
  (exists x, IN x Omega /\ forall y, ~ IN y x) /\
  (forall x, IN x Omega -> exists y, IN y Omega /\
                                     forall z, IN z y <-> EQ z x \/ IN z x).
Proof.
 split.
 - exists Vide; split; try apply Vide_spec.
   apply (Nat_IN_Omega 0).
 - intros x Hx. exists (Succ x); split; try apply Succ_spec.
   destruct (IN_Omega_EXType _ Hx) as (n & <-).
   apply (Nat_IN_Omega (S n)).
Qed.

Lemma Comp_spec (P:Ens->Prop) :
 (Proper (EQ==>iff) P) ->
 forall a x, IN x (Comp a P) <-> IN x a /\ P x.
Proof.
 intros HP a x.
 assert (E : forall u v, P u -> EQ u v -> P v) by now intros ? ? ? <-.
 split.
 - intros H. split. revert H. apply Comp_INC. eapply IN_Comp_P; eauto.
 - intros (H,H'). apply IN_P_Comp; auto.
Qed.

Definition zfc_exists_uniq (P:Ens->Prop) :=
 exists x, P x /\ forall y, P y -> EQ y x.

Definition miquel_replacement :=
 forall (P:Ens->Ens->Prop), Proper (EQ==>EQ==>iff) P ->
 forall a,
  (forall x, IN x a -> zfc_exists_uniq (P x)) ->
  exists b,
    forall x, IN x a -> exists y, IN y b /\ P x y.

Lemma replacement_alt : zfc.replacement -> miquel_replacement.
Proof.
intros R P HP a EXU.
set (Q := fun x y => IN x a /\ P x y).
assert (HQ1 : functional Q).
{ intros x y y' (Hx,Hy) (_,Hy').
  destruct (EXU x Hx) as (z & _ & Hz).
  transitivity z. now apply Hz. symmetry. now apply Hz. }
assert (HQ2 : forall x y y', EQ y y' -> Q x y -> Q x y').
{ intros x y y' E (H,H'). split; auto. now rewrite <-E. }
assert (HQ3 : forall x x' y, EQ x x' -> Q x y -> Q x' y).
{ intros x x' y E (H,H'). split; now rewrite <-E. }
destruct (R Q HQ1 HQ2 HQ3 a) as (b & Hb). clear HQ1 HQ2 HQ3.
exists b.
intros x Hx.
destruct (EXU x Hx) as (y & Hy & _).
exists y; split; auto. apply Hb. now exists x.
Qed.

(** Reverse statement. Not reused below, but good to know.
    The proof is an adaptation of zfc.classical_Collection_Replacement *)
Lemma replacement_recip :
 (forall A, A\/~A) -> miquel_replacement -> zfc.replacement.
Proof.
 intros EM R P HP1 HP2 HP3.
 assert (HP : Proper (EQ==>EQ==>iff) P).
 { intros x x' Hx y y' Hy. split; intros.
   apply HP2 with y; auto. apply HP3 with x; auto.
   apply HP2 with y'; try easy. apply HP3 with x'; easy. }
 cut (forall a, exists b, forall y, (exists x, IN x a /\ P x y) -> IN y b).
 { intros H a.
   destruct (H a) as (b & Hb).
   set (A := fun y => exists x, IN x a /\ P x y).
   exists (Comp b A).
   intros y. rewrite Comp_spec. split.
   - intros (U,(x & Hx & Hx')). now exists x.
   - intros (x & Hx & Hx'). split. apply Hb. now exists x. now exists x.
   - intros z z' Hz. unfold A. split.
     intros (x & Hx & Hx'). exists x. split; auto. eapply HP2; eauto.
     intros (x & Hx & Hx'). exists x. split; auto. eapply HP2; eauto.
     easy. }
 set (Q := fun x y => P x y \/ (forall y, ~P x y) /\ EQ y Vide).
 assert (HQ : Proper (EQ ==> EQ ==> iff) Q).
 { intros x x' Hx y y' Hy. unfold Q. rewrite Hx, Hy.
   now setoid_rewrite Hx. }
 intros a. destruct (R Q HQ a) as (b, Hb).
 { intros x Hx.
   destruct (EM (exists y, P x y)) as [(y,Hy)|N].
   - exists y. split. now left.
     intros z [H|(H,->)].
     + eauto.
     + destruct (H _ Hy).
   - exists Vide. split. right. split; auto with zfc. firstorder.
     intros y [H|(H,->)]; auto with zfc. firstorder. }
 exists b.
 intros y (x & Hx & Hx').
 destruct (Hb x Hx) as (z & Hz & [Hz'|(Hz',E)]).
 - assert (EQ y z) by eauto. now rewrite H.
 - firstorder.
Qed.


Section Model.
Variable EM : forall A:Prop, A \/ ~A.
Variable Choice : FunctionalChoice. (* from ∀∃ to a ∃ function s.t. ... *)

Lemma Choice' : zfc.choice.
Proof.
 unfold zfc.choice; intros.
 rewrite EXType_exists. apply Choice. intros x.
 rewrite <- EXType_exists. apply H.
Qed.

Definition Replacement : zfc.replacement :=
 classical_Collection_Replacement EM (Choice_Collection Choice').

Definition ZFFuns (f:string) : optnfun Ens Ens := Nop.

Definition ZFPreds (p:string) : optnfun Ens Prop :=
  if p =? "=" then NFun 2 EQ
  else if p =? "∈" then NFun 2 IN
  else Nop.

Lemma ZFFuns_ok s :
 funsymbs ZFSign s = get_arity (ZFFuns s).
Proof.
 reflexivity.
Qed.

Lemma ZFPreds_ok s :
 predsymbs ZFSign s = get_arity (ZFPreds s).
Proof.
 unfold ZFSign, zf_sign, ZFPreds. simpl.
 repeat (case eqbspec; cbn; try easy).
Qed.

Definition preZF : PreModel Ens ZF :=
 {| someone := Vide;
    funs := ZFFuns;
    preds := ZFPreds;
    funsOk := ZFFuns_ok;
    predsOk := ZFPreds_ok |}.

Lemma tinterp_zf_congr G L L' (t:term) :
 (forall k, EQ (nth k L Vide) (nth k L' Vide)) ->
 EQ (tinterp preZF G L t) (tinterp preZF G L' t).
Proof.
 destruct t; cbn -[EQ]; intros; auto with zfc.
Qed.

Lemma finterp_zf_congr G L L' A :
 check ZFSign A = true ->
 (forall k, EQ (nth k L Vide) (nth k L' Vide)) ->
 finterp preZF G L A <-> finterp preZF G L' A.
Proof.
 revert L L'.
 induction A; cbn -[EQ]; intros L L' C E; try easy.
 - revert C. unfold ZFPreds. unfold predicate_symbol, name in *.
   case eqbspec; intros.
   + rewrite lazy_andb_iff in C. destruct C as (C,_).
     destruct l as [|a [|b [|c l]]]; try easy. cbn.
     f_equiv; apply tinterp_zf_congr; auto.
   + revert C.
     case eqbspec; intros; try easy.
     rewrite lazy_andb_iff in C. destruct C as (C,_).
     destruct l as [|a [|b [|c l]]]; try easy. cbn.
     f_equiv; apply tinterp_zf_congr; auto.
 - f_equiv. auto.
 - rewrite lazy_andb_iff in C. destruct C as (C1,C2). f_equiv; auto.
 - apply interp_quant. intros m. apply IHA; auto.
   intros [|k]; cbn -[EQ]; auto with zfc.
Qed.

Lemma ZFAxOk A : IsAxiom ZF A -> forall G, finterp preZF G [] A.
Proof.
 unfold ZF. simpl.
 unfold ZFAx.IsAx.
 intros [HA|[(B & -> & CK & CL)|(B & -> & CK & CL)]].
 - unfold axioms_list in HA.
   simpl in HA; intuition; subst; cbn -[EQ IN].
   + exact EQ_refl.
   + exact EQ_sym.
   + intros x y z (H,H'). now apply EQ_tran with y.
   + intros y x' x (H,H'). now rewrite <- H.
   + intros y' y x (H,H'). now rewrite <- H'.
   + (* ext *) intros a b E. apply INC_EQ; intro x; apply E.
   + intros a b. exists (Paire a b). apply Paire_spec.
   + intros a. exists (Union a). apply Union_spec.
   + intros a. exists (Power a). apply Power_spec.
   + exists Omega. apply Omega_spec.
 - (* separation *)
   intros G.
   unfold separation_schema.
   apply interp_nforall. intros stk Len. rewrite app_nil_r. cbn.
   setoid_rewrite finterp_lift. cbn.
   intros a.
   set (A := fun x => finterp preZF G (x :: a :: stk) B).
   exists (Comp a A). apply Comp_spec.
   { intros u v E. apply finterp_zf_congr; auto.
     destruct k; cbn -[EQ]; auto with zfc. }
 - (* replacement *)
   intros G. unfold replacement_schema.
   apply interp_nforall. intros stk Len. rewrite app_nil_r.
   cbn -[exists_uniq].
   setoid_rewrite finterp_lift. cbn -[exists_uniq].
   intros a Ha.
   apply replacement_alt.
   + apply Replacement.
   + intros x x' Hx y y' Hy. apply finterp_zf_congr; auto.
     destruct k as [|[|?]]; cbn -[EQ]; auto with zfc.
   + intros x Hx. destruct (Ha x Hx) as (y,Hy). exists y.
     cbn -[EQ] in Hy. now setoid_rewrite finterp_lift in Hy.
Qed.

Definition ZFModel : Model Ens ZF :=
 {| pre := preZF;
    AxOk := ZFAxOk |}.

End Model.

(*
Print Assumptions ZFModel.
Print ZFModel.
*)
