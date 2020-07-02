
(** * The Theory of Peano Arithmetic and its Coq model *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Meta Theories PreModels Models.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

(** The Peano axioms *)

Definition PeanoSign := Finite.to_infinite peano_sign.

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
Definition ax11 := ∀ (Zero * #0 = Zero).
Definition ax12 := ∀∀ (Succ(#1) * #0 = (#1 * #0) + #0).

Definition ax13 := ∀∀ (Succ(#1) = Succ(#0) -> #1 = #0).
Definition ax14 := ∀ ~(Succ(#0) = Zero).

Definition axioms_list :=
 [ ax1; ax2; ax3; ax4; ax5; ax6; ax7; ax8;
    ax9; ax10; ax11; ax12; ax13; ax14 ].

(** Beware, [bsubst] is ok below for turning [#0] into [Succ #0], but
    only since it contains now a [lift] of substituted terms inside
    quantifiers.
    And the unconventional [∀] before [A[0]] is to get the right
    bounded vars (Hack !). *)

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

(** Useful lemmas so as to be able to write proofs that take less than 1000 lines. *)

Import PeanoAx.

Lemma Symmetry : forall logic A B Γ, BClosed A -> BClosed B -> In ax2 Γ -> Pr logic (Γ ⊢ A = B) -> Pr logic (Γ ⊢ B = A).
Proof.
  intros.
  apply R_Imp_e with (A := A = B); [ | assumption ].
  assert (AX2 : Pr logic (Γ ⊢ ax2)).
  { apply R_Ax. exact H1. }
  unfold ax2 in AX2.
  apply R_All_e with (t := A) in AX2; [ | assumption ].
  apply R_All_e with (t := B) in AX2; [ | assumption ].
  cbn in AX2.
  assert (bsubst 0 B (lift A) = A).
  { assert (lift A = A). { apply lift_nop. exact H. } rewrite H3. apply bclosed_bsubst_id. exact H. }
  rewrite H3 in AX2.
  exact AX2.
Qed.

Lemma Transitivity : forall logic A B C Γ, BClosed A -> BClosed B -> BClosed C -> In ax3 Γ -> Pr logic (Γ ⊢ A = B) -> Pr logic (Γ ⊢ B = C) -> Pr logic (Γ ⊢ A = C).
Proof.
  intros.
  apply R_Imp_e with (A := A = B /\ B = C); [ | apply R_And_i; assumption ].
  assert (AX3 : Pr logic (Γ ⊢ ax3)).
  { apply R_Ax. exact H2. }
  unfold ax3 in AX3.
  apply R_All_e with (t := A) in AX3; [ | assumption ].
  apply R_All_e with (t := B) in AX3; [ | assumption ].
  apply R_All_e with (t := C) in AX3; [ | assumption ].
  cbn in AX3.
  assert (bsubst 0 C (lift B) = B).
  { assert (lift B = B). {apply lift_nop. assumption. } rewrite H5. apply bclosed_bsubst_id. assumption. }
  rewrite H5 in AX3.
  assert (bsubst 0 C (bsubst 1 (lift B) (lift (lift A))) = A).
  { assert (lift A = A). { apply lift_nop. assumption. } rewrite H6. rewrite H6.
    assert (lift B = B). { apply lift_nop. assumption. } rewrite H7.
    assert (bsubst 1 B A = A). { apply bclosed_bsubst_id. assumption. } rewrite H8.
    apply bclosed_bsubst_id. assumption. }
  rewrite H6 in AX3.
  assumption.
Qed.

Lemma Hereditarity : forall logic A B Γ, BClosed A -> BClosed B -> In ax4 Γ -> Pr logic (Γ ⊢ A = B) -> Pr logic (Γ ⊢ Succ A = Succ B).
Proof.
  intros.
  apply R_Imp_e with (A := A = B); [ | assumption ].
  assert (AX4 : Pr logic (Γ ⊢ ax4)).
  { apply R_Ax. assumption. }
  unfold ax4 in AX4.
  apply R_All_e with (t := A) in AX4; [ | assumption ].
  apply R_All_e with (t := B) in AX4; [ | assumption ].
  cbn in AX4.
  assert (bsubst 0 B (lift A) = A).
  { assert (lift A = A). { apply lift_nop. assumption. } rewrite H3.
    apply bclosed_bsubst_id. assumption. }
  rewrite H3 in AX4.
  assumption.
Qed.

Lemma AntiHereditarity : forall logic A B Γ, BClosed A -> BClosed B -> In ax13 Γ -> Pr logic (Γ ⊢ Succ A = Succ B) -> Pr logic (Γ ⊢ A = B).
Proof.
  intros.
  apply R_Imp_e with (A := Succ A = Succ B); [ | assumption ].
  assert (AX13 : Pr logic (Γ ⊢ ax13)).
  { apply R_Ax. assumption. }
  unfold ax13 in AX13.
  apply R_All_e with (t := A) in AX13; [ | assumption ].
  apply R_All_e with (t := B) in AX13; [ | assumption ].
  cbn in AX13.
  assert (bsubst 0 B (lift A) = A).
  { assert (lift A = A). { apply lift_nop. assumption. } rewrite H3.
    apply bclosed_bsubst_id. assumption. }
  rewrite H3 in AX13.
  assumption.
Qed.

Ltac axiom ax name :=
  match goal with
    | |- Pr ?l (?ctx ⊢ _) => assert (name : Pr l (ctx ⊢ ax)); [ apply R_Ax; compute; intuition | ]; unfold ax in name
  end.

Ltac app_R_All_i t := apply R_All_i with (x := t); [ rewrite<- Names.mem_spec; now compute | ].
Ltac eapp_R_All_i := eapply R_All_i; [ rewrite<- Names.mem_spec; now compute | ].

Ltac sym := apply Symmetry; [ auto | auto | compute; intuition | ].

Ltac ahered := apply Hereditarity; [ auto | auto | compute; intuition | ].

Ltac hered := apply AntiHereditarity; [ auto | auto | compute; intuition | ].

Ltac trans b := apply Transitivity with (B := b); [ auto | auto | auto | compute; intuition | | ].

Ltac thm := unfold IsTheorem; split; [ unfold Wf; split; [ auto | split; auto ] | ].

Ltac change_succ :=
  match goal with
  | |- context[ Fun "S" [?t] ] => change (Fun "S" [t]) with (Succ (t)); change_succ
  | _ => idtac
  end.

Ltac cbm := cbn; change (Fun "O" []) with Zero; change_succ.

Ltac parse term :=
  match term with
  | (_ -> ?queue)%form => parse queue
  | (∀ ?formula)%form => formula
  end.

Ltac rec :=
  match goal with
  | |- exists axs, (Forall (IsAxiom PeanoTheory) axs /\ Pr ?l (axs ⊢ ?A))%type => 
    let form := parse A in  
    exists (induction_schema form :: axioms_list); set (Γ := induction_schema form :: axioms_list); set (rec := induction_schema form); split;
      [ apply Forall_forall; intros x H; destruct H;
        [ simpl; unfold IsAx; right; exists form ; split;
          [ auto | split; [ auto | auto ]] | 
          simpl; unfold IsAx; left; assumption ] |
        repeat apply R_Imp_i;
        eapply R_Imp_e;
        [ apply R_Ax; unfold induction_schema; cbm; intuition | simpl; apply R_And_i; cbn ]
      ]; cbm
    (* | _ => idtac *)
  end.

            
(** Some basic proofs in Peano arithmetics. *)

Lemma ZeroRight : IsTheorem Intuiti PeanoTheory (∀ (#0 = #0 + Zero)).
Proof.
 thm.
 rec.
 + app_R_All_i "y". cbm.
   sym.
   axiom ax9 AX9.
   apply R_All_e with (t := Zero) in AX9; auto.
 + app_R_All_i "y". cbm.
   apply R_Imp_i. set (H1 := FVar _ = _).
   sym.
   trans (Succ ((FVar "y") + Zero)).
   - axiom ax10 AX10.
     apply R_All_e with (t := FVar "y") in AX10; auto.
     apply R_All_e with (t := Zero) in AX10; auto.
   - ahered.
     sym.
     apply R_Ax.
     apply in_eq.
Qed.

Lemma SuccRight : IsTheorem Intuiti PeanoTheory (∀∀ (Succ(#1 + #0) = #1 + Succ(#0))).
Proof.
  thm.
  rec.
  + app_R_All_i "x".
    app_R_All_i "y".
    cbm.
    sym.
    trans (Succ (FVar "y")).
    - axiom ax9 AX9.
      apply R_All_e with (t := Succ (FVar "y")) in AX9; auto.
    - ahered.
      sym.
      axiom ax9 AX9.
      apply R_All_e with (t := FVar "y") in AX9; auto.
  + app_R_All_i "x".
    cbm.
    apply R_Imp_i.
    app_R_All_i "y".
    cbm.
    set (hyp := ∀ Succ _ = _).
    trans (Succ (Succ (FVar "x" + FVar "y"))).
    - ahered.
      axiom ax10 AX10.
      apply R_All_e with (t := FVar "x") in AX10; auto.
      apply R_All_e with (t := FVar "y") in AX10; auto.
    - trans (Succ (FVar "x" + Succ (FVar "y"))).
      * ahered.
        axiom hyp Hyp.
        apply R_All_e with (t := FVar "y") in Hyp; auto.
      * axiom ax10 AX10.
        sym.
        apply R_All_e with (t := FVar "x") in AX10; auto.
        apply R_All_e with (t := Succ (FVar "y")) in AX10; auto.
Qed.
 
Lemma Comm :
  IsTheorem Intuiti PeanoTheory
            ((∀ #0 = #0 + Zero) -> (∀∀ Succ(#1 + #0) = #1 + Succ(#0)) ->
               (∀∀ #0 + #1 = #1 + #0)).
Proof.
  thm.
  rec; set (Γ' := _ :: _ :: Γ).
  + app_R_All_i "x".
    cbm.
    app_R_All_i "x".
    cbm.
    trans (FVar "x").
    - sym.
      assert (Pr Intuiti (Γ' ⊢ ∀ # 0 = # 0 + Zero)). { apply R_Ax. simpl in *; intuition. }
      apply R_All_e with (t := FVar "x") in H; auto.
    - sym.
      axiom ax9 AX9.
      apply R_All_e with (t := FVar "x") in AX9; auto.
  + app_R_All_i "y".
    cbm.
    apply R_Imp_i.
    app_R_All_i "x".
    cbm.
    trans (Succ (FVar "x" + FVar "y")).
    - sym.
      assert (Pr Intuiti ((∀ # 0 + FVar "y" = FVar "y" + # 0) :: Γ' ⊢ ∀ ∀ Succ (#1 + #0) = #1 + Succ (#0))). { apply R_Ax. simpl in *; intuition. }
      apply R_All_e with (t := FVar "x") in H; auto.
      apply R_All_e with (t := FVar "y") in H; auto.
    - trans (Succ (FVar "y" + FVar "x")).
      * ahered.
        assert (Pr Intuiti ((∀ #0 + FVar "y" = FVar "y" + #0) :: Γ' ⊢ ∀ #0 + FVar "y" = FVar "y" + #0)). { apply R_Ax. apply in_eq. }
                                                                                                           apply R_All_e with (t := FVar "x") in H; auto.
      * sym.
        axiom ax10 AX10.
        apply R_All_e with (t := FVar "y") in AX10; auto.
        apply R_All_e with (t := FVar "x") in AX10; auto.
Qed.

Lemma Commutativity : IsTheorem Intuiti PeanoTheory (∀∀ #0 + #1 = #1 + #0).
Proof.
  apply ModusPonens with (A := (∀∀ Succ(#1 + #0) = #1 + Succ(#0))).
  + apply ModusPonens with (A := ∀ #0 = #0 + Zero).
    * apply Comm.
    * apply ZeroRight.
  + apply SuccRight.
Qed.
      
(** A Coq model of this Peano theory, based on the [nat] type *)

Definition PeanoFuns : modfuns nat :=
  fun f =>
  if f =? "O" then Some (existT _ 0 0)
  else if f =? "S" then Some (existT _ 1 S)
  else if f =? "+" then Some (existT _ 2 Nat.add)
  else if f =? "*" then Some (existT _ 2 Nat.mul)
  else None.

Definition PeanoPreds : modpreds nat :=
  fun p =>
  if p =? "=" then Some (existT _ 2 (@Logic.eq nat))
  else None.

Lemma PeanoFuns_ok s :
 funsymbs PeanoSign s = get_arity (PeanoFuns s).
Proof.
 unfold PeanoSign, peano_sign, PeanoFuns. simpl.
 unfold eqb, eqb_inst_string.
 repeat (case string_eqb; auto).
Qed.

Lemma PeanoPreds_ok s :
 predsymbs PeanoSign s = get_arity (PeanoPreds s).
Proof.
 unfold PeanoSign, peano_sign, PeanoPreds. simpl.
 unfold eqb, eqb_inst_string.
 case string_eqb; auto.
Qed.

Definition PeanoPreModel : PreModel nat PeanoTheory :=
 {| someone := 0;
    funs := PeanoFuns;
    preds := PeanoPreds;
    funsOk := PeanoFuns_ok;
    predsOk := PeanoPreds_ok |}.

Lemma PeanoAxOk A :
  IsAxiom PeanoTheory A ->
  forall genv, interp_form PeanoPreModel genv [] A.
Proof.
 unfold PeanoTheory. simpl.
 unfold PeanoAx.IsAx.
 intros [IN|(B & -> & CK & CL)].
 - compute in IN. intuition; subst; cbn; intros; subst; omega.
 - intros genv.
   unfold PeanoAx.induction_schema.
   apply interp_nforall.
   intros stk Len. rewrite app_nil_r. cbn.
   intros (Base,Step).
   (* The Peano induction emulated by a Coq induction :-) *)
   induction m.
   + specialize (Base 0).
     apply -> interp_form_bsubst_gen in Base; simpl; eauto.
   + apply Step in IHm.
     apply -> interp_form_bsubst_gen in IHm; simpl; eauto.
     now intros [|k].
Qed.

Definition PeanoModel : Model nat PeanoTheory :=
 {| pre := PeanoPreModel;
    AxOk := PeanoAxOk |}.
