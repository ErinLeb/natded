
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

Lemma Symmetry : forall logic A B Γ, BClosed A /\ BClosed B /\ In ax2 Γ /\ Pr logic (Γ ⊢ A = B) -> Pr logic (Γ ⊢ B = A).
Proof.
  intros.
  destruct H. destruct H0. destruct H1.
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

(** Some basic proofs in Peano arithmetics. *)

Lemma ZeroRight : IsTheorem Intuiti PeanoTheory (∀ (#0 = #0 + Zero)).
Proof.
  unfold IsTheorem.
  split.
  + unfold Wf. split; [ auto | split; auto ].
  + exists ((PeanoAx.induction_schema (#0 = #0 + Zero))::axioms_list).
    split.
    - apply Forall_forall. intros. destruct H.
      * simpl. unfold IsAx. right. exists (#0 = #0 + Zero). split; [ auto | split ; [ auto | auto ] ].
      * simpl. unfold IsAx. left. exact H.
    - apply R_Imp_e with (A := (nForall (Nat.pred (level (# 0 = # 0 + Zero)))
       ((∀ bsubst 0 Zero (# 0 = # 0 + Zero)) /\
        (∀ # 0 = # 0 + Zero -> bsubst 0 (Succ (# 0)) (# 0 = # 0 + Zero))))).
      * apply R_Ax. unfold induction_schema. apply in_eq.
      * simpl. apply R_And_i. cbn. change (Fun "O" []) with Zero. apply R_All_i with (x := "x").
        ++ compute. inversion 1. (* ATROCE *)
        ++ cbn. change (Fun "O" []) with Zero. eapply R_Imp_e. set (hyp := (_ -> _)%form).
           assert ( sym : Pr Intuiti (hyp::axioms_list ⊢ ∀∀ (#1 = #0 -> #0 = #1))).
           { apply R_Ax. compute; intuition. }
           apply R_All_e with (t := Zero + Zero) in sym. cbn in sym. apply R_All_e with (t := Zero) in sym. cbn in sym. exact sym.
           -- reflexivity.
           -- reflexivity.
           -- set (hyp := (_ -> _)%form). change (Fun "O" []) with Zero. change (Zero + Zero = Zero) with (bsubst 0 Zero (Zero + #0 = #0)). apply R_All_e. reflexivity. apply R_Ax. compute; intuition.
       ++ cbn. change (Fun "O" []) with Zero. apply R_All_i with (x := "y").
          -- compute. inversion 1.
          -- cbn. change (Fun "O" []) with Zero. apply R_Imp_i. set (H1 := FVar _ = _). set (H2 := _ -> _).
             assert (hyp : Pr Intuiti (H1 :: H2 :: axioms_list ⊢ Fun "S" [FVar "y"] = Fun "S" [FVar "y" + Zero] /\ Fun "S" [FVar "y" + Zero] = Fun "S" [FVar "y"] + Zero)).
             { apply R_And_i.
               + assert (AX4 : Pr Intuiti (H1 :: H2 :: axioms_list ⊢ ax4)). { apply R_Ax. compute; intuition. } apply R_Imp_e with (A := (FVar "y" = FVar "y" + Zero)%form); [ | apply R_Ax; compute; intuition ]. unfold ax4 in AX4. apply R_All_e with (t := FVar "y") in AX4; [ | auto ]. apply R_All_e with (t := FVar "y" + Zero) in AX4; [ | auto ]. cbn in AX4. exact AX4. 
             + apply R_Imp_e with (A := Fun "S" [FVar "y"] + Zero = Fun "S" [FVar "y" + Zero]).
               - assert (AX2 : Pr Intuiti (H1 :: H2 :: axioms_list ⊢ ax2)). { apply R_Ax. compute; intuition. } unfold ax2 in AX2. apply R_All_e with (t := Fun "S" [FVar "y"] + Zero) in AX2; [ | auto ]. apply R_All_e with (t := Fun "S" [FVar "y" + Zero]) in AX2; [ | auto ]. cbn in AX2. exact AX2.
               - assert (AX10 : Pr Intuiti (H1 :: H2 :: axioms_list ⊢ ax10)). { apply R_Ax. compute; intuition. } unfold ax10 in AX10. apply R_All_e with (t:= FVar "y") in AX10; [ | auto ]. apply R_All_e with (t := Zero) in AX10; [ | auto ]. cbn in AX10. exact AX10. }
             apply R_Imp_e with (A :=  Fun "S" [FVar "y"] = Fun "S" [FVar "y" + Zero] /\ Fun "S" [FVar "y" + Zero] = Fun "S" [FVar "y"] + Zero).
             ** assert (AX3 : Pr Intuiti (H1 :: H2 :: axioms_list ⊢ ax3)). { apply R_Ax. compute; intuition. } unfold ax3 in AX3. apply R_All_e with (t:= Fun "S" [FVar "y"]) in AX3; [ | auto ]. apply R_All_e with (t := Fun "S" [FVar "y" + Zero]) in AX3; [ | auto ]. apply R_All_e with (t := Fun "S" [FVar "y"] + Zero) in AX3; [ | auto ]. cbn in AX3. exact AX3.
             ** exact hyp.
Qed.

Lemma SuccRight : IsTheorem Intuiti PeanoTheory (∀∀ (Succ(#1 + #0) = #1 + Succ(#0))).
Proof.
  unfold IsTheorem.
  split.
  + unfold Wf. split; [ auto | split; auto ].
  + exists (induction_schema ( ∀ Succ (#1 + #0) = (#1 + Succ (#0)) ) :: axioms_list).
    split.
    - apply Forall_forall. intros. destruct H.
      * simpl. unfold IsAx. right. exists (∀ Succ (#1 + #0) = #1 + Succ (#0)). split; [ auto | split; [ auto | auto ]].
      * simpl. unfold IsAx. left. assumption.
    - apply R_Imp_e with ( A:= nForall (Nat.pred (level (∀ Succ (# 1 + # 0) = # 1 + Succ (# 0))))
       ((∀ bsubst 0 Zero (∀ Succ (# 1 + # 0) = # 1 + Succ (# 0))) /\
        (∀ (∀ Succ (# 1 + # 0) = # 1 + Succ (# 0)) ->
           bsubst 0 (Succ (# 0)) (∀ Succ (# 1 + # 0) = # 1 + Succ (# 0))))).
      * apply R_Ax. unfold induction_schema. apply in_eq.
      * simpl. apply R_And_i.
        ++ compute. change (Fun "O" []) with Zero.
           apply R_All_i with (x := "x"); [ | compute; change (Fun "O" []) with Zero ].
           -- unfold Names.In. compute. inversion 1.
           -- apply R_All_i with (x := "y"); [ compute; inversion 1 | ]. compute. change (Fun "O" []) with Zero. set (Γ := [(∀ ∀ Fun "S" [Zero + # 0] = Zero + Fun "S" [# 0]) /\
      (∀ (∀ Fun "S" [# 1 + # 0] = # 1 + Fun "S" [# 0]) ->
         ∀ Fun "S" [Fun "S" [# 1] + # 0] = Fun "S" [# 1] + Fun "S" [# 0]) ->
      ∀ ∀ Fun "S" [# 1 + # 0] = # 1 + Fun "S" [# 0]; ∀ # 0 = # 0; ∀ ∀ 
     # 1 = # 0 -> # 0 = # 1; ∀ ∀ ∀ # 2 = # 1 /\ # 1 = # 0 -> # 2 = # 0;
     ∀ ∀ # 1 = # 0 -> Fun "S" [# 1] = Fun "S" [# 0]; ∀ ∀ ∀ # 2 = # 1 -> # 2 + # 0 = # 1 + # 0;
     ∀ ∀ ∀ # 1 = # 0 -> # 2 + # 1 = # 2 + # 0; ∀ ∀ ∀ # 2 = # 1 -> # 2 * # 0 = # 1 * # 0;
     ∀ ∀ ∀ # 1 = # 0 -> # 2 * # 1 = # 2 * # 0; ∀ Zero + # 0 = # 0;
     ∀ ∀ Fun "S" [# 1] + # 0 = Fun "S" [# 1 + # 0]; ∀ Zero * # 0 = Zero;
     ∀ ∀ Fun "S" [# 1] * # 0 = # 1 * # 0 + # 0; ∀ ∀ Fun "S" [# 1] = Fun "S" [# 0] -> # 1 = # 0;
     ∀ ~ Fun "S" [# 0] = Zero]).  assert (Pr Intuiti (Γ ⊢ Zero + FVar "y" = FVar "y")). 
              { assert (AX9 : Pr Intuiti (Γ ⊢ ax9)). { apply R_Ax. compute; intuition. }
                unfold ax9 in AX9.
                apply R_All_e with (t := FVar "y") in AX9; [ | auto ].
                compute in AX9. assumption. }
              Print bsubst. apply 
           
Lemma Comm : IsTheorem Intuiti PeanoTheory (∀∀ (#0 + #1 = #1 + #0)).
Admitted.

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
