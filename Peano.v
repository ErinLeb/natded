
(** * The Theory of Peano Arithmetic and its Coq model *)

(** The NatDed development, Pierre Letouzey, Samuel Ben Hamou, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Meta Toolbox.
Require Import Wellformed Theories Nary PreModels Models.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

(** The Peano axioms *)

Definition PeanoSign := Finite.to_infinite peano_sign.

Notation Zero := (Fun "O" []).
Notation Succ x := (Fun "S" [x]).

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

Lemma WCAx A : IsAx A -> WC PeanoSign A.
Proof.
 intros [ IN | (B & -> & HB & HB')].
 - apply wc_iff. revert A IN. now apply forallb_forall.
 - repeat split; unfold induction_schema; cbn.
   + rewrite nForall_check. cbn.
     rewrite !check_bsubst, HB; auto.
   + red. rewrite nForall_level. cbn.
     assert (level (bsubst 0 Zero B) <= level B).
     { apply level_bsubst'. auto. }
     assert (level (bsubst 0 (Succ(BVar 0)) B) <= level B).
     { apply level_bsubst'. auto. }
     lia.
   + apply nForall_fclosed. rewrite <- form_fclosed_spec in *.
     cbn. now rewrite !fclosed_bsubst, HB'.
Qed.

End PeanoAx.

Local Open Scope formula_scope.

Definition PeanoTheory :=
 {| sign := PeanoSign;
    IsAxiom := PeanoAx.IsAx;
    WCAxiom := PeanoAx.WCAx |}.

(** Useful lemmas so as to be able to write proofs that take less than 1000 lines. *)

Import PeanoAx.

Lemma Symmetry :
  forall logic A B Γ, BClosed A -> In ax2 Γ -> Pr logic (Γ ⊢ A = B) ->
                      Pr logic (Γ ⊢ B = A).
Proof.
  intros.
  apply R_Imp_e with (A := A = B); [ | assumption ].
  assert (AX2 : Pr logic (Γ ⊢ ax2)).
  { apply R_Ax. exact H0. }
  unfold ax2 in AX2.
  apply R_All_e with (t := A) in AX2.
  apply R_All_e with (t := B) in AX2.
  cbn in AX2.
  assert (bsubst 0 B (lift 0 A) = A).
  { assert (lift 0 A = A). { apply lift_nop. exact H. } rewrite H2. apply bclosed_bsubst_id. exact H. }
  rewrite H2 in AX2.
  exact AX2.
Qed.

Lemma Transitivity :
  forall logic A B C Γ, BClosed A -> BClosed B -> In ax3 Γ ->
                        Pr logic (Γ ⊢ A = B) -> Pr logic (Γ ⊢ B = C) -> Pr logic (Γ ⊢ A = C).
Proof.
  intros.
  apply R_Imp_e with (A := A = B /\ B = C); [ | apply R_And_i; assumption ].
  assert (AX3 : Pr logic (Γ ⊢ ax3)).
  { apply R_Ax. exact H1. }
  unfold ax3 in AX3.
  apply R_All_e with (t := A) in AX3.
  apply R_All_e with (t := B) in AX3.
  apply R_All_e with (t := C) in AX3.
  cbn in AX3.
  assert (bsubst 0 C (lift 0 B) = B).
  { assert (lift 0 B = B). {apply lift_nop. assumption. } rewrite H4. apply bclosed_bsubst_id. assumption. }
  rewrite H4 in AX3.
  assert (bsubst 0 C (bsubst 1 (lift 0 B) (lift 0 (lift 0 A))) = A).
  { assert (lift 0 A = A). { apply lift_nop. assumption. } rewrite H5. rewrite H5.
    assert (lift 0 B = B). { apply lift_nop. assumption. } rewrite H6.
    assert (bsubst 1 B A = A). { apply bclosed_bsubst_id. assumption. } rewrite H7.
    apply bclosed_bsubst_id. assumption. }
  rewrite H5 in AX3.
  assumption.
Qed.

Lemma Hereditarity :
  forall logic A B Γ, BClosed A -> In ax4 Γ -> Pr logic (Γ ⊢ A = B) ->
                      Pr logic (Γ ⊢ Succ A = Succ B).
Proof.
  intros.
  apply R_Imp_e with (A := A = B); [ | assumption ].
  assert (AX4 : Pr logic (Γ ⊢ ax4)).
  { apply R_Ax. assumption. }
  unfold ax4 in AX4.
  apply R_All_e with (t := A) in AX4.
  apply R_All_e with (t := B) in AX4.
  cbn in AX4.
  assert (bsubst 0 B (lift 0 A) = A).
  { assert (lift 0 A = A). { apply lift_nop. assumption. } rewrite H2.
    apply bclosed_bsubst_id. assumption. }
  rewrite H2 in AX4.
  assumption.
Qed.

Lemma AntiHereditarity :
  forall logic A B Γ, BClosed A -> In ax13 Γ -> Pr logic (Γ ⊢ Succ A = Succ B) ->
                      Pr logic (Γ ⊢ A = B).
Proof.
  intros.
  apply R_Imp_e with (A := Succ A = Succ B); [ | assumption ].
  assert (AX13 : Pr logic (Γ ⊢ ax13)).
  { apply R_Ax. assumption. }
  unfold ax13 in AX13.
  apply R_All_e with (t := A) in AX13.
  apply R_All_e with (t := B) in AX13.
  cbn in AX13.
  assert (bsubst 0 B (lift 0 A) = A).
  { assert (lift 0 A = A). { apply lift_nop. assumption. } rewrite H2.
    apply bclosed_bsubst_id. assumption. }
  rewrite H2 in AX13.
  assumption.
Qed.

Lemma IsAx_adhoc form :
  check PeanoSign form = true ->
  FClosed form ->
  Forall IsAx (induction_schema form ::axioms_list).
Proof.
  intros.
  apply Forall_forall.
  intros x Hx.
  destruct Hx.
  + simpl. unfold IsAx. right. exists form. split; [ auto | split; [ auto | auto ]].
  + simpl. unfold IsAx. left. assumption.
Qed.

Lemma rec0_rule l Γ A_x :
  BClosed (∀ A_x) ->
  In (induction_schema A_x) Γ ->
  Pr l (Γ ⊢ bsubst 0 Zero A_x) ->
  Pr l (Γ ⊢ ∀ (A_x -> bsubst 0 (Succ(#0)) A_x)) ->
  Pr l (Γ ⊢ ∀ A_x).
Proof.
  intros.
  eapply R_Imp_e.
  + apply R_Ax.
    unfold induction_schema in H0.
    unfold BClosed in H.
    cbn in H.
    rewrite H in H0.
    cbn in H0.
    apply H0.
  + simpl.
    apply R_And_i; cbn.
    * set (v := fresh (fvars (Γ ⊢ ∀ bsubst 0 Zero A_x)%form)).
      apply R_All_i with (x:=v).
      apply fresh_ok.
      rewrite form_level_bsubst_id.
      - assumption.
      - now apply level_bsubst, pred_0.
    * assumption.
Qed.

(* And tactics to make the proofs look like natural deduction proofs. *)

Ltac reIff :=
  match goal with
  | |- context [ ((?A -> ?B) /\ _ )%form ] => fold (Iff A B); reIff
  | H : context [ ((?A -> ?B) /\ _ )%form ] |- _ => fold (Iff A B) in H; reIff
  | _ => idtac
  end.

Ltac calc :=
  match goal with
  | |- BClosed _ => reflexivity
  | |- In _ _ => rewrite <- list_mem_in; reflexivity
  | |- ~Names.In _ _ => rewrite<- Names.mem_spec; now compute
  | _ => trivial
  end.

Ltac inst H l :=
  match l with
  | [] => idtac
  | (?u::?l) => apply R_All_e with (t := u) in H; inst H l
  end.

Ltac axiom ax name :=
  match goal with
    | |- Pr ?l (?ctx ⊢ _) =>
      assert (name : Pr l (ctx ⊢ ax)); [ apply R_Ax; calc | ];
      try unfold ax in name
  end.

Ltac inst_axiom ax l :=
 let H := fresh in
 axiom ax H; inst H l; try easy.

Ltac app_R_All_i t v := apply R_All_i with (x := t); calc; cbn; set (v := FVar t); reIff.
Ltac eapp_R_All_i := eapply R_All_i; calc.

Ltac sym := apply Symmetry; calc.

Ltac ahered := apply Hereditarity; calc.

Ltac hered := apply AntiHereditarity; calc.

Ltac trans b := apply Transitivity with (B := b); calc.

Ltac thm := unfold IsTheorem; split; [ now apply wc_iff | ].

Ltac parse term :=
  match term with
  | (_ -> ?queue)%form => parse queue
  | (∀ ?formula)%form => formula
  end.

Ltac rec :=
  match goal with
  | |- exists axs, (Forall (IsAxiom PeanoTheory) axs /\ Pr ?l (axs ⊢ ?A))%type => 
    let form := parse A in  
    exists (induction_schema form :: axioms_list); set (rec := induction_schema form); set (Γ := rec :: axioms_list); split;
      [ apply IsAx_adhoc; auto |
        repeat apply R_Imp_i;
        apply rec0_rule; calc ]; cbn
    (* | _ => idtac *)
  end.

            
(** Some basic proofs in Peano arithmetics. *)

Lemma ZeroRight :
  IsTheorem J PeanoTheory
            (∀ (#0 = #0 + Zero)).
Proof.
 thm.
 rec.
 + sym.
   inst_axiom ax9 [Zero].
 + app_R_All_i "y" y.
   apply R_Imp_i. set (H1 := _ = _).
   sym.
   trans (Succ (y + Zero)).
   - inst_axiom ax10 [y; Zero].
   - ahered.
     sym.
     apply R_Ax.
     apply in_eq.
Qed.

Lemma SuccRight : IsTheorem J PeanoTheory (∀∀ (Succ(#1 + #0) = #1 + Succ(#0))).
Proof.
  thm.
  rec.
  + app_R_All_i "y" y.
    sym.
    trans (Succ y).
    - inst_axiom ax9 [Succ y].
    - ahered.
      sym.
      inst_axiom ax9 [y].
  + app_R_All_i "x" x.
    apply R_Imp_i.
    app_R_All_i "y" y. fold x.
    set (hyp := ∀ Succ _ = _).
    trans (Succ (Succ (x + y))).
    - ahered.
      inst_axiom ax10 [x; y].
    - trans (Succ (x + Succ y)).
      * ahered.
        inst_axiom hyp [y].
      * sym.
        inst_axiom ax10 [x; Succ y].
Qed.

Lemma Comm :
  IsTheorem J PeanoTheory
            ((∀ #0 = #0 + Zero) -> (∀∀ Succ(#1 + #0) = #1 + Succ(#0)) ->
               (∀∀ #0 + #1 = #1 + #0)).
Proof.
  thm.
  rec; set (Γ' := _ :: _ :: Γ).
  + app_R_All_i "x" x.
    trans x.
    - sym.
      assert (Pr J (Γ' ⊢ ∀ # 0 = # 0 + Zero)). { apply R_Ax. calc. }
      apply R_All_e with (t := x) in H; auto.
    - sym.
      inst_axiom ax9 [x].
  + app_R_All_i "y" y.
    apply R_Imp_i.
    app_R_All_i "x" x.
    trans (Succ (x + y)).
    - sym.
      assert (Pr J ((∀ #0 + y = y + #0) :: Γ' ⊢ ∀ ∀ Succ (#1 + #0) = #1 + Succ (#0))). { apply R_Ax. calc. }
      apply R_All_e with (t := x) in H; auto.
      apply R_All_e with (t := y) in H; auto.
    - trans (Succ (y + x)).
      * ahered.
        assert (Pr J ((∀ #0 + y = y + #0) :: Γ' ⊢ ∀ #0 + y = y + #0)). { apply R_Ax. apply in_eq. }
        apply R_All_e with (t := x) in H; auto.
      * sym.
        inst_axiom ax10 [y; x].
Qed.

Lemma Commutativity : IsTheorem J PeanoTheory (∀∀ #0 + #1 = #1 + #0).
Proof.
  apply ModusPonens with (A := (∀∀ Succ(#1 + #0) = #1 + Succ(#0))).
  + apply ModusPonens with (A := ∀ #0 = #0 + Zero).
    * apply Comm.
    * apply ZeroRight.
  + apply SuccRight.
Qed.

Lemma Predecessor : IsTheorem J PeanoTheory (∀ (~#0=Zero -> ∃ Succ(#0) = #1)).
Proof.
 thm.
 rec.
 - apply R_Imp_i.
   apply R_Fa_e.
   eapply R_Not_e; [ | apply R'_Ax].
   now inst_axiom ax1 [Zero].
 - app_R_All_i "x" x.
   apply R_Imp_i.
   apply R_Imp_i.
   apply R_Ex_i with x. now inst_axiom ax1 [Succ(x)].
Qed.

Lemma Middle : IsTheorem J PeanoTheory (∀∃ (#0+#0 = #1 \/ Succ(#0+#0) = #1)).
Proof.
 eapply ModusPonens; [ | exact SuccRight].
 thm.
 set (SR := ∀ _).
 rec.
 - apply R_Ex_i with Zero. cbn.
   apply R_Or_i1. now inst_axiom ax9 [Zero].
 - app_R_All_i "x" x.
   apply R_Imp_i.
   eapply R'_Ex_e with "y". calc. cbn. set (y := FVar "y") in *.
   fold x.
   apply R'_Or_e.
   + apply R_Ex_i with y. cbn. fold x; fold y.
     apply R_Or_i2. ahered. apply R'_Ax.
   + apply R_Ex_i with (Succ y). cbn. fold x; fold y.
     apply R_Or_i1.
     trans (Succ (y+Succ(y))).
     * now inst_axiom ax10 [y;Succ(y)].
     * ahered.
       trans (Succ (y+y)).
       { sym. inst_axiom SR [y;y]. }
       { apply R'_Ax. }
Qed.

(** A Coq model of this Peano theory, based on the [nat] type *)

Definition PeanoFuns : string -> optnfun nat nat :=
  fun f =>
  if f =? "O" then NFun 0 0
  else if f =? "S" then NFun 1 S
  else if f =? "+" then NFun 2 Nat.add
  else if f =? "*" then NFun 2 Nat.mul
  else Nop.

Definition PeanoPreds : string -> optnfun nat Prop :=
  fun p =>
  if p =? "=" then NFun 2 Logic.eq
  else Nop.

Lemma PeanoFuns_ok s :
 funsymbs PeanoSign s = get_arity (PeanoFuns s).
Proof.
 unfold PeanoSign, peano_sign, PeanoFuns. simpl.
 repeat (case eqbspec; auto); congruence.
Qed.

Lemma PeanoPreds_ok s :
 predsymbs PeanoSign s = get_arity (PeanoPreds s).
Proof.
 unfold PeanoSign, peano_sign, PeanoPreds. simpl.
 repeat (case eqbspec; auto); congruence.
Qed.

Definition PeanoPreModel : PreModel nat PeanoTheory :=
 {| someone := 0;
    funs := PeanoFuns;
    preds := PeanoPreds;
    funsOk := PeanoFuns_ok;
    predsOk := PeanoPreds_ok |}.

Lemma PeanoAxOk A :
  IsAxiom PeanoTheory A -> interp PeanoPreModel A.
Proof.
 unfold PeanoTheory. simpl.
 unfold PeanoAx.IsAx.
 intros [IN|(B & -> & CK & CL)] G.
 - compute in IN. intuition; subst; cbn; intros; subst; lia.
 - unfold PeanoAx.induction_schema.
   apply interp_nforall.
   intros stk Len. rewrite app_nil_r. cbn.
   intros (Base,Step).
   (* The Peano induction emulated by a Coq induction :-) *)
   induction m.
   + specialize (Base 0).
     apply -> finterp_bsubst_gen in Base; simpl; eauto.
   + apply Step in IHm.
     apply -> finterp_bsubst_gen in IHm; simpl; eauto.
     now intros [|k].
Qed.

Definition PeanoModel : Model nat PeanoTheory :=
 {| pre := PeanoPreModel;
    AxOk := PeanoAxOk |}.

(** Essais de tactiques faisant de l'unification *)

Definition first_success (f:term->term->option term) :=
 fix first_success l l' :=
 match l, l' with
 | t::l, t'::l' =>
   match f t t' with
   | None => first_success l l'
   | r => r
   end
 | _, _ => None
 end.

Fixpoint get_inst_term n t t' :=
  match t, t' with
  | BVar k, _ => if k =? n then Some t' else None
  | Fun _ l, Fun _ l' => first_success (get_inst_term n) l l'
  | _, _ => None
  end.

Fixpoint get_inst n f f' :=
  match f, f' with
  | Pred _ l, Pred _ l' => first_success (get_inst_term n) l l'
  | Not f, Not f' => get_inst n f f'
  | Op _ f1 f2, Op _ f1' f2' =>
    match get_inst n f1 f1' with
    | None => get_inst n f2 f2'
    | r => r
    end
  | Quant _ f, f' => get_inst (S n) f f'
  | _, _ => None
  end.

Ltac autoinst H :=
  match type of H with
  | Pr _ (_ ⊢ ∀ ?f) =>
    match goal with
    | |- Pr _ (_ ⊢ ?f') =>
      let r := eval compute in (get_inst 0 f f') in
      match r with
      | Some ?u => apply R_All_e with (t := u) in H;
                   [cbn in H; autoinst H | calc]
      end
    end
  | _ => idtac
  end.

Ltac autoinstax ax := let H := fresh in axiom ax H; autoinst H; exact H.
