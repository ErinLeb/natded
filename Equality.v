
(** * Facts about Equality *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

From NatDed Require Import
  Defs NameProofs Mix Wellformed Toolbox Meta ProofExamples
  Theories Models Peano ZF.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

Ltac closed_bsubst :=
 apply Nat.le_0_r, level_bsubst_term; auto; now apply Nat.le_0_r.

Local Open Scope form.

(** Proof of Leibniz's principle for Peano theory *)

Import Peano.PeanoAx.

Lemma add_compat G x x' y y' :
 BClosed x -> BClosed x' -> BClosed y ->
 In ax3 G -> In ax5 G -> In ax6 G ->
 Pr Intuiti (G ⊢ x = x')%form ->
 Pr Intuiti (G ⊢ y = y')%form ->
 Pr Intuiti (G ⊢ x + y = x' + y').
Proof.
 intros Hx Hx' Hy IN3 IN5 IN6 Hxx' Hyy'.
 trans (x' + y); auto.
 - red. red in Hx, Hy. cbn. omega with *.
 - red. red in Hx', Hy. cbn. omega with *.
 - eapply R_Imp_e; [ | exact Hxx'].
   inst_axiom ax5 [x; x'; y]. revert H. cbn.
   rewrite !(lift_nop _ x), !lift_nop by auto.
   rewrite (bclosed_bsubst_id 1), !bclosed_bsubst_id; eauto.
 - eapply R_Imp_e; [ | exact Hyy'].
   inst_axiom ax6 [x'; y; y']. revert H. cbn.
   rewrite !(lift_nop _ x'), !lift_nop by auto.
   rewrite (bclosed_bsubst_id 1), !bclosed_bsubst_id; eauto.
Qed.

Lemma mul_compat G x x' y y' :
 BClosed x -> BClosed x' -> BClosed y ->
 In ax3 G -> In ax7 G -> In ax8 G ->
 Pr Intuiti (G ⊢ x = x')%form ->
 Pr Intuiti (G ⊢ y = y')%form ->
 Pr Intuiti (G ⊢ x * y = x' * y').
Proof.
 intros Hx Hx' Hy IN3 IN5 IN6 Hxx' Hyy'.
 trans (x' * y); auto.
 - red. red in Hx, Hy. cbn. omega with *.
 - red. red in Hx', Hy. cbn. omega with *.
 - eapply R_Imp_e; [ | exact Hxx'].
   inst_axiom ax7 [x; x'; y]. revert H. cbn.
   rewrite !(lift_nop _ x), !lift_nop by auto.
   rewrite (bclosed_bsubst_id 1), !bclosed_bsubst_id; eauto.
 - eapply R_Imp_e; [ | exact Hyy'].
   inst_axiom ax8 [x'; y; y']. revert H. cbn.
   rewrite !(lift_nop _ x'), !lift_nop by auto.
   rewrite (bclosed_bsubst_id 1), !bclosed_bsubst_id; eauto.
Qed.

Lemma Leibniz_term (t:term) n u u' :
  check PeanoSign t = true ->
  BClosed (bsubst n u t) -> BClosed (bsubst n u' t) ->
  Pr Intuiti ((u = u')%form :: axioms_list ⊢ bsubst n u t = bsubst n u' t).
Proof.
 induction t as [ v | m | f l IH] using term_ind'; intros Ht Hu Hu'.
 - cbn. now inst_axiom ax1 [FVar v].
 - cbn in Hu,Hu'. cbn. revert Hu Hu'. case eqbspec.
   + intros -> _ _. apply R'_Ax.
   + intros _ [= ] _.
 - cbn in Ht. revert Ht.  repeat case eqbspec; try easy.
   + (* O *)
     intros ? -> C.
     destruct l; try easy. cbn in *.
     now inst_axiom ax1 [Zero].
   + (* S *)
     intros Hl -> _ C.
     destruct l as [|x [| ]]; try easy. cbn in *.
     rewrite andb_true_r in C.
     ahered.
     * red; red in Hu. cbn in Hu. omega with *.
     * apply IH; auto.
       { red; red in Hu. cbn in Hu. omega with *. }
       { red; red in Hu'. cbn in Hu'. omega with *. }
   + (* + *)
     intros Hl -> _ _ C.
     destruct l as [|x [|y [| ]]]; try easy. cbn in *.
     rewrite andb_true_r in C. rewrite andb_true_iff in C.
     red in Hu. cbn in Hu. rewrite !max_0 in Hu.
     red in Hu'. cbn in Hu'. rewrite !max_0 in Hu'.
     apply add_compat; calc; try apply IH; intuition; red; auto.
   + (* * *)
     intros Hl -> _ _ _ C.
     destruct l as [|x [|y [| ]]]; try easy. cbn in *.
     rewrite andb_true_r in C. rewrite andb_true_iff in C.
     red in Hu. cbn in Hu. rewrite !max_0 in Hu.
     red in Hu'. cbn in Hu'. rewrite !max_0 in Hu'.
     apply mul_compat; calc; try apply IH; intuition; red; auto.
Qed.

Ltac All_i_fresh :=
  match goal with
  | |- Pr _ ?s =>
    let v := fresh "v" in
    let Hv := fresh "Hv" in
    destruct (exist_fresh (fvars s)) as (v,Hv);
    apply R_All_i with (x:=v); [exact Hv| ]
  end.

Lemma Leibniz_term' (t:term) :
  level t <= 1 ->
  check PeanoSign t = true ->
  Pr Intuiti (axioms_list ⊢ ∀∀ #1 = #0 -> bsubst 0 (#1) t = bsubst 0 (#0) t).
Proof.
 intros.
 All_i_fresh. cbn.
 All_i_fresh. cbn. clear Hv Hv0.
 rewrite term_bsubst_bsubst, term_bsubst_id; auto.
 rewrite (term_level_bsubst_id 1); auto.
 rewrite (bclosed_bsubst_id 0) by closed_bsubst.
 apply R_Imp_i. apply Leibniz_term; auto; closed_bsubst.
Qed.

Lemma Leibniz_main N A n (u u' : term) :
  height A < N ->
  check PeanoSign A = true ->
  BClosed (bsubst n u A) -> BClosed (bsubst n u' A) ->
  Pr Intuiti ((u=u')%form :: axioms_list ⊢ bsubst n u A <-> bsubst n u' A).
Proof.
 revert A n u u'.
 induction N; [inversion 1 | ].
 destruct A; intros n u u' HN HA Hu Hu'.
 - cbn. apply R_And_i; apply R_Imp_i, R'_Ax.
 - cbn. apply R_And_i; apply R_Imp_i, R'_Ax.
 - cbn.
   cbn in Hu, Hu'. red in Hu, Hu'. cbn in Hu, Hu'.
   revert HA.
   cbn.
   repeat case eqbspec; try easy. intros Hl -> C.
   destruct l as [|x [|y [| ]]]; try easy. cbn in *.
   rewrite andb_true_r in C. rewrite andb_true_iff in C.
   rewrite !max_0 in *.
   destruct Hu as (Hux & Huy & _), Hu' as (Hux' & Huy' & _).
   set (X := bsubst n u x) in *.
   set (X' := bsubst n u' x) in *.
   set (Y := bsubst n u y) in *.
   set (Y' := bsubst n u' y) in *.
   apply R_And_i; apply R_Imp_i.
   + trans X; auto.
     * sym; auto.
       apply Pr_pop. apply Leibniz_term; intuition.
     * trans Y; auto. apply R'_Ax.
       apply Pr_pop. apply Leibniz_term; intuition.
   + trans X'; auto.
     * apply Pr_pop. apply Leibniz_term; intuition.
     * trans Y'; auto. apply R'_Ax.
       apply Pr_pop. sym; auto. apply Leibniz_term; intuition.
 - cbn. apply ContraIff. apply IHN; auto. cbn in HN. omega.
 - cbn. red in Hu,Hu'. cbn in Hu,Hu'. rewrite !max_0 in *.
   destruct Hu as (Hu1 & Hu2), Hu' as (Hu1' & Hu2').
   cbn in HA. rewrite <- andb_lazy_alt, andb_true_iff in HA.
   cbn in HN. apply OpIff; apply IHN; intuition; omega with *.
 - cbn. red in Hu,Hu'. cbn in Hu,Hu'. rewrite pred_0 in Hu,Hu'.
   apply QuantIff.
   All_i_fresh. clear Hv.
   cbn. reIff.
   destruct (level_subst_inv (S n) (lift 0 u) A).
   + omega with *.
   + rewrite !(form_level_bsubst_id (S n)); auto.
     apply R_And_i; apply R_Imp_i, R'_Ax.
   + destruct (level_subst_inv (S n) (lift 0 u') A).
     * omega with *.
     * rewrite !(form_level_bsubst_id (S n)); auto.
       apply R_And_i; apply R_Imp_i, R'_Ax.
     * assert (BClosed u).
       { red. generalize (lift_incrlevel 0 u). omega. }
       assert (BClosed u').
       { red. generalize (lift_incrlevel 0 u'). omega. }
       rewrite !lift_nop in * by auto.
       rewrite !(swap_bsubst 0); auto.
       apply IHN; auto.
       { rewrite height_bsubst. cbn in HN. omega. }
       { cbn in HA. apply check_bsubst; auto. }
       { apply Nat.le_0_r. now rewrite swap_bsubst, level_bsubst. }
       { apply Nat.le_0_r. now rewrite swap_bsubst, level_bsubst. }
Qed.

Lemma Leibniz_Pr A :
  WF PeanoSign (∀A) ->
  Pr Intuiti (axioms_list ⊢ ∀∀ #0 = #1 -> A -> bsubst 0 (#1) A).
Proof.
 intros (HA,HA'). cbn in HA. red in HA'. cbn in HA'.
 assert (HA'' : level A <= 1) by omega with *.
 All_i_fresh. cbn.
 All_i_fresh. cbn. clear Hv Hv0.
 rewrite (form_level_bsubst_id 1 _ A) by easy.
 rewrite bsubst_bsubst by easy.
 rewrite (form_level_bsubst_id 0 _ (bsubst _ _ _))
   by (apply level_bsubst; auto).
 apply R_Imp_i. eapply R_And_e1.
 eapply Leibniz_main with (N:=(S (height A))); auto with *.
 apply Nat.le_0_r, level_bsubst; auto.
 apply Nat.le_0_r, level_bsubst; auto.
Qed.

Lemma Leibniz_thm A :
  WC PeanoSign (∀A) ->
  IsTheorem J PeanoTheory (∀∀ #0 = #1 -> A -> bsubst 0 (#1) A).
Proof.
 intros ((CA,LA),FA). cbn in *.
 split.
 - repeat split.
   + cbn. now rewrite check_bsubst, CA.
   + red. cbn -[Nat.max]. rewrite !pred_max. cbn.
     generalize (level_bsubst_max 0 (#1) A). cbn - [Nat.max].
     red in LA. cbn in LA. omega with *.
   + rewrite <- form_fclosed_spec in *. cbn in *.
     rewrite fclosed_bsubst; auto. now rewrite FA.
 - exists axioms_list. split.
   + apply Forall_forall. intros x Hx. now left.
   + apply Leibniz_Pr; auto with *.
Qed.
