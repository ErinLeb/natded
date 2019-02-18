
(** Some Meta-properties (proved on the Mix encoding) *)

Require Import RelationClasses Arith Omega Defs Proofs Mix.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

Lemma closed_bsubst n u (t:term) :
 closed t = true -> bsubst n u t = t.
Proof.
 unfold closed.
 case eqbspec; [ intros H _ | easy ].
 revert t H.
 fix IH 1. destruct t; cbn; try easy.
 intros H. f_equal. clear f.
 revert l H.
 fix IH' 1. destruct l; cbn; try easy.
 intros H. f_equal. apply IH. omega with *. apply IH'. omega with *.
Qed.

Lemma term_vmap_ext h h' (t:term) :
 (forall v:variable, Vars.In v (fvars t) -> h v = h' v) ->
 vmap h t = vmap h' t.
Proof.
 revert t.
 fix IH 1; destruct t; cbn; intros E; trivial.
 - auto with set.
 - f_equal. clear f. revert l E.
   fix IH' 1; destruct l; cbn; intros; f_equal; auto with set.
Qed.

Lemma form_vmap_ext h h' (f:formula) :
 (forall v:variable, Vars.In v (fvars f) -> h v = h' v) ->
 vmap h f = vmap h' f.
Proof.
 induction f; cbn; intro; f_equal; auto with set.
 now injection (term_vmap_ext h h' (Fun "" l)).
Qed.

Lemma ctx_vmap_ext h h' (c:context) :
 (forall v:variable, Vars.In v (fvars c) -> h v = h' v) ->
 vmap h c = vmap h' c.
Proof.
 induction c; cbn; intros; f_equal;
  auto using form_vmap_ext with set.
Qed.

Lemma term_vmap_id h (t:term) :
 (forall v:variable, Vars.In v (fvars t) -> h v = FVar v) ->
 vmap h t = t.
Proof.
 revert t.
 fix IH 1; destruct t; cbn; intros E; trivial.
 - auto with set.
 - f_equal. clear f. revert l E.
   fix IH' 1; destruct l; cbn; intros; f_equal; auto with set.
Qed.

Lemma form_vmap_id h (f:formula) :
 (forall v:variable, Vars.In v (fvars f) -> h v = FVar v) ->
 vmap h f = f.
Proof.
 induction f; cbn; intro; f_equal; auto with set.
 now injection (term_vmap_id h (Fun "" l)).
Qed.

Lemma ctx_vmap_id h (c:context) :
 (forall v:variable, Vars.In v (fvars c) -> h v = FVar v) ->
 vmap h c = c.
Proof.
 induction c; cbn; intros; f_equal;
  auto using form_vmap_id with set.
Qed.

Lemma term_vmap_vmap h h' (t:term) :
 vmap h (vmap h' t) = vmap (fun v => vmap h (h' v)) t.
Proof.
 revert t.
 fix IH 1; destruct t; cbn; trivial.
 f_equal. clear f. revert l.
 fix IH' 1; destruct l; cbn; f_equal; auto.
Qed.

Lemma form_vmap_vmap h h' (f:formula) :
 vmap h (vmap h' f) = vmap (fun v => vmap h (h' v)) f.
Proof.
 induction f; cbn; f_equal; auto.
 now injection (term_vmap_vmap h h' (Fun "" l)).
Qed.

Lemma ctx_vmap_vmap h h' (c:context) :
 vmap h (vmap h' c) = vmap (fun v => vmap h (h' v)) c.
Proof.
 induction c; cbn; f_equal; auto using form_vmap_vmap with set.
Qed.

Lemma term_fvars_vmap h (t:term) :
  Vars.Subset
    (fvars (vmap h t))
    (vars_flatmap (fun v => fvars (h v)) (fvars t)).
Proof.
 revert t.
 fix IH 1. destruct t; cbn.
 - varsdec.
 - varsdec.
 - clear f. revert l. fix IH' 1. destruct l; cbn.
   + varsdec.
   + specialize (IH t). specialize (IH' l).
     rewrite vars_flatmap_union. varsdec.
Qed.

Lemma form_fvars_vmap h (f:formula) :
  Vars.Subset
    (fvars (vmap h f))
    (vars_flatmap (fun v => fvars (h v)) (fvars f)).
Proof.
 induction f; cbn; try varsdec.
 - apply (term_fvars_vmap h (Fun "" l)).
 - rewrite vars_flatmap_union. varsdec.
Qed.

Lemma ctx_fvars_vmap h (c:context) :
  Vars.Subset
    (fvars (vmap h c))
    (vars_flatmap (fun v => fvars (h v)) (fvars c)).
Proof.
 induction c as [|f c IH]; cbn.
 - varsdec.
 - generalize (form_fvars_vmap h f).
   rewrite vars_flatmap_union. varsdec.
Qed.

Lemma seq_fvars_vmap h (s:sequent) :
  Vars.Subset
    (fvars (vmap h s))
    (vars_flatmap (fun v => fvars (h v)) (fvars s)).
Proof.
 destruct s. cbn.
 rewrite vars_flatmap_union.
 generalize (form_fvars_vmap h f) (ctx_fvars_vmap h c). varsdec.
Qed.

Lemma term_vmap_bsubst h n u (t:term) :
 (forall v, closed (h v) = true) ->
 vmap h (bsubst n u t) = bsubst n (vmap h u) (vmap h t).
Proof.
 intros CL.
 revert t.
 fix IH 1. destruct t; cbn.
 - symmetry. apply closed_bsubst. apply CL.
 - auto with eqb.
 - f_equal. clear f.
   revert l. fix IH' 1. destruct l; simpl; f_equal; auto.
Qed.

Lemma form_vmap_bsubst h n u (f:formula) :
 (forall v, closed (h v) = true) ->
 vmap h (bsubst n u f) = bsubst n (vmap h u) (vmap h f).
Proof.
 intros CL. revert n.
 induction f; cbn; intros n; f_equal; auto.
 injection (term_vmap_bsubst h n u (Fun "" l)); auto.
Qed.

Lemma vmap_bsubst_adhoc h x t (f:formula) :
 (forall v, closed (h v) = true) ->
 closed t = true ->
 ~Vars.In x (fvars f) ->
 bsubst 0 t (vmap h f) =
  vmap (fun v => if v =? x then t else h v) (bsubst 0 (FVar x) f).
Proof.
 intros.
 rewrite form_vmap_bsubst by (auto with eqb).
 cbn. rewrite eqb_refl. f_equal.
 apply form_vmap_ext; auto with set eqb.
Qed.

Lemma Pr_vmap logic (s:sequent) :
  Pr logic s ->
  forall h, (forall v, closed (h v) = true) ->
  Pr logic (vmap h s).
Proof.
 induction 1; cbn in *; intros; auto.
 - apply R_Ax. now apply in_map.
 - apply R_Not_e with (vmap h A); auto.
 - apply R_And_e1 with (vmap h B); auto.
 - apply R_And_e2 with (vmap h A); auto.
 - apply R_Or_e with (vmap h A) (vmap h B); auto.
 - apply R_Imp_e with (vmap h A); auto.
 - set (vars := Vars.union (fvars (Γ⊢A))
                           (fvars (vmap h (Γ⊢A)))).
   set (z := fresh_var vars).
   apply R_All_i with z.
   + intro. apply (fresh_var_ok vars). varsdec.
   + rewrite vmap_bsubst_adhoc with (x:=x) by auto with set.
     erewrite ctx_vmap_ext; try apply IHPr; cbn;
      intros; case eqbspec; auto with set.
 - rewrite form_vmap_bsubst by auto. apply R_All_e; auto.
 - apply R_Ex_i with (vmap h t).
   rewrite <- form_vmap_bsubst by auto. apply IHPr; auto.
 - set (vars := Vars.union (fvars (A::Γ⊢B))
                           (fvars (vmap h (A::Γ⊢B)))).
   set (z := fresh_var vars).
   apply R_Ex_e with z (vmap h A); clear H0 H1.
   + intro. apply (fresh_var_ok vars). varsdec.
   + apply IHPr1; auto.
   + rewrite vmap_bsubst_adhoc with (x:=x) by auto with set.
     erewrite (ctx_vmap_ext h), (form_vmap_ext h);
      try apply IHPr2; cbn; intros; case eqbspec; auto with set.
 - apply R_Absu with l. auto.
Qed.

Lemma Pr_fsubst logic (s:sequent) :
  Pr logic s ->
  forall v t, closed t = true ->
  Pr logic (fsubst v t s).
Proof.
 intros.
 change (fsubst v t) with (vmap (varsubst v t)).
 apply Pr_vmap; auto.
 intros x. unfold varsubst. case eqbspec; auto.
Qed.

Definition ListSubset {A} (l l': list A) :=
  forall a, In a l -> In a l'.

Inductive SubsetSeq : sequent -> sequent -> Prop :=
 | SubSeq Γ Γ' A : ListSubset Γ Γ' -> SubsetSeq (Γ⊢A) (Γ'⊢A).
Hint Constructors SubsetSeq.

Lemma ListSubset_cons {A} (l l': list A) x :
  ListSubset l l' -> ListSubset (x::l) (x::l').
Proof.
 intros H y [Hy|Hy]; simpl; auto.
Qed.
Hint Resolve ListSubset_cons.

Lemma ListSubset_map {A B} (f:A->B) (l l': list A) :
  ListSubset l l' -> ListSubset (map f l) (map f l').
Proof.
 intros SU b. rewrite !in_map_iff.
 intros (a & Ha & Ha'). apply SU in Ha'. now exists a.
Qed.

Ltac varsdec' := cbn in *; varsdec.

Lemma Pr_weakening logic s s' :
  Pr logic s ->
  SubsetSeq s s' ->
  Pr logic s'.
Proof.
 intros H. revert s'.
 induction H; inversion_clear 1; auto.
 - eapply R_Not_e with A; auto.
 - apply R_And_e1 with B; auto.
 - apply R_And_e2 with A; auto.
 - apply R_Or_e with A B; auto.
 - apply R_Imp_e with A; auto.
 - set (vars := Vars.add x (fvars (Γ' ⊢ A))).
   set (z := fresh_var vars).
   assert (Hz : ~Vars.In z vars) by (apply fresh_var_ok).
   clearbody z; unfold vars in *; clear vars. cbn in *.
   set (h := fun v => if v =? x then FVar z else FVar v).
   set (Γ2 := vmap h Γ').
   assert (~Vars.In x (fvars Γ2)).
   { unfold Γ2. intros IN. apply ctx_fvars_vmap in IN.
     rewrite vars_flatmap_in in IN.
     destruct IN as (v & IN & IN'). revert IN.
     unfold h. case eqbspec; cbn; varsdec. }
   assert (ListSubset Γ Γ2).
   { rewrite <- (ctx_vmap_id h Γ).
     now apply ListSubset_map.
     unfold h. auto with eqb set. }
   assert (PR : Pr l (Γ2 ⊢ ∀A)).
   { apply R_All_i with x; cbn; auto with set. }
   set (h' := fun v => if v =? z then FVar x else FVar v).
   assert (forall v, closed (h' v) = true).
   { unfold h'. auto with eqb. }
   apply Pr_vmap with (h := h') in PR; auto.
   cbn in PR. unfold Γ2 in PR.
   rewrite ctx_vmap_vmap, ctx_vmap_id, form_vmap_id in PR; auto.
   + unfold h'. auto with eqb set.
   + unfold h, h'. intros. do 2 (case eqbspec; cbn); auto with set.
 - apply R_Ex_i with t; auto.
 - set (vars := Vars.add x (fvars (A::Γ' ⊢ B))).
   set (z := fresh_var vars).
   assert (Hz : ~Vars.In z vars) by (apply fresh_var_ok).
   clearbody z; unfold vars in *; clear vars. cbn in *.
   set (h := fun v => if v =? x then FVar z else FVar v).
   set (Γ2 := vmap h Γ').
   assert (~Vars.In x (fvars Γ2)).
   { unfold Γ2. intros IN. apply ctx_fvars_vmap in IN.
     rewrite vars_flatmap_in in IN.
     destruct IN as (v & IN & IN'). revert IN.
     unfold h. case eqbspec; cbn; varsdec. }
   assert (ListSubset Γ Γ2).
   { rewrite <- (ctx_vmap_id h Γ).
     now apply ListSubset_map.
     unfold h. auto with eqb set. }
   assert (PR : Pr l (Γ2 ⊢ B)).
   { apply R_Ex_e with x A; cbn; auto with set. }
   set (h' := fun v => if v =? z then FVar x else FVar v).
   assert (forall v, closed (h' v) = true).
   { unfold h'. intros. case eqbspec; now cbn. }
   apply Pr_vmap with (h := h') in PR; auto.
   cbn in PR. unfold Γ2 in PR.
   rewrite ctx_vmap_vmap, ctx_vmap_id, form_vmap_id in PR; auto.
   + unfold h'. auto with eqb set.
   + unfold h, h'. intros. do 2 (case eqbspec; cbn); auto with set.
 - apply R_Absu with l; auto.
Qed.
