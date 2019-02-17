
(** Some Meta-properties (proved on the Mix encoding) *)

Require Import RelationClasses Arith Omega Defs Proofs Mix.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

Hint Extern 10 => varsdec : sets.

Lemma closed_bsubst n u t :
 term_closed t = true -> term_bsubst n u t = t.
Proof.
 unfold term_closed.
 case eqbspec; [ intros H _ | easy ].
 revert t H.
 fix IH 1. destruct t; simpl; try easy.
 intros H. f_equal. clear f.
 revert l H.
 fix IH' 1. destruct l; simpl; try easy.
 intros H. f_equal. apply IH. omega with *. apply IH'. omega with *.
Qed.

Lemma term_vmap_ext h h' (t:term) :
 (forall v:variable, Vars.In v (fvars t) -> h v = h' v) ->
 term_vmap h t = term_vmap h' t.
Proof.
 revert t.
 fix IH 1; destruct t; cbn; intros E; trivial.
 - auto with sets.
 - f_equal. clear f. revert l E.
   fix IH' 1; destruct l; cbn; intros; f_equal; auto with sets.
Qed.

Lemma form_vmap_ext h h' (f:formula) :
 (forall v:variable, Vars.In v (fvars f) -> h v = h' v) ->
 form_vmap h f = form_vmap h' f.
Proof.
 induction f; cbn; intro; f_equal; auto with sets.
 now injection (term_vmap_ext h h' (Fun "" l)).
Qed.

Lemma ctx_vmap_ext h h' (c:context) :
 (forall v:variable, Vars.In v (fvars c) -> h v = h' v) ->
 ctx_vmap h c = ctx_vmap h' c.
Proof.
 induction c; cbn; intros; f_equal;
  auto using form_vmap_ext with sets.
Qed.

Lemma term_vmap_id h (t:term) :
 (forall v:variable, Vars.In v (fvars t) -> h v = FVar v) ->
 term_vmap h t = t.
Proof.
 revert t.
 fix IH 1; destruct t; cbn; intros E; trivial.
 - auto with sets.
 - f_equal. clear f. revert l E.
   fix IH' 1; destruct l; cbn; intros; f_equal; auto with sets.
Qed.

Lemma form_vmap_id h (f:formula) :
 (forall v:variable, Vars.In v (fvars f) -> h v = FVar v) ->
 form_vmap h f = f.
Proof.
 induction f; cbn; intro; f_equal; auto with sets.
 now injection (term_vmap_id h (Fun "" l)).
Qed.

Lemma ctx_vmap_id h (c:context) :
 (forall v:variable, Vars.In v (fvars c) -> h v = FVar v) ->
 ctx_vmap h c = c.
Proof.
 induction c; cbn; intros; f_equal;
  auto using form_vmap_id with sets.
Qed.

Lemma term_vmap_vmap h h' (t:term) :
 term_vmap h (term_vmap h' t) =
 term_vmap (fun v => term_vmap h (h' v)) t.
Proof.
 revert t.
 fix IH 1; destruct t; simpl; trivial.
 f_equal. clear f. revert l.
 fix IH' 1; destruct l; simpl; f_equal; auto.
Qed.

Lemma form_vmap_vmap h h' (f:formula) :
 form_vmap h (form_vmap h' f) =
 form_vmap (fun v => term_vmap h (h' v)) f.
Proof.
 induction f; cbn; f_equal; auto.
 now injection (term_vmap_vmap h h' (Fun "" l)).
Qed.

Lemma ctx_vmap_vmap h h' (c:context) :
 ctx_vmap h (ctx_vmap h' c) =
 ctx_vmap (fun v => term_vmap h (h' v)) c.
Proof.
 induction c; cbn; f_equal; auto using form_vmap_vmap with sets.
Qed.

Arguments Vars.union !_ !_.

Lemma term_fvars_vmap h (t:term) :
  Vars.Subset
    (fvars (term_vmap h t))
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
    (fvars (form_vmap h f))
    (vars_flatmap (fun v => fvars (h v)) (fvars f)).
Proof.
 induction f; cbn; try varsdec.
 - apply (term_fvars_vmap h (Fun "" l)).
 - rewrite vars_flatmap_union. varsdec.
Qed.

Lemma ctx_fvars_vmap h (c:context) :
  Vars.Subset
    (fvars (ctx_vmap h c))
    (vars_flatmap (fun v => fvars (h v)) (fvars c)).
Proof.
 induction c as [|f c IH]; cbn.
 - varsdec.
 - generalize (form_fvars_vmap h f).
   rewrite vars_flatmap_union. varsdec.
Qed.

Lemma seq_fvars_vmap h (s:sequent) :
  Vars.Subset
    (fvars (seq_vmap h s))
    (vars_flatmap (fun v => fvars (h v)) (fvars s)).
Proof.
 destruct s. cbn.
 rewrite vars_flatmap_union.
 generalize (form_fvars_vmap h f) (ctx_fvars_vmap h c). varsdec.
Qed.

Lemma term_vmap_bsubst h n u t :
 (forall v, term_closed (h v) = true) ->
 term_vmap h (term_bsubst n u t) =
  term_bsubst n (term_vmap h u) (term_vmap h t).
Proof.
 intros CL.
 revert t.
 fix IH 1. destruct t; cbn.
 - symmetry. apply closed_bsubst. apply CL.
 - case eqbspec; simpl; auto.
 - f_equal. clear f.
   revert l. fix IH' 1. destruct l; simpl; auto.
   f_equal. apply IH. apply IH'.
Qed.

Lemma form_vmap_bsubst h n u f :
 (forall v, term_closed (h v) = true) ->
 form_vmap h (form_bsubst n u f) =
  form_bsubst n (term_vmap h u) (form_vmap h f).
Proof.
 intros CL. revert n.
 induction f; cbn; intros n; f_equal; auto.
 injection (term_vmap_bsubst h n u (Fun "" l)); auto.
Qed.

Lemma vmap_bsubst_adhoc h x t f :
 (forall v, term_closed (h v) = true) ->
 term_closed t = true ->
 ~Vars.In x (fvars f) ->
 form_vmap (fun v => if v =? x then t else h v)
   (form_bsubst 0 (FVar x) f) =
 form_bsubst 0 t (form_vmap h f).
Proof.
 intros.
 rewrite form_vmap_bsubst.
 - simpl. rewrite eqb_refl. f_equal.
   apply form_vmap_ext.
   intros v Hv. case eqbspec; auto with sets.
 - intros v. case eqbspec; auto.
Qed.

Lemma Pr_vmap logic s :
  Pr logic s ->
  forall h, (forall v, term_closed (h v) = true) ->
  Pr logic (seq_vmap h s).
Proof.
 induction 1; cbn in *; intros; auto.
 - apply R_Ax. now apply in_map.
 - apply R_Not_e with (form_vmap h A); auto.
 - apply R_And_e1 with (form_vmap h B); auto.
 - apply R_And_e2 with (form_vmap h A); auto.
 - apply R_Or_e with (form_vmap h A) (form_vmap h B); auto.
 - apply R_Imp_e with (form_vmap h A); auto.
 - set (vars := Vars.union (fvars (Γ⊢A))
                  (vars_flatmap (fun v => fvars (h v)) (fvars (Γ⊢A)))).
   set (z := fresh_var vars).
   apply R_All_i with z.
   + intros H'. apply (seq_fvars_vmap h (Γ⊢A)) in H'.
     apply (fresh_var_ok vars). varsdec.
   + specialize (IHPr (fun v => if v =? x then FVar z else h v)).
     rewrite <- (ctx_vmap_ext h) in IHPr by
       (intros; case eqbspec; auto with sets).
     rewrite <- vmap_bsubst_adhoc with (x:=x); auto with sets.
     apply IHPr.
     intros v; case eqbspec; auto.
 - rewrite form_vmap_bsubst by auto.
   apply R_All_e; auto.
 - specialize (IHPr h).
   rewrite form_vmap_bsubst in IHPr by auto.
   apply R_Ex_i with (term_vmap h t); auto.
 - set (vars := Vars.union (fvars (A::Γ⊢B))
                 (vars_flatmap (fun v => fvars (h v)) (fvars (A::Γ⊢B)))).
   set (z := fresh_var vars).
   apply R_Ex_e with z (form_vmap h A).
   + intros H'. apply (seq_fvars_vmap h (A::Γ⊢B) z) in H'.
     apply (fresh_var_ok vars). varsdec.
   + now apply IHPr1.
   + specialize (IHPr2 (fun v => if v =? x then FVar z else h v)).
     rewrite <- (ctx_vmap_ext h) in IHPr2 by
       (intros; case eqbspec; auto with sets).
     rewrite <- (form_vmap_ext h _ B) in IHPr2 by
       (intros; case eqbspec; auto with sets).
     rewrite <- vmap_bsubst_adhoc with (x:=x); auto with sets.
     apply IHPr2.
     intros v; case eqbspec; auto.
 - apply R_Absu with l. auto.
Qed.

Lemma Pr_fsubst logic s :
  Pr logic s ->
  forall v t, term_closed t = true ->
  Pr logic (seq_fsubst v t s).
Proof.
 intros.
 change (seq_fsubst v t) with (seq_vmap (fsubst v t)).
 apply Pr_vmap; auto.
 intros x. unfold fsubst. case eqbspec; auto.
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
   clearbody z; unfold vars in *; clear vars.
   set (h := fun v => if v =? x then FVar z else FVar v).
   set (Γ2 := ctx_vmap h Γ').
   assert (~Vars.In x (fvars Γ2)).
   { intros IN. apply ctx_fvars_vmap in IN.
     rewrite vars_flatmap_in in IN.
     destruct IN as (v & IN & IN'). revert IN.
     unfold h. case eqbspec; cbn; varsdec. }
   assert (ListSubset Γ Γ2).
   { rewrite <- (ctx_vmap_id h Γ).
     now apply ListSubset_map.
     intros v Hv. unfold h. case eqbspec; auto. varsdec'. }
   assert (PR : Pr l (Γ2 ⊢ ∀A)).
   { apply R_All_i with x; auto. varsdec'. }
   set (h' := fun v => if v =? z then FVar x else FVar v).
   assert (forall v, term_closed (h' v) = true).
   { intros v. unfold h'. case eqbspec; now cbn. }
   apply Pr_vmap with (h := h') in PR; auto.
   simpl in PR. unfold Γ2 in PR.
   rewrite ctx_vmap_vmap, ctx_vmap_id, form_vmap_id in PR; auto.
   + intros v hv. unfold h'. case eqbspec; auto. varsdec'.
   + intros v hv. unfold h, h'.
     do 2 (case eqbspec; cbn); intros; subst; try easy. varsdec'.
 - apply R_Ex_i with t; auto.
 - set (vars := Vars.add x (fvars (A::Γ' ⊢ B))).
   set (z := fresh_var vars).
   assert (Hz : ~Vars.In z vars) by (apply fresh_var_ok).
   clearbody z; unfold vars in *; clear vars.
   set (h := fun v => if v =? x then FVar z else FVar v).
   set (Γ2 := ctx_vmap h Γ').
   assert (~Vars.In x (fvars Γ2)).
   { intros IN. apply ctx_fvars_vmap in IN.
     rewrite vars_flatmap_in in IN.
     destruct IN as (v & IN & IN'). revert IN.
     unfold h. case eqbspec; cbn; varsdec. }
   assert (ListSubset Γ Γ2).
   { rewrite <- (ctx_vmap_id h Γ).
     now apply ListSubset_map.
     intros v Hv. unfold h. case eqbspec; auto. varsdec'. }
   assert (PR : Pr l (Γ2 ⊢ B)).
   { apply R_Ex_e with x A; auto. varsdec'. }
   set (h' := fun v => if v =? z then FVar x else FVar v).
   assert (forall v, term_closed (h' v) = true).
   { intros v. unfold h'. case eqbspec; now cbn. }
   apply Pr_vmap with (h := h') in PR; auto.
   simpl in PR. unfold Γ2 in PR.
   rewrite ctx_vmap_vmap, ctx_vmap_id, form_vmap_id in PR; auto.
   + intros v hv. unfold h'. case eqbspec; auto. varsdec'.
   + intros v hv. unfold h, h'.
     do 2 (case eqbspec; cbn); intros; subst; try easy. varsdec'.
 - apply R_Absu with l; auto.
Qed.
