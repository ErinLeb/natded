
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

(*
Lemma freevars_fsubst v u t :
 ~Vars.In v (term_fvars t) -> term_fsubst v u t = t.
Proof.
 revert t.
 fix IH 1. destruct t; simpl; trivial.
 - case eqbspec; trivial. intros <-. varsdec.
 - intros H. f_equal. clear f.
   revert l H.
   fix IH' 1. destruct l; simpl; trivial.
   intros H. f_equal. apply IH. varsdec. apply IH'. varsdec.
Qed.

Lemma term_fsubst_bsubst v t n u T :
  ~Vars.In v (term_fvars u) ->
  term_closed t = true ->
  term_fsubst v t (term_bsubst n u T) =
  term_bsubst n u (term_fsubst v t T).
Proof.
 revert T. fix IH 1. destruct T; simpl; intros.
 - case eqbspec; simpl; auto.
   intros <-. now rewrite closed_bsubst.
 - case eqbspec; simpl; auto.
   intros _. now apply freevars_fsubst.
 - f_equal. clear f.
   revert l. fix IH' 1. destruct l; simpl; trivial.
   f_equal. now apply IH. now apply IH'.
Qed.

Lemma fsubst_bsubst v t n u f :
  ~Vars.In v (term_fvars u) ->
  term_closed t = true ->
  form_fsubst v t (form_bsubst n u f) =
  form_bsubst n u (form_fsubst v t f).
Proof.
 revert n.
 induction f; simpl; intros; f_equal; auto.
 injection (term_fsubst_bsubst v t n u (Fun "" l)); auto.
Qed.
*)

Definition subinvars (sub : subst) :=
  vars_unionmap (fun '(v,_) => Vars.singleton v) sub.

Definition suboutvars (sub : subst) :=
  vars_unionmap (fun '(_,t) => fvars t) sub.

Definition subvars (sub : subst) :=
  Vars.union (subinvars sub) (suboutvars sub).

Definition sub_closed (sub : subst) :=
  forallb (fun '(_,t) => term_closed t) sub.

Lemma subinvars_in sub (z:variable) :
 Vars.In z (subinvars sub) <-> In z (map fst sub).
Proof.
 induction sub as [|(a,u) sub IH]; simpl;
  rewrite <- ?IH; auto with sets.
Qed.

Lemma list_assoc_suboutvars sub t v :
 list_assoc v sub = Some t ->
 Vars.Subset (term_fvars t) (suboutvars sub).
Proof.
 induction sub as [|(x,u) sub IH]; simpl.
 - easy.
 - case eqbspec.
   + intros <- [= ->]. varsdec.
   + intros NE H. specialize (IH H). varsdec.
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

Lemma term_vmap_vmap h h' (t:term) :
 term_vmap h (term_vmap h' t) =
 term_vmap (fun v => term_vmap h (h' v)) t.
Proof.
 revert t.
 fix IH 1; destruct t; simpl; trivial.
 f_equal. clear f. revert l.
 fix IH' 1; destruct l; simpl; f_equal; auto.
Qed.

Lemma form_vmap_ext h h' (f:formula) :
 (forall v:variable, Vars.In v (fvars f) -> h v = h' v) ->
 form_vmap h f = form_vmap h' f.
Proof.
 induction f; cbn; intro; f_equal; auto with sets.
 now injection (term_vmap_ext h h' (Fun "" l)).
Qed.

Lemma form_vmap_id h (f:formula) :
 (forall v:variable, Vars.In v (fvars f) -> h v = FVar v) ->
 form_vmap h f = f.
Proof.
 induction f; cbn; intro; f_equal; auto with sets.
 now injection (term_vmap_id h (Fun "" l)).
Qed.

Lemma form_vmap_vmap h h' (f:formula) :
 form_vmap h (form_vmap h' f) =
 form_vmap (fun v => term_vmap h (h' v)) f.
Proof.
 induction f; cbn; f_equal; auto.
 now injection (term_vmap_vmap h h' (Fun "" l)).
Qed.

Lemma ctx_vmap_ext h h' (c:context) :
 (forall v:variable, Vars.In v (fvars c) -> h v = h' v) ->
 ctx_vmap h c = ctx_vmap h' c.
Proof.
 induction c; cbn; intros; f_equal;
  auto using form_vmap_ext with sets.
Qed.

Lemma ctx_vmap_id h (c:context) :
 (forall v:variable, Vars.In v (fvars c) -> h v = FVar v) ->
 ctx_vmap h c = c.
Proof.
 induction c; cbn; intros; f_equal;
  auto using form_vmap_id with sets.
Qed.

Lemma ctx_vmap_vmap h h' (c:context) :
 ctx_vmap h (ctx_vmap h' c) =
 ctx_vmap (fun v => term_vmap h (h' v)) c.
Proof.
 induction c; cbn; f_equal; auto using form_vmap_vmap with sets.
Qed.

Lemma ctx_fsubsts_alt sub c :
 ctx_fsubsts sub c = ctx_vmap (fsubsts sub) c.
Proof.
 reflexivity.
Qed.

(*
Lemma term_fvars_vmap h t :
  Vars.Subset
    (term_fvars (term_vmap h t))
    (vars_flatmap (fun v => term_fvars (h v))
                  (Vars.elements (term_fvars t))).
Proof.
 revert t.
 fix IH 1. destruct t; simpl.
 - varsdec.
 - varsdec.
 - clear f. revert l. fix IH' 1. destruct l; simpl.
   + varsdec.
   + specialize (IH t). specialize (IH' l). varsdec.
*)

Lemma term_fvars_fsubsts sub (t:term) :
  Vars.Subset
    (fvars (term_fsubsts sub t))
    (Vars.union (suboutvars sub)
                (Vars.diff (fvars t) (subinvars sub))).
Proof.
 revert t.
 fix IH 1. destruct t; cbn.
 - unfold fsubsts. rewrite ?list_assoc_dft_alt.
   destruct (list_assoc v sub) eqn:E; cbn.
   + apply list_assoc_suboutvars in E. varsdec.
   + rewrite list_assoc_notin, <- subinvars_in in E. varsdec.
 - varsdec.
 - clear f. revert l. fix IH' 1. destruct l; cbn.
   + varsdec.
   + specialize (IH t). specialize (IH' l). varsdec.
Qed.

Lemma fvars_fsubsts sub (f:formula) :
  Vars.Subset
    (fvars (form_fsubsts sub f))
    (Vars.union (suboutvars sub)
                (Vars.diff (fvars f) (subinvars sub))).
Proof.
 induction f; cbn; auto; try varsdec.
 apply (term_fvars_fsubsts sub (Fun "" l)).
Qed.

Lemma fvars_fsubsts_ctx sub (c:context) :
  Vars.Subset
    (fvars (ctx_fsubsts sub c))
    (Vars.union (suboutvars sub)
                (Vars.diff (fvars c) (subinvars sub))).
Proof.
 induction c as [|f c IH]; cbn.
 - varsdec.
 - generalize (fvars_fsubsts sub f). varsdec.
Qed.

Lemma fvars_fsubsts_seq sub (s:sequent) :
  Vars.Subset
    (fvars (seq_fsubsts sub s))
    (Vars.union (suboutvars sub)
                (Vars.diff (fvars s) (subinvars sub))).
Proof.
 destruct s as (c,f). cbn.
 generalize (fvars_fsubsts_ctx sub c) (fvars_fsubsts sub f).
 varsdec.
Qed.

Lemma term_fsubsts_notIn sub (x:variable) u t :
 ~Vars.In x (fvars t) ->
 term_fsubsts ((x, u) :: sub) t = term_fsubsts sub t.
Proof.
 intros NI. apply term_vmap_ext.
 intros v IN. unfold fsubsts. rewrite !list_assoc_dft_alt.
 simpl. case eqbspec; auto with sets.
Qed.

Lemma form_fsubsts_notIn sub (x:variable) u f :
 ~Vars.In x (fvars f) ->
 form_fsubsts ((x, u) :: sub) f = form_fsubsts sub f.
Proof.
 intros NI. apply form_vmap_ext.
 intros v IN. unfold fsubsts. rewrite !list_assoc_dft_alt.
 simpl. case eqbspec; auto with sets.
Qed.

Lemma ctx_fsubsts_notIn sub (x:variable) u c :
 ~Vars.In x (fvars c) ->
 ctx_fsubsts ((x,u)::sub) c = ctx_fsubsts sub c.
Proof.
 intros NI. apply ctx_vmap_ext.
 intros v IN. unfold fsubsts. rewrite !list_assoc_dft_alt.
 simpl. case eqbspec; auto with sets.
Qed.

Lemma term_fsubsts_nop sub t :
 Vars.Empty (Vars.inter (subinvars sub) (fvars t)) ->
 term_fsubsts sub t = t.
Proof.
 intros E. apply term_vmap_id.
 intros v Hv. unfold fsubsts. rewrite list_assoc_dft_alt.
 assert (H : ~Vars.In v (subinvars sub)) by varsdec.
 rewrite subinvars_in, <- list_assoc_notin in H.
 now rewrite H.
Qed.

Lemma form_fsubsts_nop sub f :
 Vars.Empty (Vars.inter (subinvars sub) (fvars f)) ->
 form_fsubsts sub f = f.
Proof.
 intros E. apply form_vmap_id.
 intros v Hv. unfold fsubsts. rewrite list_assoc_dft_alt.
 assert (H : ~Vars.In v (subinvars sub)) by varsdec.
 rewrite subinvars_in, <- list_assoc_notin in H.
 now rewrite H.
Qed.

Lemma ctx_fsubsts_nop sub c:
 Vars.Empty (Vars.inter (subinvars sub) (fvars c)) ->
 ctx_fsubsts sub c = c.
Proof.
 intros E. apply ctx_vmap_id.
 intros v Hv. unfold fsubsts. rewrite list_assoc_dft_alt.
 assert (H : ~Vars.In v (subinvars sub)) by varsdec.
 rewrite subinvars_in, <- list_assoc_notin in H.
 now rewrite H.
Qed.

Lemma term_fsubsts_bsubst sub n u t :
 sub_closed sub = true ->
 term_fsubsts sub (term_bsubst n u t) =
  term_bsubst n (term_fsubsts sub u) (term_fsubsts sub t).
Proof.
 intros CL.
 revert t.
 fix IH 1. destruct t; simpl; auto.
 - unfold fsubsts; rewrite list_assoc_dft_alt.
   destruct (list_assoc v sub) eqn:E; simpl; auto.
   symmetry. apply closed_bsubst.
   apply list_assoc_in2 in E.
   unfold sub_closed in CL. rewrite forallb_forall in CL.
   now apply (CL (v,t)).
 - case eqbspec; simpl; auto.
 - f_equal. clear f.
   revert l. fix IH' 1. destruct l; simpl; auto.
   f_equal. apply IH. apply IH'.
Qed.

Lemma fsubsts_bsubst sub n u A :
 sub_closed sub = true ->
 form_fsubsts sub (form_bsubst n u A) =
  form_bsubst n (term_fsubsts sub u) (form_fsubsts sub A).
Proof.
 intros CL. revert n.
 induction A; simpl; intros n; f_equal; auto.
 injection (term_fsubsts_bsubst sub n u (Fun "" l)); auto.
Qed.

Lemma fsubsts_bsubst_adhoc sub x t f :
 sub_closed ((x,t)::sub) = true ->
 ~Vars.In x (fvars f) ->
 form_fsubsts ((x,t)::sub) (form_bsubst 0 (FVar x) f) =
 form_bsubst 0 t (form_fsubsts sub f).
Proof.
 intros.
 rewrite fsubsts_bsubst by trivial.
 simpl. unfold fsubsts. rewrite list_assoc_dft_alt. simpl.
 rewrite eqb_refl.
 f_equal.
 now apply form_fsubsts_notIn.
Qed.

Lemma Pr_fsubsts logic s :
  Pr logic s ->
  forall sub, sub_closed sub = true ->
  Pr logic (seq_fsubsts sub s).
Proof.
 induction 1; cbn in *; intros; auto.
 - apply R_Ax. now apply in_map.
 - apply R_Not_e with (form_fsubsts sub A); auto.
 - apply R_And_e1 with (form_fsubsts sub B); auto.
 - apply R_And_e2 with (form_fsubsts sub A); auto.
 - apply R_Or_e with (form_fsubsts sub A) (form_fsubsts sub B); auto.
 - apply R_Imp_e with (form_fsubsts sub A); auto.
 - set (vars := Vars.union (fvars (Γ⊢A)) (subvars sub)).
   set (z := fresh_var vars).
   apply R_All_i with z.
   + intros H'. apply (fvars_fsubsts_seq sub (Γ⊢A)) in H'.
     apply (fresh_var_ok vars). unfold subvars in vars. varsdec.
   + specialize (IHPr ((x,FVar z)::sub)).
     rewrite ctx_fsubsts_notIn in IHPr by varsdec.
     rewrite <- fsubsts_bsubst_adhoc with (x:=x); auto with sets.
 - rewrite fsubsts_bsubst by auto.
   apply R_All_e; auto.
 - specialize (IHPr sub).
   rewrite fsubsts_bsubst in IHPr by auto.
   apply R_Ex_i with (term_fsubsts sub t); auto.
 - set (vars := Vars.union (fvars (A::Γ⊢B)) (subvars sub)).
   set (z := fresh_var vars).
   apply R_Ex_e with z (form_fsubsts sub A).
   + intros H'. apply (fvars_fsubsts_seq sub (A::Γ⊢B) z) in H'.
     apply (fresh_var_ok vars). unfold subvars in vars. varsdec.
   + now apply IHPr1.
   + specialize (IHPr2 ((x,FVar z)::sub)).
     rewrite ctx_fsubsts_notIn in IHPr2 by varsdec.
     rewrite fsubsts_bsubst_adhoc in IHPr2; auto; try varsdec.
     rewrite form_fsubsts_notIn in IHPr2 by varsdec.
     auto.
 - apply R_Absu with l. auto.
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
 - apply R_Not_e with A; auto.
 - apply R_And_e1 with B; auto.
 - apply R_And_e2 with A; auto.
 - apply R_Or_e with A B; auto.
 - apply R_Imp_e with A; auto.
 - set (vars := Vars.add x (fvars (Γ' ⊢ A))).
   set (z := fresh_var vars).
   assert (Hz : ~Vars.In z vars) by (apply fresh_var_ok).
   clearbody z; unfold vars in *; clear vars.
   set (Γ2 := ctx_fsubsts [(x,FVar z)] Γ').
   assert (~Vars.In x (fvars Γ2)).
   { intros IN. apply fvars_fsubsts_ctx in IN. varsdec'. }
   assert (PR : Pr l (Γ2 ⊢ ∀A)).
   { apply R_All_i with x.
     - varsdec'.
     - apply IHPr. clear IHPr. constructor.
       rewrite <- (ctx_fsubsts_nop [(x, FVar z)] Γ) by varsdec'.
       now apply ListSubset_map. }
   apply Pr_fsubsts with (sub:=[(z,FVar x)]) in PR; auto.
   simpl in PR.
   assert (E : ctx_fsubsts [(z, FVar x)] Γ2 = Γ').
   { unfold Γ2.
     rewrite !ctx_fsubsts_alt.
     rewrite ctx_vmap_vmap. apply ctx_vmap_id.
     intros v IN. unfold fsubsts. simpl.
     case eqbspec; simpl; case eqbspec; intros; subst; auto.
     easy.
     varsdec'. }
   rewrite E in PR.
   rewrite form_fsubsts_nop in PR by varsdec'.
   trivial.
 - apply R_Ex_i with t; auto.
 - set (vars := Vars.add x (fvars (A::Γ' ⊢ B))).
   set (z := fresh_var vars).
   assert (Hz : ~Vars.In z vars) by (apply fresh_var_ok).
   clearbody z; unfold vars in *; clear vars.
   set (Γ2 := ctx_fsubsts [(x,FVar z)] Γ').
   assert (~Vars.In x (fvars Γ2)).
   { intros IN. apply fvars_fsubsts_ctx in IN. varsdec'. }
   assert (PR : Pr l (Γ2 ⊢ B)).
   { apply R_Ex_e with x A.
     - varsdec'.
     - apply IHPr1. clear IHPr1 IHPr2. constructor.
       rewrite <- (ctx_fsubsts_nop [(x, FVar z)] Γ) by varsdec'.
       now apply ListSubset_map.
     - apply IHPr2. clear IHPr1 IHPr2. constructor.
       apply ListSubset_cons.
       rewrite <- (ctx_fsubsts_nop [(x, FVar z)] Γ) by varsdec'.
       now apply ListSubset_map. }
   apply Pr_fsubsts with (sub:=[(z,FVar x)]) in PR; auto.
   simpl in PR.
   assert (E : ctx_fsubsts [(z, FVar x)] Γ2 = Γ').
   { unfold Γ2.
     rewrite !ctx_fsubsts_alt.
     rewrite ctx_vmap_vmap. apply ctx_vmap_id.
     intros v IN. unfold fsubsts. simpl.
     case eqbspec; simpl; case eqbspec; intros; subst; auto.
     easy.
     varsdec'. }
   rewrite E in PR.
   rewrite form_fsubsts_nop in PR by varsdec'.
   trivial.
 - apply R_Absu with l; auto.
Qed.
