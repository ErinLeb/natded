
(** Some Meta-properties (proved on the Mix encoding) *)

Require Import RelationClasses Arith Omega Defs Proofs Mix.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

Lemma closed_bsubst_id n u (t:term) :
 closed t -> bsubst n u t = t.
Proof.
 unfold closed. intros H. revert t H.
 fix IH 1. destruct t; cbn; try easy.
 intros H. f_equal. clear f.
 revert l H.
 fix IH' 1. destruct l; cbn; try easy.
 intros H. f_equal. apply IH. omega with *. apply IH'. omega with *.
Qed.

(** [vmap] basic results : extensionality, identity, composition *)

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

(** Estimating free variables of a substitution *)

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

(** Alternating [vmap] and [bsubst] *)

Definition closed_sub (h:variable->term) :=
 forall v, closed (h v).

Lemma term_vmap_bsubst h n u (t:term) :
 closed_sub h ->
 vmap h (bsubst n u t) = bsubst n (vmap h u) (vmap h t).
Proof.
 intros CL.
 revert t.
 fix IH 1. destruct t; cbn.
 - symmetry. apply closed_bsubst_id. apply CL.
 - auto with eqb.
 - f_equal. clear f.
   revert l. fix IH' 1. destruct l; simpl; f_equal; auto.
Qed.

Lemma form_vmap_bsubst h n u (f:formula) :
 closed_sub h ->
 vmap h (bsubst n u f) = bsubst n (vmap h u) (vmap h f).
Proof.
 intros CL. revert n.
 induction f; cbn; intros n; f_equal; auto.
 injection (term_vmap_bsubst h n u (Fun "" l)); auto.
Qed.

Definition sub_set (x:variable)(t:term)(h:variable->term) :=
 fun v => if v =? x then t else h v.

Lemma closed_sub_set x t h :
 closed_sub h -> closed t -> closed_sub (sub_set x t h).
Proof.
 unfold sub_set, closed_sub; auto with eqb.
Qed.

Lemma sub_set_at x t h : sub_set x t h x = t.
Proof.
 unfold sub_set. now rewrite eqb_refl.
Qed.

Lemma sub_set_else x t h v : v<>x -> sub_set x t h v = h v.
Proof.
 unfold sub_set. now case eqbspec.
Qed.

Lemma form_sub_set_ext x t h (f:formula) :
 ~Vars.In x (fvars f) -> vmap (sub_set x t h) f = vmap h f.
Proof.
 intros. apply form_vmap_ext. intros.
 rewrite sub_set_else; auto with set.
Qed.

Lemma ctx_sub_set_ext x t h (c:context) :
 ~Vars.In x (fvars c) -> vmap (sub_set x t h) c = vmap h c.
Proof.
 intros. apply ctx_vmap_ext. intros.
 rewrite sub_set_else; auto with set.
Qed.

Lemma vmap_bsubst_adhoc h x t (f:formula) :
 closed_sub h ->
 closed t ->
 ~Vars.In x (fvars f) ->
 bsubst 0 t (vmap h f) =
  vmap (sub_set x t h) (bsubst 0 (FVar x) f).
Proof.
 intros.
 rewrite form_vmap_bsubst by now apply closed_sub_set.
 cbn. rewrite sub_set_at. f_equal. now rewrite form_sub_set_ext.
Qed.

(** The substitution lemma for proof derivations *)

Ltac Fresh z vars :=
  set (z := fresh_var vars);
  assert (Hz : ~Vars.In z vars) by (apply fresh_var_ok);
  clearbody z.

Ltac tryinst :=
 repeat match goal with
 | H : (forall h, closed_sub h -> _), H' : closed_sub _ |- _ =>
   specialize (H _ H') end.

Lemma Pr_vmap logic (s:sequent) :
  Pr logic s ->
  forall h, closed_sub h ->
  Pr logic (vmap h s).
Proof.
 induction 1; cbn in *; intros; try (tryinst; eauto 2; fail).
 - now apply R_Ax, in_map.
 - Fresh z (Vars.union (fvars (Γ⊢A)) (fvars (vmap h (Γ⊢A)))).
   rewrite Vars.union_spec in *.
   apply R_All_i with z; auto.
   rewrite (vmap_bsubst_adhoc h x) by auto.
   rewrite <- (ctx_sub_set_ext x (FVar z)) by auto.
   apply IHPr. now apply closed_sub_set.
 - rewrite form_vmap_bsubst by auto. apply R_All_e; auto.
 - apply R_Ex_i with (vmap h t).
   rewrite <- form_vmap_bsubst by auto. apply IHPr; auto.
 - Fresh z (Vars.union (fvars (A::Γ⊢B)) (fvars (vmap h (A::Γ⊢B)))).
   rewrite Vars.union_spec in Hz.
   rewrite !Vars.union_spec in H.
   apply R_Ex_e with z (vmap h A); auto.
   rewrite (vmap_bsubst_adhoc h x) by auto.
   rewrite <- (ctx_sub_set_ext x (FVar z)) by auto.
   rewrite <- (form_sub_set_ext x (FVar z) h B) by auto.
   apply IHPr2. now apply closed_sub_set.
Qed.

Lemma Pr_fsubst logic (s:sequent) :
  Pr logic s ->
  forall v t, closed t ->
  Pr logic (fsubst v t s).
Proof.
 intros.
 change (fsubst v t) with (vmap (varsubst v t)).
 apply Pr_vmap; auto.
 intros x. unfold varsubst. case eqbspec; auto.
Qed.

(** Weakening of contexts and sequents *)

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

Lemma ListSubset_map {A B} (f:A->B) (l l': list A) :
  ListSubset l l' -> ListSubset (map f l) (map f l').
Proof.
 intros SU b. rewrite !in_map_iff.
 intros (a & Ha & Ha'). apply SU in Ha'. now exists a.
Qed.
Hint Resolve ListSubset_cons ListSubset_map.

(** The weakening lemma for proof derivations *)

Definition sub_rename (x z : variable) :=
 fun v => if v =? x then FVar z else FVar v.

Lemma sub_rename_closed x z : closed_sub (sub_rename x z).
Proof.
 unfold closed_sub, sub_rename. auto with eqb.
Qed.

Lemma sub_rename_at x z : sub_rename x z x = FVar z.
Proof.
 unfold sub_rename. now rewrite eqb_refl.
Qed.

Lemma sub_rename_else x z v : v<>x -> sub_rename x z v = FVar v.
Proof.
 unfold sub_rename. now case eqbspec.
Qed.

Lemma vmap_rename_notIn x z (c:context) :
 x<>z -> ~Vars.In x (fvars (vmap (sub_rename x z) c)).
Proof.
 intros NE IN. apply ctx_fvars_vmap in IN.
 rewrite vars_flatmap_in in IN. destruct IN as (v & IN & _).
 revert IN. unfold sub_rename. case eqbspec; cbn; varsdec.
Qed.

Lemma form_rename_id x z (f:formula) :
 ~Vars.In x (fvars f) -> vmap (sub_rename x z) f = f.
Proof.
 intros. apply form_vmap_id. intros. apply sub_rename_else. varsdec.
Qed.

Lemma ctx_rename_id x z (c:context) :
 ~Vars.In x (fvars c) -> vmap (sub_rename x z) c = c.
Proof.
 intros. apply ctx_vmap_id. intros. apply sub_rename_else. varsdec.
Qed.

Lemma ctx_rename_rename x z (c:context) :
 ~Vars.In z (fvars c) ->
 vmap (sub_rename z x) (vmap (sub_rename x z) c) = c.
Proof.
 intros.
 rewrite ctx_vmap_vmap.
 apply ctx_vmap_id.
 unfold sub_rename. intros. case eqbspec; cbn; auto with eqb set.
Qed.

Ltac tryinst2 :=
 repeat match goal with
 | H : (forall s, SubsetSeq _ s -> _),
   H' : ListSubset _ _ |- _ => specialize (H _ (SubSeq _ _ _ H')) end.

Lemma Pr_weakening logic s s' :
  Pr logic s ->
  SubsetSeq s s' ->
  Pr logic s'.
Proof.
 intros H. revert s'.
 induction H; inversion_clear 1; auto; try (tryinst2; eauto 2; fail).
 - apply R_Or_e with A B; auto.
 - Fresh z (Vars.add x (fvars (Γ' ⊢ A))). cbn in *.
   rewrite Vars.add_spec, Vars.union_spec in *.
   set (Γ'z := vmap (sub_rename x z) Γ').
   assert (~Vars.In x (fvars Γ'z))
    by (apply vmap_rename_notIn; intuition).
   assert (ListSubset Γ Γ'z).
   { rewrite <- (ctx_rename_id x z Γ) by tauto.
     now apply ListSubset_map. }
   assert (PR : Pr logic (Γ'z ⊢ ∀A)).
   { apply R_All_i with x; cbn; intuition. }
   apply Pr_vmap with (h := sub_rename z x) in PR;
    auto using sub_rename_closed.
   revert PR. cbn; unfold Γ'z.
   rewrite ctx_rename_rename, form_rename_id; intuition.
 - Fresh z (Vars.add x (fvars (A::Γ' ⊢ B))). cbn in *.
   rewrite Vars.add_spec, ?Vars.union_spec in *.
   set (Γ'z := vmap (sub_rename x z) Γ').
   assert (~Vars.In x (fvars Γ'z))
    by (apply vmap_rename_notIn; intuition).
   assert (ListSubset Γ Γ'z).
   { rewrite <- (ctx_rename_id x z Γ) by tauto.
     now apply ListSubset_map. }
   assert (PR : Pr logic (Γ'z ⊢ B)).
   { apply R_Ex_e with x A; cbn; intuition. }
   apply Pr_vmap with (h := sub_rename z x) in PR;
    auto using sub_rename_closed.
   revert PR. cbn; unfold Γ'z.
   rewrite ctx_rename_rename, form_rename_id; intuition.
Qed.

(** Some examples of weakening *)

Lemma Pr_pop logic A B Γ :
  Pr logic (Γ ⊢ A) ->
  Pr logic (B::Γ ⊢ A).
Proof.
 intros. eapply Pr_weakening; eauto. constructor.
 intro. intuition.
Qed.

Lemma Pr_dup logic A B Γ :
  Pr logic (A::A::Γ ⊢ B) ->
  Pr logic (A::Γ ⊢ B).
Proof.
 intros. eapply Pr_weakening; eauto. constructor.
 intro. cbn. intuition.
Qed.

Lemma Pr_swap logic A B C Γ :
  Pr logic (A::B::Γ ⊢ C) ->
  Pr logic (B::A::Γ ⊢ C).
Proof.
 intros. eapply Pr_weakening; eauto. constructor.
 intro. cbn. intuition.
Qed.

(** Admissible rules *)

Lemma R'_Ax logic Γ A :
 Pr logic (A::Γ ⊢ A).
Proof.
 apply R_Ax. simpl; auto.
Qed.

Lemma R'_And_e logic Γ A B C :
 Pr logic (A::B::Γ ⊢ C) ->
 Pr logic ((A/\B)::Γ ⊢ C)%form.
Proof.
 intro.
 apply R_Imp_e with A.
 - apply R_Imp_e with B.
   + apply Pr_pop.
     apply R_Imp_i.
     now apply R_Imp_i.
   + apply R_And_e2 with A. apply R'_Ax.
 - apply R_And_e1 with B. apply R'_Ax.
Qed.

Lemma R'_Or_e logic Γ A B C :
 Pr logic (A::Γ ⊢ C) -> Pr logic (B::Γ ⊢ C) ->
 Pr logic ((A\/B)::Γ ⊢ C)%form.
Proof.
 intros.
 apply R_Or_e with A B.
 - apply R'_Ax.
 - now apply Pr_swap, Pr_pop.
 - now apply Pr_swap, Pr_pop.
Qed.

Lemma R'_Imp_e logic Γ A B :
 Pr logic (Γ ⊢ A) ->
 Pr logic ((A->B)::Γ ⊢ B)%form.
Proof.
 intro.
 apply R_Imp_e with A.
 - apply R'_Ax.
 - now apply Pr_pop.
Qed.

Lemma R'_Imp_e_bis logic Γ A B C :
 Pr logic (B::Γ ⊢ C) ->
 Pr logic (A::(A->B)::Γ ⊢ C)%form.
Proof.
 intro.
 apply R_Imp_e with B.
 - now apply Pr_pop, Pr_pop, R_Imp_i.
 - apply Pr_swap. apply R'_Imp_e. apply R'_Ax.
Qed.

Lemma R'_All_e logic Γ A B t :
 Pr logic (bsubst 0 t A :: Γ ⊢ B) ->
 Pr logic ((∀A) :: Γ ⊢ B)%form.
Proof.
 intros.
 apply R_Imp_e with (bsubst 0 t A).
 - now apply Pr_pop, R_Imp_i.
 - apply R_All_e, R'_Ax.
Qed.

Lemma R'_Ex_e logic Γ A B x :
 ~Vars.In x (fvars (A::Γ⊢B)) ->
 Pr logic (bsubst 0 (FVar x) A :: Γ ⊢ B) ->
 Pr logic ((∃A) :: Γ ⊢ B)%form.
Proof.
 intros.
 apply R_Ex_e with x A.
 - cbn in *. varsdec.
 - apply R'_Ax.
 - now apply Pr_swap, Pr_pop.
Qed.

(** A few classical proofs *)

Lemma DoubleNeg A :
 Pr Classic ([] ⊢ ~~A -> A)%form.
Proof.
 apply R_Imp_i.
 apply R_Absu; trivial.
 apply R_Not_e with (~A)%form; apply R_Ax; cbn; auto.
Qed.

Lemma Excluded_Middle_core logic A :
 Pr logic ([] ⊢ ~~(A\/~A)).
Proof.
 apply R_Not_i.
 apply R_Not_e with (A\/~A)%form; [|apply R'_Ax].
 apply R_Or_i2.
 apply R_Not_i.
 apply R_Not_e with (A\/~A)%form; [|apply Pr_pop, R'_Ax ].
 apply R_Or_i1.
 apply R'_Ax.
Qed.

Lemma Excluded_Middle A :
 Pr Classic ([] ⊢ A\/~A).
Proof.
 apply R_Imp_e with (~~(A\/~A))%form.
 - apply DoubleNeg.
 - apply Excluded_Middle_core.
Qed.

Lemma Peirce A B :
 Pr Classic ([] ⊢ ((A->B)->A)->A).
Proof.
 apply R_Imp_i.
 apply R_Absu; trivial.
 apply R_Not_e with A; [|apply R'_Ax].
 apply Pr_swap.
 apply R'_Imp_e.
 apply R_Imp_i.
 apply R_Fa_e.
 apply R_Not_e with A; apply R_Ax; cbn; auto.
Qed.

(** TODO: prove that these classical laws imply Absurd *)
