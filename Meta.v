
(** * Some meta-properties of the Mix encoding *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Toolbox.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Implicit Type t u : term.
Implicit Type f : formula.

(** The substitution lemma for proof derivations *)

Ltac tryinst :=
 repeat match goal with
 | H : (forall h, BClosed_sub h -> _), H' : BClosed_sub _ |- _ =>
   specialize (H _ H') end.

Lemma Pr_vmap logic (s:sequent) :
  Pr logic s ->
  forall h, BClosed_sub h ->
  Pr logic (vmap h s).
Proof.
 induction 1; cbn in *; intros; try (tryinst; eauto 2; fail).
 - now apply R_Ax, in_map.
 - destruct (exist_fresh (fvars (vmap h (Γ⊢A)))) as (z,Hz).
   rewrite Names.union_spec in *.
   apply R_All_i with z; auto.
   rewrite (vmap_bsubst_adhoc h x) by auto.
   rewrite <- (ctx_sub_set_ext x (FVar z)) by auto.
   apply IHPr. now apply bclosed_sub_set.
 - rewrite form_vmap_bsubst by auto. apply R_All_e; auto.
 - apply R_Ex_i with (vmap h t); auto.
   rewrite <- form_vmap_bsubst by auto. apply IHPr; auto.
 - destruct (exist_fresh (fvars (vmap h (A::Γ⊢B)))) as (z,Hz).
   rewrite !Names.union_spec in H.
   apply R_Ex_e with z (vmap h A); auto.
   rewrite (vmap_bsubst_adhoc h x) by auto.
   rewrite <- (ctx_sub_set_ext x (FVar z)) by auto.
   rewrite <- (form_sub_set_ext x (FVar z) h B) by auto.
   apply IHPr2. now apply bclosed_sub_set.
Qed.

Lemma Pr_fsubst logic (s:sequent) :
  Pr logic s ->
  forall v t, BClosed t ->
  Pr logic (fsubst v t s).
Proof.
 intros.
 unfold fsubst.
 apply Pr_vmap; auto.
 intros x. unfold varsubst. case eqbspec; auto.
Qed.

Lemma Valid_vmap logic (d:derivation) :
 Valid logic d ->
 forall h, BClosed_sub h ->
  exists d', Valid logic d' /\ claim d' = vmap h (claim d).
Proof.
 intros.
 apply Provable_alt.
 apply Pr_vmap; auto.
 apply Provable_alt.
 now exists d.
Qed.

Lemma Valid_fsubst logic (d:derivation) :
  Valid logic d ->
  forall v t, BClosed t ->
   exists d', Valid logic d' /\ claim d' = fsubst v t (claim d).
Proof.
 intros.
 apply Valid_vmap; auto.
 intros x. unfold varsubst. case eqbspec; auto.
Qed.

(** We could even be more specific about the derivation of
    the substituted sequent : it is roughly the substituted
    derivation, apart for rules [R_All_i] and [R_Ex_e] where
    we shift to some fresh variable. *)

Definition getA ds :=
 match ds with
 | (Rule _ (_⊢A) _) :: _ => A
 | _ => True
 end.

Instance deriv_vmap : VMap derivation :=
 fix deriv_vmap h d :=
  let '(Rule r s ds) := d in
  match r with
  | All_i x =>
    let z := fresh (fvars (vmap h s)) in
    let h' := sub_set x (FVar z) h in
    Rule (All_i z) (vmap h s) (List.map (deriv_vmap h') ds)
  | Ex_e x =>
    let z := fresh (Names.union (fvars (vmap h (getA ds)))
                                (fvars (vmap h s))) in
    let h' := sub_set x (FVar z) h in
    Rule (Ex_e z) (vmap h s) (List.map (deriv_vmap h') ds)
  | _ =>
    Rule (vmap h r) (vmap h s) (List.map (deriv_vmap h) ds)
  end.

Lemma claim_vmap h d s : Claim d s -> Claim (vmap h d) (vmap h s).
Proof.
 destruct d as ([ ],s',ds); simpl; intros <-; auto.
Qed.

Ltac doClaim h :=
 match goal with
 | H : Claim _ _ |- _ => apply (claim_vmap h) in H; exact H
 end.

Lemma Valid_vmap_direct logic (d:derivation) :
 Valid logic d ->
 forall h, BClosed_sub h ->
 Valid logic (vmap h d).
Proof.
 induction 1; intros h CL; cbn; try (econstructor; eauto; doClaim h).
 - constructor. now apply in_map.
 - setfresh vars z Hz.
   set (h':=sub_set x (FVar z) h).
   constructor.
   + cbn. namedec.
   + apply IHValid, bclosed_sub_set; auto.
   + cbn in H.
     rewrite <- (ctx_sub_set_ext x (FVar z)) by namedec.
     rewrite (vmap_bsubst_adhoc h x) by (auto; namedec).
     doClaim h'.
 - rewrite form_vmap_bsubst by auto. constructor; auto.
   doClaim h.
 - constructor; auto.
   rewrite <- form_vmap_bsubst by auto. doClaim h.
 - fold (getA [d1;d2]).
   assert (E : getA [d1;d2] = (∃A)%form).
   { destruct d1. cbn in H2. now subst s. }
   rewrite E.
   setfresh vars z Hz.
   set (h':=sub_set x (FVar z) h).
   apply V_Ex_e with (vmap h A).
   + cbn. namedec.
   + apply IHValid1, bclosed_sub_set; auto.
   + apply IHValid2, bclosed_sub_set; auto.
   + cbn in H.
     rewrite <- (ctx_sub_set_ext x (FVar z)) by namedec.
     rewrite <- (form_sub_set_ext x (FVar z) h A) by namedec.
     doClaim h'.
   + cbn in H.
     rewrite <- (ctx_sub_set_ext x (FVar z)) by namedec.
     rewrite <- (form_sub_set_ext x (FVar z) h B) by namedec.
     rewrite (vmap_bsubst_adhoc h x) by (auto; namedec).
     doClaim h'.
Qed.

(** Same in the case of a simple [fsubst] substitution. *)

Lemma Valid_fsubst_direct logic (d:derivation) v t :
  BClosed t ->
  Valid logic d ->
  Valid logic (fsubst v t d) /\
  Claim (fsubst v t d) (fsubst v t (claim d)).
Proof.
 intros.
 split. apply Valid_vmap_direct; auto.
 intros x. unfold varsubst. case eqbspec; auto.
 now apply claim_vmap.
Qed.

(** Thanks to this more precise result, we could say that
    a BClosed derivation stays BClosed after a BClosed substitution. *)

Lemma closed_deriv_vmap (d:derivation) :
 BClosed d -> forall h, BClosed_sub h -> BClosed (vmap h d).
Proof.
 unfold BClosed.
 induction d as [r s ds IH] using derivation_ind'.
 intros H. cbn in H. rewrite !max_0 in H. destruct H as (Hr & Hs & Hds).
 assert (IH' : forall h, BClosed_sub h -> list_max (map level (map (vmap h) ds)) = 0).
 { intros h Hh. apply list_max_0. intros n.
   unfold vmap, vmap_list. rewrite map_map.
   rewrite in_map_iff. intros (d & Hd & Hd').
   rewrite Forall_forall in IH.
   rewrite IH in Hd; auto.
   rewrite list_max_0 in Hds. apply Hds. now apply in_map. }
 clear IH Hds.
 intros h Hh; destruct r; cbn; repeat (apply max_0; split);
 try apply IH'; auto; try apply bclosed_seq_vmap; auto;
 try apply bclosed_sub_set; try apply bclosed_term_vmap; auto.
Qed.

Lemma closed_deriv_fsubst (d:derivation) v t :
 BClosed d -> BClosed t -> BClosed (fsubst v t d).
Proof.
 intros. apply closed_deriv_vmap; auto.
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

Lemma sub_rename_bclosed x z : BClosed_sub (sub_rename x z).
Proof.
 unfold BClosed_sub, sub_rename. auto with eqb.
Qed.

Hint Resolve sub_rename_bclosed.

Lemma sub_rename_at x z : sub_rename x z x = FVar z.
Proof.
 unfold sub_rename. now rewrite eqb_refl.
Qed.

Lemma sub_rename_else x z v : v<>x -> sub_rename x z v = FVar v.
Proof.
 unfold sub_rename. now case eqbspec.
Qed.

Lemma vmap_rename_notIn x z (c:context) :
 x<>z -> ~Names.In x (fvars (vmap (sub_rename x z) c)).
Proof.
 intros NE IN. apply ctx_fvars_vmap in IN.
 rewrite flatmap_in in IN. destruct IN as (v & IN & _).
 revert IN. unfold sub_rename. case eqbspec; cbn; namedec.
Qed.

Lemma form_rename_id x z (f:formula) :
 ~Names.In x (fvars f) -> vmap (sub_rename x z) f = f.
Proof.
 intros. apply form_vmap_id. intros. apply sub_rename_else. namedec.
Qed.

Lemma ctx_rename_id x z (c:context) :
 ~Names.In x (fvars c) -> vmap (sub_rename x z) c = c.
Proof.
 intros. apply ctx_vmap_id. intros. apply sub_rename_else. namedec.
Qed.

Lemma ctx_rename_rename x z (c:context) :
 ~Names.In z (fvars c) ->
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
 - destruct (exist_fresh (Names.add x (fvars (Γ' ⊢ A)))) as (z,Hz).
   cbn in *.
   rewrite Names.add_spec, Names.union_spec in *.
   set (Γ'z := vmap (sub_rename x z) Γ').
   assert (~Names.In x (fvars Γ'z))
    by (apply vmap_rename_notIn; intuition).
   assert (ListSubset Γ Γ'z).
   { rewrite <- (ctx_rename_id x z Γ) by tauto.
     now apply ListSubset_map. }
   assert (PR : Pr logic (Γ'z ⊢ ∀A)).
   { apply R_All_i with x; cbn; intuition. }
   apply Pr_vmap with (h := sub_rename z x) in PR; auto.
   revert PR. cbn; unfold Γ'z.
   rewrite ctx_rename_rename, form_rename_id; intuition.
 - destruct (exist_fresh (Names.add x (fvars (A::Γ' ⊢ B)))) as (z,Hz).
   cbn in *.
   rewrite Names.add_spec, ?Names.union_spec in *.
   set (Γ'z := vmap (sub_rename x z) Γ').
   assert (~Names.In x (fvars Γ'z))
    by (apply vmap_rename_notIn; intuition).
   assert (ListSubset Γ Γ'z).
   { rewrite <- (ctx_rename_id x z Γ) by tauto.
     now apply ListSubset_map. }
   assert (PR : Pr logic (Γ'z ⊢ B)).
   { apply R_Ex_e with x A; cbn; intuition. }
   apply Pr_vmap with (h := sub_rename z x) in PR; auto.
   revert PR. cbn; unfold Γ'z.
   rewrite ctx_rename_rename, form_rename_id; intuition.
Qed.

Lemma Valid_weakening logic d :
  Valid logic d ->
  forall s', SubsetSeq (claim d) s' ->
  exists d', Valid logic d' /\ Claim d' s'.
Proof.
 intros.
 apply Provable_alt.
 apply Pr_weakening with (claim d); auto.
 apply Provable_alt.
 now exists d.
Qed.

Fixpoint subset_deriv (c:context)(d:derivation) : derivation :=
  match d with
  | Rule Not_i (_⊢~A) [d1] =>
    Rule Not_i (c⊢~A) [subset_deriv (A::c) d1]
  | Rule Or_e (_⊢f) [(Rule _ (_⊢A\/B) _ as d1);d2;d3] =>
    Rule Or_e (c⊢f)
     [subset_deriv c d1; subset_deriv (A::c) d2; subset_deriv (B::c) d3]
  | Rule Imp_i (_⊢A->B) [d1] =>
    Rule Imp_i (c⊢A->B) [subset_deriv (A::c) d1]
  | Rule (All_i x) (_⊢f) [d1] =>
    let z := fresh (Names.add x (fvars (c⊢f))) in
    let h' := sub_rename x z in
    let cz := vmap h' c in
    let d' := Rule (All_i x) (cz⊢f) [subset_deriv cz d1] in
    vmap (sub_rename z x) d'
  | Rule (Ex_e x) (_⊢f) [(Rule _ (_ ⊢ ∃A) _ as d1);d2] =>
    let z := fresh (Names.add x (fvars (A::c⊢f))) in
    let h' := sub_rename x z in
    let cz := vmap h' c in
    let ds' :=
     [subset_deriv cz d1; subset_deriv ((bsubst 0 (FVar x) A)::cz) d2] in
    let d' := Rule (Ex_e x) (cz⊢f) ds' in
    vmap (sub_rename z x) d'
  | Rule Absu (_⊢f) [d1] =>
    Rule Absu (c⊢f) [subset_deriv ((~f)::c) d1]%form
  | Rule r (_⊢f) ds =>
    Rule r (c⊢f) (List.map (subset_deriv c) ds)
  end.

Ltac break :=
 match goal with
 | |- context [match ?x with _ => _ end] => destruct x; break
 | _ => idtac
 end.

Lemma claim_subset c c' d f :
 Claim d (c⊢f) -> Claim (subset_deriv c' d) (c'⊢f).
Proof.
 destruct d as (r,(c0,f0),ds). intros [= -> ->].
 destruct r; cbn -[fresh vmap]; break; auto.
 - setfresh vars z Hz.
   cbn. f_equal.
   + apply ctx_rename_rename. namedec.
   + apply form_rename_id. namedec.
 - setfresh vars z Hz.
   cbn. f_equal.
   + apply ctx_rename_rename. namedec.
   + apply form_rename_id. namedec.
Qed.

Lemma Valid_weakening_direct logic d :
  Valid logic d ->
  forall f c c',
    Claim d (c⊢f) -> ListSubset c c' ->
    Valid logic (subset_deriv c' d).
Proof.
 induction 1; intros f c c' [= <- <-] SU; cbn -[fresh vmap];
 try (econstructor; eauto using claim_subset; fail).
 - destruct d1. cbn in H2; subst s.
   econstructor; eauto using claim_subset.
 - setfresh vars z Hz.
   set (h := sub_rename x z).
   apply Valid_vmap_direct; auto.
   cbn in H.
   constructor; eauto using claim_subset.
   + unfold h. cbn - [vmap sub_rename].
     generalize (vmap_rename_notIn x z c'). namedec.
   + eapply IHValid; eauto.
     rewrite <- (ctx_rename_id x z Γ) by namedec.
     now apply ListSubset_map.
 - destruct d1. cbn in H2; subst s.
   setfresh vars z Hz.
   set (h := sub_rename x z).
   apply Valid_vmap_direct; auto.
   cbn in H.
   econstructor; eauto using claim_subset.
   + unfold h. cbn - [vmap sub_rename].
     generalize (vmap_rename_notIn x z c'). namedec.
   + eapply IHValid1; eauto.
     rewrite <- (ctx_rename_id x z Γ) by namedec.
     now apply ListSubset_map.
   + eapply IHValid2; eauto.
     apply ListSubset_cons.
     rewrite <- (ctx_rename_id x z Γ) by namedec.
     now apply ListSubset_map.
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

Lemma Pr_app_l logic Γ Δ A :
 Pr logic (Γ ⊢ A) ->
 Pr logic (Γ++Δ ⊢ A).
Proof.
 intros. eapply Pr_weakening; eauto. constructor. intro.
 rewrite in_app_iff. now left.
Qed.

Lemma Pr_app_r logic Γ Δ A :
 Pr logic (Δ ⊢ A) ->
 Pr logic (Γ++Δ ⊢ A).
Proof.
 intros. eapply Pr_weakening; eauto. constructor. intro.
 rewrite in_app_iff. now right.
Qed.

Lemma Valid_pop logic A B Γ d :
 Valid logic d -> Claim d (Γ ⊢ A) ->
 let d' := subset_deriv (B::Γ) d in
 Valid logic d' /\ Claim d' (B::Γ ⊢ A).
Proof.
 intros. split. eapply Valid_weakening_direct; eauto.
 intro. cbn. intuition.
 eapply claim_subset; eauto.
Qed.

Lemma Valid_dup logic A B Γ d :
 Valid logic d -> Claim d (A::Γ ⊢ B) ->
 let d' := subset_deriv (A::A::Γ) d in
 Valid logic d' /\ Claim d' (A::A::Γ ⊢ B).
Proof.
 intros. split. eapply Valid_weakening_direct; eauto.
 intro. cbn. intuition.
 eapply claim_subset; eauto.
Qed.

Lemma Valid_swap logic A B C Γ d :
 Valid logic d -> Claim d (A::B::Γ ⊢ C) ->
 let d' := subset_deriv (B::A::Γ) d in
 Valid logic d' /\ Claim d' (B::A::Γ ⊢ C).
Proof.
 intros. split. eapply Valid_weakening_direct; eauto.
 intro. cbn. intuition.
 eapply claim_subset; eauto.
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
 BClosed t ->
 Pr logic (bsubst 0 t A :: Γ ⊢ B) ->
 Pr logic ((∀A) :: Γ ⊢ B)%form.
Proof.
 intros.
 apply R_Imp_e with (bsubst 0 t A).
 - now apply Pr_pop, R_Imp_i.
 - now apply R_All_e, R'_Ax.
Qed.

Lemma R'_Ex_e logic Γ A B x :
 ~Names.In x (fvars (A::Γ⊢B)) ->
 Pr logic (bsubst 0 (FVar x) A :: Γ ⊢ B) ->
 Pr logic ((∃A) :: Γ ⊢ B)%form.
Proof.
 intros.
 apply R_Ex_e with x A.
 - cbn in *. namedec.
 - apply R'_Ax.
 - now apply Pr_swap, Pr_pop.
Qed.
