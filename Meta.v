
(** Some Meta-properties (proved on the Mix encoding) *)

Require Import RelationClasses Arith Omega Defs Proofs Mix.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Lemma closed_bsubst_id n u (t:term) :
 closed t -> bsubst n u t = t.
Proof.
 unfold closed.
 induction t as [ | |f l IH] using term_ind'; cbn; try easy.
 rewrite list_max_map_0.
 intros H. f_equal. apply map_id_iff. intuition.
Qed.

(** [vmap] basic results : extensionality, identity, composition *)

Lemma term_vmap_ext h h' (t:term) :
 (forall v:variable, Vars.In v (fvars t) -> h v = h' v) ->
 vmap h t = vmap h' t.
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn; auto with set.
 intros H. f_equal. apply map_ext_in; eauto with set.
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

Lemma seq_vmap_ext h h' (s:sequent) :
 (forall v:variable, Vars.In v (fvars s) -> h v = h' v) ->
 vmap h s = vmap h' s.
Proof.
 destruct s; intros. cbn in *. f_equal.
 apply ctx_vmap_ext; auto with set.
 apply form_vmap_ext; auto with set.
Qed.

Lemma term_vmap_id h (t:term) :
 (forall v:variable, Vars.In v (fvars t) -> h v = FVar v) ->
 vmap h t = t.
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn; auto with set.
 intros H. f_equal. apply map_id_iff; eauto with set.
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
 induction t as [ | |f l IH] using term_ind'; cbn; trivial.
 f_equal. rewrite map_map. apply map_ext_in; auto.
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
 induction t as [ | |f l IH] using term_ind'; cbn.
 - varsdec.
 - varsdec.
 - intros v. rewrite vars_unionmap_in. intros (a & Ha & Ha').
   rewrite in_map_iff in Ha'. destruct Ha' as (t & <- & Ht).
   generalize (IH t Ht v Ha). apply vars_flatmap_subset; auto.
   intro. eauto with set.
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
 induction t as [ | | f l IH] using term_ind'; cbn.
 - symmetry. apply closed_bsubst_id. apply CL.
 - auto with eqb.
 - f_equal. rewrite !map_map. now apply map_ext_in.
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
 - Fresh z (fvars (vmap h (Γ⊢A))).
   rewrite Vars.union_spec in *.
   apply R_All_i with z; auto.
   rewrite (vmap_bsubst_adhoc h x) by auto.
   rewrite <- (ctx_sub_set_ext x (FVar z)) by auto.
   apply IHPr. now apply closed_sub_set.
 - rewrite form_vmap_bsubst by auto. apply R_All_e; auto.
 - apply R_Ex_i with (vmap h t).
   rewrite <- form_vmap_bsubst by auto. apply IHPr; auto.
 - Fresh z (fvars (vmap h (A::Γ⊢B))).
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

Lemma Valid_vmap logic (d:derivation) :
 Valid logic d ->
 forall h, closed_sub h ->
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
  forall v t, closed t ->
   exists d', Valid logic d' /\ claim d' = fsubst v t (claim d).
Proof.
 intros.
 apply Valid_vmap; auto.
 intros x. unfold varsubst. case eqbspec; auto.
Qed.

(** We could even be more specific about the derivation of
    the substituted sequent : it is roughly the substituted
    derivation, apart for rules [R_All_i] and [R_Ex_e] were
    we shift to some fresh variable. *)

Instance vmap_rule : VMap rule_kind :=
 fun h r =>
 match r with
 | All_e wit => All_e (vmap h wit)
 | Ex_i wit => Ex_i (vmap h wit)
 | r => r
 end.

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
    let z := fresh_var (fvars (vmap h s)) in
    let h' := sub_set x (FVar z) h in
    Rule (All_i z) (vmap h s) (List.map (deriv_vmap h') ds)
  | Ex_e x =>
    let z := fresh_var (Vars.union (fvars (vmap h (getA ds)))
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
 forall h, closed_sub h ->
 Valid logic (vmap h d).
Proof.
 induction 1; intros h CL; cbn; try (econstructor; eauto; doClaim h).
 - constructor. now apply in_map.
 - set (vars:=Vars.union _ _).
   assert (Hz := fresh_var_ok vars).
   set (z:=fresh_var vars) in *.
   set (h':=sub_set x (FVar z) h).
   constructor.
   + cbn. varsdec.
   + apply IHValid, closed_sub_set; auto.
   + cbn in H.
     rewrite <- (ctx_sub_set_ext x (FVar z)) by varsdec.
     rewrite (vmap_bsubst_adhoc h x) by (auto; varsdec).
     doClaim h'.
 - rewrite form_vmap_bsubst by auto. constructor; auto.
   doClaim h.
 - constructor; auto.
   rewrite <- form_vmap_bsubst by auto. doClaim h.
 - fold (getA [d1;d2]).
   assert (E : getA [d1;d2] = (∃A)%form).
   { destruct d1. cbn in H2. now subst s. }
   rewrite E.
   set (vars:=Vars.union _ _).
   assert (Hz := fresh_var_ok vars).
   set (z:=fresh_var vars) in *.
   set (h':=sub_set x (FVar z) h).
   apply V_Ex_e with (vmap h A).
   + cbn. varsdec.
   + apply IHValid1, closed_sub_set; auto.
   + apply IHValid2, closed_sub_set; auto.
   + cbn in H.
     rewrite <- (ctx_sub_set_ext x (FVar z)) by varsdec.
     rewrite <- (form_sub_set_ext x (FVar z) h A) by varsdec.
     doClaim h'.
   + cbn in H.
     rewrite <- (ctx_sub_set_ext x (FVar z)) by varsdec.
     rewrite <- (form_sub_set_ext x (FVar z) h B) by varsdec.
     rewrite (vmap_bsubst_adhoc h x) by (auto; varsdec).
     doClaim h'.
Qed.

(** Same in the case of a simple [fsubst] substitution. *)

Lemma Valid_fsubst_direct logic (d:derivation) v t :
  closed t ->
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
    a closed derivation stays closed after a closed substitution. *)

Lemma level_term_vmap h (t:term) :
 closed_sub h -> level (vmap h t) <= level t.
Proof.
 intros Hh.
 induction t as [ | |f l IH] using term_ind'; cbn.
 - now rewrite (Hh v).
 - trivial.
 - rewrite map_map. now apply list_max_map_incr.
Qed.

Lemma level_form_vmap h (f:formula) :
 closed_sub h -> level (vmap h f) <= level f.
Proof.
 intros Hh.
 induction f; cbn; auto with *.
 - apply (level_term_vmap h (Fun "" l) Hh).
 - omega with *.
Qed.

Lemma closed_term_vmap h (t:term) :
 closed_sub h -> closed t -> closed (vmap h t).
Proof.
 unfold closed. intros Hh Ht.
 generalize (level_term_vmap h t Hh). omega.
Qed.

Lemma closed_form_vmap h (f:formula) :
 closed_sub h -> closed f -> closed (vmap h f).
Proof.
 unfold closed. intros Hh Hf.
 generalize (level_form_vmap h f Hh). omega.
Qed.

Lemma closed_ctx_vmap h (c:context) :
 closed_sub h -> closed c -> closed (vmap h c).
Proof.
 unfold closed. intros Hh.
 induction c as [|f c IH]; cbn; auto.
 rewrite !max_0. intuition. now apply closed_form_vmap.
Qed.

Lemma closed_seq_vmap h (s:sequent) :
 closed_sub h -> closed s -> closed (vmap h s).
Proof.
 destruct s as (c,f). intros Hh. unfold closed. cbn.
 rewrite !max_0. intuition.
 now apply closed_ctx_vmap.
 now apply closed_form_vmap.
Qed.

Lemma closed_deriv_vmap (d:derivation) :
 closed d -> forall h, closed_sub h -> closed (vmap h d).
Proof.
 unfold closed.
 induction d as [r s ds IH] using derivation_ind'.
 intros H. cbn in H. rewrite !max_0 in H. destruct H as (Hr & Hs & Hds).
 assert (IH' : forall h, closed_sub h -> list_max (map level (vmap h ds)) = 0).
 { intros h Hh. apply list_max_0. intros n.
   unfold vmap, vmap_list. rewrite map_map.
   rewrite in_map_iff. intros (d & Hd & Hd').
   rewrite Forall_forall in IH.
   rewrite IH in Hd; auto.
   rewrite list_max_0 in Hds. apply Hds. now apply in_map. }
 clear IH Hds.
 intros h Hh; destruct r; cbn; repeat (apply max_0; split);
 try apply IH'; auto; try apply closed_seq_vmap; auto;
 try apply closed_sub_set; try apply closed_term_vmap; auto.
Qed.

Lemma closed_deriv_fsubst (d:derivation) v t :
 closed d -> closed t -> closed (fsubst v t d).
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
    let z := fresh_var (Vars.add x (fvars (c⊢f))) in
    let h' := sub_rename x z in
    let cz := vmap h' c in
    let d' := Rule (All_i x) (cz⊢f) [subset_deriv cz d1] in
    vmap (sub_rename z x) d'
  | Rule (Ex_e x) (_⊢f) [(Rule _ (_ ⊢ ∃A) _ as d1);d2] =>
    let z := fresh_var (Vars.add x (fvars (A::c⊢f))) in
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
 destruct r; cbn -[fresh_var vmap]; break; auto.
 - set (vars := Vars.add v _).
   assert (Hz := fresh_var_ok vars).
   set (z := fresh_var vars) in *.
   cbn -[fresh_var]. f_equal.
   + apply ctx_rename_rename. varsdec.
   + apply form_rename_id. varsdec.
 - set (vars := Vars.add v _).
   assert (Hz := fresh_var_ok vars).
   set (z := fresh_var vars) in *.
   cbn -[fresh_var]. f_equal.
   + apply ctx_rename_rename. varsdec.
   + apply form_rename_id. varsdec.
Qed.

Lemma Valid_weakening_direct logic d :
  Valid logic d ->
  forall f c c',
    Claim d (c⊢f) -> ListSubset c c' ->
    Valid logic (subset_deriv c' d).
Proof.
 induction 1; intros f c c' [= <- <-] SU; cbn -[fresh_var vmap];
 try (econstructor; eauto using claim_subset; fail).
 - destruct d1. cbn in H2; subst s.
   econstructor; eauto using claim_subset.
 - set (vars := Vars.add x _).
   assert (Hz := fresh_var_ok vars).
   set (z := fresh_var vars) in *.
   set (h := sub_rename x z).
   apply Valid_vmap_direct; auto using sub_rename_closed.
   cbn in H.
   constructor; eauto using claim_subset.
   + unfold h. cbn - [z vmap sub_rename].
     generalize (vmap_rename_notIn x z c'). varsdec.
   + eapply IHValid; eauto.
     rewrite <- (ctx_rename_id x z Γ) by varsdec.
     now apply ListSubset_map.
 - destruct d1. cbn in H2; subst s.
   set (vars := Vars.add x _).
   assert (Hz := fresh_var_ok vars).
   set (z := fresh_var vars) in *.
   set (h := sub_rename x z).
   apply Valid_vmap_direct; auto using sub_rename_closed.
   cbn in H.
   econstructor; eauto using claim_subset.
   + unfold h. cbn - [z vmap sub_rename].
     generalize (vmap_rename_notIn x z c'). varsdec.
   + eapply IHValid1; eauto.
     rewrite <- (ctx_rename_id x z Γ) by varsdec.
     now apply ListSubset_map.
   + eapply IHValid2; eauto.
     apply ListSubset_cons.
     rewrite <- (ctx_rename_id x z Γ) by varsdec.
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

(** Conversely, with these classical laws, we could
    simulate the "Reductio ad absurdum" rule.
    We do this in any logic (which amounts to say intuititionistic) *)

Lemma DoubleNeg_to_Absurdum l Γ A :
 Pr l (Γ ⊢ ~~A->A) ->
 Pr l ((~A) :: Γ ⊢ False)%form -> Pr l (Γ ⊢ A).
Proof.
 intros DNEG HYP.
 apply R_Imp_e with (~ ~ A)%form.
 - apply DNEG.
 - apply R_Not_i, HYP.
Qed.

Lemma ExcludedMiddle_to_Absurdum l Γ A :
 Pr l (Γ ⊢ A \/ ~A)%form ->
 Pr l ((~A) :: Γ ⊢ False)%form -> Pr l (Γ ⊢ A).
Proof.
 intros EM HYP.
 apply R_Or_e with A (~ A)%form.
 - apply EM.
 - apply R'_Ax.
 - apply R_Fa_e. apply HYP.
Qed.

Lemma Pierce_to_Absurdum l Γ A :
 (forall B, Pr l (Γ ⊢ ((A->B)->A)->A)) ->
 Pr l ((~A) :: Γ ⊢ False)%form -> Pr l (Γ ⊢ A).
Proof.
 intros PEI HYP.
 apply R_Imp_e with ((A->False)->A)%form.
 - apply PEI.
 - apply R_Imp_i.
   apply R_Fa_e.
   apply R_Imp_e with (~A)%form.
   apply Pr_pop.
   apply R_Imp_i; assumption.
   apply R_Not_i.
   apply R_Imp_e with A; apply R_Ax; simpl; auto.
Qed.

(** One example of classic law through its derivation *)

Definition Excluded_Middle_core_deriv A :=
 Rule Not_i ([] ⊢ ~~(A\/~A))
  [Rule Not_e ([~(A\/~A)] ⊢ False)
    [Rule Or_i2 ([~(A\/~A)] ⊢ A\/~A)
      [Rule Not_i ([~(A\/~A)] ⊢ ~A)
        [Rule Not_e ([A;~(A\/~A)] ⊢ False)
          [Rule Or_i1 ([A;~(A\/~A)] ⊢ A\/~A)
            [Rule Ax ([A;~(A\/~A)] ⊢ A) []];
           Rule Ax ([A;~(A\/~A)] ⊢ ~(A\/~A)) []]]];
     Rule Ax ([~(A\/~A)] ⊢ ~(A\/~A)) []]]%form.

Lemma Excluded_Middle_core_valid logic A :
 Valid logic (Excluded_Middle_core_deriv A).
Proof.
 unfold Excluded_Middle_core_deriv.
 repeat (econstructor; eauto; unfold In; intuition).
Qed.

Definition Excluded_Middle_deriv A :=
 Rule Absu ([] ⊢ A\/~A)
  (let '(Rule _ _ ds) := Excluded_Middle_core_deriv A in ds).

Lemma Excluded_Middle_valid A :
 Valid Classic (Excluded_Middle_deriv A).
Proof.
 unfold Excluded_Middle_deriv.
 unfold Excluded_Middle_core_deriv.
 repeat (econstructor; eauto; unfold In; intuition).
Qed.
