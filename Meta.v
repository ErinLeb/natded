
(** Some Meta-properties (proved on the Mix encoding) *)

Require Import RelationClasses Arith Omega Defs Proofs Mix.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

(** [bsubst] and [check] *)

Lemma check_bsubst_term sign n (u t:term) :
 check sign u = true -> check sign t = true ->
 check sign (bsubst n u t) = true.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 - case eqbspec; auto.
 - destruct gen_fun_symbs; auto.
   rewrite !lazy_andb_iff, map_length.
   intros Hu (Hl,Hl'); split; auto.
   rewrite forallb_forall in *. intros t Ht.
   rewrite in_map_iff in Ht. destruct Ht as (t' & <- & Ht'); auto.
Qed.

Lemma check_bsubst sign n u (f:formula) :
 check sign u = true -> check sign f = true ->
 check sign (bsubst n u f) = true.
Proof.
 revert n.
 induction f; cbn; intros n Hu Hf; auto.
 - destruct gen_pred_symbs; auto.
   rewrite !lazy_andb_iff in *. rewrite map_length.
   destruct Hf as (Hl,Hl'); split; auto.
   rewrite forallb_forall in *. intros t Ht.
   rewrite in_map_iff in Ht.
   destruct Ht as (t' & <- & Ht'); auto using check_bsubst_term.
 - rewrite !lazy_andb_iff in *; intuition.
Qed.

(** [bsubst] and [level] *)

Lemma level_bsubst_term n (u t:term) :
 level t <= S n -> level u <= n ->
 level (bsubst n u t) <= n.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto with arith.
 - case eqbspec; cbn; auto. intros; omega.
 - intros Hl Hu. rewrite map_map. apply list_max_map_le.
   rewrite list_max_map_le in Hl; auto.
Qed.

Lemma level_bsubst n u (f:formula) :
 level f <= S n -> level u <= n ->
 level (bsubst n u f) <= n.
Proof.
 revert n.
 induction f; cbn; intros n Hf Hu; auto with arith.
 - rewrite map_map. apply list_max_map_le.
   rewrite list_max_map_le in Hf; auto using level_bsubst_term.
 - rewrite max_le in *; intuition.
 - specialize (IHf (S n)). omega.
Qed.

(** [bsubst] and [fvars] *)

Lemma bsubst_term_fvars n (u t:term) :
 Vars.Subset (fvars (bsubst n u t)) (Vars.union (fvars u) (fvars t)).
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto with *.
 intros v. rewrite Vars.union_spec, !vars_unionmap_in.
 intros (a & Hv & Ha). rewrite in_map_iff in Ha.
 destruct Ha as (a' & <- & Ha'). apply IH in Hv; auto.
 rewrite Vars.union_spec in Hv; destruct Hv as [Hv|Hv]; auto.
 right. now exists a'.
Qed.

Lemma bsubst_fvars n u (f:formula) :
 Vars.Subset (fvars (bsubst n u f)) (Vars.union (fvars u) (fvars f)).
Proof.
 revert n.
 induction f; cbn; intros; auto with *.
 - intros v. rewrite Vars.union_spec, !vars_unionmap_in.
   intros (a & Hv & Ha). rewrite in_map_iff in Ha.
   destruct Ha as (a' & <- & Ha'). apply bsubst_term_fvars in Hv; auto.
   rewrite Vars.union_spec in Hv; destruct Hv as [Hv|Hv]; auto.
   right. now exists a'.
 - rewrite IHf1, IHf2. varsdec.
Qed.

Lemma bsubst_ctx_fvars n u (c:context) :
 Vars.Subset (fvars (bsubst n u c)) (Vars.union (fvars u) (fvars c)).
Proof.
 induction c as [|f c IH]; cbn; auto with *.
 rewrite bsubst_fvars, IH. varsdec.
Qed.

(** [bsubst] above the level does nothing *)

Lemma term_level_bsubst_id n u (t:term) :
 level t <= n -> bsubst n u t = t.
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn; try easy.
 - case eqbspec; auto. intros ->. omega.
 - intros LE.
   rewrite list_max_map_le in LE. f_equal. apply map_id_iff. intuition.
Qed.

Lemma form_level_bsubst_id n u (f:formula) :
 level f <= n -> bsubst n u f = f.
Proof.
 revert n.
 induction f; cbn; intros n LE; f_equal; auto.
 - injection (term_level_bsubst_id n u (Fun "" l)); cbn; auto.
 - apply IHf1. omega with *.
 - apply IHf2. omega with *.
 - apply IHf. omega with *.
Qed.

Lemma closed_bsubst_id n u (t:term) :
 closed t -> bsubst n u t = t.
Proof.
 unfold closed. intros. apply term_level_bsubst_id. auto with *.
Qed.

(** [bsubst] to a fesh variable is injective *)

Lemma term_bsubst_fresh_inj n z (t t':term):
 ~ Vars.In z (Vars.union (fvars t) (fvars t')) ->
 bsubst n (FVar z) t = bsubst n (FVar z) t' ->
 t = t'.
Proof.
 revert t t'.
 fix IH 1; destruct t, t'; cbn; intros NI; try discriminate.
 - intro E. exact E.
 - clear IH. case eqbspec; auto. intros -> [= ->]. varsdec.
 - clear IH. case eqbspec; auto. intros -> [= ->]. varsdec.
 - clear IH. do 2 case eqbspec; intros; subst; easy.
 - clear IH. case eqbspec; easy.
 - clear IH. case eqbspec; easy.
 - intros [= <- E]; f_equal.
   revert l l0 NI E.
   fix IH' 1; destruct l, l0; cbn; trivial; try discriminate.
   intros NI. intros [= E E']. f_equal. apply IH; auto. varsdec.
   apply IH'; auto. varsdec.
Qed.

Lemma bsubst_fresh_inj n z (f f':formula):
 ~ Vars.In z (Vars.union (fvars f) (fvars f')) ->
 Mix.bsubst n (Mix.FVar z) f = Mix.bsubst n (Mix.FVar z) f' ->
 f = f'.
Proof.
 revert f' n.
 induction f; destruct f'; cbn; intros n NI; try easy.
 - intros[= <- E]. f_equal.
   injection (term_bsubst_fresh_inj n z (Mix.Fun "" l) (Mix.Fun "" l0));
    cbn; auto. now f_equal.
 - intros [= E]. f_equal; eauto.
 - intros [= <- E1 E2]. f_equal. eapply IHf1; eauto. varsdec.
   eapply IHf2; eauto. varsdec.
 - intros [= <- E]. f_equal. eapply IHf; eauto.
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
 - unfold Vars.singleton. cbn. varsdec.
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
 induction f; simpl; try varsdec.
 - apply (term_fvars_vmap h (Fun "" l)).
 - cbn. rewrite vars_flatmap_union. varsdec.
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

(** [fsubst] commutes *)

Lemma term_fsubst_fsubst x y (u v t:term) :
 x<>y -> ~Vars.In x (fvars v) ->
 fsubst y v (fsubst x u t) =
 fsubst x (fsubst y v u) (fsubst y v t).
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn;
  intros NE NI; auto.
 - do 2 (unfold varsubst; case eqbspec; cbn); intros; subst.
   + easy.
   + unfold varsubst. now rewrite eqb_refl.
   + unfold fsubst. symmetry. apply term_vmap_id.
     intros z Hz. unfold varsubst.
     case eqbspec; auto. varsdec.
   + unfold varsubst. now case eqbspec.
 - f_equal. rewrite !map_map.
   apply map_ext_iff. intros a Ha.
   apply IH; auto.
Qed.

Lemma form_fsubst_fsubst x y (u v:term)(f:formula) :
 x<>y -> ~Vars.In x (fvars v) ->
 fsubst y v (fsubst x u f) =
 fsubst x (fsubst y v u) (fsubst y v f).
Proof.
 induction f; cbn; intros NE NI; f_equal; auto.
 injection (term_fsubst_fsubst x y u v (Fun "" l)); auto.
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
 unfold fsubst.
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
 assert (IH' : forall h, closed_sub h -> list_max (map level (map (vmap h) ds)) = 0).
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

(** We could restrict a proof to use only some signature
    (and only correctly). For that we replace unknown or incorrect
    terms by a free variable, and unknown or incorrect predicates
    by False. *)

Fixpoint restrict_term sign x t :=
 match t with
 | Fun f l =>
   match sign.(gen_fun_symbs) f with
   | None => FVar x
   | Some ar =>
     if length l =? ar then Fun f (map (restrict_term sign x) l)
     else FVar x
   end
 | _ => t
 end.

Fixpoint restrict sign x f :=
 match f with
 | True => True
 | False => False
 | Pred p l =>
   match sign.(gen_pred_symbs) p with
   | None => False
   | Some ar =>
     if length l =? ar then Pred p (map (restrict_term sign x) l)
     else False
   end
 | Not f => Not (restrict sign x f)
 | Op o f1 f2 => Op o (restrict sign x f1) (restrict sign x f2)
 | Quant q f => Quant q (restrict sign x f)
 end.

Definition restrict_ctx sign x c :=
  map (restrict sign x) c.

Definition restrict_seq sign x '(c ⊢ f) :=
  (restrict_ctx sign x c ⊢ restrict sign x f).

Definition restrict_rule sign x r :=
 match r with
 | All_e t => All_e (restrict_term sign x t)
 | Ex_i t => Ex_i (restrict_term sign x t)
 | _ => r
 end.

Fixpoint restrict_deriv sign x d :=
 let '(Rule r s l) := d in
 Rule (restrict_rule sign x r)
      (restrict_seq sign x s)
      (map (restrict_deriv sign x) l).

Lemma claim_restrict sign x d :
  claim (restrict_deriv sign x d) =
  restrict_seq sign x (claim d).
Proof.
 now destruct d.
Qed.

Lemma restrict_term_fvars sign x t :
 Vars.Subset (fvars (restrict_term sign x t))
             (Vars.add x (fvars t)).
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto with *.
 destruct gen_fun_symbs; cbn; auto with *.
 case eqbspec; cbn; auto with *.
 intros _. clear f a.
 intros v. rewrite Vars.add_spec, !vars_unionmap_in.
 intros (t & Hv & Ht).
 rewrite in_map_iff in Ht.
 destruct Ht as (a & <- & Ha).
 apply IH in Hv; auto.
 rewrite Vars.add_spec in Hv. destruct Hv as [Hv|Hv]; auto.
 right. now exists a.
Qed.

Lemma restrict_form_fvars sign x f :
 Vars.Subset (fvars (restrict sign x f))
             (Vars.add x (fvars f)).
Proof.
 induction f; cbn; auto with *.
 destruct gen_pred_symbs; cbn; auto with *.
 case eqbspec; cbn; auto with *.
 intros _. clear p a.
 intros v. rewrite Vars.add_spec, !vars_unionmap_in.
 intros (t & Hv & Ht).
 rewrite in_map_iff in Ht.
 destruct Ht as (a & <- & Ha).
 apply restrict_term_fvars in Hv; auto.
 rewrite Vars.add_spec in Hv. destruct Hv as [Hv|Hv]; auto.
 right. now exists a.
Qed.

Lemma restrict_ctx_fvars sign x c :
 Vars.Subset (fvars (restrict_ctx sign x c))
             (Vars.add x (fvars c)).
Proof.
 unfold restrict_ctx.
 intros v. unfold fvars, fvars_list.
 rewrite Vars.add_spec, !vars_unionmap_in.
 intros (f & Hv & Hf).
 rewrite in_map_iff in Hf.
 destruct Hf as (a & <- & Ha).
 apply restrict_form_fvars in Hv; auto.
 rewrite Vars.add_spec in Hv. destruct Hv as [Hv|Hv]; auto.
 right. now exists a.
Qed.

Lemma restrict_seq_fvars sign x s :
 Vars.Subset (fvars (restrict_seq sign x s))
             (Vars.add x (fvars s)).
Proof.
 destruct s; cbn. rewrite restrict_ctx_fvars, restrict_form_fvars.
 varsdec.
Qed.

Lemma restrict_term_bsubst sign x n (t u:term) :
  restrict_term sign x (bsubst n u t) =
  bsubst n (restrict_term sign x u) (restrict_term sign x t).
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn; auto.
 - case eqbspec; auto.
 - destruct gen_fun_symbs; cbn; auto with *.
   rewrite map_length.
   case eqbspec; cbn; auto.
   intros _.
   f_equal. rewrite !map_map. apply map_ext_iff; auto.
Qed.

Lemma restrict_bsubst sign x n t f :
  restrict sign x (bsubst n t f) =
  bsubst n (restrict_term sign x t) (restrict sign x f).
Proof.
 revert n.
 induction f; cbn; intros; f_equal; auto.
 destruct gen_pred_symbs; cbn; auto with *.
 rewrite map_length.
 case eqbspec; cbn; auto.
 intros _.
 f_equal. rewrite !map_map.
 apply map_ext_iff; auto using restrict_term_bsubst.
Qed.

Ltac solver :=
  try econstructor; auto;
  try match goal with
  | H : ~Vars.In _ _ -> Valid _ ?d |- Valid _ ?d => apply H; varsdec end;
  try (unfold Claim; rewrite claim_restrict);
  try match goal with
  | H : claim ?d = _ |- context [claim ?d] => now rewrite H end.

Lemma restrict_valid logic sign x (d:derivation) :
 ~Vars.In x (fvars d) ->
 Valid logic d ->
 Valid logic (restrict_deriv sign x d).
Proof.
 induction 2; cbn - [Vars.union] in *; try (solver; fail).
  - constructor. now apply in_map.
  - constructor.
    + cbn. rewrite restrict_ctx_fvars, restrict_form_fvars. varsdec.
    + apply IHValid; varsdec.
    + unfold Claim. rewrite claim_restrict. rewrite H2. simpl.
      f_equal. apply restrict_bsubst.
  - rewrite restrict_bsubst.
    constructor.
    + apply IHValid; varsdec.
    + unfold Claim. rewrite claim_restrict. now rewrite H1.
  - constructor.
    + apply IHValid; varsdec.
    + unfold Claim. rewrite claim_restrict. rewrite H1.
      cbn. now rewrite restrict_bsubst.
  - apply V_Ex_e with (restrict sign x A).
    + cbn. rewrite restrict_ctx_fvars, !restrict_form_fvars. varsdec.
    + apply IHValid1; varsdec.
    + apply IHValid2; varsdec.
    + unfold Claim. rewrite claim_restrict. now rewrite H1.
    + unfold Claim. rewrite claim_restrict. rewrite H2.
      cbn. f_equal. f_equal. apply restrict_bsubst.
Qed.

Lemma check_restrict_term_id sign x (t:term) :
 check sign t = true -> restrict_term sign x t = t.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 destruct gen_fun_symbs; try easy.
 rewrite lazy_andb_iff. intros (->,H). f_equal.
 rewrite forallb_forall in H.
 apply map_id_iff; auto.
Qed.

Lemma check_restrict_id sign x (f:formula) :
 check sign f = true -> restrict sign x f = f.
Proof.
 induction f; cbn; intros; f_equal; auto.
 - destruct gen_pred_symbs; try easy.
   rewrite lazy_andb_iff in H. destruct H as (->,H). f_equal.
   rewrite forallb_forall in H.
   apply map_id_iff; auto using check_restrict_term_id.
 - rewrite ?lazy_andb_iff in H; intuition.
 - rewrite ?lazy_andb_iff in H; intuition.
Qed.

Lemma check_restrict_ctx_id sign x (c:context) :
 check sign c = true -> restrict_ctx sign x c = c.
Proof.
 induction c as [|f c IH]; cbn; rewrite ?andb_true_iff; intros;
  f_equal; auto.
 - now apply check_restrict_id.
 - now apply IH.
Qed.

Lemma restrict_term_check sign x (t:term) :
 check sign (restrict_term sign x t) = true.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 destruct gen_fun_symbs eqn:E; try easy.
 case eqbspec; cbn; auto.
 intros <-.
 rewrite E.
 rewrite map_length, eqb_refl.
 rewrite forallb_forall. intros t Ht.
 rewrite in_map_iff in Ht. destruct Ht as (a & <- & Ha); auto.
Qed.

Lemma restrict_form_check sign x (f:formula) :
 check sign (restrict sign x f) = true.
Proof.
 induction f; cbn; auto.
 - destruct gen_pred_symbs eqn:E; try easy.
   case eqbspec; cbn; auto.
   intros <-.
   rewrite E.
   rewrite map_length, eqb_refl.
   rewrite forallb_forall. intros t Ht.
   rewrite in_map_iff in Ht.
   destruct Ht as (a & <- & Ha); auto using restrict_term_check.
 - now rewrite IHf1, IHf2.
Qed.

Lemma restrict_ctx_check sign x (c:context) :
 check sign (restrict_ctx sign x c) = true.
Proof.
 induction c as [ |f c IH]; cbn; auto.
 rewrite andb_true_iff; split; auto using restrict_form_check.
Qed.

Lemma restrict_seq_check sign x (s:sequent) :
 check sign (restrict_seq sign x s) = true.
Proof.
 destruct s. cbn.
 now rewrite restrict_ctx_check, restrict_form_check.
Qed.

Lemma restrict_rule_check sign x (r:rule_kind) :
 check sign (restrict_rule sign x r) = true.
Proof.
 destruct r; cbn; auto using restrict_term_check.
Qed.

Lemma restrict_deriv_check sign x (d:derivation) :
 check sign (restrict_deriv sign x d) = true.
Proof.
 induction d as [r s ds IH] using derivation_ind'; cbn.
 rewrite restrict_rule_check, restrict_seq_check.
 rewrite forallb_forall. intros d Hd.
 apply in_map_iff in Hd. destruct Hd as (d' & <- & Hd').
 rewrite Forall_forall in IH; auto.
Qed.

(** When a derivation has some bounded variables, we could
    replace them by anything free. *)

Fixpoint forcelevel_term n x t :=
 match t with
 | FVar _ => t
 | BVar m => if m <? n then t else FVar x
 | Fun f l => Fun f (map (forcelevel_term n x) l)
 end.

Fixpoint forcelevel n x f :=
 match f with
 | True => True
 | False => False
 | Pred p l => Pred p (map (forcelevel_term n x) l)
 | Not f => Not (forcelevel n x f)
 | Op o f1 f2 => Op o (forcelevel n x f1) (forcelevel n x f2)
 | Quant q f => Quant q (forcelevel (S n) x f)
 end.

Definition forcelevel_ctx x (c:context) :=
  map (forcelevel 0 x) c.

Definition forcelevel_seq x '(c ⊢ f) :=
 forcelevel_ctx x c ⊢ forcelevel 0 x f.

Definition forcelevel_rule x r :=
 match r with
 | All_e wit => All_e (forcelevel_term 0 x wit)
 | Ex_i wit => Ex_i (forcelevel_term 0 x wit)
 | _ => r
 end.

Fixpoint forcelevel_deriv x d :=
 let '(Rule r s ds) := d in
 Rule (forcelevel_rule x r) (forcelevel_seq x s)
      (map (forcelevel_deriv x) ds).

Lemma claim_forcelevel x d :
 claim (forcelevel_deriv x d) = forcelevel_seq x (claim d).
Proof.
 now destruct d.
Qed.

Lemma forcelevel_term_fvars n x t :
 Vars.Subset (fvars (forcelevel_term n x t)) (Vars.add x (fvars t)).
Proof.
 induction t as [ | | f l IH] using term_ind';
   cbn - [Nat.ltb]; auto with *.
 - case Nat.ltb_spec; cbn; auto with *.
 - intros v. rewrite Vars.add_spec, !vars_unionmap_in.
   intros (a & Hv & Ha).
   rewrite in_map_iff in Ha. destruct Ha as (a' & <- & Ha').
   apply IH in Hv; auto. apply Vars.add_spec in Hv.
   destruct Hv; auto. right; now exists a'.
Qed.

Lemma forcelevel_fvars n x f :
 Vars.Subset (fvars (forcelevel n x f)) (Vars.add x (fvars f)).
Proof.
 revert n.
 induction f; cbn; intros; auto with *.
 - intros v. rewrite Vars.add_spec, !vars_unionmap_in.
   intros (a & Hv & Ha).
   rewrite in_map_iff in Ha. destruct Ha as (a' & <- & Ha').
   apply forcelevel_term_fvars in Hv; auto. apply Vars.add_spec in Hv.
   destruct Hv; auto. right; now exists a'.
 - rewrite IHf1, IHf2. varsdec.
Qed.

Lemma forcelevel_ctx_fvars x (c:context) :
 Vars.Subset (fvars (forcelevel_ctx x c)) (Vars.add x (fvars c)).
Proof.
 unfold forcelevel_ctx. unfold fvars, fvars_list.
 intros v. rewrite Vars.add_spec, !vars_unionmap_in.
 intros (a & Hv & Ha).
 rewrite in_map_iff in Ha. destruct Ha as (a' & <- & Ha').
 apply forcelevel_fvars in Hv; auto. apply Vars.add_spec in Hv.
 destruct Hv; auto. right; now exists a'.
Qed.

Lemma forcelevel_term_level n x t :
  level (forcelevel_term n x t) <= n.
Proof.
 induction t as [ | | f l IH] using term_ind';
   cbn - [Nat.ltb]; auto with *.
 - case Nat.ltb_spec; cbn; auto with *.
 - rewrite map_map. apply list_max_map_le; auto.
Qed.

Lemma forcelevel_term_id n x t :
 level t <= n -> forcelevel_term n x t = t.
Proof.
 induction t as [ | | f l IH] using term_ind';
   cbn - [Nat.ltb]; intros H; auto with *.
 - case Nat.ltb_spec; cbn; auto; omega.
 - f_equal.
   rewrite list_max_map_le in H.
   apply map_id_iff; auto.
Qed.

Lemma forcelevel_bsubst_term n x (u t:term) :
  forcelevel_term n x (bsubst n u t) =
  bsubst n (forcelevel_term n x u) (forcelevel_term (S n) x t).
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 - case eqbspec.
   + intros; subst.
     case Nat.leb_spec; try omega. cbn. now rewrite eqb_refl.
   + simpl.
     case Nat.leb_spec.
     * intros LE NE. cbn - [Nat.ltb].
       case eqbspec; [intros; exfalso; omega|intros _].
       case Nat.ltb_spec; auto; omega.
     * intros LT _. cbn - [Nat.ltb].
       case Nat.ltb_spec; auto; omega.
 - f_equal. rewrite !map_map. apply map_ext_iff; auto.
Qed.

Lemma forcelevel_bsubst_term' n x (u t:term) :
  level u <= n ->
  forcelevel_term n x (bsubst n u t) =
  bsubst n u (forcelevel_term (S n) x t).
Proof.
 intros Hu.
 rewrite forcelevel_bsubst_term. f_equal.
 now apply forcelevel_term_id.
Qed.

Lemma forcelevel_bsubst n x u f :
  level u <= n ->
  forcelevel n x (bsubst n u f) =
  bsubst n u (forcelevel (S n) x f).
Proof.
 revert n.
 induction f; cbn; intros; f_equal; auto.
 rewrite !map_map. apply map_ext_iff.
 auto using forcelevel_bsubst_term'.
Qed.

(*
Lemma forcelevel_bsubst' n x u f :
  forcelevel n x (bsubst n u f) =
  bsubst n (forcelevel_term n x u) (forcelevel (S n) x f).
Proof.
 revert n u.
 induction f; cbn; intros; f_equal; auto.
 - rewrite !map_map. apply map_ext_iff.
   auto using forcelevel_bsubst_term.
 - rewrite IHf.

Qed.
*)
(*
Lemma forcelevel_bsubst_adhoc n x u f :
 forcelevel n x (bsubst n u f) =
 forcelevel n x (bsubst n (forcelevel_term n x u) f).
Proof.
 revert n.
 induction f; cbn; intros; f_equal; auto.
 rewrite !map_map. apply map_ext_iff.
 intros a Ha.
 rewrite !forcelevel_bsubst_term. f_equal.
 symmetry. apply forcelevel_term_id. apply forcelevel_term_level.
*)

Ltac solver' :=
  try econstructor; auto;
  try match goal with
  | H : ~Vars.In _ _ -> Valid _ ?d |- Valid _ ?d => apply H; varsdec end;
  try (unfold Claim; rewrite claim_forcelevel);
  try match goal with
  | H : claim ?d = _ |- context [claim ?d] => now rewrite H end.

Lemma forcelevel_deriv_valid logic x (d:derivation) :
 ~Vars.In x (fvars d) ->
 Valid logic d ->
 Valid logic (forcelevel_deriv x d).
Proof.
 induction 2; cbn - [Vars.union] in *; try (solver'; fail).
 - constructor. now apply in_map.
 - constructor.
   + cbn. rewrite forcelevel_ctx_fvars, forcelevel_fvars.
     varsdec.
   + apply IHValid. varsdec.
   + unfold Claim; rewrite claim_forcelevel, H2. cbn. f_equal.
     rewrite forcelevel_bsubst; auto.
 - replace (forcelevel 0 x (bsubst 0 t A))
       with (bsubst 0 (forcelevel_term 0 x t) (forcelevel 1 x A)).
   constructor.
   + apply IHValid; varsdec.
   + unfold Claim. now rewrite claim_forcelevel, H1.
   + rewrite <- forcelevel_bsubst.
     admit.
     now rewrite forcelevel_term_level.
 - constructor.
   + apply IHValid. varsdec.
   + unfold Claim; rewrite claim_forcelevel, H1. cbn. f_equal.
     admit.
 - apply V_Ex_e with (forcelevel 1 x A).
   + cbn. rewrite forcelevel_ctx_fvars, !forcelevel_fvars.
     varsdec.
   + apply IHValid1. varsdec.
   + apply IHValid2. varsdec.
   + unfold Claim; now rewrite claim_forcelevel, H1.
   + unfold Claim; rewrite claim_forcelevel, H2. cbn. f_equal.
     f_equal. apply forcelevel_bsubst; auto.
Admitted.