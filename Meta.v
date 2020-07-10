
(** * Some meta-properties of the Mix encoding *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Implicit Type t u : term.
Implicit Type f : formula.

(** [lift] does nothing on a [BClosed] term *)

Lemma lift_nop t : BClosed t -> lift t = t.
Proof.
 unfold BClosed.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 - easy.
 - rewrite list_max_map_0. intros H. f_equal. apply map_id_iff; auto.
Qed.

(** [bsubst] and [check] *)

Lemma check_lift sign t :
 check sign (lift t) = check sign t.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 destruct funsymbs; auto.
 rewrite map_length. case eqb; auto.
 apply eq_true_iff_eq. rewrite forallb_map, !forallb_forall.
 split; intros H x Hx. rewrite <- IH; auto. rewrite IH; auto.
Qed.

Lemma check_bsubst_term sign n (u t:term) :
 check sign u = true -> check sign t = true ->
 check sign (bsubst n u t) = true.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 - case eqbspec; auto.
 - destruct funsymbs; auto.
   rewrite !lazy_andb_iff, map_length.
   intros Hu (Hl,Hl'); split; auto.
   rewrite forallb_map, forallb_forall in *. auto.
Qed.

Lemma check_bsubst sign n u (f:formula) :
 check sign u = true -> check sign f = true ->
 check sign (bsubst n u f) = true.
Proof.
 revert n u.
 induction f; cbn; intros n u Hu Hf; auto.
 - destruct predsymbs; auto.
   rewrite !lazy_andb_iff in *. rewrite map_length.
   destruct Hf as (Hl,Hl'); split; auto.
   rewrite forallb_map, forallb_forall in *.
   auto using check_bsubst_term.
 - rewrite !lazy_andb_iff in *; intuition.
 - apply IHf; auto. now rewrite check_lift.
Qed.

(** [bsubst] and [level] *)

Lemma level_lift t : level (lift t) <= S (level t).
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto with arith.
 rewrite map_map.
 apply list_max_map_le. intros a Ha. transitivity (S (level a)); auto.
 rewrite <- Nat.succ_le_mono. now apply list_max_map_in.
Qed.

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
 revert n u.
 induction f; cbn; intros n u Hf Hu; auto with arith.
 - apply (level_bsubst_term n u (Fun "" l)); auto.
 - rewrite max_le in *; intuition.
 - change n with (Nat.pred (S n)) at 2. apply Nat.pred_le_mono.
   apply IHf. omega. transitivity (S (level u)). apply level_lift.
   omega.
Qed.

Lemma level_bsubst_term' n (u t : term) :
  level u <= S n -> level (bsubst n u t) <= level t.
Proof.
 intro Hu. revert t. fix IH 1. destruct t; cbn; auto.
 - case eqbspec; intros; subst; auto.
 - revert l. fix IH' 1. destruct l; cbn; auto.
   apply Nat.max_le_compat; auto.
Qed.

Lemma level_bsubst' n u (f:formula) :
  level u <= S n -> level (bsubst n u f) <= level f.
Proof.
 revert n u. induction f; cbn; intros n u Hu; auto with arith.
 - now apply (level_bsubst_term' n u (Fun "" l)).
 - apply Nat.max_le_compat; auto.
 - apply Nat.pred_le_mono; auto with arith.
   apply IHf. transitivity (S (level u)). apply level_lift. omega.
Qed.

(** [bsubst] and [fvars] : over-approximations *)

Lemma lift_fvars t : fvars (lift t) = fvars t.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto with *.
 induction l; simpl; auto.
 rewrite IH, IHl; simpl; auto.
 intros x Hx. apply IH. simpl; auto.
Qed.

Lemma bsubst_term_fvars n (u t:term) :
 Names.Subset (fvars (bsubst n u t)) (Names.union (fvars u) (fvars t)).
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto with *.
 apply subset_unionmap_map; auto.
Qed.

Lemma bsubst_fvars n u (f:formula) :
 Names.Subset (fvars (bsubst n u f)) (Names.union (fvars u) (fvars f)).
Proof.
 revert n u.
 induction f; cbn; intros; auto with *.
 - apply (bsubst_term_fvars n u (Fun "" l)).
 - rewrite IHf1, IHf2. namedec.
 - rewrite IHf. now rewrite lift_fvars.
Qed.

Lemma bsubst_ctx_fvars n u (c:context) :
 Names.Subset (fvars (bsubst n u c)) (Names.union (fvars u) (fvars c)).
Proof.
 induction c as [|f c IH]; cbn; auto with *.
 rewrite bsubst_fvars, IH. namedec.
Qed.

(** [bsubst] and [fvars] : under-approximations *)

Lemma bsubst_term_fvars' n (u t : term) :
  Names.Subset (fvars t) (fvars (bsubst n u t)).
Proof.
 revert t. fix IH 1. destruct t; cbn; auto with set.
 clear f.
 revert l. fix IH' 1. destruct l; cbn; auto with set.
 intro x. NamesF.set_iff. intros [IN|IN].
 - left; now apply IH.
 - right. now apply IH'.
Qed.

Lemma bsubst_fvars' n u (f:formula) :
  Names.Subset (fvars f) (fvars (bsubst n u f)).
Proof.
 revert n u; induction f; cbn; intros n u; auto with set.
 - apply (bsubst_term_fvars' n u (Fun "" l)).
 - intro x. NamesF.set_iff. intros [IN|IN].
   left; now apply IHf1.
   right; now apply IHf2.
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
 revert n u.
 induction f; cbn; intros n u LE; f_equal; auto.
 - injection (term_level_bsubst_id n u (Fun "" l)); cbn; auto.
 - apply IHf1. omega with *.
 - apply IHf2. omega with *.
 - apply IHf. omega with *.
Qed.

Lemma bclosed_bsubst_id n u (t:term) :
 BClosed t -> bsubst n u t = t.
Proof.
 unfold BClosed. intros. apply term_level_bsubst_id. auto with *.
Qed.

(** [bsubst] to a fresh variable is injective *)

Lemma term_bsubst_fresh_inj n z (t t':term):
 ~ Names.In z (Names.union (fvars t) (fvars t')) ->
 bsubst n (FVar z) t = bsubst n (FVar z) t' ->
 t = t'.
Proof.
 revert t t'.
 fix IH 1; destruct t, t'; cbn; intros NI; try discriminate.
 - intro E. exact E.
 - clear IH. case eqbspec; auto. intros -> [= ->]. namedec.
 - clear IH. case eqbspec; auto. intros -> [= ->]. namedec.
 - clear IH. do 2 case eqbspec; intros; subst; easy.
 - clear IH. case eqbspec; easy.
 - clear IH. case eqbspec; easy.
 - intros [= <- E]; f_equal.
   revert l l0 NI E.
   fix IH' 1; destruct l, l0; cbn; trivial; try discriminate.
   intros NI. intros [= E E']. f_equal. apply IH; auto. namedec.
   apply IH'; auto. namedec.
Qed.

Lemma bsubst_fresh_inj n z (f f':formula):
 ~ Names.In z (Names.union (fvars f) (fvars f')) ->
 Mix.bsubst n (Mix.FVar z) f = Mix.bsubst n (Mix.FVar z) f' ->
 f = f'.
Proof.
 revert f' n.
 induction f; destruct f'; cbn; intros n NI; try easy.
 - intros[= <- E]. f_equal.
   injection (term_bsubst_fresh_inj n z (Mix.Fun "" l) (Mix.Fun "" l0));
    cbn; auto. now f_equal.
 - intros [= E]. f_equal; eauto.
 - intros [= <- E1 E2]. f_equal. eapply IHf1; eauto. namedec.
   eapply IHf2; eauto. namedec.
 - intros [= <- E]. f_equal. eapply IHf; eauto.
Qed.

(** [vmap] basic results : extensionality, identity, composition *)

Lemma term_vmap_ext h h' (t:term) :
 (forall v:variable, Names.In v (fvars t) -> h v = h' v) ->
 vmap h t = vmap h' t.
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn; auto with set.
 intros H. f_equal. apply map_ext_in; eauto with set.
Qed.

Lemma form_vmap_ext h h' (f:formula) :
 (forall v:variable, Names.In v (fvars f) -> h v = h' v) ->
 vmap h f = vmap h' f.
Proof.
 induction f; cbn; intro; f_equal; auto with set.
 now injection (term_vmap_ext h h' (Fun "" l)).
Qed.

Lemma ctx_vmap_ext h h' (c:context) :
 (forall v:variable, Names.In v (fvars c) -> h v = h' v) ->
 vmap h c = vmap h' c.
Proof.
 induction c; cbn; intros; f_equal;
  auto using form_vmap_ext with set.
Qed.

Lemma seq_vmap_ext h h' (s:sequent) :
 (forall v:variable, Names.In v (fvars s) -> h v = h' v) ->
 vmap h s = vmap h' s.
Proof.
 destruct s; intros. cbn in *. f_equal.
 apply ctx_vmap_ext; auto with set.
 apply form_vmap_ext; auto with set.
Qed.

Lemma term_vmap_id h (t:term) :
 (forall v:variable, Names.In v (fvars t) -> h v = FVar v) ->
 vmap h t = t.
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn; auto with set.
 intros H. f_equal. apply map_id_iff; eauto with set.
Qed.

Lemma form_vmap_id h (f:formula) :
 (forall v:variable, Names.In v (fvars f) -> h v = FVar v) ->
 vmap h f = f.
Proof.
 induction f; cbn; intro; f_equal; auto with set.
 now injection (term_vmap_id h (Fun "" l)).
Qed.

Lemma ctx_vmap_id h (c:context) :
 (forall v:variable, Names.In v (fvars c) -> h v = FVar v) ->
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
  Names.Subset
    (fvars (vmap h t))
    (Names.flatmap (fun v => fvars (h v)) (fvars t)).
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn.
 - unfold Names.singleton. cbn. namedec.
 - namedec.
 - intros v. rewrite unionmap_map_in. intros (a & Hv & Ha).
   generalize (IH a Ha v Hv). apply flatmap_subset; auto.
   intro. eauto with set.
Qed.

Lemma form_fvars_vmap h (f:formula) :
  Names.Subset
    (fvars (vmap h f))
    (Names.flatmap (fun v => fvars (h v)) (fvars f)).
Proof.
 induction f; simpl; try namedec.
 - apply (term_fvars_vmap h (Fun "" l)).
 - cbn. rewrite flatmap_union. namedec.
Qed.

Lemma ctx_fvars_vmap h (c:context) :
  Names.Subset
    (fvars (vmap h c))
    (Names.flatmap (fun v => fvars (h v)) (fvars c)).
Proof.
 induction c as [|f c IH]; cbn.
 - namedec.
 - generalize (form_fvars_vmap h f).
   rewrite flatmap_union. namedec.
Qed.

Lemma seq_fvars_vmap h (s:sequent) :
  Names.Subset
    (fvars (vmap h s))
    (Names.flatmap (fun v => fvars (h v)) (fvars s)).
Proof.
 destruct s. cbn.
 rewrite flatmap_union.
 generalize (form_fvars_vmap h f) (ctx_fvars_vmap h c). namedec.
Qed.

(** [fsubst] commutes *)

Lemma term_fsubst_fsubst x y (u v t:term) :
 x<>y -> ~Names.In x (fvars v) ->
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
     case eqbspec; auto. namedec.
   + unfold varsubst. now case eqbspec.
 - f_equal. rewrite !map_map.
   apply map_ext_iff. intros a Ha.
   apply IH; auto.
Qed.

Lemma form_fsubst_fsubst x y (u v:term)(f:formula) :
 x<>y -> ~Names.In x (fvars v) ->
 fsubst y v (fsubst x u f) =
 fsubst x (fsubst y v u) (fsubst y v f).
Proof.
 induction f; cbn; intros NE NI; f_equal; auto.
 injection (term_fsubst_fsubst x y u v (Fun "" l)); auto.
Qed.


(** Alternating [vmap] and [bsubst] *)

Definition BClosed_sub (h:variable->term) :=
 forall v, BClosed (h v).

Lemma lift_vmap (h:variable->term) t :
 lift (vmap h t) = vmap (fun v => lift (h v)) (lift t).
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 f_equal. rewrite !map_map. apply map_ext_iff; auto.
Qed.

Lemma lift_vmap' (h:variable->term) t :
 BClosed_sub h ->
 lift (vmap h t) = vmap h (lift t).
Proof.
 intros CL. rewrite lift_vmap.
 apply term_vmap_ext. intros v _. now apply lift_nop.
Qed.

Lemma term_vmap_bsubst h n u (t:term) :
 BClosed_sub h ->
 vmap h (bsubst n u t) = bsubst n (vmap h u) (vmap h t).
Proof.
 intros CL.
 induction t as [ | | f l IH] using term_ind'; cbn.
 - symmetry. apply bclosed_bsubst_id. apply CL.
 - auto with eqb.
 - f_equal. rewrite !map_map. now apply map_ext_in.
Qed.

Lemma form_vmap_bsubst h n u (f:formula) :
 BClosed_sub h ->
 vmap h (bsubst n u f) = bsubst n (vmap h u) (vmap h f).
Proof.
 intros CL. revert n u.
 induction f; cbn; intros n u; f_equal; auto.
 - injection (term_vmap_bsubst h n u (Fun "" l)); auto.
 - now rewrite IHf, lift_vmap'.
Qed.

Definition sub_set (x:variable)(t:term)(h:variable->term) :=
 fun v => if v =? x then t else h v.

Lemma bclosed_sub_set x t h :
 BClosed_sub h -> BClosed t -> BClosed_sub (sub_set x t h).
Proof.
 unfold sub_set, BClosed_sub; auto with eqb.
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
 ~Names.In x (fvars f) -> vmap (sub_set x t h) f = vmap h f.
Proof.
 intros. apply form_vmap_ext. intros.
 rewrite sub_set_else; auto with set.
Qed.

Lemma ctx_sub_set_ext x t h (c:context) :
 ~Names.In x (fvars c) -> vmap (sub_set x t h) c = vmap h c.
Proof.
 intros. apply ctx_vmap_ext. intros.
 rewrite sub_set_else; auto with set.
Qed.

Lemma vmap_bsubst_adhoc h x t (f:formula) :
 BClosed_sub h ->
 BClosed t ->
 ~Names.In x (fvars f) ->
 bsubst 0 t (vmap h f) =
  vmap (sub_set x t h) (bsubst 0 (FVar x) f).
Proof.
 intros.
 rewrite form_vmap_bsubst by now apply bclosed_sub_set.
 cbn. rewrite sub_set_at. f_equal. now rewrite form_sub_set_ext.
Qed.

(** Bounded variables after a [vmap] *)

Lemma level_term_vmap h (t:term) :
 BClosed_sub h -> level (vmap h t) <= level t.
Proof.
 intros Hh.
 induction t as [ | |f l IH] using term_ind'; cbn.
 - now rewrite (Hh v).
 - trivial.
 - rewrite map_map. now apply list_max_map_incr.
Qed.

Lemma level_form_vmap h (f:formula) :
 BClosed_sub h -> level (vmap h f) <= level f.
Proof.
 intros Hh.
 induction f; cbn; auto with *.
 - apply (level_term_vmap h (Fun "" l) Hh).
 - omega with *.
Qed.

Lemma bclosed_term_vmap h (t:term) :
 BClosed_sub h -> BClosed t -> BClosed (vmap h t).
Proof.
 unfold BClosed. intros Hh Ht.
 generalize (level_term_vmap h t Hh). omega.
Qed.

Lemma bclosed_form_vmap h (f:formula) :
 BClosed_sub h -> BClosed f -> BClosed (vmap h f).
Proof.
 unfold BClosed. intros Hh Hf.
 generalize (level_form_vmap h f Hh). omega.
Qed.

Lemma bclosed_ctx_vmap h (c:context) :
 BClosed_sub h -> BClosed c -> BClosed (vmap h c).
Proof.
 unfold BClosed. intros Hh.
 induction c as [|f c IH]; cbn; auto.
 rewrite !max_0. intuition. now apply bclosed_form_vmap.
Qed.

Lemma bclosed_seq_vmap h (s:sequent) :
 BClosed_sub h -> BClosed s -> BClosed (vmap h s).
Proof.
 destruct s as (c,f). intros Hh. unfold BClosed. cbn.
 rewrite !max_0. intuition.
 now apply bclosed_ctx_vmap.
 now apply bclosed_form_vmap.
Qed.

Hint Resolve bclosed_term_vmap bclosed_form_vmap.
Hint Resolve bclosed_ctx_vmap bclosed_seq_vmap.

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
   match sign.(funsymbs) f with
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
   match sign.(predsymbs) p with
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

Lemma restrict_term_level sign x t :
  level (restrict_term sign x t) <= level t.
Proof.
 revert t.
 fix IH 1. destruct t as [ | | f l]; cbn; auto with *.
 destruct funsymbs; cbn; auto with *.
 case eqbspec; cbn; auto with *.
 intros _. clear f a.
 revert l.
 fix IH' 1. destruct l as [ |t l]; cbn; auto using Nat.max_le_compat with *.
Qed.

Lemma restrict_term_bclosed sign x t :
 BClosed t -> BClosed (restrict_term sign x t).
Proof.
 unfold BClosed. assert (H := restrict_term_level sign x t). auto with *.
Qed.

Lemma restrict_level sign x f :
  level (restrict sign x f) <= level f.
Proof.
 induction f; cbn; auto using Nat.max_le_compat with *.
 destruct predsymbs; cbn; auto with *.
 case eqbspec; cbn; auto with *.
 intros _. clear p a.
 induction l as [|t l IH]; cbn;
   auto using Nat.max_le_compat, restrict_term_level.
Qed.

Lemma restrict_bclosed sign x f :
 BClosed f -> BClosed (restrict sign x f).
Proof.
 unfold BClosed. assert (H := restrict_level sign x f). auto with *.
Qed.

Lemma restrict_term_fvars sign x t :
 Names.Subset (fvars (restrict_term sign x t))
              (Names.add x (fvars t)).
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto with *.
 destruct funsymbs; cbn; auto with *.
 case eqbspec; cbn; auto with *.
 intros _. apply subset_unionmap_map'; auto.
Qed.

Lemma restrict_form_fvars sign x f :
 Names.Subset (fvars (restrict sign x f))
              (Names.add x (fvars f)).
Proof.
 induction f; cbn; auto with *.
 destruct predsymbs; cbn; auto with *.
 case eqbspec; cbn; auto with *.
 intros _. apply subset_unionmap_map'.
 intros t _. apply restrict_term_fvars.
Qed.

Lemma restrict_ctx_fvars sign x c :
 Names.Subset (fvars (restrict_ctx sign x c))
              (Names.add x (fvars c)).
Proof.
 unfold restrict_ctx.
 apply subset_unionmap_map'.
 intros f _. apply restrict_form_fvars.
Qed.

Lemma restrict_seq_fvars sign x s :
 Names.Subset (fvars (restrict_seq sign x s))
              (Names.add x (fvars s)).
Proof.
 destruct s; cbn. rewrite restrict_ctx_fvars, restrict_form_fvars.
 namedec.
Qed.

Lemma restrict_rule_fvars sign x r :
 Names.Subset (fvars (restrict_rule sign x r))
              (Names.add x (fvars r)).
Proof.
 destruct r; cbn; rewrite ?restrict_term_fvars; auto with *.
Qed.

Lemma restrict_deriv_fvars sign x d :
 Names.Subset (fvars (restrict_deriv sign x d))
              (Names.add x (fvars d)).
Proof.
 induction d as [r s ds IH] using derivation_ind'; cbn.
 rewrite restrict_rule_fvars, restrict_seq_fvars.
 rewrite Forall_forall in IH.
 apply subset_unionmap_map' in IH. rewrite IH. namedec.
Qed.


Lemma restrict_term_bsubst sign x n (t u:term) :
  restrict_term sign x (bsubst n u t) =
  bsubst n (restrict_term sign x u) (restrict_term sign x t).
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn; auto.
 - case eqbspec; auto.
 - destruct funsymbs; cbn; auto with *.
   rewrite map_length.
   case eqbspec; cbn; auto.
   intros _.
   f_equal. rewrite !map_map. apply map_ext_iff; auto.
Qed.

Lemma restrict_lift sign x t :
 restrict_term sign x (lift t) = lift (restrict_term sign x t).
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn; auto.
 destruct funsymbs; cbn; auto with *.
 rewrite map_length.
 case eqbspec; cbn; auto.
 intros _. f_equal. rewrite !map_map. apply map_ext_iff; auto.
Qed.

Lemma restrict_bsubst sign x n t f :
  restrict sign x (bsubst n t f) =
  bsubst n (restrict_term sign x t) (restrict sign x f).
Proof.
 revert n t.
 induction f; cbn; intros; f_equal; auto.
 destruct predsymbs; cbn; auto with *.
 rewrite map_length.
 case eqbspec; cbn; auto.
 intros _.
 f_equal. rewrite !map_map.
 apply map_ext_iff; auto using restrict_term_bsubst.
 rewrite <- restrict_lift. auto.
Qed.

Ltac solver :=
  try econstructor; auto;
  try match goal with
  | H : ~Names.In _ _ -> Valid _ ?d |- Valid _ ?d => apply H; namedec end;
  try (unfold Claim; rewrite claim_restrict);
  try match goal with
  | H : claim ?d = _ |- context [claim ?d] => now rewrite H end.

Lemma restrict_valid logic sign x (d:derivation) :
 ~Names.In x (fvars d) ->
 Valid logic d ->
 Valid logic (restrict_deriv sign x d).
Proof.
 induction 2; cbn - [Names.union] in *; try (solver; fail).
  - constructor. now apply in_map.
  - constructor.
    + cbn. rewrite restrict_ctx_fvars, restrict_form_fvars. namedec.
    + apply IHValid; namedec.
    + unfold Claim. rewrite claim_restrict. rewrite H2. simpl.
      f_equal. apply restrict_bsubst.
  - rewrite restrict_bsubst.
    constructor.
    + apply IHValid; namedec.
    + unfold Claim. rewrite claim_restrict. now rewrite H1.
  - constructor.
    + apply IHValid; namedec.
    + unfold Claim. rewrite claim_restrict. rewrite H1.
      cbn. now rewrite restrict_bsubst.
  - apply V_Ex_e with (restrict sign x A).
    + cbn. rewrite restrict_ctx_fvars, !restrict_form_fvars. namedec.
    + apply IHValid1; namedec.
    + apply IHValid2; namedec.
    + unfold Claim. rewrite claim_restrict. now rewrite H1.
    + unfold Claim. rewrite claim_restrict. rewrite H2.
      cbn. f_equal. f_equal. apply restrict_bsubst.
Qed.

Lemma check_restrict_term_id sign x (t:term) :
 check sign t = true -> restrict_term sign x t = t.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 destruct funsymbs; try easy.
 rewrite lazy_andb_iff. intros (->,H). f_equal.
 rewrite forallb_forall in H.
 apply map_id_iff; auto.
Qed.

Lemma check_restrict_id sign x (f:formula) :
 check sign f = true -> restrict sign x f = f.
Proof.
 induction f; cbn; intros; f_equal; auto.
 - destruct predsymbs; try easy.
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
 destruct funsymbs eqn:E; try easy.
 case eqbspec; cbn; auto.
 intros <-.
 rewrite E, map_length, eqb_refl, forallb_map, forallb_forall; auto.
Qed.

Lemma restrict_form_check sign x (f:formula) :
 check sign (restrict sign x f) = true.
Proof.
 induction f; cbn; auto.
 - destruct predsymbs eqn:E; try easy.
   case eqbspec; cbn; auto.
   intros <-.
   rewrite E, map_length, eqb_refl, forallb_map, forallb_forall;
    auto using restrict_term_check.
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
 rewrite forallb_map, forallb_forall, Forall_forall in *; auto.
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
 Names.Subset (fvars (forcelevel_term n x t)) (Names.add x (fvars t)).
Proof.
 induction t as [ | | f l IH] using term_ind';
   cbn - [Nat.ltb]; auto with *.
 - case Nat.ltb_spec; cbn; auto with *.
 - apply subset_unionmap_map'; auto.
Qed.

Lemma forcelevel_fvars n x f :
 Names.Subset (fvars (forcelevel n x f)) (Names.add x (fvars f)).
Proof.
 revert n.
 induction f; cbn; intros; auto with *.
 - apply subset_unionmap_map'.
   intros t _. apply forcelevel_term_fvars.
 - rewrite IHf1, IHf2. namedec.
Qed.

Lemma forcelevel_ctx_fvars x (c:context) :
 Names.Subset (fvars (forcelevel_ctx x c)) (Names.add x (fvars c)).
Proof.
 unfold forcelevel_ctx. unfold fvars, fvars_list.
 apply subset_unionmap_map'.
 intros f _. apply forcelevel_fvars.
Qed.

Lemma forcelevel_term_level n x t :
  level (forcelevel_term n x t) <= n.
Proof.
 induction t as [ | | f l IH] using term_ind';
   cbn - [Nat.ltb]; auto with *.
 - case Nat.ltb_spec; cbn; auto with *.
 - rewrite map_map. apply list_max_map_le; auto.
Qed.

Lemma forcelevel_term_bclosed x t :
  BClosed (forcelevel_term 0 x t).
Proof.
 assert (H := forcelevel_term_level 0 x t). auto with *.
Qed.

Lemma forcelevel_level n x f :
 level (forcelevel n x f) <= n.
Proof.
 revert n.
 induction f; cbn; intros; auto with *.
 - rewrite map_map. apply list_max_map_le.
   auto using forcelevel_term_level.
 - apply max_le; auto.
 - specialize (IHf (S n)). auto with *.
Qed.

Lemma forcelevel_bclosed x f :
 BClosed (forcelevel 0 x f).
Proof.
 assert (H := forcelevel_level 0 x f). auto with *.
Qed.

Lemma forcelevel_ctx_bclosed x c :
 BClosed (forcelevel_ctx x c).
Proof.
 induction c as [|f c IH]; cbn; auto.
 unfold BClosed, level, level_list. cbn.
 now rewrite forcelevel_bclosed, IH.
Qed.

Lemma forcelevel_seq_bclosed x s :
 BClosed (forcelevel_seq x s).
Proof.
 destruct s; cbn.
 unfold BClosed, level, level_seq.
 now rewrite forcelevel_bclosed, forcelevel_ctx_bclosed.
Qed.

Lemma forcelevel_rule_bclosed x r :
 BClosed (forcelevel_rule x r).
Proof.
 destruct r; cbn; auto.
 unfold BClosed; cbn; apply forcelevel_term_bclosed.
 unfold BClosed; cbn; apply forcelevel_term_bclosed.
Qed.

Lemma forcelevel_deriv_bclosed x d :
 BClosed (forcelevel_deriv x d).
Proof.
 induction d as [r s ds IH] using derivation_ind'.
 unfold BClosed; cbn.
 rewrite forcelevel_rule_bclosed, forcelevel_seq_bclosed.
 simpl.
 apply list_max_0.
 rewrite map_map.
 intros n. rewrite in_map_iff. intros (d & <- & IN).
 rewrite Forall_forall in IH. now apply IH.
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

Lemma forcelevel_id n x f :
 level f <= n -> forcelevel n x f = f.
Proof.
 revert n.
 induction f; cbn; intros; rewrite ?max_le in *; f_equal; intuition.
 apply map_id_iff. rewrite list_max_map_le in H.
 auto using forcelevel_term_id.
Qed.

Lemma forcelevel_ctx_id x c :
 BClosed c -> forcelevel_ctx x c = c.
Proof.
 induction c as [|f c IH]; cbn; auto.
 unfold BClosed, level, level_list; cbn. rewrite max_0.
 intros (Hf,Hc); f_equal; auto. apply forcelevel_id. now rewrite Hf.
Qed.

Lemma forcelevel_seq_id x s :
 BClosed s -> forcelevel_seq x s = s.
Proof.
 destruct s; cbn. unfold BClosed, level, level_seq. rewrite max_0.
 intros (Hc,Hf). f_equal. now apply forcelevel_ctx_id.
 apply forcelevel_id. now rewrite Hf.
Qed.

Lemma forcelevel_rule_id x r :
 BClosed r -> forcelevel_rule x r = r.
Proof.
 destruct r; cbn; auto.
 unfold BClosed; cbn; intros Hw. f_equal.
  apply forcelevel_term_id. now rewrite Hw.
 unfold BClosed; cbn; intros Hw. f_equal.
  apply forcelevel_term_id. now rewrite Hw.
Qed.

Lemma forcelevel_deriv_id x d :
 BClosed d -> forcelevel_deriv x d = d.
Proof.
 induction d as [r s ds IH] using derivation_ind'; cbn.
 unfold BClosed. cbn. rewrite !max_0.
 intros (Hr & Hs & Hds).
 f_equal.
 now apply forcelevel_rule_id.
 now apply forcelevel_seq_id.
 rewrite Forall_forall in IH.
 rewrite list_max_map_0 in Hds.
 apply map_id_iff. auto.
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

Lemma forcelevel_lift n x u :
  forcelevel_term (S n) x (lift u) = lift (forcelevel_term n x u).
Proof.
 induction u using term_ind'; simpl; auto.
 - change (S n0 <? S n) with (n0 <? n).
   case Nat.ltb_spec; simpl; auto.
 - f_equal. rewrite !map_map. apply map_ext_in; auto.
Qed.

Lemma forcelevel_bsubst n x u f :
  forcelevel n x (bsubst n u f) =
  bsubst n (forcelevel_term n x u) (forcelevel (S n) x f).
Proof.
 revert n u.
 induction f; cbn; intros; f_equal; auto.
 - rewrite !map_map. apply map_ext_iff.
   auto using forcelevel_bsubst_term.
 - rewrite IHf.
   f_equal. apply forcelevel_lift.
Qed.

Ltac solver' :=
  try econstructor; auto;
  try match goal with
  | H : ~Names.In _ _ -> Valid _ ?d |- Valid _ ?d => apply H; namedec end;
  try (unfold Claim; rewrite claim_forcelevel);
  try match goal with
  | H : claim ?d = _ |- context [claim ?d] => now rewrite H end.

Lemma forcelevel_deriv_valid logic x (d:derivation) :
 ~Names.In x (fvars d) ->
 Valid logic d ->
 Valid logic (forcelevel_deriv x d).
Proof.
 induction 2; cbn - [Names.union] in *; try (solver'; fail).
 - constructor. now apply in_map.
 - constructor.
   + cbn. rewrite forcelevel_ctx_fvars, forcelevel_fvars.
     namedec.
   + apply IHValid. namedec.
   + unfold Claim; rewrite claim_forcelevel, H2. cbn. f_equal.
     rewrite forcelevel_bsubst; auto.
 - rewrite forcelevel_bsubst.
   constructor; auto.
   + apply IHValid; namedec.
   + unfold Claim. now rewrite claim_forcelevel, H1.
 - constructor; auto.
   + apply IHValid. namedec.
   + unfold Claim; rewrite claim_forcelevel, H1. cbn. f_equal.
     apply forcelevel_bsubst.
 - apply V_Ex_e with (forcelevel 1 x A).
   + cbn. rewrite forcelevel_ctx_fvars, !forcelevel_fvars. namedec.
   + apply IHValid1. namedec.
   + apply IHValid2. namedec.
   + unfold Claim; now rewrite claim_forcelevel, H1.
   + unfold Claim; rewrite claim_forcelevel, H2. cbn. f_equal.
     f_equal. apply forcelevel_bsubst; auto.
Qed.

Lemma restrict_forcelevel_term sign x n y t :
 restrict_term sign x (forcelevel_term n y t) =
 forcelevel_term n y (restrict_term sign x t).
Proof.
 induction t as [ | | f l IH] using term_ind';
  cbn - [Nat.ltb]; auto.
 - case Nat.ltb_spec; auto.
 - destruct funsymbs as [ar|] eqn:E; auto.
   rewrite map_length.
   case eqbspec; cbn; auto.
   intros _. f_equal.
   rewrite !map_map.
   apply map_ext_iff; auto.
Qed.

Lemma restrict_forcelevel sign x n y f :
 restrict sign x (forcelevel n y f) =
 forcelevel n y (restrict sign x f).
Proof.
 revert n.
 induction f; cbn; intros; f_equal; auto.
 destruct predsymbs as [ar|] eqn:E; auto.
 rewrite map_length.
 case eqbspec; cbn; auto.
 intros _. f_equal.
 rewrite !map_map.
 apply map_ext_iff; auto using restrict_forcelevel_term.
Qed.

Lemma restrict_forcelevel_ctx sign x y c :
 restrict_ctx sign x (forcelevel_ctx y c) =
 forcelevel_ctx y (restrict_ctx sign x c).
Proof.
 induction c; cbn; f_equal; auto using restrict_forcelevel.
Qed.

Lemma restrict_forcelevel_seq sign x y s :
 restrict_seq sign x (forcelevel_seq y s) =
 forcelevel_seq y (restrict_seq sign x s).
Proof.
 destruct s; cbn; f_equal;
 auto using restrict_forcelevel, restrict_forcelevel_ctx.
Qed.

Lemma restrict_forcelevel_rule sign x y r :
 restrict_rule sign x (forcelevel_rule y r) =
 forcelevel_rule y (restrict_rule sign x r).
Proof.
 destruct r; cbn; f_equal; auto using restrict_forcelevel_term.
Qed.

Lemma restrict_forcelevel_deriv sign x y d :
 restrict_deriv sign x (forcelevel_deriv y d) =
 forcelevel_deriv y (restrict_deriv sign x d).
Proof.
 induction d as [r s ds IH] using derivation_ind'; cbn.
 f_equal.
 - apply restrict_forcelevel_rule.
 - apply restrict_forcelevel_seq.
 - rewrite !map_map. apply map_ext_iff.
   rewrite Forall_forall in IH; auto.
Qed.

(* A few examples of proofs in NJ1 and NK1 (Samuel). *)

Lemma ex1 f1 f2 : Provable Intuiti ([] ⊢ (f1 /\ f2) -> (f1 \/ f2)).
Proof.
  apply Provable_alt.
  apply R_Imp_i.
  apply R_Or_i1.
  apply R_And_e1 with (B := f2).
  apply R_Ax.
  apply in_eq.
Qed.

Lemma ex2 f1 f2 f3 : Provable Intuiti ([] ⊢ (f1 -> f2 -> f3) <-> (f1 /\ f2 -> f3)).
Proof.
  apply Provable_alt.
  apply R_And_i.
  + apply R_Imp_i.
    apply R_Imp_i.
    apply R_Imp_e with (A := f2).
    - apply R_Imp_e with (A := f1).
      * apply R_Ax. apply in_cons. apply in_eq.
      * apply R_And_e1 with (B := f2). apply R_Ax. apply in_eq.
    - apply R_And_e2 with (A := f1). apply R_Ax. apply in_eq.
  + apply R_Imp_i.
    apply R_Imp_i.
    apply R_Imp_i.
    apply R_Imp_e with (A := (f1 /\ f2)%form).
    - apply R_Ax. apply in_cons. apply in_cons. apply in_eq.
    - apply R_And_i; apply R_Ax.
      * apply in_cons. apply in_eq.
      * apply in_eq.
Qed.

Lemma RAA f1 Γ : Pr Classic (Γ ⊢ ~~f1) -> Pr Classic (Γ ⊢ f1).
Proof.
  intro.
  apply R_Absu.
  + reflexivity.
  + apply R_Not_e with (A := (~ f1)%form).
    - apply R_Ax. apply in_eq.
    - apply Pr_pop. exact H.
Qed.

Lemma DeMorgan f1 f2 Γ : Pr Classic (Γ ⊢ ~(~f1 /\ f2)) -> Pr Classic (Γ ⊢ ~~(f1 \/ ~f2)).
Proof.
  intro.
  apply R_Not_i.
  apply R_Not_e with (A := (~f1 /\ f2)%form).
  + apply RAA with (f1 := (~f1 /\ f2)%form).
    apply R_Not_i.
    apply R_Not_e with (A := (f1\/~f2)%form).
    - apply R_Or_i1.
      apply RAA.
      apply R_Not_i.
      apply R_Not_e with (A := (f1\/~f2)%form).
      * apply R_Or_i2. apply R_Not_i. apply R_Not_e with (A := (~f1 /\ f2)%form).
        ++ apply R_And_i.
           -- apply R_Ax. apply in_cons. apply in_eq.
           -- apply R_Ax. apply in_eq.
        ++ apply R_Ax. apply in_cons. apply in_cons. apply in_eq.
      * apply R_Ax. apply in_cons. apply in_cons. apply in_eq.
    - apply R_Ax. apply in_cons. apply in_eq.
  + apply Pr_pop. exact H.
Qed.

Lemma ExcludedMiddle f1 : Provable Classic ([] ⊢ f1 \/ ~f1).
Proof.
  apply Provable_alt.
  apply RAA.
  apply DeMorgan with (f2 := f1) (Γ := []).
  apply R_Not_i.
  apply R_Not_e with (A := f1).
  + apply R_And_e2 with (A := (~f1)%form). apply R_Ax. apply in_eq.
  + apply R_And_e1 with (B := f1). apply R_Ax. apply in_eq.
Qed.
