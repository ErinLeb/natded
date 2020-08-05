
(** * Toolbox : basic properties of the Mix functions like bsubst *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Implicit Type t u : term.
Implicit Type f : formula.

(** Summary of this file :
    1) [lift]
    2) [bsubst]
    3) [fclosed]
    4) [vmap] and [fsubst]
*)

(** ** Part 1 : Properties of [lift] *)

Lemma level_lift k t : level (lift k t) <= S (level t).
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto with arith.
 - case Nat.leb_spec; auto.
 - rewrite map_map.
   apply list_max_map_le. intros a Ha. transitivity (S (level a)); auto.
   rewrite <- Nat.succ_le_mono. now apply list_max_map_in.
Qed.

Lemma lift_nop_le k t : level t <= k -> lift k t = t.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 - case Nat.leb_spec; auto. omega.
 - rewrite list_max_map_le. intros H. f_equal. apply map_id_iff; auto.
Qed.

Lemma lift_nop k t : BClosed t -> lift k t = t.
Proof.
 unfold BClosed. intros H. apply lift_nop_le. rewrite H; omega.
Qed.

Lemma lift_incrlevel k t : k < level t -> level (lift k t) = S (level t).
Proof.
 revert t. fix IH 1; destruct t; cbn.
 - inversion 1.
 - case Nat.leb_spec; cbn; omega.
 - revert l; fix IHl 1; destruct l as [|t l]; cbn.
   + inversion 1.
   + rewrite Nat.max_lt_iff. intros LT.
     destruct (Nat.lt_ge_cases k (level t)),
              (Nat.lt_ge_cases k (list_max (map level l))).
     * rewrite (IH t), (IHl l); auto.
     * rewrite (IH t); auto.
       generalize (lift_nop_le k (Fun f l) H0). cbn - [Nat.max].
       intros [= ->]. omega with *.
     * rewrite (IHl l), (lift_nop_le k t); auto. omega with *.
     * omega with *.
Qed.

Lemma check_lift sign k t :
 check sign (lift k t) = check sign t.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 - case Nat.leb_spec; auto.
 - destruct funsymbs; auto.
   rewrite map_length. case eqb; auto.
   apply eq_true_iff_eq. rewrite forallb_map, !forallb_forall.
   split; intros H x Hx. rewrite <- IH; auto. rewrite IH; auto.
Qed.

Lemma fvars_lift k t : fvars (lift k t) = fvars t.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto with *.
 - case Nat.leb_spec; auto.
 - induction l; simpl; auto.
   rewrite IH, IHl; simpl; auto.
   intros x Hx. apply IH. simpl; auto.
Qed.

Lemma level_lift_form k f : level (lift k f) <= S (level f).
Proof.
  revert k. induction f; intro; cbn; auto with arith.
  + rewrite map_map.
    rewrite list_max_map_le.
    intros.
    transitivity (S (level a)).
    - apply level_lift.
    - apply-> Nat.succ_le_mono.
      apply list_max_map_in.
      assumption.
  + specialize (IHf1 k).
    specialize (IHf2 k).
    omega with *.
  + specialize (IHf (S k)).
    omega.
Qed.

Lemma check_lift_form sign f k :
  check sign (lift k f) = check sign f.
Proof.
  revert k. induction f; cbn; auto.
  + destruct (predsymbs sign p); auto.
    intro. rewrite map_length. case eqb; auto.
    apply eq_true_iff_eq. rewrite forallb_map, !forallb_forall.
    split; intros.
    - destruct H with (x := x); auto. rewrite check_lift. reflexivity.
    - destruct H with (x := x); auto. rewrite check_lift. reflexivity.
  + intro. rewrite IHf1. rewrite IHf2. reflexivity.
Qed.

Lemma fvars_lift_form f k :
  fvars (lift k f) = fvars f.
Proof.
  revert k. induction f; intro; cbn; auto with *.
  - induction l; simpl; auto.
    rewrite fvars_lift, IHl; simpl; auto.
  - rewrite IHf1. rewrite IHf2. auto.
Qed.

(** ** Part 2 : [bsubst] *)

(** [bsubst] and [check] *)

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

Lemma level_bsubst_term_max n u t :
  level (bsubst n u t) <= Nat.max (level u) (level t).
Proof.
 revert t. fix IH 1; destruct t; cbn -[Nat.max].
 - auto with arith.
 - case eqbspec; cbn -[Nat.max]; omega with *.
 - revert l. fix IHl 1; destruct l; cbn -[Nat.max].
   + auto with arith.
   + specialize (IH t). specialize (IHl l). omega with *.
Qed.

Lemma level_bsubst_max n u f :
  level (bsubst n u f) <= Nat.max (level u) (level f).
Proof.
 revert n u.
 induction f; intros; cbn -[Nat.max]; auto with arith.
 - apply (level_bsubst_term_max n u (Fun "" l)).
 - specialize (IHf1 n u). specialize (IHf2 n u). omega with *.
 - assert (H := level_lift 0 u).
   specialize (IHf (S n) (lift 0 u)). omega with *.
Qed.

(** When substituting the highest var (or above), we can be
    slightly more precise than the previous generic results. *)

Lemma level_bsubst_term n u t :
 level t <= S n ->
 level (bsubst n u t) <= Nat.max n (level u).
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto with arith.
 - case eqbspec; cbn; auto; intros; omega with *.
 - intros Hl. rewrite map_map. apply list_max_map_le.
   rewrite list_max_map_le in Hl; auto.
Qed.

Lemma level_bsubst n u f :
 level f <= S n ->
 level (bsubst n u f) <= Nat.max n (level u).
Proof.
 revert n u.
 induction f; cbn; intros n u Hf; auto with arith.
 - apply (level_bsubst_term n u (Fun "" l)); auto.
 - rewrite max_le in *; intuition.
 - rewrite Nat.le_pred_le_succ in Hf.
   apply Nat.le_pred_le_succ. rewrite IHf; auto.
   generalize (level_lift 0 u). omega with *.
Qed.

(** Other specialized results when [u] has no higher vars than [n] *)

Lemma level_bsubst_term' n (u t : term) :
  level u <= S n ->
  level (bsubst n u t) <= level t.
Proof.
 intro Hu. revert t. fix IH 1. destruct t; cbn; auto.
 - case eqbspec; intros; subst; auto.
 - revert l. fix IH' 1. destruct l; cbn; auto.
   apply Nat.max_le_compat; auto.
Qed.

Lemma level_bsubst' n u (f:formula) :
  level u <= S n ->
  level (bsubst n u f) <= level f.
Proof.
 revert n u. induction f; cbn; intros n u Hu; auto with arith.
 - now apply (level_bsubst_term' n u (Fun "" l)).
 - apply Nat.max_le_compat; auto.
 - apply Nat.pred_le_mono; auto with arith.
   apply IHf. transitivity (S (level u)). apply level_lift. omega.
Qed.

(** A reverse result about the level of [bsubst] :
    The substituted variable is gone if it was lacking before or
    if it isn't there in the substituted term. *)

Lemma level_term_subst_inv n u t :
  level (bsubst n u t) <= n ->
  level t <= n \/ level u <= level (bsubst n u t).
Proof.
 revert t. fix IH 1; destruct t; cbn.
 - auto.
 - case eqbspec; intros; subst; auto.
 - revert l. fix IHl 1; destruct l; cbn.
   + auto.
   + intros H. apply Nat.max_lub_iff in H. destruct H as (H,Hl).
     destruct (IH t H), (IHl l Hl);
     try (right; omega with * ). left; omega with *.
Qed.

Lemma level_subst_inv n u f :
  level (bsubst n u f) <= n ->
  level f <= n \/ level u <= level (bsubst n u f).
Proof.
 revert n u.
 induction f; cbn; intros; auto.
 - apply (level_term_subst_inv n u (Fun "" l) H).
 - apply Nat.max_lub_iff in H. destruct H as (H1,H2).
   destruct (IHf1 _ _ H1), (IHf2 _ _ H2);
     try (right; omega with * ). left; omega with *.
 - destruct (IHf (S n) (lift 0 u)).
   + omega with *.
   + left; omega.
   + right.
     case (Nat.leb_spec (level u) 0). omega.
     intros LT. rewrite (lift_incrlevel 0 u LT) in *. omega.
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

(** [bsubst] by the same [BVar] does nothing *)

Lemma term_bsubst_id n t : bsubst n (BVar n) t = t.
Proof.
 induction t as [ v | m | f l IH] using term_ind'; cbn; auto.
 - case eqbspec; auto.
 - f_equal. rewrite <- (map_id l) at 2.
   apply map_ext_in. intros a IN. apply IH; auto.
Qed.

Lemma bsubst_id n f : bsubst n (BVar n) f = f.
Proof.
 revert n. induction f; intros n; cbn; f_equal; auto.
 now injection (term_bsubst_id n (Fun "" l)).
Qed.

(** Commuting two different [bsubst] *)

Lemma swap_term_bsubst n m u v t :
 n <> m -> BClosed u -> BClosed v ->
 bsubst n u (bsubst m v t) = bsubst m v (bsubst n u t).
Proof.
 induction t using term_ind'; cbn; auto.
 - repeat (case eqbspec; cbn; intros; subst); auto; try easy;
   now rewrite bclosed_bsubst_id.
 - intros. f_equal. rewrite !map_map. apply map_ext_in; auto.
Qed.

Lemma swap_bsubst n m u v f :
 n <> m -> BClosed u -> BClosed v ->
 bsubst n u (bsubst m v f) = bsubst m v (bsubst n u f).
Proof.
 revert n m.
 induction f; cbn; intros; f_equal; auto.
 - rewrite !map_map. apply map_ext_in.
   intros. now apply swap_term_bsubst.
 - rewrite !lift_nop; auto.
Qed.

(** [bsubst] "transitivity" : two [bsubst] in a row may give a single one *)

Lemma term_bsubst_bsubst n m u t :
 level t <= m ->
 bsubst m u (bsubst n (BVar m) t) = bsubst n u t.
Proof.
 induction t as [ v | k | f l IH] using term_ind'; intros Ht.
 - now cbn.
 - cbn in Ht. cbn.
   case eqbspec; intros; subst; cbn; case eqbspec; auto; try easy.
   intros. exfalso. omega.
 - cbn. f_equal. rewrite map_map.
   apply map_ext_in. intros a IN. apply IH; auto.
   cbn in Ht. rewrite list_max_map_le in Ht; auto.
Qed.

Lemma bsubst_bsubst n m u f :
 level f <= m ->
 bsubst m u (bsubst n (BVar m) f) = bsubst n u f.
Proof.
 revert n m u.
 induction f; cbn; intros; f_equal; auto.
 - injection (term_bsubst_bsubst n m u (Fun "" l) H) as E. exact E.
 - apply Nat.max_lub_iff in H. destruct H as (H1,H2); auto.
 - apply Nat.max_lub_iff in H. destruct H as (H1,H2); auto.
 - apply (IHf (S n) (S m) (lift _ u)). omega.
Qed.

(** [bsubst] and [fvars] : over-approximations *)

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
 - rewrite IHf. now rewrite fvars_lift.
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

(** ** Part 3 : properties of [fclosed] *)

Lemma term_fclosed_spec t : fclosed t = true <-> FClosed t.
Proof.
 unfold FClosed.
 induction t using term_ind'; cbn.
 - rewrite <- Names.is_empty_spec. namedec.
 - rewrite <- Names.is_empty_spec. reflexivity.
 - rewrite forallb_forall. unfold Names.Empty.
   setoid_rewrite unionmap_in. split.
   + intros F a (t & IN & IN').
     specialize (F t IN'). rewrite H in F; auto. now apply (F a).
   + intros G x Hx. rewrite H; auto. intros a Ha. apply (G a).
     now exists x.
Qed.

Lemma form_fclosed_spec f : fclosed f = true <-> FClosed f.
Proof.
 unfold FClosed.
 induction f; cbn; auto.
 - rewrite <- Names.is_empty_spec. namedec.
 - rewrite <- Names.is_empty_spec. namedec.
 - apply (term_fclosed_spec (Fun "" l)).
 - rewrite lazy_andb_iff, IHf1, IHf2.
   intuition.
Qed.

Lemma fclosed_bsubst n t f :
 fclosed t = true -> fclosed (bsubst n t f) = fclosed f.
Proof.
 intros E. apply eq_true_iff_eq. rewrite !form_fclosed_spec.
 rewrite term_fclosed_spec in E. unfold FClosed in *.
 assert (Names.Equal (fvars (bsubst n t f)) (fvars f)).
 { intros a. split. rewrite bsubst_fvars. namedec.
   apply bsubst_fvars'. }
 now rewrite H.
Qed.

Lemma fclosed_lift n f : fclosed (lift n f) = fclosed f.
Proof.
 apply eq_true_iff_eq. rewrite !form_fclosed_spec.
 unfold FClosed. now rewrite fvars_lift_form.
Qed.

(** ** Part 4 : [vmap] and [fsubst] *)

(** basic results : extensionality, identity, composition *)

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

Lemma lift_vmap (h:variable->term) k t :
 lift k (vmap h t) = vmap (fun v => lift k (h v)) (lift k t).
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 - case Nat.leb_spec; auto.
 - f_equal. rewrite !map_map. apply map_ext_iff; auto.
Qed.

Lemma lift_vmap' (h:variable->term) k t :
 BClosed_sub h ->
 lift k (vmap h t) = vmap h (lift k t).
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
