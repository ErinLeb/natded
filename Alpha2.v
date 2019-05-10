
(** * Equivalence between various substs and alpha for named formulas *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Nam Alpha Meta Equiv.
Import ListNotations.
Import Nam.Form.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Lemma invars_in sub v :
  Names.In v (Subst.invars sub) <-> In v (map fst sub).
Proof.
 induction sub as [|(x,t) sub IH]; simpl. namedec.
 nameiff. intuition.
Qed.

Lemma invars_app h h' :
  Names.Equal (Subst.invars (h++h'))
             (Names.union (Subst.invars h) (Subst.invars h')).
Proof.
 induction h; simpl; auto with set.
Qed.

Lemma invars_unassoc v h :
  Names.Equal (Subst.invars (list_unassoc v h))
             (Names.remove v (Subst.invars h)).
Proof.
 induction h as [|(x,u) h IH]; simpl.
 - namedec.
 - case eqbspec; simpl.
   + intros ->. rewrite IH. namedec.
   + intros NE. rewrite IH. namedec.
Qed.

Lemma outvars_app h h' :
 Names.Equal (Subst.outvars (h++h'))
            (Names.union (Subst.outvars h) (Subst.outvars h')).
Proof.
 unfold Subst.outvars.
 apply unionmap_app.
Qed.

Lemma outvars_unassoc v h :
 Names.Subset (Subst.outvars (list_unassoc v h))
             (Subst.outvars h).
Proof.
 induction h as [|(x,t) h IH]; simpl.
 - namedec.
 - case eqbspec; simpl; namedec.
Qed.

(** Free variables after [substs] *)

Lemma term_substs_vars h t :
 Names.Subset (Term.vars (Term.substs h t))
             (Names.union (Names.diff (Term.vars t) (Subst.invars h))
                         (Subst.outvars h)).
Proof.
 revert t.
 fix IH 1. destruct t as [v|f l]; cbn.
 - rewrite list_assoc_dft_alt.
   assert (H := list_assoc_in2 h v).
   assert (H' := list_assoc_notin h v).
   destruct (list_assoc v h).
   + specialize (H t).
     unfold Subst.outvars.
     intros y Hy.
     rewrite Names.union_spec, unionmap_in.
     right. exists (v,t); auto.
   + simpl. intros y. rewrite Names.singleton_spec. intros ->.
     nameiff. left; split; auto.
     rewrite invars_in; intuition.
 - clear f. revert l.
   fix IH' 1. destruct l as [|t l]; cbn -[Names.diff].
   + namedec.
   + specialize (IH t). specialize (IH' l). namedec.
Qed.

Lemma substs_freevars h f :
 Names.Subset (freevars (substs h f))
             (Names.union (Names.diff (freevars f) (Subst.invars h))
                         (Subst.outvars h)).
Proof.
 revert h.
 induction f; cbn -[Subst.invars Subst.outvars Names.diff]; intros; auto.
 - namedec.
 - namedec.
 - apply (term_substs_vars h (Fun "" l)).
 - rewrite IHf1, IHf2. namedec.
 - destruct (Names.mem _ _) eqn:E; simpl.
   + setfresh vars z Hz.
     rewrite IHf; simpl.
     rewrite invars_unassoc, outvars_unassoc. namedec.
   + rewrite IHf; simpl.
     rewrite invars_unassoc, outvars_unassoc. namedec.
Qed.

(** [nam2mix] and free variables *)

Lemma nam2mix_tvars stk t :
  Names.Equal (Mix.fvars (nam2mix_term stk t))
              (Names.diff (Term.vars t) (Names.of_list stk)).
Proof.
 revert t.
 fix IH 1. destruct t as [v|f l]; cbn.
 - destruct list_index eqn:E; cbn.
   + assert (NE : list_index v stk <> None) by congruence.
     rewrite list_index_in in NE. rewrite <-names_of_list_in in NE. namedec.
   + rewrite list_index_notin, <-names_of_list_in in E. namedec.
 - clear f. revert l.
   fix IH' 1. destruct l as [|t l]; cbn; rewrite ?IH, ?IH'; namedec.
Qed.

Lemma nam2mix_fvars stk f :
  Names.Equal (Mix.fvars (nam2mix stk f))
              (Names.diff (freevars f) (Names.of_list stk)).
Proof.
 revert stk.
 induction f; intros; cbn.
 - namedec.
 - namedec.
 - apply (nam2mix_tvars stk (Fun "" l)).
 - auto.
 - rewrite IHf1, IHf2; namedec.
 - rewrite IHf. simpl. namedec.
Qed.

(** [nam2mix] and modifying the stack while keeping the result *)

Lemma nam2mix_term_indep (stk stk' : list variable) t :
 (forall (v:variable), Names.In v (Term.vars t) ->
            list_index v stk = list_index v stk') ->
 nam2mix_term stk t = nam2mix_term stk' t.
Proof.
 induction t as [v|f l IH] using term_ind'; cbn; intros Ht.
 - rewrite Ht; auto with set.
 - f_equal. clear f. apply map_ext_iff. intros a Ha.
   apply IH; auto. intros v Hv. apply Ht.
   rewrite unionmap_in. now exists a.
Qed.

Lemma nam2mix_indep (stk stk' : list variable) f :
 (forall (v:variable), Names.In v (freevars f) ->
            list_index v stk = list_index v stk') ->
 nam2mix stk f = nam2mix stk' f.
Proof.
 revert stk stk'.
 induction f; simpl; intros stk stk' EQ; f_equal; auto with set.
 - injection (nam2mix_term_indep stk stk' (Fun "" l)); auto.
 - apply IHf. intros v' Hv'; simpl.
   case eqbspec; auto.
   intros NE. f_equal. apply EQ. namedec.
Qed.

Lemma nam2mix_term_nostack stk t :
 (forall v, In v stk -> ~Names.In v (Term.vars t)) ->
 nam2mix_term stk t = nam2mix_term [] t.
Proof.
 intros H. apply nam2mix_term_indep.
 intros v Hv. simpl. rewrite list_index_notin.
 intros IN. apply (H v IN Hv).
Qed.

Lemma nam2mix_shadowstack stk x f :
 In x stk ->
 nam2mix (stk++[x]) f = nam2mix stk f.
Proof.
 intros H. apply nam2mix_indep.
 intros v Hv. case (eqbspec v x).
 - intros ->. now rewrite list_index_app_l.
 - intros NE. rewrite list_index_app_l'; auto. simpl; intuition.
Qed.

Lemma nam2mix_shadowstack' stk stk' x y f :
 In x stk \/ ~Names.In x (freevars f) ->
 In y stk \/ ~Names.In y (freevars f) ->
 nam2mix (stk++x::stk') f = nam2mix (stk++y::stk') f.
Proof.
 intros Hx Hy. apply nam2mix_indep.
 intros v Hv.
 destruct (in_dec string_dec v stk).
 - rewrite 2 list_index_app_l; auto.
 - rewrite 2 list_index_app_r; auto. simpl.
   case eqbspec; [intros ->;intuition|].
   case eqbspec; [intros ->;intuition|auto].
Qed.

Lemma nam2mix_shadowstack_map stk stk' x y f :
 In x stk \/ ~Names.In x (freevars f) ->
 In y stk \/ ~Names.In y (freevars f) ->
 nam2mix (stk++map (fun a => if a =?x then y else a) stk') f =
 nam2mix (stk++stk') f.
Proof.
 intros Hx Hy. apply nam2mix_indep.
 intros v Hv.
 destruct (in_dec string_dec v stk).
 - rewrite 2 list_index_app_l; auto.
 - rewrite 2 list_index_app_r; auto. f_equal.
   induction stk' as [|a stk' IH]; auto.
   simpl. rewrite IH.
   case (eqbspec a x); auto.
   repeat case eqbspec; intros; subst; intuition.
Qed.


(** [Term.substs] may do nothing *)

Lemma term_substs_notin h t :
 Names.Empty (Names.inter (Term.vars t) (Subst.invars h)) ->
 Term.substs h t = t.
Proof.
 induction t as [v |f l IH] using term_ind'; intros EM; cbn in *.
 - rewrite list_assoc_dft_alt.
   assert (NI : ~In v (map fst h)).
   { rewrite <- invars_in. namedec. }
   rewrite <- list_assoc_notin in NI. now rewrite NI.
 - f_equal. clear f.
   apply map_id_iff.
   intros a Ha. apply IH; auto. intros v. nameiff. intros (Hv,Hv').
   apply (EM v). nameiff. split; auto.
   rewrite unionmap_in. now exists a.
Qed.

Lemma nam2mix_term_subst stk x u t:
 ~In x stk ->
 nam2mix_term stk (Term.subst x u t) =
 Mix.fsubst x (nam2mix_term stk u) (nam2mix_term stk t).
Proof.
 induction t as [v|f l IH] using term_ind'; intros NI; cbn.
 - case eqbspec.
   + intros ->.
     rewrite <-list_index_notin in NI. rewrite NI.
     cbn. unfold Mix.varsubst. now rewrite eqb_refl.
   + intros NE.
     cbn.
     destruct (list_index v stk); cbn; auto.
     unfold Mix.varsubst. case eqbspec; congruence.
 - f_equal; clear f.
   rewrite !map_map.
   apply map_ext_in. intros t Ht. apply IH; auto.
Qed.

Lemma nam2mix_partialsubst stk x u f :
 ~In x stk ->
 (forall v, In v stk -> ~Names.In v (Term.vars u)) ->
 IsSimple x u f ->
 nam2mix stk (partialsubst x u f) =
 Mix.fsubst x (nam2mix_term [] u) (nam2mix stk f).
Proof.
 revert stk.
 induction f; cbn; intros stk Hx Hu IS; f_equal; auto.
 - rewrite <- (nam2mix_term_nostack stk); auto.
   injection (nam2mix_term_subst stk x u (Fun "" l)); easy.
 - intuition.
 - intuition.
 - case eqbspec; cbn.
   + intros ->.
     unfold Mix.fsubst.
     rewrite form_vmap_id; auto.
     intros x. rewrite nam2mix_fvars. simpl.
     unfold Mix.varsubst.
     intros IN.
     case eqbspec; auto. intros <-. namedec.
   + intros NE.
     destruct IS as [-> | (NI,IS)]; [easy|].
     rewrite mem_false by trivial.
     apply IHf; simpl; intuition auto; subst; eauto.
Qed.

Lemma nam2mix_term_subst' stk stk' x z t :
 ~In x stk ->
 ~In z stk ->
 ~Names.In z (Term.vars t) ->
 nam2mix_term (stk++z::stk') (Term.subst x (Var z) t) =
 nam2mix_term (stk++x::stk') t.
Proof.
 induction t as [v|f l IH] using term_ind'; intros Hx Hz NI; cbn in *.
 - case eqbspec; cbn.
   + intros ->.
     rewrite 2 list_index_app_r by intuition.
     simpl; rewrite 2 eqb_refl. simpl; auto.
   + intros NE. destruct (In_dec string_dec v stk).
     * rewrite 2 list_index_app_l; auto.
     * rewrite 2 list_index_app_r by auto. simpl.
       do 2 case eqbspec; auto. namedec. intuition.
 - f_equal; clear f.
   rewrite !map_map.
   apply map_ext_in. intros t Ht. apply IH; auto.
   eapply unionmap_notin; eauto.
Qed.

Lemma nam2mix_partialsubst' stk stk' x z f :
 ~In x stk ->
 ~In z stk ->
 ~Names.In z (allvars f) ->
 nam2mix (stk++z::stk') (partialsubst x (Var z) f) =
 nam2mix (stk++x::stk') f.
Proof.
 revert stk.
 induction f; cbn; intros stk Hx Hz IS; f_equal; auto.
 - injection (nam2mix_term_subst' stk stk' x z (Fun "" l)); easy.
 - intuition.
 - intuition.
 - rewrite mem_false by namedec.
   case eqbspec; cbn.
   + intros <-.
     symmetry.
     apply (nam2mix_shadowstack' (x::stk)). simpl; auto.
     right. rewrite freevars_allvars. namedec.
   + intros NE.
     apply (IHf (v::stk)).
     simpl. intuition.
     simpl. intuition.
     namedec.
Qed.

Lemma nam2mix0_partialsubst x u f :
 IsSimple x u f ->
 nam2mix [] (partialsubst x u f) =
  Mix.fsubst x (nam2mix_term [] u) (nam2mix [] f).
Proof.
 apply nam2mix_partialsubst; auto.
Qed.

Lemma term_subst_bsubst stk (x:variable) u t :
 ~In x stk ->
 (forall v, In v stk -> ~Names.In v (Term.vars u)) ->
 nam2mix_term stk (Term.subst x u t) =
  Mix.bsubst (length stk) (nam2mix_term [] u)
             (nam2mix_term (stk++[x]) t).
Proof.
  induction t as [v|f l IH] using term_ind'; intros X U; cbn in *.
 - case eqbspec.
   + intros ->.
     rewrite list_index_app_r; auto. cbn. rewrite eqb_refl. cbn.
     rewrite Nat.add_0_r. rewrite eqb_refl.
     now apply nam2mix_term_nostack.
   + intros NE. cbn.
     rewrite list_index_app_l' by (simpl; intuition).
     destruct (list_index v stk) eqn:E; cbn; auto.
     apply list_index_lt_length in E.
     case eqbspec; intros; subst; auto; omega.
 - f_equal; clear f.
   rewrite !map_map.
   apply map_ext_in. intros t Ht. apply IH; auto.
Qed.

Lemma partialsubst_bsubst stk x u f :
 ~In x stk ->
 (forall v, In v stk -> ~Names.In v (Term.vars u)) ->
 IsSimple x u f ->
 nam2mix stk (partialsubst x u f) =
  Mix.bsubst (length stk) (nam2mix_term [] u)
             (nam2mix (stk++[x]) f).
Proof.
 revert stk.
 induction f; cbn; intros stk X U IS; f_equal; auto.
 - injection (term_subst_bsubst stk x u (Fun "" l)); auto.
 - destruct IS as (IS1,IS2); auto.
 - destruct IS as (IS1,IS2); auto.
 - case eqbspec; cbn.
   + intros <-.
     change (x::stk++[x]) with ((x::stk)++[x]).
     rewrite nam2mix_shadowstack by (simpl; auto).
     symmetry.
     apply form_level_bsubst_id.
     now rewrite nam2mix_level.
   + intros NE.
     destruct IS as [->|(NI,IS)]; [easy|].
     rewrite mem_false by namedec0.
     apply IHf; simpl; auto.
     intuition.
     intros y [<-|Hy]; auto.
Qed.

Lemma partialsubst_bsubst0 x u f :
 IsSimple x u f ->
 nam2mix [] (partialsubst x u f) =
  Mix.bsubst 0 (nam2mix_term [] u) (nam2mix [x] f).
Proof.
 apply partialsubst_bsubst; auto.
Qed.

Lemma partialsubst_bsubst0_var x z f :
 ~Names.In z (allvars f) ->
 nam2mix [] (partialsubst x (Var z) f) =
  Mix.bsubst 0 (Mix.FVar z) (nam2mix [x] f).
Proof.
 intros.
 apply (partialsubst_bsubst0 x (Var z)); auto.
Qed.

Lemma nam2mix_rename_iff z v v' f f' :
  ~ Names.In z (Names.union (allvars f) (allvars f')) ->
  nam2mix [] (partialsubst v (Var z) f) =
  nam2mix [] (partialsubst v' (Var z) f')
  <->
  nam2mix [v] f = nam2mix [v'] f'.
Proof.
 intros Hz.
 rewrite 2 partialsubst_bsubst0_var by namedec.
 split.
 - intros H. apply bsubst_fresh_inj in H; auto.
   rewrite !nam2mix_fvars. cbn. rewrite !freevars_allvars. namedec.
 - now intros ->.
Qed.

Lemma nam2mix_term_inj t t' : nam2mix_term [] t = nam2mix_term [] t' -> t = t'.
Proof.
 intro E.
 apply (nam2mix_term_ok [] []) in E; auto.
 rewrite !term_substs_notin in E; cbn; auto with set.
Qed.

Lemma nam2mix_canonical' f f' :
 nam2mix [] f = nam2mix [] f' <-> Ind.AlphaEq f f'.
Proof.
 split.
 - set (h := S (Nat.max (height f) (height f'))).
   assert (LT : height f < h) by (unfold h; auto with *).
   assert (LT' : height f' < h) by (unfold h; auto with *).
   clearbody h. revert f f' LT LT'.
   induction h as [|h IH]; [inversion 1|].
   destruct f, f'; simpl; intros LT LT'; simpl_height; try easy.
   + intros [= <- E].
     injection (nam2mix_term_inj (Fun "" l) (Fun "" l0)) as <-; cbn; auto.
     now f_equal.
   + intros [= E]; auto.
   + intros [= <- E1 E2]; auto.
   + intros [= <- E].
     destruct (exist_fresh (Names.union (allvars f) (allvars f'))) as (z,Hz).
     apply Ind.AEqQu with z; auto.
     apply IH; try rewrite partialsubst_height; auto.
     apply nam2mix_rename_iff; auto.
 - induction 1; cbn; f_equal; auto.
   apply (nam2mix_rename_iff z); auto.
Qed.

Lemma AlphaEq_equiv f f' : Form.AlphaEq f f' <-> Ind.AlphaEq f f'.
Proof.
 now rewrite <- nam2mix_canonical', nam2mix_canonical.
Qed.

Lemma AlphaEq_alt f f' :
  Form.Alt.AlphaEq f f' <-> Form.AlphaEq f f'.
Proof.
 now rewrite AlphaEq_equiv, Alpha.AlphaEq_equiv.
Qed.

Lemma αeq_alt f f' : Alt.αeq f f' = αeq f f'.
Proof.
 apply eq_true_iff_eq. apply AlphaEq_alt.
Qed.

(** For the rest of the file, we use the [Ind.AlphaEq] variant. *)

Import Ind.

(** We've seen that [nam2mix []] maps alpha-equivalent formulas
    to equal formulas. This is actually also true for
    [nam2mix stk] with any [stk]. Here comes a first part
    of this statement, the full version is below in
    [nam2mix_canonical_gen].
*)

Lemma AlphaEq_nam2mix_gen stk f f' :
 AlphaEq f f' -> nam2mix stk f = nam2mix stk f'.
Proof.
 intros H. revert stk.
 induction H; cbn; intros stk; f_equal; auto.
 generalize (IHAlphaEq (z::stk)).
 rewrite (nam2mix_partialsubst' [] stk v z) by (auto; namedec).
 rewrite (nam2mix_partialsubst' [] stk v' z) by (auto; namedec).
 auto.
Qed.

(** SUBST *)

Lemma nam2mix_Subst_fsubst stk (x:variable) u f f' :
 ~In x stk ->
 (forall v, In v stk -> ~Names.In v (Term.vars u)) ->
 Subst x u f f' ->
 nam2mix stk f' = Mix.fsubst x (nam2mix_term [] u) (nam2mix stk f).
Proof.
 intros NI CL (f0 & EQ & SI).
 apply AlphaEq_nam2mix_gen with (stk:=stk) in EQ. rewrite EQ.
 apply SimpleSubst_carac in SI. destruct SI as (<- & IS).
 apply nam2mix_partialsubst; auto.
Qed.

Lemma nam2mix_altsubst_fsubst stk (x:variable) u f :
 ~In x stk ->
 (forall v, In v stk -> ~Names.In v (Term.vars u)) ->
 nam2mix stk (Alt.subst x u f) =
 Mix.fsubst x (nam2mix_term [] u) (nam2mix stk f).
Proof.
 intros.
 apply nam2mix_Subst_fsubst; auto.
 apply Subst_subst.
Qed.

Lemma nam2mix0_altsubst_fsubst x u f :
 nam2mix [] (Alt.subst x u f) =
  Mix.fsubst x (nam2mix_term [] u) (nam2mix [] f).
Proof.
 apply nam2mix_altsubst_fsubst; auto.
Qed.

Lemma nam2mix_Subst_bsubst stk x u f f' :
 ~In x stk ->
 (forall v, In v stk -> ~Names.In v (Term.vars u)) ->
 Subst x u f f' ->
 nam2mix stk f' =
 Mix.bsubst (length stk) (nam2mix_term [] u)
            (nam2mix (stk++[x]) f).
Proof.
 intros NI CL (f0 & EQ & SI).
 apply AlphaEq_nam2mix_gen with (stk:=stk++[x]) in EQ.
 rewrite EQ.
 apply SimpleSubst_carac in SI. destruct SI as (<- & IS).
 now apply partialsubst_bsubst.
Qed.

Lemma nam2mix_altsubst_bsubst stk (x:variable) u f :
 ~In x stk ->
 (forall v, In v stk -> ~Names.In v (Term.vars u)) ->
 nam2mix stk (Alt.subst x u f) =
  Mix.bsubst (length stk) (nam2mix_term [] u)
             (nam2mix (stk++[x]) f).
Proof.
 intros.
 apply nam2mix_Subst_bsubst; auto.
 apply Subst_subst.
Qed.

Lemma nam2mix_altsubst_bsubst0 x u f :
 nam2mix [] (Alt.subst x u f) =
  Mix.bsubst 0 (nam2mix_term [] u) (nam2mix [x] f).
Proof.
 apply nam2mix_altsubst_bsubst; auto.
Qed.

Lemma nam2mix_rename_iff2 z v v' f f' :
  ~ Names.In z (Names.union (freevars f) (freevars f')) ->
  nam2mix [] (Alt.subst v (Var z) f) =
  nam2mix [] (Alt.subst v' (Var z) f')
  <->
  nam2mix [v] f = nam2mix [v'] f'.
Proof.
 intros Hz.
 rewrite 2 nam2mix_altsubst_bsubst0. cbn.
 split.
 - intros H. apply bsubst_fresh_inj in H; auto.
   rewrite !nam2mix_fvars. cbn. namedec.
 - now intros ->.
Qed.

Lemma nam2mix_altsubst_nop x f :
  nam2mix [] (Alt.subst x (Var x) f) = nam2mix [] f.
Proof.
 rewrite nam2mix0_altsubst_fsubst. simpl.
 unfold Mix.fsubst.
 apply form_vmap_id.
 intros y Hy. unfold Mix.varsubst.
 case eqbspec; intros; subst; auto.
Qed.

Lemma altsubst_nop x f :
  AlphaEq (Alt.subst x (Var x) f) f.
Proof.
 apply nam2mix_canonical'.
 apply nam2mix_altsubst_nop.
Qed.

Lemma nam2mix_rename_iff3 (v x : variable) f f' :
  ~ Names.In x (Names.remove v (freevars f)) ->
  nam2mix [] (Alt.subst v (Var x) f) = nam2mix [] f'
  <->
  nam2mix [v] f = nam2mix [x] f'.
Proof.
 intros Hx.
 rewrite nam2mix_altsubst_bsubst0. cbn.
 split.
 - rewrite <- (nam2mix_altsubst_nop x f').
   rewrite nam2mix_altsubst_bsubst0. cbn.
   apply bsubst_fresh_inj.
   rewrite !nam2mix_fvars. cbn. namedec.
 - intros ->.
   rewrite <- (nam2mix_altsubst_bsubst0 x (Var x)).
   apply nam2mix_altsubst_nop.
Qed.

Lemma nam2mix_nostack stk f f' :
 nam2mix stk f = nam2mix stk f' <->
 nam2mix [] f = nam2mix [] f'.
Proof.
 split.
 - rewrite <- (rev_involutive stk).
   set (s := rev stk). clearbody s.
   revert f f'.
   induction s as [|x s IH].
   + trivial.
   + intros f f'. simpl.
     destruct (List.In_dec string_dec x (rev s)) as [IN|NI].
     * rewrite 2 nam2mix_shadowstack; auto.
     * intros Eq.
       apply IH.
       assert (E := altsubst_nop x f).
       apply AlphaEq_nam2mix_gen with (stk:=rev s) in E.
       rewrite <- E.
       assert (E' := altsubst_nop x f').
       apply AlphaEq_nam2mix_gen with (stk:=rev s) in E'.
       rewrite <- E'.
       clear E E'.
       rewrite !nam2mix_altsubst_bsubst, Eq; simpl; auto.
       intros v Hv. nameiff. now intros ->.
       intros v Hv. nameiff. now intros ->.
 - rewrite nam2mix_canonical'. apply AlphaEq_nam2mix_gen.
Qed.

Lemma nam2mix_canonical_gen stk f f' :
 nam2mix stk f = nam2mix stk f' <-> AlphaEq f f'.
Proof.
 rewrite nam2mix_nostack. apply nam2mix_canonical'.
Qed.

(** Let's show that [subst] (based on [substs]) and [Alt.subst]
    (written with a counter, and double nested rec calls)
    produce alpha-equivalent results.
    This is surprinsingly painful to prove, we'll need quite
    some tooling first.
*)

Definition renaming := list (variable*variable).

Definition putVar : variable*variable -> variable*term :=
 fun '(a,b) => (a,Var b).

Definition chgVar : renaming -> variable -> variable :=
  fun h v => list_assoc_dft v h v.

Lemma fst_putVar (h:renaming) :
  map fst (map putVar h) = map fst h.
Proof.
 induction h as [|(a,b) l IH]; simpl; f_equal; auto.
Qed.

Lemma assoc_putVar (h:renaming) v :
  list_assoc v (map putVar h) = option_map Var (list_assoc v h).
Proof.
 induction h as [|(a,b) h IH]; simpl; auto.
 case eqbspec; auto.
Qed.

Lemma unassoc_putVar (h:renaming) v :
  list_unassoc v (map putVar h) = map putVar (list_unassoc v h).
Proof.
 induction h as [|(a,b) h IH]; simpl; auto.
 case eqbspec; simpl; intros; f_equal; auto.
Qed.

Lemma chgVar_some (h:renaming) x z :
 list_assoc x h = Some z -> chgVar h x = z.
Proof.
 unfold chgVar. rewrite list_assoc_dft_alt. now intros ->.
Qed.

Lemma chgVar_none (h:renaming) x :
 list_assoc x h = None -> chgVar h x = x.
Proof.
 unfold chgVar. rewrite list_assoc_dft_alt. now intros ->.
Qed.

Lemma chgVar_unassoc_at x (h:renaming) :
  chgVar (list_unassoc x h) x = x.
Proof.
  unfold chgVar.
  induction h as [|(a,b) h IH]; simpl in *; auto.
  repeat (case eqbspec; simpl; auto). congruence.
Qed.

Lemma chgVar_unassoc_else x y (h:renaming) :
  x<>y -> chgVar (list_unassoc x h) y = chgVar h y.
Proof.
  unfold chgVar.
  induction h as [|(a,b) h IH]; simpl in *; auto.
  repeat (case eqbspec; simpl; auto). congruence.
Qed.

Fixpoint Inv vs (h:renaming) :=
  match h with
  | [] => Logic.True
  | (v,z)::h => ~Names.In z vs /\
                (forall a b, In (a,b) h -> z<>a/\z<>b) /\
                Inv vs h
  end.

Lemma Inv_subset vs vs' h :
  Names.Subset vs vs' -> Inv vs' h -> Inv vs h.
Proof.
 induction h as [|(v,z) h IH]; simpl; intuition.
Qed.

Lemma Inv_add vs x (h:renaming) :
  Names.Subset vs (Names.add x vs) ->
  ~Names.In x (Subst.vars (map putVar h)) ->
  Inv vs h -> Inv (Names.add x vs) h.
Proof.
 induction h as [|(v,z) h IH]; simpl; auto.
 intros SU NI (NI' & H & IV).
 unfold Subst.vars in *. simpl in NI.
 split; [|split; auto with set].
 nameiff.
 intros [->|IN]; auto with set.
Qed.

Lemma Inv_notin vs (h:renaming) v z :
  Inv vs h -> list_assoc v h = Some z -> ~Names.In z vs.
Proof.
 induction h as [|(a,b) h IH]; simpl; try easy.
 intros (H & H' & IV).
 case eqbspec; auto.
 now intros <- [= ->].
Qed.

Lemma Inv_notin_unassoc vs (h:renaming) v z :
 Inv vs h -> list_assoc v h = Some z ->
 ~Names.In z (Subst.outvars (map putVar (list_unassoc v h))).
Proof.
 induction h as [|(a,b) h IH]; simpl; try easy.
 intros (H & H' & IV).
 rewrite eqb_sym.
 case eqbspec; simpl.
 - intros -> [= ->].
   rewrite <- unassoc_putVar.
   unfold Subst.outvars.
   rewrite unionmap_in.
   intros ((x,t) & IN & IN').
   rewrite unassoc_in, in_map_iff in IN'.
   destruct IN' as (((a,b) & [=] & IN'),NE).
   subst t a. cbn in *. apply H' in IN'. namedec.
 - intros NE EQ.
   specialize (IH IV EQ). unfold Subst.vars in IH.
   assert (IN: In (v,z) h).
   { now apply list_assoc_in2. }
   apply H' in IN.
   namedec.
Qed.

Lemma Inv_notin' vs (h:renaming) (v x:variable) :
  Inv vs h -> (Names.In x vs \/ list_assoc v h = Some x) ->
  ~Names.In x (Subst.outvars (map putVar (list_unassoc v h))).
Proof.
 intros IV.
 induction h as [|(a,b) h IH]; simpl in *; auto.
 - namedec.
 - destruct IV as (H & H' & IV).
   rewrite eqb_sym.
   case eqbspec; simpl.
   + intros -> [IN|[= ->]]. intuition.
     unfold Subst.outvars. rewrite unionmap_map_in.
     intros ((a,b) & IN & IN'). rewrite unassoc_in in IN'.
     simpl in IN. rewrite Names.singleton_spec in IN.
     destruct (H' a b); intuition.
   + intros NE [IN|SO];
      rewrite Names.union_spec, Names.singleton_spec.
     * intuition.
     * intros [<-|IN]; [|intuition].
       apply list_assoc_in2 in SO. now apply H' in SO.
Qed.

Lemma Inv_inj vs (h:renaming) x y z :
 Inv vs h ->
 list_assoc x h = Some z ->
 list_assoc y h = Some z ->
 x = y.
Proof.
 induction h as [|(a,b) h IH]; cbn; try easy.
 intros (H & H' & IV).
 repeat case eqbspec; auto.
 - congruence.
 - intros NE <- [= <-] EQ.
   apply list_assoc_in2 in EQ. now apply H' in EQ.
 - intros <- NE [= <-] EQ.
   symmetry in EQ. apply list_assoc_in2 in EQ. now apply H' in EQ.
Qed.

Lemma Inv_inj' vs (h:renaming) (x y:variable) :
  Inv vs h ->
  Names.In x vs -> Names.In y vs ->
  chgVar h x = chgVar h y -> x = y.
Proof.
 intros IV Hx Hy.
 unfold chgVar. rewrite !list_assoc_dft_alt.
 destruct (list_assoc x h) eqn:E, (list_assoc y h) eqn:E'.
 - intros <-. eapply Inv_inj; eauto.
 - intros ->. eapply Inv_notin in E; eauto. easy.
 - intros ->. eapply Inv_notin in E'; eauto. easy.
 - easy.
Qed.

Lemma Inv_unassoc vs (h:renaming) v :
 Inv vs h -> Inv vs (list_unassoc v h).
Proof.
 induction h as [|(a,b) h IH]; simpl; auto.
 intros (H & H' & IV).
 case eqbspec; simpl; auto.
 intros NE. do 2 (split; auto).
 intros a' b'. rewrite unassoc_in. firstorder.
Qed.

Lemma nam2mix_substs_rename_aux stk stk' v (h:renaming) f :
  let g := list_unassoc v h in
  In (chgVar h v) stk \/ ~Names.In (chgVar h v) (freevars f) ->
  In v stk ->
  nam2mix (stk ++ map (chgVar h) stk') f =
  nam2mix (stk ++ map (chgVar g) stk') f.
Proof.
 revert stk.
 induction stk' as [|x stk' IH]; simpl; intros stk OR IN; auto.
 case (eqbspec x v).
 - intros ->.
   rewrite chgVar_unassoc_at.
   rewrite nam2mix_shadowstack' with (y:=v) by intuition.
   rewrite cons_app, <- app_ass, IH, app_ass; simpl; auto.
   rewrite in_app_iff; intuition.
   rewrite in_app_iff; right; simpl; auto.
 - intros NE.
   rewrite chgVar_unassoc_else by auto.
   rewrite cons_app, <- app_ass, IH, app_ass; simpl; auto.
   rewrite in_app_iff; intuition.
   rewrite in_app_iff; intuition.
Qed.

Lemma nam2mix_term_chgVar_some stk (h:renaming) (v z:variable) :
  Inv (Names.union (Names.of_list stk) (Names.singleton v)) h ->
  list_assoc v h = Some z -> In v stk ->
  nam2mix_term (map (chgVar h) stk) (Var z) =
  nam2mix_term stk (Var v).
Proof.
 intros IV EQ IN. simpl.
 induction stk; simpl in *; try easy.
 case (eqbspec v a).
 - intros <-. now rewrite (chgVar_some h v z), eqb_refl.
 - intros NE.
   case eqbspec.
   + intros EQ'. destruct NE.
     rewrite <- (chgVar_some _ _ _ EQ) in EQ'.
     eapply Inv_inj'; eauto with set.
   + intros NE'.
     destruct IN; [subst;easy|].
     assert (H' : Inv (Names.union (Names.of_list stk) (Names.singleton v)) h).
     { eapply Inv_subset; eauto. namedec. }
     specialize (IHstk H' H).
     destruct (list_index z (map (chgVar h) stk)),
              (list_index v stk); simpl; try easy.
     injection IHstk as ->; auto.
Qed.

Lemma nam2mix_term_chgVar_none stk (h:renaming) (v:variable) :
  Inv (Names.union (Names.of_list stk) (Names.singleton v)) h ->
  list_assoc v h = None ->
  nam2mix_term (map (chgVar h) stk) (Var v) =
  nam2mix_term stk (Var v).
Proof.
 intros IV EQ. simpl.
 induction stk; simpl in *; auto.
 case (eqbspec v a).
 - intros <-. now rewrite chgVar_none, eqb_refl.
 - intros NE.
   case eqbspec.
   + intros EQ'. destruct NE.
     rewrite <- (chgVar_none _ _ EQ) in EQ'.
     eapply Inv_inj'; eauto with set.
   + intros NE'.
     assert (H : Inv (Names.union (Names.of_list stk) (Names.singleton v)) h).
     { eapply Inv_subset; eauto. namedec. }
     specialize (IHstk H).
     destruct (list_index v (map (chgVar h) stk)),
              (list_index v stk); simpl; try easy.
     injection IHstk as ->; auto.
Qed.

Lemma nam2mix_term_substs_rename stk (h:renaming) t :
 Inv (Names.union (Names.of_list stk) (Term.vars t)) h ->
 (forall a b, In (a,b) h -> In a stk) ->
 nam2mix_term (map (chgVar h) stk) (Term.substs (map putVar h) t) =
 nam2mix_term stk t.
Proof.
 revert t.
 fix IH 1. destruct t as [v|f l]; cbn; intros IV SU.
 - clear IH. rewrite list_assoc_dft_alt.
   rewrite assoc_putVar.
   destruct (list_assoc v h) as [z|] eqn:E; simpl.
   + apply nam2mix_term_chgVar_some; auto.
     apply list_assoc_in2 in E. eapply SU; eauto.
   + apply nam2mix_term_chgVar_none; auto.
 - f_equal. clear f.
   revert l IV.
   fix IH' 1. destruct l as [|t l]; cbn; intros IV; auto.
   f_equal.
   apply IH; auto. eapply Inv_subset; eauto. namedec.
   apply IH'; auto. eapply Inv_subset; eauto. namedec.
Qed.

Lemma nam2mix_substs_rename stk (h:renaming) f:
 Inv (Names.union (Names.of_list stk) (allvars f)) h ->
 (forall a b, In (a,b) h -> In a stk) ->
 nam2mix (map (chgVar h) stk) (substs (map putVar h) f) =
 nam2mix stk f.
Proof.
 revert stk h.
 induction f; intros stk h IV SU; cbn in *; auto.
 - f_equal.
   injection (nam2mix_term_substs_rename stk h (Fun "" l)); auto.
 - f_equal; auto.
 - f_equal. apply IHf1; auto. eapply Inv_subset; eauto. namedec.
   apply IHf2; auto. eapply Inv_subset; eauto. namedec.
 - set (g' := list_unassoc v (map putVar h)).
   set (g := list_unassoc v h).
   assert (~Names.In v (Subst.outvars g')).
   { unfold g'. rewrite unassoc_putVar.
     eapply Inv_notin'; eauto. left; namedec. }
   rewrite mem_false by trivial; simpl.
   f_equal.
   rewrite <- IHf with (h:=g).
   2:{ apply Inv_unassoc.
       eapply Inv_subset; eauto. simpl; namedec. }
   2:{ intros a b. unfold g.
       rewrite unassoc_in. intros (IN,_); simpl; eauto. }
   cbn.
   rewrite chgVar_none.
   2:{ apply list_assoc_notin.
       (* sous-lemme ? *)
       unfold g. rewrite in_map_iff.
       intros ((a,b) & <- & IN); simpl in IN.
       rewrite unassoc_in in IN. easy. }
   unfold g at 2. rewrite <- unassoc_putVar. fold g'.
   apply (nam2mix_substs_rename_aux [v]); simpl; auto.
   rewrite substs_freevars, freevars_allvars.
   destruct (list_assoc v h) as [z|] eqn:Hz.
   + right.
     rewrite (chgVar_some _ _ _ Hz).
     assert (IV2 := Inv_notin _ _ _ _ IV Hz).
     assert (IV3 := Inv_notin' _ _ _ _ IV (or_intror _ Hz)).
     rewrite <- unassoc_putVar in IV3. fold g' in IV3.
     namedec.
   + left; left. symmetry. now apply chgVar_none.
Qed.

Lemma nam2mix_term_substs stk h x u t:
 Inv (Names.unions [Names.of_list stk;
                   Term.vars t;
                   Names.add x (Term.vars u)]) h ->
 (forall a b , In (a,b) h -> In a stk) ->
 ~In x stk ->
 (forall v, In v stk -> ~Names.In (chgVar h v) (Term.vars u)) ->
 nam2mix_term (map (chgVar h) stk)
              (Term.substs (map putVar h ++ [(x,u)]) t) =
 Mix.fsubst x (nam2mix_term [] u) (nam2mix_term stk t).
Proof.
 intros IV SU NI CL.
 revert t IV.
 fix IH 1. destruct t as [v|f l]; cbn; intros IV.
 - clear IH. rewrite list_assoc_dft_alt.
   destruct (In_dec string_dec v (map fst h)) as [IN|NI'].
   + assert (In v (map fst (map putVar h))).
     { rewrite map_map. rewrite in_map_iff in *.
       destruct IN as ((a,b) & EQ & IN). now exists (a,b). }
     rewrite list_assoc_app_l by auto.
     rewrite assoc_putVar.
     rewrite <- list_assoc_in in IN.
     destruct (list_assoc v h) as [z|] eqn:E; simpl; try easy.
     assert (IN' : In v stk).
     { now apply list_assoc_in2, SU in E. }
     generalize (nam2mix_term_chgVar_some stk h v z).
     simpl.
     intros ->; auto; [ | eapply Inv_subset; eauto; namedec].
     rewrite <- list_index_in in IN'.
     now destruct (list_index v stk).
   + assert (~In v (map fst (map putVar h))).
     { rewrite map_map. rewrite in_map_iff in *.
       intros ((a,b) & EQ & IN). apply NI'. now exists (a,b). }
     rewrite list_assoc_app_r by auto.
     simpl. case eqbspec; simpl.
     * intros <-. apply list_index_notin in NI.
       change Names.elt with variable in *.
       rewrite NI. cbn. unfold Mix.varsubst. rewrite eqb_refl.
       apply nam2mix_term_nostack.
       intros y. rewrite in_map_iff. intros (x & <- & Hx); auto.
     * intros NE.
       generalize (nam2mix_term_chgVar_none stk h v).
       simpl.
       intros ->; auto.
       2:{ eapply Inv_subset; eauto. namedec. }
       2:{ now apply list_assoc_notin. }
       unfold Mix.fsubst.
       rewrite term_vmap_id; auto.
       intros y. unfold Mix.varsubst.
       destruct (list_index v stk); cbn; nameiff; intuition.
 - f_equal. clear f.
   revert l IV.
   fix IH' 1. destruct l as [|t l]; cbn; intros IV; auto.
   f_equal.
   apply IH; auto. eapply Inv_subset; eauto. simpl. namedec.
   apply IH'; auto. eapply Inv_subset; eauto. simpl. namedec.
Qed.

Ltac namedec00 := clear; nameiff; intuition auto.

Lemma stack_notin_term
  (v z z' : variable)(t : term)
  (stk : list variable)(h g : renaming) g' :
  g = list_unassoc v h ->
  g' = map putVar g ->
  ~Names.In z (Term.vars t) ->
  ~Names.In z' (Names.union (Subst.vars g') (Names.add v (Term.vars t))) ->
  let stk' := map (fun a : variable => if a =? z then z' else a) stk in
  (forall v : variable,
    In v stk -> ~ Names.In (chgVar h v) (Term.vars t)) ->
  forall v' : variable,
    In v' (v :: stk') ->
    ~ Names.In (chgVar ((v, z) :: g) v') (Term.vars t).
Proof.
 intros Hg Hg' Hz Hz' stk' CL v0 [<-|IN].
 - unfold chgVar. simpl. rewrite eqb_refl. namedec0.
 - unfold stk' in IN. rewrite in_map_iff in IN.
   destruct IN as (y & EQ & IN). revert EQ.
   case eqbspec.
   + intros -> <-.
     rewrite chgVar_none; [namedec0|]; simpl.
     case eqbspec; [intros <-;namedec0|].
     intros _.
     assert (NO : list_assoc z' g' = None).
     { apply list_assoc_notin.
       rewrite <- invars_in. unfold Subst.vars in Hz'. namedec0. }
     revert NO.
     rewrite Hg'. rewrite assoc_putVar.
     now destruct (list_assoc z' g).
   + intros NE' ->. unfold chgVar. simpl.
     case eqbspec; [namedec0|].
     intros NE''.
     fold (chgVar g v0). rewrite Hg.
     rewrite chgVar_unassoc_else by auto.
     now apply CL.
Qed.

Lemma Inv_Inv
  (x v z z' : variable)(t : term)(f : formula)
  (stk : list variable)(h g : renaming) g' :
  let vars := Names.union (Names.add v (allvars f))
                         (Names.add x (Term.vars t)) in
  Inv (Names.union (Names.of_list stk) vars) h ->
  g = list_unassoc v h ->
  g' = map putVar g ->
  ~Names.In z (Names.union (Subst.vars g') vars) ->
  ~Names.In z' (Names.union (Subst.vars g') vars) ->
  ~Names.In z' (Names.of_list stk) ->
  let stk' := map (fun a : variable => if a =? z then z' else a) stk in
  Inv
    (Names.union (Names.of_list (v :: stk'))
       (Names.union (allvars f)
          (Names.union (Names.add x (Term.vars t)) Names.empty)))
    ((v, z) :: g).
Proof.
 intros vars IV Hg Hg' Hz Hz' Hz'' stk'.
 simpl. split; [|split].
 - assert (NI' : ~Names.In z (Names.of_list stk')).
   { rewrite names_of_list_in.
     unfold stk'. rewrite in_map_iff.
     intros (z0 & EQ & IN). rewrite <- names_of_list_in in IN.
     revert EQ. case eqbspec; [|easy].
     intros -> <-; exact (Hz'' IN). }
   revert Hz NI'. unfold vars. namedec00.
 - intros a b Hab.
   assert (In (a,Var b) g').
   { rewrite Hg'. rewrite in_map_iff. now exists (a,b). }
   assert (Names.In a (Subst.invars g')).
   { rewrite invars_in. rewrite in_map_iff. now exists (a,Var b). }
   assert (Names.In b (Subst.outvars g')).
   { unfold Subst.outvars. rewrite unionmap_in. exists (a,Var b).
     simpl. auto with set. }
   unfold vars, Subst.vars in Hz.
   split; namedec.
 - apply Inv_unassoc with (v:=v) in IV. rewrite <- Hg in IV.
   apply Inv_add with (x:=z') in IV;
     [ | namedec| rewrite <- Hg'; revert Hz'; namedec00].
   eapply Inv_subset; eauto.
   assert (Names.Subset (Names.of_list stk')
                        (Names.add z' (Names.of_list stk))).
   { unfold stk'. clear. intros x.
     rewrite Names.add_spec, !names_of_list_in, in_map_iff.
     intros (x0 & EQ & IN). revert EQ.
     case eqbspec; intros; subst; auto. }
   rewrite H. intro. unfold vars. namedec00.
Qed.

Lemma nam2mix_substs_aux1
  (x v z z' : variable)(t : term)(f : formula)
  (stk : list variable)(h g : renaming) g' :
  let vars := Names.union (Names.add v (allvars f))
                         (Names.add x (Term.vars t)) in
  Inv vars h ->
  g = list_unassoc v h ->
  g' = map putVar g ->
  ~Names.In z (Names.union (Subst.vars g') vars) ->
  ~Names.In z' (Names.union (Subst.vars g') vars) ->
  ~Names.In z' (Names.of_list stk) ->
  (In v stk -> chgVar h v <> v) ->
  let stk' := map (fun a : variable => if a =? z then z' else a) stk in
  nam2mix (z :: map (chgVar h) stk)
    (substs ((v, Var z) :: g' ++ [(x, t)]) f) =
  nam2mix (map (chgVar ((v, z) :: g)) (v :: stk'))
    (substs (map putVar ((v, z) :: g) ++ [(x, t)]) f).
Proof.
 intros vars IV Hg Hg' Hz Hz' Hz'' CL stk'.
 unfold Subst.vars in *; simpl in *.
 rewrite chgVar_some with (z:=z) by (simpl; now rewrite eqb_refl).
 rewrite <-Hg'.
 set (f' := substs _ f).
 unfold stk'. clear stk'. rewrite map_map.
 apply nam2mix_indep.
 intros y Hy.
 simpl.
 case eqbspec; auto.
 intros Hyz. f_equal.
 unfold f' in Hy.
 rewrite substs_freevars in Hy. simpl in Hy.
 rewrite invars_app, outvars_app in Hy.
 simpl in Hy.
 rewrite freevars_allvars in Hy.
 assert (Hyz' : y <> z').
 { intros ->. revert Hz' Hy Hyz. unfold vars. namedec00. }
 assert (H : ~Names.In z (Subst.invars g')) by namedec0.
 assert (Hzv : z<>v) by (unfold vars in Hz; namedec0).
 rewrite Hg',Hg, <- unassoc_putVar in H.
 rewrite invars_unassoc in H.
 assert (Hzh : ~Names.In z (Subst.invars (map putVar h))).
 { revert H Hzv. namedec00. }
 clear H.
 rewrite invars_in, fst_putVar in Hzh.
 assert (Hhz : chgVar h z = z).
 { apply chgVar_none. now apply list_assoc_notin. }
 assert (Hgz' : chgVar ((v, z) :: g) z' = z').
 { apply chgVar_none. simpl.
   case eqbspec; [unfold vars in Hz';namedec0|].
   intros NE2. apply list_assoc_notin.
   rewrite <- fst_putVar, <- Hg'.
   rewrite <- invars_in. namedec0. }
 assert (NI := Inv_notin _ _ v (chgVar h v) IV).
 assert (NI' := Inv_notin_unassoc _ _ v (chgVar h v) IV).
 clear IV.
 revert stk CL Hz''.
 induction stk as [|s stk IH]; simpl; auto.
 intros CL Hz''.
 rewrite Names.add_spec in Hz''.
 apply Decidable.not_or in Hz''.
 destruct Hz'' as (Hsz',Hz'').
 case (eqbspec s z).
 - intros ->.
   rewrite Hhz, Hgz'.
   do 2 (case eqbspec; easy || intros _). f_equal; auto.
 - intros Hsz.
   case (eqbspec s v).
   + intros ->.
     set (hv := chgVar h v) in *.
     unfold chgVar at 2. simpl. rewrite eqb_refl.
     case (eqbspec y z); easy || intros _.
     case eqbspec; [|intros;f_equal;auto].
     intros ->. exfalso.
     clear IH Hz' Hyz' Hgz'.
     assert (list_assoc v h = Some hv).
     { generalize (CL (or_introl _ (eq_refl))).
       unfold hv, chgVar. rewrite list_assoc_dft_alt.
       destruct list_assoc; intuition. }
     generalize (NI H) (NI' H) Hy Hyz.
     rewrite <- Hg, <- Hg'. unfold vars. namedec00.
   + intros NE.
     replace (chgVar ((v, z)::g) s) with (chgVar h s).
     { case eqbspec; intros; f_equal; auto. }
     { symmetry. unfold chgVar at 1. simpl.
       case eqbspec; easy || intros _.
       fold (chgVar g s). rewrite Hg.
       apply chgVar_unassoc_else; auto. }
Qed.

Lemma form_substs_aux2
  (x v : variable)(t : term)(f : formula)
  (stk : list variable)(h g : renaming) g' :
  let vars := Names.union (Names.add v (allvars f))
                         (Names.add x (Term.vars t)) in
  Inv vars h ->
  g = list_unassoc v h ->
  g' = map putVar g ->
  let f' := substs (g' ++ [(x,t)]) f in
  nam2mix (v :: map (chgVar h) stk) f' =
  nam2mix (map (chgVar g) (v::stk)) f'.
Proof.
 intros vars IV Hg Hg' f'.
 simpl.
 rewrite Hg at 1. rewrite chgVar_unassoc_at.
 apply nam2mix_indep.
 intros y Hy.
 simpl. case eqbspec; auto.
 intros NE. f_equal.
 assert (NE' : y <> chgVar h v).
 { unfold chgVar. rewrite list_assoc_dft_alt.
   destruct (list_assoc v h) eqn:E; auto.
   intros <-.
   revert Hy.
   unfold f'.
   rewrite substs_freevars, freevars_allvars.
   rewrite invars_app, outvars_app.
   generalize (Inv_notin _ _ _ _ IV E). simpl.
   generalize (Inv_notin_unassoc _ _ _ _ IV E).
   rewrite <- Hg, <- Hg'.
   revert NE. unfold vars. namedec00. }
 rewrite Hg.
 clear - NE NE'.
 induction stk; simpl; auto.
 case (eqbspec a v).
 - intros ->.
   rewrite chgVar_unassoc_at.
   do 2 (case eqbspec; easy || intros _).
   now f_equal.
 - intros NE2.
   rewrite chgVar_unassoc_else; auto.
   case eqbspec; auto. intros _. now f_equal.
Qed.

Lemma nam2mix_substs (stk:list variable) h (x:variable) t f:
 Inv (Names.unions [Names.of_list stk;
                   allvars f;
                   Names.add x (Term.vars t)]) h ->
 (forall a b , In (a,b) h -> In a stk) ->
 ~In x stk ->
 (forall v, In v stk -> ~Names.In (chgVar h v) (Term.vars t)) ->
 nam2mix (map (chgVar h) stk)
         (substs (map putVar h ++ [(x,t)]) f) =
 Mix.fsubst x (nam2mix_term [] t) (nam2mix stk f).
Proof.
 revert stk h.
 induction f; intros stk h IV SU NI CL; cbn in *; auto.
 - f_equal.
   injection (nam2mix_term_substs stk h x t (Fun "" l)); auto.
 - f_equal; auto.
 - f_equal. apply IHf1; auto. eapply Inv_subset; eauto. namedec.
   apply IHf2; auto. eapply Inv_subset; eauto. namedec.
 - rewrite !unassoc_app. cbn.
   set (g' := list_unassoc v (map putVar h)).
   set (g := list_unassoc v h).
   assert (Hg : g' = map putVar g).
   { unfold g', g. apply unassoc_putVar. }
   case eqbspec; cbn.
   + (* x = v *)
     intros <-.
     rewrite app_nil_r.
     unfold Mix.fsubst.
     rewrite form_vmap_id.
     2:{ intros v. unfold Mix.varsubst. case eqbspec; auto.
         intros <-. rewrite nam2mix_fvars. simpl. namedec. }
     change
       (nam2mix (map (chgVar h) stk)
                (substs (map putVar h) (Quant q x f))
        = nam2mix stk (Quant q x f)).
     apply nam2mix_substs_rename; auto.
     eapply Inv_subset; eauto. cbn. namedec.
   + (* x <> v *)
     intros NE.
     destruct (Names.mem _ _) eqn:MM; cbn; f_equal;
     rewrite outvars_app in MM; simpl in MM.
     * (* Capture of variable v, which occurs in t *)
       assert (IN : Names.In v (Term.vars t)).
       { revert MM.
         rewrite Names.mem_spec.
         rewrite Hg. unfold g.
         generalize (Inv_notin' _ _ v v IV). namedec00. }
       clear MM.
       setfresh vars z Hz.
       destruct (exist_fresh (Names.union vars (Names.of_list stk)))
        as (z',Hz').
       set (stk' := map (fun a => if a =? z then z' else a) stk).
       rewrite Names.union_spec in Hz'. apply Decidable.not_or in Hz'.
       destruct Hz' as (Hz',Hz'2).
       unfold vars in Hz,Hz'. clear vars.
       rewrite outvars_app, invars_app in Hz,Hz'.
       simpl in Hz, Hz'.
       assert (CL' : In v stk -> chgVar h v <> v).
       { intros IN' EQ. apply (CL v IN'). now rewrite EQ. }
       erewrite nam2mix_substs_aux1; eauto; fold stk'; fold g.
       2:{clear -IV. eapply Inv_subset; eauto. simpl. intro. namedec00. }
       2:{revert Hz. unfold Subst.vars; simpl. namedec00. }
       2:{revert Hz'. unfold Subst.vars; simpl. namedec00. }
       rewrite IHf; clear IHf.
       { f_equal.
         apply (nam2mix_shadowstack_map [v] stk);
          right; rewrite freevars_allvars; namedec0. }
       { eapply Inv_Inv with (h:=h); auto.
         eapply Inv_subset; eauto. intro. namedec00.
         revert Hz. rewrite <- Hg. unfold Subst.vars. namedec00.
         revert Hz'. rewrite <- Hg. unfold Subst.vars. namedec00. }
       { clear CL CL' IN.
         intros a b [[= -> ->]|IN]; simpl; auto.
         assert (Names.In a (Subst.invars g')).
         { unfold g'.
           rewrite invars_in. rewrite unassoc_putVar. fold g.
           rewrite map_map. apply in_map_iff. now exists (a,b). }
         assert (a <> z) by (intros ->; namedec0).
         unfold g in IN. rewrite unassoc_in in IN. right.
         unfold stk'. rewrite in_map_iff. exists a.
         case eqbspec; try easy. split; auto. eapply SU. apply IN. }
       { clear CL CL' IN.
         intros [->|IN]; [easy|]. unfold stk' in IN. rewrite in_map_iff in IN.
         destruct IN as (x0 & EQ & IN). revert EQ.
         case eqbspec; intros; subst; auto. namedec0. }
       { apply stack_notin_term with (h:=h)(g':=g'); auto.
         revert Hz. namedec00.
         revert Hz'. unfold Subst.vars. namedec00. }
     * (* No capture of variable v *)
       assert (~Names.In v (Term.vars t)).
       { simpl in MM. rewrite <-not_true_iff_false, Names.mem_spec in MM.
         namedec0. }
       clear MM.
       rewrite form_substs_aux2 with (g:=g); auto.
       2:{clear -IV. eapply Inv_subset; eauto. simpl. intro. namedec00. }
       rewrite Hg.
       apply IHf; clear IHf.
       { apply Inv_unassoc.
         eapply Inv_subset; eauto. simpl. namedec. }
       { intros a b. unfold g.
         rewrite unassoc_in. intros (IN,_); simpl; eauto. }
       { simpl. intros [->|IN]; intuition. }
       { intros y.
         case (eqbspec y v).
         - intros -> _. unfold g. now rewrite chgVar_unassoc_at.
         - intros NE' [->|IN]; [easy|].
           unfold g. rewrite chgVar_unassoc_else; auto. }
Qed.

Lemma nam2mix_substs_alt x t f:
 nam2mix [] (substs [(x,t)] f) = nam2mix [] (Alt.subst x t f).
Proof.
 rewrite nam2mix0_altsubst_fsubst.
 apply (nam2mix_substs [] []); simpl; intuition.
Qed.

(** And at last : *)

Lemma nam2mix_subst_alt x t f:
 nam2mix [] (subst x t f) = nam2mix [] (Alt.subst x t f).
Proof.
 apply nam2mix_substs_alt.
Qed.

Lemma subst_alt x t f:
 AlphaEq (subst x t f) (Alt.subst x t f).
Proof.
 apply nam2mix_canonical'.
 apply nam2mix_substs_alt.
Qed.

Instance : Proper (eq ==> eq ==> AlphaEq ==> AlphaEq) subst.
Proof.
 intros x x' <- t t' <- f f' Hf.
 now rewrite !subst_alt, Hf.
Qed.

(** Swapping substitutions.
    This technical lemma is described in Alexandre's course notes.
    See also [Alpha.partialsubst_partialsubst]. In fact, we won't
    reuse it afterwards. *)

Lemma altsubst_altsubst x y u v f :
 x<>y -> ~Names.In x (Term.vars v) ->
 AlphaEq (Alt.subst y v (Alt.subst x u f))
         (Alt.subst x (Term.subst y v u) (Alt.subst y v f)).
Proof.
 intros NE NI.
 apply nam2mix_canonical'.
 rewrite !nam2mix0_altsubst_fsubst.
 rewrite nam2mix_term_subst by auto.
 apply form_fsubst_fsubst; auto.
 rewrite nam2mix_tvars. cbn. namedec.
Qed.

Lemma subst_subst x y u v f :
 x<>y -> ~Names.In x (Term.vars v) ->
 AlphaEq (subst y v (subst x u f))
         (subst x (Term.subst y v u) (subst y v f)).
Proof.
 intros.
 rewrite !subst_alt.
 apply altsubst_altsubst; auto.
Qed.

(** The general equation defining [subst] on a quantified formula,
    via renaming. *)

Lemma altsubst_QuGen (x z:variable) t q v f :
 x<>v ->
 ~Names.In z (Names.add x (Names.union (freevars f) (Term.vars t))) ->
 AlphaEq (Alt.subst x t (Quant q v f))
         (Quant q z (Alt.subst x t (Alt.subst v (Var z) f))).
Proof.
 intros NE NI.
 apply nam2mix_canonical'. cbn - [Alt.subst].
 rewrite !nam2mix0_altsubst_fsubst. cbn - [Alt.subst].
 f_equal.
 rewrite nam2mix_altsubst_fsubst by (simpl; namedec).
 f_equal.
 apply nam2mix_rename_iff3; auto. namedec.
Qed.

Lemma subst_QuGen (x z:variable) t q v f :
 x<>v ->
 ~Names.In z (Names.add x (Names.union (freevars f) (Term.vars t))) ->
 AlphaEq (subst x t (Quant q v f))
         (Quant q z (subst x t (subst v (Var z) f))).
Proof.
 intros.
 rewrite subst_alt.
 rewrite altsubst_QuGen with (z:=z); auto.
 apply AEqQu_nosubst.
 now rewrite !subst_alt.
Qed.
