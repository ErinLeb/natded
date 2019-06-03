
(** * Conversion between Named formulas and Locally Nameless formulas *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Nam Alpha Subst Meta.
Import ListNotations.
Import Nam.Form.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Implicit Types x y z v : variable.
Implicit Types stack stk : list variable.

(** From named to locally nameless *)

Fixpoint nam2mix_term stack t :=
  match t with
  | Var v =>
    match list_index v stack with
    | None => Mix.FVar v
    | Some n => Mix.BVar n
    end
  | Fun f args => Mix.Fun f (List.map (nam2mix_term stack) args)
  end.

Fixpoint nam2mix stack f :=
  match f with
  | True => Mix.True
  | False => Mix.False
  | Not f => Mix.Not (nam2mix stack f)
  | Op o f1 f2 => Mix.Op o (nam2mix stack f1) (nam2mix stack f2)
  | Pred p args => Mix.Pred p (List.map (nam2mix_term stack) args)
  | Quant q v f => Mix.Quant q (nam2mix (v::stack) f)
  end.

(** Opposite direction *)

Fixpoint mix2nam_term stack t :=
  match t with
  | Mix.FVar v => Var v
  | Mix.BVar n => Var (List.nth n stack EmptyString)
  | Mix.Fun f args => Fun f (List.map (mix2nam_term stack) args)
  end.

Fixpoint mix2nam stack f :=
  match f with
  | Mix.True => True
  | Mix.False => False
  | Mix.Not f => Not (mix2nam stack f)
  | Mix.Op o f1 f2 => Op o (mix2nam stack f1) (mix2nam stack f2)
  | Mix.Pred p args => Pred p (List.map (mix2nam_term stack) args)
  | Mix.Quant q f =>
    let v := fresh (Names.union (Names.of_list stack) (Mix.fvars f)) in
    Nam.Quant q v (mix2nam (v::stack) f)
  end.

(** Basic properties of [nam2mix] : level, free variables, etc *)

Lemma nam2mix_term_level stack t :
  Mix.level (nam2mix_term stack t) <= List.length stack.
Proof.
 revert t.
 fix IH 1. destruct t; cbn.
 - destruct (list_index v stack) eqn:E; cbn; auto with arith.
   apply list_index_lt_length in E. omega.
 - clear f. revert l.
   fix IH' 1. destruct l as [|t l]; cbn; auto with arith.
   apply Nat.max_lub; auto.
Qed.

Lemma nam2mix_level stack f :
  Mix.level (nam2mix stack f) <= List.length stack.
Proof.
 revert stack.
 induction f; intros stack; cbn; auto with arith.
 - apply (nam2mix_term_level stack (Nam.Fun "" l)).
 - apply Nat.max_lub; auto.
 - specialize (IHf (v::stack)). cbn in *. omega.
Qed.

Lemma nam2mix_term_bclosed t :
 Mix.BClosed (nam2mix_term [] t).
Proof.
 unfold Mix.BClosed.
 generalize (nam2mix_term_level [] t); simpl; omega.
Qed.

Lemma nam2mix_bclosed f :
  Mix.BClosed (nam2mix [] f).
Proof.
 unfold Mix.BClosed.
 generalize (nam2mix_level [] f). simpl. auto with *.
Qed.

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

Lemma nam2mix_term_indep stk stk' t :
 (forall v, Names.In v (Term.vars t) ->
            list_index v stk = list_index v stk') ->
 nam2mix_term stk t = nam2mix_term stk' t.
Proof.
 induction t as [v|f l IH] using term_ind'; cbn; intros Ht.
 - rewrite Ht; auto with set.
 - f_equal. clear f. apply map_ext_iff. intros a Ha.
   apply IH; auto. intros v Hv. apply Ht.
   rewrite unionmap_in. now exists a.
Qed.

Lemma nam2mix_indep stk stk' f :
 (forall v, Names.In v (freevars f) ->
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

(** [nam2mix] and [partialsubst] *)

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
     apply IHf; simpl; intuition; subst; eauto.
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

Lemma nam2mix0_partialsubst x u f :
 IsSimple x u f ->
 nam2mix [] (partialsubst x u f) =
  Mix.fsubst x (nam2mix_term [] u) (nam2mix [] f).
Proof.
 apply nam2mix_partialsubst; auto.
Qed.

Lemma nam2mix_rename stk stk' x z f :
 ~In x stk ->
 ~In z stk ->
 ~Names.In z (allvars f) ->
 nam2mix (stk++z::stk') (rename x z f) =
 nam2mix (stk++x::stk') f.
Proof.
 revert stk.
 induction f; cbn; intros stk Hx Hz IS; f_equal; auto.
 - injection (nam2mix_term_subst' stk stk' x z (Fun "" l)); easy.
 - intuition.
 - intuition.
 - case eqbspec; cbn.
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

Lemma term_subst_bsubst stk x u t :
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

Lemma rename_bsubst0 x z f :
 ~Names.In z (allvars f) ->
 nam2mix [] (rename x z f) =
  Mix.bsubst 0 (Mix.FVar z) (nam2mix [x] f).
Proof.
 intros.
 rewrite rename_partialsubst by auto.
 apply (partialsubst_bsubst0 x (Var z)); auto.
Qed.

Lemma nam2mix_rename_iff z v v' f f' :
  ~ Names.In z (Names.union (allvars f) (allvars f')) ->
  nam2mix [] (rename v z f) = nam2mix [] (rename v' z f')
  <->
  nam2mix [v] f = nam2mix [v'] f'.
Proof.
 intros Hz.
 rewrite 2 rename_bsubst0 by namedec.
 split.
 - intros H. apply bsubst_fresh_inj in H; auto.
   rewrite !nam2mix_fvars. cbn. rewrite !freevars_allvars. namedec.
 - now intros ->.
Qed.

Lemma nam2mix_term_inj t t' :
 nam2mix_term [] t = nam2mix_term [] t' <-> t = t'.
Proof.
 split; [ | intros <-; auto ].
 revert t t'.
 fix IH 1. destruct t, t'; cbn; try easy.
 - now intros [= <-].
 - intros [= <- EQ]. f_equal.
   revert l l0 EQ.
   fix IH' 1. destruct l, l0; cbn; try easy.
   intros [= EQ EQ']. f_equal; auto.
Qed.

Lemma nam2mix_canonical f f' :
 nam2mix [] f = nam2mix [] f' <-> AlphaEq f f'.
Proof.
 split.
 - set (h := S (Nat.max (height f) (height f'))).
   assert (LT : height f < h) by (unfold h; auto with *).
   assert (LT' : height f' < h) by (unfold h; auto with *).
   clearbody h. revert f f' LT LT'.
   induction h as [|h IH]; [inversion 1|].
   destruct f, f'; simpl; intros LT LT'; simpl_height; try easy.
   + intros [= <- E].
     destruct (nam2mix_term_inj (Fun "" l) (Fun "" l0)) as (H,_).
     simpl in H. injection H as <-; auto. now f_equal.
   + intros [= E]; auto.
   + intros [= <- E1 E2]; auto.
   + intros [= <- E].
     destruct (exist_fresh (Names.union (allvars f) (allvars f'))) as (z,Hz).
     apply AEqQu with z; auto.
     apply IH; try rewrite rename_height; auto.
     apply nam2mix_rename_iff; auto.
 - induction 1; cbn; f_equal; auto.
   apply (nam2mix_rename_iff z); auto.
Qed.

(** We've just seen that [nam2mix []] maps alpha-equivalent formulas
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
 rewrite (nam2mix_rename [] stk v z) by (auto; namedec).
 rewrite (nam2mix_rename [] stk v' z) by (auto; namedec).
 auto.
Qed.

(** SUBST *)

Lemma nam2mix_Subst_fsubst stk x u f f' :
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

Lemma nam2mix_subst_fsubst stk x u f :
 ~In x stk ->
 (forall v, In v stk -> ~Names.In v (Term.vars u)) ->
 nam2mix stk (subst x u f) =
 Mix.fsubst x (nam2mix_term [] u) (nam2mix stk f).
Proof.
 intros.
 apply nam2mix_Subst_fsubst; auto.
 apply Subst_subst.
Qed.

Lemma nam2mix0_subst_fsubst x u f :
 nam2mix [] (subst x u f) =
  Mix.fsubst x (nam2mix_term [] u) (nam2mix [] f).
Proof.
 apply nam2mix_subst_fsubst; auto.
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

Lemma nam2mix_subst_bsubst stk x u f :
 ~In x stk ->
 (forall v, In v stk -> ~Names.In v (Term.vars u)) ->
 nam2mix stk (subst x u f) =
  Mix.bsubst (length stk) (nam2mix_term [] u)
             (nam2mix (stk++[x]) f).
Proof.
 intros.
 apply nam2mix_Subst_bsubst; auto.
 apply Subst_subst.
Qed.

Lemma nam2mix_subst_bsubst0 x u f :
 nam2mix [] (subst x u f) =
  Mix.bsubst 0 (nam2mix_term [] u) (nam2mix [x] f).
Proof.
 apply nam2mix_subst_bsubst; auto.
Qed.

Lemma nam2mix_rename_iff2 z v v' f f' :
  ~ Names.In z (Names.union (freevars f) (freevars f')) ->
  nam2mix [] (subst v (Var z) f) =
  nam2mix [] (subst v' (Var z) f')
  <->
  nam2mix [v] f = nam2mix [v'] f'.
Proof.
 intros Hz.
 rewrite 2 nam2mix_subst_bsubst0. cbn.
 split.
 - intros H. apply bsubst_fresh_inj in H; auto.
   rewrite !nam2mix_fvars. cbn. namedec.
 - now intros ->.
Qed.

Lemma nam2mix_subst_nop x f :
  nam2mix [] (subst x (Var x) f) = nam2mix [] f.
Proof.
 rewrite nam2mix0_subst_fsubst. simpl.
 unfold Mix.fsubst.
 apply form_vmap_id.
 intros y Hy. unfold Mix.varsubst.
 case eqbspec; intros; subst; auto.
Qed.

Lemma subst_nop x f :
  AlphaEq (subst x (Var x) f) f.
Proof.
 apply nam2mix_canonical.
 apply nam2mix_subst_nop.
Qed.

Lemma nam2mix_rename_iff3 v x f f' :
  ~ Names.In x (Names.remove v (freevars f)) ->
  nam2mix [] (subst v (Var x) f) = nam2mix [] f'
  <->
  nam2mix [v] f = nam2mix [x] f'.
Proof.
 intros Hx.
 rewrite nam2mix_subst_bsubst0. cbn.
 split.
 - rewrite <- (nam2mix_subst_nop x f').
   rewrite nam2mix_subst_bsubst0. cbn.
   apply bsubst_fresh_inj.
   rewrite !nam2mix_fvars. cbn. namedec.
 - intros ->.
   rewrite <- (nam2mix_subst_bsubst0 x (Var x)).
   apply nam2mix_subst_nop.
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
       assert (E := subst_nop x f).
       apply AlphaEq_nam2mix_gen with (stk:=rev s) in E.
       rewrite <- E.
       assert (E' := subst_nop x f').
       apply AlphaEq_nam2mix_gen with (stk:=rev s) in E'.
       rewrite <- E'.
       clear E E'.
       rewrite !nam2mix_subst_bsubst, Eq; simpl; auto.
       intros v Hv. nameiff. now intros ->.
       intros v Hv. nameiff. now intros ->.
 - rewrite nam2mix_canonical. apply AlphaEq_nam2mix_gen.
Qed.

(** TODO Again !! *)

Lemma nam2mix_canonical_gen stk f f' :
 nam2mix stk f = nam2mix stk f' <-> AlphaEq f f'.
Proof.
 rewrite nam2mix_nostack. apply nam2mix_canonical.
Qed.

(** Swapping substitutions.
    This technical lemma is described in Alexandre's course notes.
    See also [Alpha.partialsubst_partialsubst]. In fact, we won't
    reuse it afterwards. *)

Lemma subst_subst x x' u u' f :
 x<>x' -> ~Names.In x (Term.vars u') ->
 AlphaEq (subst x' u' (subst x u f))
         (subst x (Term.subst x' u' u) (subst x' u' f)).
Proof.
 intros NE NI.
 apply nam2mix_canonical.
 rewrite !nam2mix0_subst_fsubst.
 rewrite nam2mix_term_subst by auto.
 apply form_fsubst_fsubst; auto.
 rewrite nam2mix_tvars. cbn. namedec.
Qed.

(** The general equation defining [subst] on a quantified formula,
    via renaming. *)

Lemma subst_QuGen x z t q v f :
 x<>v ->
 ~Names.In z (Names.add x (Names.union (freevars f) (Term.vars t))) ->
 AlphaEq (subst x t (Quant q v f))
         (Quant q z (subst x t (subst v (Var z) f))).
Proof.
 intros NE NI.
 apply nam2mix_canonical. cbn - [subst].
 rewrite !nam2mix0_subst_fsubst. cbn - [subst].
 f_equal.
 rewrite nam2mix_subst_fsubst by (simpl; namedec).
 f_equal.
 apply nam2mix_rename_iff3; auto. namedec.
Qed.

Lemma nam2mix_eqb (f f' : Nam.formula) :
 (nam2mix [] f =? nam2mix [] f') = (f =? f').
Proof.
 case eqbspec; rewrite nam2mix_canonical.
 - intros. symmetry. now apply AlphaEq_equiv.
 - intros H. rewrite <- AlphaEq_equiv in H.
   symmetry. exact (not_true_is_false _ H).
Qed.

(** Proofs about [mix2nam] *)

Lemma mix_nam_mix_term_gen stack t :
 NoDup stack ->
 Mix.level t <= List.length stack ->
 (forall v, In v stack -> ~Names.In v (Mix.fvars t)) ->
 nam2mix_term stack (mix2nam_term stack t) = t.
Proof.
 intros ND.
 revert t. fix IH 1. destruct t; cbn; trivial; intros LE FR.
 - destruct (list_index v stack) eqn:E; auto.
   assert (IN : In v stack).
   { apply list_index_in. now rewrite E. }
   apply FR in IN. namedec.
 - rewrite list_index_nth; auto.
 - f_equal. clear f.
   revert l LE FR.
   fix IHl 1. destruct l as [|t l]; simpl; trivial.
   intros LE FR.
   f_equal.
   + apply IH; auto. omega with *.
     intros v IN. apply FR in IN. namedec.
   + apply IHl; auto. omega with *.
     intros v IN. apply FR in IN. namedec.
Qed.

Lemma mix_nam_mix_gen stack f :
 NoDup stack ->
 Mix.level f <= List.length stack ->
 (forall v, In v stack -> ~Names.In v (Mix.fvars f)) ->
 nam2mix stack (mix2nam stack f) = f.
Proof.
 revert stack.
 induction f; simpl; trivial; intros stack ND LE FR.
 - f_equal.
   injection (mix_nam_mix_term_gen stack (Mix.Fun "" l)); auto.
 - f_equal. auto.
 - cbn in *. f_equal.
   + apply IHf1; auto. omega with *.
     intros v IN. apply FR in IN. namedec.
   + apply IHf2; auto. omega with *.
     intros v IN. apply FR in IN. namedec.
 - cbn in *. f_equal.
   apply IHf; auto.
   + constructor; auto.
     setfresh vars z Hz. rewrite <- names_of_list_in. namedec.
   + simpl. omega with *.
   + simpl.
     intros v [<-|IN].
     * setfresh vars z Hz. namedec.
     * apply FR in IN. namedec.
Qed.

Lemma mix_nam_mix_term t :
 Mix.BClosed t ->
 nam2mix_term [] (mix2nam_term [] t) = t.
Proof.
 intros CL.
 apply mix_nam_mix_term_gen; auto. constructor.
 now rewrite CL.
Qed.

Lemma mix_nam_mix f :
  Mix.BClosed f ->
  nam2mix [] (mix2nam [] f) = f.
Proof.
 unfold Mix.BClosed. intros E.
 apply mix_nam_mix_gen; auto.
 constructor.
 simpl. rewrite E. auto.
Qed.

Lemma nam_mix_nam_term t :
 mix2nam_term [] (nam2mix_term [] t) = t.
Proof.
 apply nam2mix_term_inj.
 apply mix_nam_mix_term.
 apply nam2mix_term_bclosed.
Qed.

Lemma nam_mix_nam f :
  AlphaEq (mix2nam [] (nam2mix [] f)) f.
Proof.
 apply nam2mix_canonical.
 apply mix_nam_mix.
 apply nam2mix_bclosed.
Qed.
