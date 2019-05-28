
(** * Properties of substitutions for named formulas *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Nam Alpha.
Import ListNotations.
Import Nam.Form.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Implicit Types x y z v : variable.

Local Coercion Var : variable >-> term.

(** Basic results about [Form.subst] *)

Lemma hsubst_height v t f h :
  height f < h ->
  height (hsubst h v t f) = height f.
Proof.
 revert v t f.
 induction h.
 - inversion 1.
 - intros v t [ ] LT; simpl in *; simpl_height; auto.
   case eqb; auto.
   case negb; simpl; auto.
   rewrite IHh, rename_height; auto.
Qed.

Lemma subst_height v t f :
  height (subst v t f) = height f.
Proof.
 apply hsubst_height; auto with *.
Qed.

Lemma hsubst_indep v t f h h' :
  height f < h -> height f < h' ->
  hsubst h v t f = hsubst h' v t f.
Proof.
 revert h' v t f.
 induction h; [inversion 1|]; destruct h';[inversion 2|].
 destruct f; cbn -[fresh]; intros; simpl_height; f_equal; auto.
 case eqbspec; intros; auto.
 destruct negb eqn:E; f_equal; auto.
Qed.

Lemma hsubst_subst v t f h :
  height f < h ->
  hsubst h v t f = subst v t f.
Proof.
 intros. apply hsubst_indep; auto with *.
Qed.

(** Places where [subst] and [rename] will agree *)

Lemma rename_subst x y f :
  RenOk y f -> rename x y f = subst x y f.
Proof.
 unfold subst.
 set (h := S (height f)).
 assert (LT : height f < h) by (cbn; auto with * ).
 clearbody h. revert f LT.
 induction h as [|h IH].
 - inversion 1.
 - destruct f; simpl; intros; simpl_height; f_equal; auto with set.
   case eqbspec; auto.
   intros NE.
   rewrite mem_false; simpl; f_equal; auto with set.
Qed.

Lemma subst_eqn x t f :
 subst x t f =
 match f with
 | True => True
 | False => False
 | Pred p l => Pred p (List.map (Term.subst x t) l)
 | Not f => Not (subst x t f)
 | Op o f f' => Op o (subst x t f) (subst x t f')
 | Quant q v f' =>
    if x =? v then f
    else
      let out_vars := Term.vars t in
      if negb (Names.mem v out_vars) then
        Quant q v (subst x t f')
      else
        let z := fresh (Names.unions [allvars f; out_vars; Names.singleton x])
      in
        Quant q z (subst x t (rename v z f'))
 end.
Proof.
 destruct f; try reflexivity.
 - unfold subst.
   set (h1 := S (height f1)).
   set (h2 := S (height f2)).
   set (h := height _).
   assert (LT1 : height f1 < h1) by (cbn; auto with * ).
   assert (LT2 : height f2 < h2) by (cbn; auto with * ).
   assert (LT1' : height f1 < h) by (cbn; auto with * ).
   assert (LT2' : height f2 < h) by (cbn; auto with * ).
   clearbody h h1 h2.
   cbn. f_equal; apply hsubst_indep; auto.
 - unfold subst. rewrite rename_height; auto with *.
Qed.

(** Same, with [subst] instead of [rename] *)

Lemma subst_eqn' x t f :
 subst x t f =
 match f with
 | True => True
 | False => False
 | Pred p l => Pred p (List.map (Term.subst x t) l)
 | Not f => Not (subst x t f)
 | Op o f f' => Op o (subst x t f) (subst x t f')
 | Quant q v f' =>
    if x =? v then f
    else
      let out_vars := Term.vars t in
      if negb (Names.mem v out_vars) then
        Quant q v (subst x t f')
      else
        let z := fresh (Names.unions [allvars f; out_vars; Names.singleton x])
      in
        Quant q z (subst x t (subst v (Var z) f'))
 end.
Proof.
 rewrite subst_eqn. destruct f; auto.
 case eqbspec; auto.
 intros NE; simpl.
 destruct (Names.mem v (Term.vars t)) eqn:EQ; simpl; auto.
 f_equal. f_equal.
 apply rename_subst.
 set (vars := Names.union _ _).
 assert (Hz := fresh_ok vars). namedec.
Qed.


(** A partial substitution, which does *not* handle
    correctly variable capture (and just return [f] in this case). *)

Fixpoint partialsubst x t f :=
  match f with
  | True | False => f
  | Pred p args => Pred p (List.map (Term.subst x t) args)
  | Not f => Not (partialsubst x t f)
  | Op o f f' => Op o (partialsubst x t f) (partialsubst x t f')
  | Quant q v f' =>
    Quant q v
     (if (x=?v) || Names.mem v (Term.vars t) then f'
      else partialsubst x t f')
  end.

Lemma partialsubst_height x t f :
 height (partialsubst x t f) = height f.
Proof.
 induction f; cbn; auto. f_equal.
 destruct orb; auto.
Qed.

Lemma partialsubst_height_lt x t f h :
 height f < h -> height (partialsubst x t f) < h.
Proof.
 now rewrite partialsubst_height.
Qed.

Hint Resolve partialsubst_height_lt.

(** Places where [subst] and [partialsubst] will agree *)

Fixpoint IsSimple v t f :=
  match f with
  | True | False | Pred _ _ => Logic.True
  | Not f => IsSimple v t f
  | Op _ f f' => IsSimple v t f /\ IsSimple v t f'
  | Quant _ x f => v = x \/ (~Names.In x (Term.vars t)
                             /\ IsSimple v t f)
  end.

(** A sufficient condition for simplicity: *)

Lemma noninter_IsSimple x t f :
  Names.Empty (Names.inter (allvars f) (Term.vars t)) -> IsSimple x t f.
Proof.
 induction f; cbn in *; auto.
 intros E; split; (apply IHf1 || apply IHf2); namedec.
 intros E.
 case (eqbspec v x).
 - now left.
 - intros NE. right; split; try apply IHf; namedec.
Qed.

(** Same, when t is a variable *)

Lemma notin_IsSimple (x z:variable) f :
  ~Names.In z (allvars f) -> IsSimple x z f.
Proof.
 intros. apply noninter_IsSimple. cbn. namedec.
Qed.

Hint Resolve notin_IsSimple.

(** Inductive description of these "simple" substitutions *)

Inductive SimpleSubst (v:variable)(t:term)
 : formula -> formula -> Prop :=
| SubTr : SimpleSubst v t True True
| SubFa : SimpleSubst v t False False
| SubPred p l :
  SimpleSubst v t (Pred p l) (Pred p (List.map (Term.subst v t) l))
| SubNot f f' :
    SimpleSubst v t f f' ->
    SimpleSubst v t (Not f) (Not f')
| SubOp o f1 f2 f1' f2' :
    SimpleSubst v t f1 f1' ->
    SimpleSubst v t f2 f2' ->
    SimpleSubst v t (Op o f1 f2) (Op o f1' f2')
| SubQu1 q f : SimpleSubst v t (Quant q v f) (Quant q v f)
| SubQu2 q f f' x : x<>v -> ~Names.In x (Term.vars t) ->
    SimpleSubst v t f f' ->
    SimpleSubst v t (Quant q x f) (Quant q x f').

Hint Constructors SimpleSubst.

Lemma SimpleSubst_fun v t f f1 f2 :
 SimpleSubst v t f f1 -> SimpleSubst v t f f2 -> f1 = f2.
Proof.
 intros H1. revert f2.
 induction H1; inversion 1; subst; f_equal; auto; easy.
Qed.

Lemma SimpleSubst_hsubst x t f h :
  height f < h ->
  IsSimple x t f ->
  SimpleSubst x t f (hsubst h x t f).
Proof.
 revert f.
 induction h.
 - inversion 1.
 - destruct f; cbn -[fresh];
   intros Hf IS; simpl_height; auto.
   + intuition.
   + case eqbspec.
     * intros ->; auto.
     * intros NE.
       destruct IS as [->|(NI,SI)]; [easy|].
       rewrite mem_false; cbn; auto.
Qed.

Lemma SimpleSubst_subst x t f :
  IsSimple x t f ->
  SimpleSubst x t f (subst x t f).
Proof.
 apply SimpleSubst_hsubst. auto with *.
Qed.

Lemma SimpleSubst_IsSimple x t f f' :
  SimpleSubst x t f f' -> IsSimple x t f.
Proof.
 induction 1; cbn; auto.
Qed.

Lemma SimpleSubst_partialsubst x t f :
  IsSimple x t f ->
  SimpleSubst x t f (partialsubst x t f).
Proof.
 induction f; cbn; auto.
 - intuition.
 - case eqbspec; cbn; intros Hxv IS; subst; auto.
   destruct IS as [->|(NI,IS)]; [easy|].
   rewrite mem_false; auto.
Qed.

Lemma rename_partialsubst x y f :
 RenOk y f ->
 rename x y f = partialsubst x (Var y) f.
Proof.
 induction f; cbn; intros; f_equal; auto with set.
 case eqbspec; simpl; auto.
 rewrite mem_false; auto with set.
Qed.

Lemma partialsubst_subst x t f :
  IsSimple x t f -> partialsubst x t f = subst x t f.
Proof.
 intros IS. apply (SimpleSubst_fun x t f).
 now apply SimpleSubst_partialsubst.
 now apply SimpleSubst_subst.
Qed.

Lemma SimpleSubst_carac x t f f' :
  SimpleSubst x t f f' <->
   partialsubst x t f = f' /\ IsSimple x t f.
Proof.
  assert (H := SimpleSubst_partialsubst x t f).
  split.
  - intros H'.
    assert (IS := SimpleSubst_IsSimple x t f f' H').
    split; auto.
    apply SimpleSubst_fun with x t f; auto.
  - intros (<-,IS); auto.
Qed.

Lemma IsSimple_partialsubst x t v t' f :
  IsSimple x t f ->
  IsSimple x t (partialsubst v t' f).
Proof.
 induction f; cbn; try (intuition; fail).
 intros [->|(NI,IS)]; [now left| right].
 split; auto.
 destruct orb; auto.
Qed.

(** No-op substitutions *)

Lemma partialsubst_notin x t f :
 ~Names.In x (freevars f) ->
 partialsubst x t f = f.
Proof.
 induction f; cbn; intros NI; f_equal; auto with set.
 - apply map_id_iff. intros a Ha. apply term_subst_notin.
   eapply unionmap_notin; eauto.
 - case eqbspec; cbn; auto.
   intros NE. case Names.mem; f_equal; auto with set.
Qed.

(** Free variables and substitutions *)

Lemma allvars_partialsubst x t f :
 Names.Subset (allvars (partialsubst x t f))
              (Names.union (allvars f) (Term.vars t)).
Proof.
 induction f; cbn; try namedec.
 - generalize (term_vars_subst x t (Fun "" l)). cbn. namedec.
 - destruct orb; cbn; namedec.
Qed.

Lemma allvars_partialsubst_2 x t f :
 IsSimple x t f ->
 Names.In x (freevars f) ->
 Names.Subset (Term.vars t) (allvars (partialsubst x t f)).
Proof.
 induction f; cbn; intros IS; try namedec.
 - apply (term_vars_subst_in' x t (Fun "" l)).
 - auto.
 - nameiff. destruct IS as (IS1,IS2).
   intros [IN|IN].
   rewrite (IHf1 IS1 IN). namedec.
   rewrite (IHf2 IS2 IN). namedec.
 - case eqbspec; cbn. namedec.
   nameiff. intros NE (IN,_).
   destruct IS as [->|(NI,IS)]; [easy|].
   specialize (IHf IS IN).
   rewrite mem_false by trivial. cbn. namedec.
Qed.

Lemma freevars_partialsubst_in x t f :
 IsSimple x t f ->
 Names.In x (freevars f) ->
 Names.Equal (freevars (partialsubst x t f))
             (Names.union (Names.remove x (freevars f)) (Term.vars t)).
Proof.
 induction f; cbn; intros IS IN.
 - namedec.
 - namedec.
 - apply (term_vars_subst_in x t (Fun "" l)); auto.
 - auto.
 - destruct IS as (IS1,IS2).
   rewrite Names.union_spec in IN.
   destruct (NamesP.In_dec x (freevars f1)) as [IN1|IN1];
    destruct (NamesP.In_dec x (freevars f2)) as [IN2|IN2];
    try rewrite (IHf1 IS1 IN1); try rewrite (IHf2 IS2 IN2);
    try rewrite (partialsubst_notin x t f2) by trivial;
    try rewrite (partialsubst_notin x t f1) by trivial;
    namedec.
 - case eqbspec; cbn. namedec.
   intros. destruct IS as [->|(NI,IS)]; [easy|].
   rewrite mem_false by trivial.
   rewrite (IHf IS); namedec.
Qed.


Lemma freevars_partialsubst_subset x t f :
 IsSimple x t f ->
 Names.Subset (freevars (partialsubst x t f))
              (Names.union (Names.remove x (freevars f)) (Term.vars t)).
Proof.
 induction f; cbn; intros IS.
 - namedec.
 - namedec.
 - apply (term_vars_subst x t (Fun "" l)).
 - auto.
 - destruct IS as (IS1,IS2).
   specialize (IHf1 IS1). specialize (IHf2 IS2). namedec.
 - case eqbspec; cbn. namedec.
   intros. destruct IS as [->|(NI,IS)]; [easy|].
   specialize (IHf IS).
   rewrite mem_false by trivial.
   cbn. namedec.
Qed.

Lemma freevars_partialsubst_subset2 x t f :
  IsSimple x t f ->
  Names.Subset (freevars f)
               (Names.add x (freevars (partialsubst x t f))).
Proof.
 intros NE.
 destruct (NamesP.In_dec x (freevars f)).
 - rewrite freevars_partialsubst_in; auto with set.
 - rewrite partialsubst_notin; auto with set.
Qed.

Lemma freevars_partialsubst_subset3 x t f :
  IsSimple x t f ->
  Names.Subset (Names.remove x (freevars f))
               (freevars (partialsubst x t f)).
Proof.
 intros NE.
 rewrite (freevars_partialsubst_subset2 x t f); auto with set.
Qed.

(** Swapping substitutions *)

Lemma partialsubst_partialsubst x x' u u' f :
 x<>x' -> ~Names.In x (Term.vars u') ->
 IsSimple x u f ->
 IsSimple x' u' f ->
 partialsubst x' u' (partialsubst x u f) =
 partialsubst x (Term.subst x' u' u) (partialsubst x' u' f).
Proof.
 intros NE NI.
 induction f; cbn; intros IS1 IS2; f_equal; auto.
 - rewrite !map_map.
   apply map_ext. intros.
   apply term_subst_subst; auto.
 - intuition.
 - intuition.
 - repeat (case eqbspec; cbn; auto); intros; subst; try easy.
   + clear IS2. destruct IS1 as [->|(NI',IS)]; [easy|].
     rewrite term_subst_notin; auto.
   + destruct IS1 as [->|(NI1,IS1)]; [easy|].
     destruct IS2 as [->|(NI2,IS2)]; [easy|].
     assert (~Names.In v (Term.vars (Term.subst x' u' u))).
     { rewrite term_vars_subst. namedec. }
     repeat (rewrite mem_false by trivial).
     auto.
Qed.

(** When defined, [partialsubst] is compatible with alpha-equivalence *)

Lemma AEq_partialsubst f f' :
 AlphaEq f f' ->
 forall x t,
 IsSimple x t f -> IsSimple x t f' ->
 AlphaEq (partialsubst x t f) (partialsubst x t f').
Proof.
 revert f'.
 induction f as [h IH f LT] using height_ind.
 destruct f, f'; intros EQ x t IS1 IS2; inversion_clear EQ;
  cbn in *; simpl_height; auto.
 - constructor; intuition.
 - rename v0 into v'.
   rename H0 into EQ.
   clear q; rename q0 into q.
   assert (IsSimple v z f) by auto with set.
   assert (IsSimple v' z f') by auto with set.
   repeat (case eqbspec; cbn); intros; auto.
   + subst v; subst v'.
     apply AEqQu with z; auto.
   + subst v. clear IS1.
     destruct IS2 as [->|(NI,IS2)]; [easy|].
     rewrite mem_false by trivial.
     rewrite partialsubst_notin. apply AEqQu with z; auto.
     { case (eqbspec x z).
       - intros ->; rewrite freevars_allvars; namedec.
       - intros NE.
         apply AEq_freevars in EQ.
         rewrite (freevars_rename_subset3 v' z), <- EQ.
         rewrite freevars_rename_subset. namedec. }
   + subst v'. clear IS2.
     destruct IS1 as [->|(NI,IS1)]; [easy|].
     rewrite mem_false by trivial.
     rewrite partialsubst_notin. apply AEqQu with z; auto.
     { case (eqbspec x z).
       - intros ->; rewrite freevars_allvars; namedec.
       - intros NE.
         apply AEq_freevars in EQ.
         rewrite (freevars_rename_subset3 v z), EQ.
         rewrite freevars_rename_subset. namedec. }
   + destruct IS1 as [->|(NI1,IS1)]; [easy|].
     destruct IS2 as [->|(NI2,IS2)]; [easy|].
     rewrite !mem_false by trivial.
     set (vars :=
            Names.add x (Names.add v (Names.add v'
              (Names.unions
                 [ Term.vars t; allvars f; allvars f'])))).
     destruct (exist_fresh vars) as (z',Hz').
     simpl_fresh vars Hz'.
     apply AEq_rename_any with (z' := z') in EQ;
       [ |namedec|namedec].
     clear z H H0 H1.
     apply AEqQu with z';
       [rewrite 2 allvars_partialsubst; namedec|].
     rewrite !rename_partialsubst in *; auto.
     rewrite 2 (partialsubst_partialsubst x); auto;
     try (rewrite !term_subst_notin by namedec);
     try (apply IH; auto); cbn; try namedec;
     try apply IsSimple_partialsubst; auto with set.
     rewrite allvars_partialsubst. namedec.
     rewrite allvars_partialsubst. namedec.
Qed.

Lemma AEq_SimpleSubst f1 f2 f1' f2' x t :
 AlphaEq f1 f2 ->
 SimpleSubst x t f1 f1' -> SimpleSubst x t f2 f2' ->
 AlphaEq f1' f2'.
Proof.
 intros EQ S1 S2. rewrite SimpleSubst_carac in *.
 destruct S1 as (<-,IS1).
 destruct S2 as (<-,IS2).
 apply AEq_partialsubst; auto.
Qed.

Lemma AEqQu_rename0 f q (v z : variable) :
 IsSimple v z f -> ~Names.In z (freevars f) ->
 AlphaEq (Quant q v f) (Quant q z (partialsubst v z f)).
Proof.
 intros IS NI.
 set (vars := Names.add z (Names.add v (allvars f))).
 destruct (exist_fresh vars) as (z',Hz').
 apply AEqQu with z'.
 - rewrite allvars_partialsubst. cbn. namedec.
 - case (eqbspec v z).
   + intros ->.
     rewrite (partialsubst_notin z z); auto. reflexivity.
   + intros NE.
     rewrite !rename_partialsubst.
     rewrite partialsubst_partialsubst; cbn; auto with set.
     now rewrite eqb_refl, (partialsubst_notin z).
     rewrite allvars_partialsubst. simpl. namedec. namedec.
Qed.

(** The full substitution, first as a relation *)

Definition Subst x t f f' :=
  exists f0, AlphaEq f f0 /\ SimpleSubst x t f0 f'.

Lemma SimpleSubst_Subst x t f f' :
  SimpleSubst x t f f' -> Subst x t f f'.
Proof.
 intros. now exists f.
Qed.

Lemma Subst_compat x t f1 f2 f1' f2' :
 AlphaEq f1 f2 -> Subst x t f1 f1' -> Subst x t f2 f2' ->
  AlphaEq f1' f2'.
Proof.
 intros EQ (f1b & EQ1 & S1) (f2b & EQ2 & S2).
 apply (AEq_SimpleSubst f1b f2b f1' f2' x t); auto.
 transitivity f1. now symmetry.
 transitivity f2; auto.
Qed.

(* Pseudo constructors for Subst. *)

Lemma Subst_True x t : Subst x t True True.
Proof.
 now apply SimpleSubst_Subst.
Qed.

Lemma Subst_False x t : Subst x t False False.
Proof.
 now apply SimpleSubst_Subst.
Qed.

Lemma Subst_Pred x t p l :
  Subst x t (Pred p l) (partialsubst x t (Pred p l)).
Proof.
 apply SimpleSubst_Subst. now apply SimpleSubst_partialsubst.
Qed.

Lemma Subst_Not x t f f' :
  Subst x t f f' -> Subst x t (~f) (~f').
Proof.
  intros (f0 & EQ & SI). exists (~ f0)%form; auto.
Qed.

Lemma Subst_Op x t o f1 f2 f1' f2' :
  Subst x t f1 f1' -> Subst x t f2 f2' ->
  Subst x t (Op o f1 f2) (Op o f1' f2').
Proof.
  intros (f1b & EQ1 & SI1) (f2b & EQ2 & SI2).
  exists (Op o f1b f2b); auto.
Qed.

Lemma Subst_Qu1 x t q f :
  Subst x t (Quant q x f) (Quant q x f).
Proof.
  exists (Quant q x f). split; auto. reflexivity.
Qed.

Lemma Subst_Qu2 x t q v f f' :
  x <> v ->
  ~Names.In v (Term.vars t) ->
  Subst x t f f' ->
  Subst x t (Quant q v f) (Quant q v f').
Proof.
  intros NE NI (f0 & EQ & IS).
  exists (Quant q v f0). auto using AEqQu_nosubst.
Qed.

Lemma Subst_Qu3 x t q (v z : variable) f f' g :
  x <> v ->
  ~Names.In z (freevars f) ->
  Subst v z f f' ->
  Subst x t (Quant q z f') (Quant q z g) ->
  Subst x t (Quant q v f) (Quant q z g).
Proof.
  intros NE NI (f0 & EQ & SI) (h & EQ' & SI').
  exists h. split; auto.
  transitivity (Quant q z f'); auto.
  transitivity (Quant q v f0).
  apply AEqQu_nosubst; auto.
  rewrite SimpleSubst_carac in SI. destruct SI as (<-,IS).
  apply AEqQu_rename0; auto.
  apply AEq_freevars in EQ. now rewrite <- EQ.
Qed.

Lemma Subst_subst x t f : Subst x t f (subst x t f).
Proof.
 unfold subst.
 set (h := S (height f)).
 assert (LT : height f < h) by (cbn; auto with * ).
 clearbody h. revert x t f LT.
 induction h as [|h IH]; [inversion 1|];
  intros x t [ ] LT; cbn -[fresh] in *; simpl_height.
 - apply Subst_True.
 - apply Subst_False.
 - apply Subst_Pred.
 - apply Subst_Not; auto.
 - apply Subst_Op; auto.
 - setfresh vars z Hz.
   case eqbspec.
   + intros ->. apply Subst_Qu1.
   + intros NE.
     destruct (Names.mem v (Term.vars t)) eqn:IN; cbn.
     * clear IN.
       apply Subst_Qu3 with (rename v z f); auto.
       { rewrite freevars_allvars. namedec. }
       { exists f. split. reflexivity.
         rewrite rename_partialsubst by namedec.
         apply SimpleSubst_partialsubst; auto with set. }
       { apply Subst_Qu2; auto; try namedec. }
     * apply Subst_Qu2; auto.
       rewrite <- Names.mem_spec. now rewrite IN.
Qed.

Lemma Subst_exists x t f : exists f', Subst x t f f'.
Proof.
 exists (subst x t f). apply Subst_subst.
Qed.

Lemma Subst_compat' x t f1 f2 f1' :
 AlphaEq f1 f2 -> Subst x t f1 f1' ->
 exists f2', Subst x t f2 f2' /\ AlphaEq f1' f2'.
Proof.
 intros EQ SU.
 exists (subst x t f2).
 split. apply Subst_subst.
 eapply Subst_compat; eauto. apply Subst_subst.
Qed.

Instance : Proper (eq ==> eq ==> AlphaEq ==> eq ==> iff) Subst.
Proof.
 intros x x' <- t t' <- f f' Hf g g' <-.
 split.
 - intros (f0 & EQ & SI).
   exists f0. split; auto. now transitivity f.
 - intros (f0 & EQ & SI).
   exists f0. split; auto. now transitivity f'.
Qed.

Instance : Proper (eq ==> eq ==> AlphaEq ==> AlphaEq) subst.
Proof.
 intros x x' <- t t' <- f f' Hf.
 apply (Subst_compat x t f f'); auto using Subst_subst.
Qed.

(** Substitution of a quantifier, general equation via a fresh
    variable. *)

Lemma subst_quant_gen q x v z t f :
 x <> v ->
 ~Names.In z (Names.add x (Names.union (allvars f) (Term.vars t))) ->
 AlphaEq (subst x t (Quant q v f))
         (Quant q z (subst x t (rename v z f))).
Proof.
 intros.
 assert (AlphaEq (Quant q v f) (Quant q z (rename v z f))).
 { apply AEqQu_rename. namedec. }
 eapply Subst_compat; [apply H1|apply Subst_subst|].
 apply Subst_Qu2.
 - namedec.
 - namedec.
 - apply Subst_subst.
Qed.

(* TODO:
    - faire sans partialsubst ?
    - essayer une version simplifiée (sans Names.mem ...) *)