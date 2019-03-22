
(** Conversion from Named formulas to Locally Nameless formulas *)

Require Import RelationClasses Arith Omega Defs Proofs.
Require Nam Mix.
Import ListNotations.
Import Nam Nam.Form.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

(** From named to locally nameless *)

Fixpoint nam2mix_term stack t :=
  match t with
  | Var v =>
    match list_index v stack with
    | None => Mix.FVar v
    | Some n => Mix.BVar n
    end
  | Fun f args =>
    Mix.Fun f (List.map (nam2mix_term stack) args)
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
    let v := fresh_var (Vars.union (vars_of_list stack) (Mix.fvars f)) in
    Nam.Quant q v (mix2nam (v::stack) f)
  end.

(** First, we prove that [nam2mix] is canonical :
    it sends alpha-equivalent named formulas to equal mixed formulas. *)

(** The invariant used during the proof *)

Module Nam2Mix.

Inductive Inv (vars:Vars.t) : Subst.t -> Subst.t -> Prop :=
 | InvNil : Inv vars [] []
 | InvCons v v' z sub sub' :
   Inv vars sub sub' ->
   ~Vars.In z vars ->
   ~Vars.In z (Nam.Subst.vars sub) ->
   ~Vars.In z (Nam.Subst.vars sub') ->
   Inv vars ((v,Var z)::sub) ((v',Var z)::sub').

End Nam2Mix.
Import Nam2Mix.

Hint Constructors Inv.

Lemma Inv_sym vars sub sub' :
 Inv vars sub sub' -> Inv vars sub' sub.
Proof.
 induction 1; auto.
Qed.

Lemma Inv_notIn sub sub' vars v :
 Inv vars sub sub' ->
  ~(Vars.In v vars /\ Vars.In v (Subst.outvars sub)).
Proof.
 induction 1; unfold Subst.vars in *; simpl; varsdec.
Qed.

Lemma Inv_weak sub sub' vars vars' :
  Vars.Subset vars' vars -> Inv vars sub sub' -> Inv vars' sub sub'.
Proof.
 induction 2; auto.
Qed.

Lemma Inv_listassoc_var vars sub sub' :
  Inv vars sub sub' ->
  forall v t, list_assoc v sub = Some t -> exists z, t = Var z.
Proof.
 induction 1.
 - easy.
 - simpl. intros x t.
   case eqbspec; eauto.
   intros -> [= <-]. now exists z.
Qed.

Lemma list_assoc_some_in v sub z :
  list_assoc v sub = Some (Var z) -> Vars.In z (Subst.outvars sub).
Proof.
 induction sub as [|(v',t) sub IH]; try easy.
 simpl.
 case eqbspec.
 - intros <- [= ->]. simpl. varsdec.
 - intros _ E. apply IH in E. simpl. varsdec.
Qed.

Lemma list_assoc_index vars v v' sub sub' z :
Inv vars sub sub' ->
list_assoc v sub = Some (Var z) ->
list_assoc v' sub' = Some (Var z) ->
exists k,
list_index v (map fst sub) = Some k /\
list_index v' (map fst sub') = Some k.
Proof.
 induction 1; try easy.
 simpl.
 do 2 case eqbspec.
 - intros. now exists 0.
 - intros NE <- [= <-] E. apply list_assoc_some_in in E.
   unfold Nam.Subst.vars in *. varsdec.
 - intros <- NE E [= <-]. apply list_assoc_some_in in E.
   unfold Nam.Subst.vars in *. varsdec.
 - intros _ _ E E'. destruct (IHInv E E') as (k & Hk & Hk').
   exists (S k). simpl in *. now rewrite Hk, Hk'.
Qed.

Lemma list_index_assoc vars v v' sub sub' n :
Inv vars sub sub' ->
list_index v (map fst sub) = Some n ->
list_index v' (map fst sub') = Some n ->
exists t,
list_assoc v sub = Some t /\
list_assoc v' sub' = Some t.
Proof.
 intros inv.
 revert n.
 induction inv; try easy.
 simpl.
 do 2 case eqbspec.
 - intros <- <- n [= <-] _. now exists (Nam.Var z).
 - intros _ <- n [= <-]. clear IHinv.
   destruct list_index; simpl; congruence.
 - intros <- _ n E [= <-]. clear IHinv.
   destruct list_index; simpl in *; congruence.
 - intros _ _ [|n].
   destruct list_index; simpl; congruence.
   intros E E'.
   apply (IHinv n).
   destruct (list_index v); simpl in *; congruence.
   destruct (list_index v'); simpl in *; congruence.
Qed.

Lemma nam2mix_term_ok sub sub' t t' :
 Inv (Vars.union (Term.vars t) (Term.vars t')) sub sub' ->
 Term.substs sub t = Term.substs sub' t' <->
 nam2mix_term (map fst sub) t = nam2mix_term (map fst sub') t'.
Proof.
 revert t t' sub sub'.
 fix IH 1. destruct t as [v|f a], t' as [v'|f' a']; intros sub sub' inv;
   simpl; rewrite ?list_assoc_dft_alt.
 - simpl in *. split.
   + destruct (list_assoc v sub) eqn:E, (list_assoc v' sub') eqn:E'.
     * intros <-.
       destruct (Inv_listassoc_var _ _ _ inv v t E) as (z, ->).
       destruct (list_assoc_index _ v v' sub sub' z inv E E') as (k & Hk & Hk').
       simpl in Hk, Hk'.
       now rewrite Hk, Hk'.
     * intros ->.
       apply list_assoc_some_in in E.
       destruct (Inv_notIn _ _ _ v' inv). varsdec.
     * intros <-.
       apply list_assoc_some_in in E'.
       apply Inv_sym in inv.
       destruct (Inv_notIn _ _ _ v inv). varsdec.
     * intros [= <-].
       rewrite list_assoc_index_none in E, E'.
       simpl in *. now rewrite E, E'.
   + destruct (list_index v) eqn:E, (list_index v') eqn:E'; intros [= <-].
     * destruct (list_index_assoc _ _ _ _ _ _ inv E E') as (k & Hk & Hk').
       simpl in *. now rewrite Hk, Hk'.
     * rewrite <- list_assoc_index_none in E, E'.
       simpl in *. now rewrite E,E'.
 - split.
   + generalize (Inv_listassoc_var _ _ _ inv v).
     destruct list_assoc as [t|]; try easy.
     intros E. destruct (E t) as (v', ->); easy.
   + destruct list_index; easy.
 - split.
   + apply Inv_sym in inv.
     generalize (Inv_listassoc_var _ _ _ inv v').
     destruct list_assoc as [t'|]; try easy.
     intros E. destruct (E t') as (v, ->); easy.
   + destruct list_index; easy.
 - split. intros [= <- E]. f_equal.
   + simpl in inv.
     clear f. revert a a' E inv.
     fix IH' 1. destruct a as [|t a], a' as [|t' a']; try easy.
     simpl.
     intros [= E E'] inv. f_equal.
     * apply IH; auto. eapply Inv_weak; eauto. varsdec.
     * apply IH'; auto. eapply Inv_weak; eauto. varsdec.
   + intros [= <- E]. f_equal.
     simpl in inv.
     clear f. revert a a' E inv.
     fix IH' 1. destruct a as [|t a], a' as [|t' a']; try easy.
     simpl.
     intros [= E E'] inv. f_equal.
     * apply IH; auto. eapply Inv_weak; eauto. varsdec.
     * apply IH'; auto. eapply Inv_weak; eauto. varsdec.
Qed.

Lemma nam2mix_canonical_gen sub sub' f f' :
 Inv (Vars.union (allvars f) (allvars f')) sub sub' ->
 αeq_gen sub f sub' f' = true <->
 nam2mix (List.map fst sub) f = nam2mix (List.map fst sub') f'.
Proof.
 revert f' sub sub'.
 induction f; destruct f'; intros sub sub'; simpl; intros IV; try easy.
 - rewrite lazy_andb_iff, !eqb_eq.
   assert (H := nam2mix_term_ok sub sub' (Nam.Fun "" l) (Nam.Fun "" l0) IV).
   simpl.
   split.
   + intros (<-,E). f_equal. injection (proj1 H); simpl; f_equal; auto.
   + intros [= <- E]. split; auto. injection (proj2 H); simpl; f_equal; auto.
 - rewrite IHf by auto.
   split; [intros <- | intros [=]]; easy.
 - rewrite !lazy_andb_iff, !eqb_eq.
   rewrite IHf1, IHf2 by (eapply Inv_weak; eauto; varsdec).
   split; [intros ((<-,<-),<-)|intros [= <- <- <-]]; easy.
 - rewrite lazy_andb_iff, !eqb_eq.
   set (vars := Vars.union _ _).
   assert (Hz := fresh_var_ok vars).
   set (z := fresh_var vars) in *.
   rewrite IHf by (constructor; try (eapply Inv_weak; eauto); varsdec).
   simpl.
   split; [intros (<-,<-) | intros [=]]; easy.
Qed.

Lemma nam2mix_canonical (f f' : Nam.formula) :
 nam2mix [] f = nam2mix [] f' <-> AlphaEq f f'.
Proof.
 symmetry. now apply nam2mix_canonical_gen.
Qed.

(** Proofs about [mix2nam] *)

Lemma mix_nam_mix_term stack t :
 NoDup stack ->
 Mix.level t <= List.length stack ->
 (forall v, In v stack -> ~Vars.In v (Mix.fvars t)) ->
 nam2mix_term stack (mix2nam_term stack t) = t.
Proof.
 intros ND.
 revert t. fix IH 1. destruct t; cbn; trivial; intros LE FR.
 - destruct (list_index v stack) eqn:E; auto.
   assert (IN : In v stack).
   { apply list_index_in. now rewrite E. }
   apply FR in IN. varsdec.
 - rewrite list_index_nth; auto.
 - f_equal. clear f.
   revert l LE FR.
   fix IHl 1. destruct l as [|t l]; simpl; trivial.
   intros LE FR.
   f_equal.
   + apply IH; auto. omega with *.
     intros v IN. apply FR in IN. varsdec.
   + apply IHl; auto. omega with *.
     intros v IN. apply FR in IN. varsdec.
Qed.

Lemma mix_nam_mix_gen stack f :
 NoDup stack ->
 Mix.level f <= List.length stack ->
 (forall v, In v stack -> ~Vars.In v (Mix.fvars f)) ->
 nam2mix stack (mix2nam stack f) = f.
Proof.
 revert stack.
 induction f; simpl; trivial; intros stack ND LE FR.
 - f_equal.
   injection (mix_nam_mix_term stack (Mix.Fun "" l)); auto.
 - f_equal. auto.
 - cbn in *. f_equal.
   + apply IHf1; auto. omega with *.
     intros v IN. apply FR in IN. varsdec.
   + apply IHf2; auto. omega with *.
     intros v IN. apply FR in IN. varsdec.
 - cbn in *. f_equal.
   apply IHf; auto.
   + constructor; auto.
     set (vars := Vars.union (vars_of_list stack) (Mix.fvars f)).
     assert (FR' := fresh_var_ok vars).
     contradict FR'.
     unfold vars at 2. VarsF.set_iff. left.
     now apply vars_of_list_in.
   + simpl. omega with *.
   + simpl.
     intros v [<-|IN].
     * set (vars := Vars.union (vars_of_list stack) (Mix.fvars f)).
       generalize (fresh_var_ok vars). varsdec.
     * apply FR in IN. varsdec.
Qed.

Lemma mix_nam_mix f :
  Mix.closed f ->
  nam2mix [] (mix2nam [] f) = f.
Proof.
 unfold Mix.closed. intros E.
 apply mix_nam_mix_gen; auto.
 constructor.
 simpl. rewrite E. auto.
Qed.

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

Lemma nam2mix_closed f :
  Mix.closed (nam2mix [] f).
Proof.
 unfold Mix.closed.
 generalize (nam2mix_level [] f). simpl. auto with *.
Qed.


Lemma nam_mix_nam f :
  AlphaEq (mix2nam [] (nam2mix [] f)) f.
Proof.
 apply nam2mix_canonical.
 apply mix_nam_mix.
 apply nam2mix_closed.
Qed.

Lemma AlphaEq_equivalence :
  Equivalence AlphaEq.
Proof.
 constructor.
 - intros f. now apply nam2mix_canonical.
 - intros f f'. rewrite <-!nam2mix_canonical. auto.
 - intros f1 f2 f3. rewrite <-!nam2mix_canonical. apply eq_trans.
Qed.

Lemma nam2mix_eqb (f f' : Nam.formula) :
 (nam2mix [] f =? nam2mix [] f') = (f =? f').
Proof.
 case eqbspec; rewrite nam2mix_canonical.
 - apply eq_sym.
 - intros H. symmetry. exact (not_true_is_false _ H).
Qed.
