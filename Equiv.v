
(** * Conversion from Named formulas to Locally Nameless formulas *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Alpha.
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
    let v := fresh (Names.union (Names.of_list stack) (Mix.fvars f)) in
    Nam.Quant q v (mix2nam (v::stack) f)
  end.

(** Simultaneous renamings of many variables.
    The bindings of this substitution will be handled in parallel,
    not sequentially. In particular, the variables introduced
    by a binding aren't modified by other bindings.
    If the substitution contains several bindings of the same
    variable, the leftmost binding wins (cf. [list_assoc]). *)

Definition substitution := list (variable * term).

Module Ren.

Definition t := list (variable * variable).

Definition invars (ren : t) :=
  List.fold_right (fun p vs => Names.add (fst p) vs) Names.empty ren.

Definition outvars (ren : t) :=
  List.fold_right (fun p vs => Names.add (snd p) vs) Names.empty ren.

Definition vars (ren : t) :=
  Names.union (invars ren) (outvars ren).

End Ren.

(** First, we prove that [nam2mix] is canonical :
    it sends alpha-equivalent named formulas to equal mixed formulas. *)

(** The invariant used during the proof *)

Module Nam2Mix.

Inductive Inv (vars:Names.t) : Ren.t -> Ren.t -> Prop :=
 | InvNil : Inv vars [] []
 | InvCons v v' z sub sub' :
   Inv vars sub sub' ->
   ~Names.In z vars ->
   ~Names.In z (Ren.vars sub) ->
   ~Names.In z (Ren.vars sub') ->
   Inv vars ((v,z)::sub) ((v',z)::sub').

Inductive HalfInv (vars:Names.t) : Ren.t -> Prop :=
 | HInvNil : HalfInv vars []
 | HInvCons v z sub :
   HalfInv vars sub ->
   ~Names.In z vars ->
   ~Names.In z (Ren.vars sub) ->
   HalfInv vars ((v,z)::sub).

End Nam2Mix.
Import Nam2Mix.

Hint Constructors Inv HalfInv.

Lemma Inv_HalfInv vars sub sub' : Inv vars sub sub' -> HalfInv vars sub.
Proof.
 induction 1; auto.
Qed.

Lemma Inv_HalfInv' vars sub sub' : Inv vars sub sub' -> HalfInv vars sub'.
Proof.
 induction 1; auto.
Qed.

Lemma Inv_sym vars sub sub' :
 Inv vars sub sub' -> Inv vars sub' sub.
Proof.
 induction 1; auto.
Qed.

Lemma Inv_notIn sub sub' vars v :
 Inv vars sub sub' ->
  ~(Names.In v vars /\ Names.In v (Ren.outvars sub)).
Proof.
 induction 1; unfold Ren.vars in *; simpl; namedec.
Qed.

Lemma Inv_weak sub sub' vars vars' :
  Names.Subset vars' vars -> Inv vars sub sub' -> Inv vars' sub sub'.
Proof.
 induction 2; auto.
Qed.

Lemma HalfInv_weak sub vars vars' :
  Names.Subset vars' vars -> HalfInv vars sub -> HalfInv vars' sub.
Proof.
 induction 2; auto.
Qed.

Lemma HalfInv_weak' (z:variable) sub vars vars' :
  Names.Subset vars' (Names.add z vars) ->
  ~Names.In z (Ren.vars sub) ->
  HalfInv vars sub -> HalfInv vars' sub.
Proof.
 induction 3; auto.
 constructor; auto.
 - apply IHHalfInv. unfold Ren.vars in *. simpl in H0. namedec.
 - rewrite H. unfold Ren.vars in *. simpl in *. namedec.
Qed.

Lemma list_assoc_some_in v sub z :
  list_assoc v sub = Some z -> Names.In z (Ren.outvars sub).
Proof.
 induction sub as [|(v',t) sub IH]; try easy.
 simpl.
 case eqbspec.
 - intros <- [= ->]. simpl. namedec.
 - intros _ E. apply IH in E. simpl. namedec.
Qed.

Lemma list_assoc_index vars v v' sub sub' z :
Inv vars sub sub' ->
list_assoc v sub = Some z ->
list_assoc v' sub' = Some z ->
exists k,
list_index v (map fst sub) = Some k /\
list_index v' (map fst sub') = Some k.
Proof.
 induction 1; try easy.
 simpl.
 do 2 case eqbspec.
 - intros. now exists 0.
 - intros NE <- [= <-] E. apply list_assoc_some_in in E.
   unfold Ren.vars in *. namedec.
 - intros <- NE E [= <-]. apply list_assoc_some_in in E.
   unfold Ren.vars in *. namedec.
 - intros _ _ E E'. destruct (IHInv E E') as (k & Hk & Hk').
   exists (S k). simpl in *. now rewrite Hk, Hk'.
Qed.

Lemma list_index_assoc vars v v' sub sub' n :
Inv vars sub sub' ->
list_index v (map fst sub) = Some n ->
list_index v' (map fst sub') = Some n ->
exists z,
list_assoc v sub = Some z /\
list_assoc v' sub' = Some z.
Proof.
 intros inv.
 revert n.
 induction inv; try easy.
 simpl.
 do 2 case eqbspec.
 - intros <- <- n [= <-] _. now exists z.
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

Fixpoint foldrename_term sub t :=
  match sub with
  | [] => t
  | (v,z)::sub => foldrename_term sub (Term.subst v (Var z) t)
  end.

Fixpoint foldrename sub f :=
  match sub with
  | [] => f
  | (v,z)::sub => foldrename sub (rename v z f)
  end.

Lemma foldrename_True sub : foldrename sub True = True.
Proof.
 induction sub as [|(v,z) sub IH]; simpl; auto.
Qed.

Lemma foldrename_False sub : foldrename sub False = False.
Proof.
 induction sub as [|(v,z) sub IH]; simpl; auto.
Qed.

Lemma foldrename_not sub f :
 foldrename sub (~f) = (~ foldrename sub f)%form.
Proof.
 revert f.
 induction sub as [|(v,z) sub IH]; simpl; auto.
Qed.

Lemma foldrename_op sub o f f' :
 foldrename sub (Op o f f') = Op o (foldrename sub f) (foldrename sub f').
Proof.
 revert f f'.
 induction sub as [|(v,z) sub IH]; simpl; auto.
Qed.

Lemma foldrename_quant_weak sub q v f :
 exists f', foldrename sub (Quant q v f) = Quant q v f'.
Proof.
 revert f.
 induction sub as [|(x,z) sub IH]; simpl; auto.
 intros f. now exists f.
Qed.

Lemma foldrename_pred sub p l :
 foldrename sub (Pred p l) = Pred p (List.map (foldrename_term sub) l).
Proof.
 revert l.
 induction sub as [|(x,z) sub IH]; simpl; auto.
 - intros l. f_equal. symmetry. apply map_id_iff; auto.
 - intros l. rewrite IH. f_equal. rewrite map_map; auto.
Qed.

Lemma foldrename_quant_swap sub f q (v:variable) :
 HalfInv (Names.add v (allvars f)) sub ->
 AlphaEq (foldrename sub (Quant q v f))
         (Quant q v (foldrename (list_unassoc v sub) f)).
Proof.
 revert f.
 induction sub as [|(x,t) sub IH].
 - simpl. reflexivity.
 - simpl. intros f. inversion 1; subst.
   case eqbspec; simpl; auto.
   intros NE.
   apply IH; auto.
   eapply HalfInv_weak'; eauto. rewrite allvars_rename. namedec.
Qed.

Lemma foldrename_rename_swap sub f (v z:variable) :
 HalfInv (Names.add v (allvars f)) ((v,z)::sub) ->
 AlphaEq (foldrename sub (rename v z f))
         (rename v z (foldrename (list_unassoc v sub) f)).
Proof.
 revert f.
 induction sub as [|(x,y) sub IH].
 - simpl. reflexivity.
 - simpl. intros f. inversion 1; subst.
   inversion H3; subst.
   simpl in H.
   case eqbspec; simpl.
   + intros ->.
     rewrite rename_bis; auto with set.
     apply IH. constructor; auto.
     unfold Ren.vars in *. simpl in *; namedec.
   + intros NE.
     assert (z <> x).
     { unfold Ren.vars in *; simpl in *; namedec. }
     rewrite rename_rename; auto with set.
     apply IH.
     apply HalfInv_weak' with y (Names.add v (allvars f)).
     rewrite allvars_rename; simpl. namedec.
     unfold Ren.vars in *. simpl in *. namedec.
     constructor; auto.
     unfold Ren.vars in *. simpl in *; namedec.
Qed.

Lemma allvars_foldrename sub f :
  Names.Subset (allvars (foldrename sub f))
               (Names.union (Ren.outvars sub) (allvars f)).
Proof.
 revert f.
 induction sub as [|(x,t) sub IH]; simpl; intros.
 - namedec.
 - rewrite IH, allvars_rename. namedec.
Qed.

Lemma unassoc_subset sub v :
 Names.Subset (Ren.outvars (list_unassoc v sub))
              (Ren.outvars sub).
Proof.
 induction sub as [|(x,y) sub IH]; simpl.
 - auto with set.
 - case eqbspec; simpl; auto with set.
Qed.

Lemma foldrename_term_fun sub f l :
  foldrename_term sub (Fun f l) = Fun f (map (foldrename_term sub) l).
Proof.
 revert f l.
 induction sub as [|(x,t) sub IH]; cbn; intros.
 - f_equal. symmetry. apply map_id.
 - rewrite IH. f_equal. apply map_map.
Qed.

Lemma foldrename_term_var_id sub (v:variable) :
  ~ Names.In v (Ren.vars sub) ->
  foldrename_term sub (Var v) = Var v.
Proof.
 revert v.
 induction sub as [|(x,t) sub IH]; cbn; intros; auto.
 case eqbspec; auto.
 - intros <-. namedec.
 - intros NI. apply IH. unfold Ren.vars. namedec.
Qed.

Lemma foldrename_term_var sub (v:variable) :
 HalfInv (Names.singleton v) sub ->
 foldrename_term sub (Var v) = Var (list_assoc_dft v sub v).
Proof.
 revert v.
 induction sub as [|(x,t) sub IH]; cbn; intros; auto.
 inversion H; subst.
 case eqbspec; auto.
 intros <-. apply foldrename_term_var_id; auto.
Qed.

Lemma nam2mix_term_ok sub sub' t t' :
 Inv (Names.union (Term.vars t) (Term.vars t')) sub sub' ->
 foldrename_term sub t = foldrename_term sub' t' <->
 nam2mix_term (List.map fst sub) t = nam2mix_term (List.map fst sub') t'.
Proof.
 revert t t'.
 fix IH 1. destruct t as [|f l], t' as [|f' l']; cbn; intro IV.
 - rewrite !foldrename_term_var.
   2:{ eapply Inv_HalfInv'; eauto. eapply Inv_weak; eauto. namedec. }
   2:{ eapply Inv_HalfInv; eauto. eapply Inv_weak; eauto. namedec. }
   rewrite !list_assoc_dft_alt.
   split.
   + destruct (list_assoc v sub) as [z|] eqn:EQ;
     destruct (list_assoc v0 sub') as [z'|] eqn:EQ'.
     * intros [= <-].
       destruct (list_assoc_index _ v v0 _ _ z IV) as (n & -> & ->); auto.
     * intros [=].
       apply list_assoc_some_in in EQ.
       apply (Inv_notIn _ _ _ z) in IV. namedec.
     * intros [=].
       apply list_assoc_some_in in EQ'.
       apply Inv_sym in IV.
       apply (Inv_notIn _ _ _ z') in IV. namedec.
     * intros [= <-].
       rewrite list_assoc_index_none in EQ. rewrite EQ.
       rewrite list_assoc_index_none in EQ'. now rewrite EQ'.
   + destruct (list_index v (map fst sub)) as [n|] eqn:EQ;
     destruct (list_index v0 (map fst sub')) as [n'|] eqn:EQ'; try easy.
     * injection 1 as <-.
       destruct (list_index_assoc _ v v0 _ _ n IV) as (t & -> & ->); auto.
     * injection 1 as <-.
       rewrite <- list_assoc_index_none in EQ. rewrite EQ.
       rewrite <- list_assoc_index_none in EQ'. now rewrite EQ'.
 - rewrite foldrename_term_fun.
   rewrite foldrename_term_var.
   2:{ eapply Inv_HalfInv; eauto. eapply Inv_weak; eauto. namedec. }
   destruct list_index; easy.
 - rewrite foldrename_term_fun.
   rewrite foldrename_term_var.
   2:{ eapply Inv_HalfInv'; eauto. eapply Inv_weak; eauto. namedec. }
   destruct list_index; easy.
 - rewrite !foldrename_term_fun.
   assert
     (map (foldrename_term sub) l = map (foldrename_term sub') l'
      <-> map (nam2mix_term (map fst sub)) l =
          map (nam2mix_term (map fst sub')) l').
   { revert l l' IV.
     fix IH' 1. destruct l as [|t l], l' as [|t' l']; cbn; intros IV;
      try easy.
     split.
     - injection 1 as EQt EQl. f_equal.
       + apply IH; auto. eapply Inv_weak; eauto. namedec.
       + apply IH'; auto. eapply Inv_weak; eauto. namedec.
     - injection 1 as EQt EQl. f_equal.
       + apply IH; auto. eapply Inv_weak; eauto. namedec.
       + apply IH'; auto. eapply Inv_weak; eauto. namedec. }
   split; injection 1 as <- EQ; f_equal; intuition.
Qed.

Lemma nam2mix_term_inj t t' :
 nam2mix_term [] t = nam2mix_term [] t' <-> t = t'.
Proof.
 split; [|now intros ->].
 rewrite <- (nam2mix_term_ok [] []); auto.
Qed.

Lemma nam2mix_canonical_gen sub sub' f f' :
 Inv (Names.union (allvars f) (allvars f')) sub sub' ->
 AlphaEq (foldrename sub f) (foldrename sub' f') <->
 nam2mix (List.map fst sub) f = nam2mix (List.map fst sub') f'.
Proof.
 revert f' sub sub'.
 induction f; destruct f'; intros sub sub'; simpl; intros IV;
  rewrite ?foldrename_True, ?foldrename_False, ?foldrename_not, ?foldrename_op,
    ?foldrename_pred; try easy;
  try (destruct (foldrename_quant_weak sub q v f) as (g,->); easy);
  try (destruct (foldrename_quant_weak sub' q v f') as (g',->); easy).
 - destruct (nam2mix_term_ok sub sub' (Fun "" l) (Fun "" l0) IV) as (U,V).
   rewrite !foldrename_term_fun in *. cbn in *.
   split.
   + inversion 1; subst. f_equal. injection U; auto. now f_equal.
   + injection 1 as <- EQ. injection V; auto. now intros ->. now f_equal.
 - split.
   + inversion_clear 1. f_equal. apply IHf; auto.
   + injection 1. rewrite <- IHf; auto.
 - split.
   + inversion_clear 1. f_equal.
     * apply IHf1; auto. eapply Inv_weak; eauto. namedec.
     * apply IHf2; auto. eapply Inv_weak; eauto. namedec.
   + injection 1 as <- EQ1 EQ2.
     rewrite <- IHf1 in EQ1 by (eapply Inv_weak; eauto; namedec).
     rewrite <- IHf2 in EQ2 by (eapply Inv_weak; eauto; namedec).
     auto.
 - destruct (exist_fresh
               (Names.union
                  (Names.union (Ren.vars sub) (Ren.vars sub'))
                  (Names.union (Names.add v (allvars f))
                               (Names.add v0 (allvars f'))))) as (z,Hz).
   assert (HalfInv (Names.add v (allvars f)) sub).
   { eapply Inv_HalfInv; eauto. eapply Inv_weak; eauto. namedec. }
   assert (HalfInv (Names.add v0 (allvars f')) sub').
   { eapply Inv_HalfInv'; eauto. eapply Inv_weak; eauto. namedec. }
   split.
   + intros EQ.
     assert (q = q0).
     { destruct (foldrename_quant_weak sub q v f) as (g,->) in EQ.
       destruct (foldrename_quant_weak sub' q0 v0 f') as (g',->) in EQ.
       inversion_clear EQ; auto. }
     subst q0. f_equal.
     change (nam2mix (map fst ((v,z)::sub)) f =
             nam2mix (map fst ((v0,z)::sub')) f').
     apply IHf.
     { constructor; auto with set.
       eapply Inv_weak; eauto. namedec. }
     { simpl.
       rewrite !foldrename_rename_swap by (constructor; auto with set).
       rewrite !foldrename_quant_swap in EQ; auto.
       apply AEqQu_iff with q; auto.
       rewrite !allvars_foldrename.
       rewrite !unassoc_subset. unfold Ren.vars in Hz. namedec. }
   + injection 1 as <- EQ.
     change (nam2mix (map fst ((v,z)::sub)) f =
             nam2mix (map fst ((v0,z)::sub')) f') in EQ.
     rewrite <- IHf in EQ.
     2:{ constructor; auto with set.
         eapply Inv_weak; eauto. namedec. }
     simpl in EQ.
     rewrite !foldrename_rename_swap in EQ by (constructor; auto with set).
     rewrite !foldrename_quant_swap; auto.
     eapply AEqQu; eauto.
     rewrite !allvars_foldrename.
     rewrite !unassoc_subset. unfold Ren.vars in Hz. namedec.
Qed.

Lemma nam2mix_canonical (f f' : Nam.formula) :
 nam2mix [] f = nam2mix [] f' <-> AlphaEq f f'.
Proof.
 symmetry.
 apply (nam2mix_canonical_gen [] []). constructor.
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

Lemma nam2mix_eqb (f f' : Nam.formula) :
 (nam2mix [] f =? nam2mix [] f') = (f =? f').
Proof.
 case eqbspec; rewrite nam2mix_canonical.
 - intros. symmetry. now apply AlphaEq_equiv.
 - intros H. rewrite <- AlphaEq_equiv in H.
   symmetry. exact (not_true_is_false _ H).
Qed.
