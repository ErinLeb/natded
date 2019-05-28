
(** * Properties of rename and alpha-equivalence for named formulas *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Nam.
Import ListNotations.
Import Nam.Form.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Implicit Types x y z v : variable.

Local Coercion Var : variable >-> term.

(** TERM SUBSTITUTION *)

Lemma term_subst_notin x u t :
 ~Names.In x (Term.vars t) ->
 Term.subst x u t = t.
Proof.
 induction t as [v|f a IH] using term_ind'; cbn.
 - case eqbspec; auto. namedec.
 - intros NI. f_equal. apply map_id_iff.
   intros t Ht. apply IH; auto. eapply unionmap_notin; eauto.
Qed.

Lemma term_vars_subst x u t :
 Names.Subset (Term.vars (Term.subst x u t))
              (Names.union (Names.remove x (Term.vars t)) (Term.vars u)).
Proof.
 induction t using term_ind'; cbn.
 - case eqbspec; cbn; auto with set.
 - intros v. rewrite unionmap_map_in.
   intros (a & IN & IN'). apply H in IN; trivial.
   revert IN.
   nameiff. intros [(U,V)|W]; auto. left; split; eauto with set.
Qed.

Lemma term_vars_subst_in x u t :
 Names.In x (Term.vars t) ->
 Names.Equal (Term.vars (Term.subst x u t))
             (Names.union (Names.remove x (Term.vars t)) (Term.vars u)).
Proof.
 revert t.
 fix IH 1; destruct t; cbn.
 - case eqbspec; cbn; auto with set.
 - revert l.
   fix IH' 1; destruct l; cbn.
   + namedec.
   + destruct (NamesP.In_dec x (Term.vars t)) as [E|E];
     destruct (NamesP.In_dec x (Names.unionmap Term.vars l)) as [E'|E'].
     * intros _.
       fold (Term.subst x u t). rewrite (IH t E).
       rewrite (IH' l E'). namedec.
     * intros _.
       assert (E'' : map (Term.subst x u) l = l).
       { apply map_id_iff. intros a Ha.
         apply term_subst_notin. eapply unionmap_notin; eauto. }
       rewrite E''.
       fold (Term.subst x u t). rewrite (IH t E).
       namedec.
     * intros _.
       fold (Term.subst x u t).
       rewrite (term_subst_notin x u t) by trivial.
       rewrite (IH' l E'). namedec.
     * nameiff. tauto.
Qed.

Lemma term_vars_subst_in' x u t :
 Names.In x (Term.vars t) ->
 Names.Subset (Term.vars u) (Term.vars (Term.subst x u t)).
Proof.
 induction t using term_ind'; cbn.
 - case eqbspec; cbn; auto with set.
 - intros IN v Hv. rewrite unionmap_map_in.
   rewrite unionmap_in in IN. destruct IN as (a & Ha & IN).
   exists a; split; auto. apply H; auto.
Qed.

(** Combining several term substitutions *)

Lemma term_subst_subst x u x' u' t :
 x<>x' -> ~Names.In x (Term.vars u') ->
  Term.subst x' u' (Term.subst x u t) =
  Term.subst x (Term.subst x' u' u) (Term.subst x' u' t).
Proof.
 intros NE NI.
 induction t using term_ind'; cbn.
 - case eqbspec; [intros ->|intros NE'].
   + rewrite <- eqb_neq in NE. rewrite NE. cbn.
     now rewrite eqb_refl.
   + case eqbspec; [intros ->|intros NE''].
     * cbn. rewrite eqb_refl.
       rewrite term_subst_notin; auto.
     * cbn. rewrite <-eqb_neq in NE',NE''. now rewrite NE', NE''.
 - f_equal.
   rewrite !map_map.
   apply map_ext_in.
   auto.
Qed.

Lemma term_subst_chain x y u t :
 ~Names.In y (Term.vars t) ->
  Term.subst y u (Term.subst x (Var y) t) = Term.subst x u t.
Proof.
 intros NI.
 induction t using term_ind'; cbn.
 - case eqbspec; [intros ->|intros NE].
   + simpl. now rewrite eqb_refl.
   + rewrite term_subst_notin; auto with set.
 - simpl in *. rewrite unionmap_in in NI.
   f_equal.
   rewrite !map_map.
   apply map_ext_in.
   intros. apply H; auto. contradict NI. now exists a.
Qed.

Lemma term_subst_bis v z u t :
 z <> v ->
 Term.subst v u (Term.subst v (Var z) t) =
 Term.subst v (Var z) t.
Proof.
 induction t as [x | f l IH] using term_ind'; intro H; cbn.
 - case eqbspec; cbn.
   + apply eqb_neq in H. now rewrite H.
   + intros H'. apply eqb_neq in H'. now rewrite H'.
 - f_equal. rewrite map_map. apply map_ext_iff. intros.
   apply IH; auto.
Qed.

(** A fresh "reconciliating" variable could be arbitrary *)

Lemma term_subst_rename x x' z z' t t':
  ~Names.In z (Names.union (Term.vars t) (Term.vars t')) ->
  ~Names.In z' (Names.union (Term.vars t) (Term.vars t')) ->
  Term.subst x z t = Term.subst x' z t' ->
  Term.subst x z' t = Term.subst x' z' t'.
Proof.
 revert t t'.
 fix IH 1. destruct t, t'; intros Hz Hz'; cbn in *; try easy.
 - do 2 case eqbspec; intros H H'; subst; intros [=]; namedec.
 - case eqbspec; intros _ [=].
 - case eqbspec; intros _ [=].
 - intros [= <- E]. f_equal. clear f.
   revert l l0 Hz Hz' E.
   fix IH' 1. destruct l, l0; intros Hz Hz'; cbn in *; try easy.
   intros [= E E']. f_equal.
   + apply IH; auto. namedec. namedec.
   + apply IH'; auto. namedec. namedec.
Qed.

(** RENAMING *)

(** For [rename x y f] to be meaningful, we ask for
    the following precondition. Actually, some simple
    properties over [rename] may even hold without this
    precondition. *)

Notation RenOk y f := (~Names.In y (allvars f)).

Lemma rename_height x y f :
 height (rename x y f) = height f.
Proof.
 induction f; cbn; auto. f_equal. destruct eqb; auto.
Qed.

Lemma rename_height_lt x y f h :
 height f < h -> height (rename x y f) < h.
Proof.
 now rewrite rename_height.
Qed.

Hint Resolve rename_height_lt.

(** No-op renaming *)

Lemma rename_notin x y f :
 ~Names.In x (freevars f) ->
 rename x y f = f.
Proof.
 induction f; cbn; intros NI; f_equal; auto with set.
 - apply map_id_iff. intros a Ha. apply term_subst_notin.
   eapply unionmap_notin; eauto.
 - case eqbspec; cbn; auto with set.
Qed.

(** Free variables and substitutions *)

Lemma freevars_allvars f : Names.Subset (freevars f) (allvars f).
Proof.
 induction f; cbn; auto with set.
Qed.

Lemma allvars_rename x y f :
 Names.Subset (allvars (rename x y f)) (Names.add y (allvars f)).
Proof.
 induction f; cbn; try namedec.
 - generalize (term_vars_subst x y (Fun "" l)). cbn. namedec.
 - destruct eqb; cbn; namedec.
Qed.

Lemma allvars_rename_2 x y f :
 Names.In x (freevars f) ->
 Names.In y (allvars (rename x y f)).
Proof.
 induction f; cbn; try namedec.
 - intros. apply (term_vars_subst_in' _ _ (Fun "" l)); auto with set.
 - case eqbspec; cbn; namedec.
Qed.

Lemma freevars_rename_in x y f :
 RenOk y f ->
 Names.In x (freevars f) ->
 Names.Equal (freevars (rename x y f))
             (Names.add y (Names.remove x (freevars f))).
Proof.
 induction f; cbn; intros NI IN.
 - namedec.
 - namedec.
 - rewrite (term_vars_subst_in x y (Fun "" l)); simpl; auto with set.
 - auto.
 - rewrite Names.union_spec in NI. apply Decidable.not_or in NI.
   rewrite Names.union_spec in IN.
   destruct (NamesP.In_dec x (freevars f1)) as [IN1|IN1];
    destruct (NamesP.In_dec x (freevars f2)) as [IN2|IN2];
    try rewrite IHf1 by intuition;
    try rewrite IHf2 by intuition;
    try rewrite (rename_notin x y f2) by trivial;
    try rewrite (rename_notin x y f1) by trivial;
    namedec.
 - case eqbspec; cbn. namedec.
   intros. rewrite IHf; namedec.
Qed.

Lemma freevars_rename_subset x y f :
 Names.Subset (freevars (rename x y f))
              (Names.add y (Names.remove x (freevars f))).
Proof.
 induction f; cbn.
 - namedec.
 - namedec.
 - rewrite (term_vars_subst x y (Fun "" l)). simpl. namedec.
 - auto.
 - rewrite IHf1, IHf2. namedec.
 - case eqbspec; cbn. namedec.
   intros. rewrite IHf. namedec.
Qed.

Lemma freevars_rename_subset2 x y f :
  Names.Subset (Names.remove x (freevars f))
               (freevars (rename x y f)).
Proof.
 induction f; cbn.
 - namedec.
 - namedec.
 - destruct (NamesP.In_dec x (Term.vars (Fun "" l))) as [H|H]; simpl in *.
   + rewrite (term_vars_subst_in x y (Fun "" l)); auto. simpl. namedec.
   + replace (map (Term.subst x y) l) with l. namedec.
     symmetry. apply map_id_iff.
     intros. apply term_subst_notin. contradict H.
     rewrite unionmap_in. now exists a.
 - auto.
 - namedec.
 - case eqbspec; cbn. namedec.
   intros. rewrite <- IHf. namedec.
Qed.

Lemma freevars_rename_subset3 x y f :
  Names.Subset (freevars f)
               (Names.add x (freevars (rename x y f))).
Proof.
 rewrite <- freevars_rename_subset2. namedec.
Qed.

(** Renaming in chain *)

Lemma rename_chain x y z f :
 RenOk y f ->
 rename y z (rename x y f) = rename x z f.
Proof.
 induction f; cbn; intros R; f_equal; auto.
 - rewrite !map_map.
   apply map_ext_in. intros. apply term_subst_chain.
   rewrite unionmap_in in R. contradict R. now exists a.
 - auto with set.
 - auto with set.
 - intros. f_equal. repeat case eqbspec; auto.
   namedec.
   intros. apply rename_notin. rewrite freevars_allvars. namedec.
   intros. apply IHf. namedec.
Qed.

(** Renaming at independent locations *)

Lemma rename_rename x y x' y' f :
 x<>y -> x<>y' -> x'<>y ->
 rename y y' (rename x x' f) = rename x x' (rename y y' f).
Proof.
 intros XY XY' YX'.
 induction f; cbn; f_equal; auto.
 - rewrite !map_map.
   apply map_ext. intros.
   rewrite term_subst_subst; simpl; auto with set.
   rewrite <-eqb_neq in YX'. now rewrite YX'.
 - intuition.
Qed.

(** Renaming twice at the same spot *)

Lemma rename_bis v z z' f :
  z <> v ->
  rename v z' (rename v z f) = rename v z f.
Proof.
 induction f; simpl; intros; f_equal; auto.
 - rewrite map_map. apply map_ext_iff. intros.
   apply term_subst_bis; auto.
 - case eqbspec; simpl; intuition.
Qed.

(** ALPHA EQUIVALENCE *)

(** A weaker but faster version of namedec *)

Ltac namedec0 :=
  repeat (rewrite ?Names.add_spec, ?Names.union_spec,
                  ?Names.remove_spec, ?Names.singleton_spec in *);
  intuition auto.

Ltac simpl_fresh vars H :=
 unfold vars in H; cbn in H;
 rewrite ?Names.add_spec, ?Names.union_spec in H;
 repeat (apply Decidable.not_or in H; destruct H as (?,H));
 clear vars H.

Ltac simpl_height :=
 match goal with
 | H : S _ < S _ |- _ =>
   apply Nat.succ_lt_mono in H; simpl_height
 | H : Nat.max _ _ < _ |- _ =>
   apply Nat.max_lub_lt_iff in H; destruct H; simpl_height
 | _ => idtac
 end.

Lemma height_ind (P : formula -> Prop) :
 (forall h, (forall f, height f < h -> P f) ->
            (forall f, height f < S h -> P f)) ->
 forall f, P f.
Proof.
 intros IH f.
 set (h := S (height f)).
 assert (LT : height f < h) by (cbn; auto with * ).
 clearbody h. revert f LT.
 induction h as [|h IHh]; [inversion 1|eauto].
Qed.

Lemma AEq_refl f :
 AlphaEq f f.
Proof.
 induction f as [h IH f LT] using height_ind.
 destruct f; cbn in *; simpl_height; auto.
 destruct (exist_fresh (allvars f)) as (z,Hz).
 apply AEqQu with (z:=z); auto with set.
Qed.

Lemma AEq_sym f f' :
 AlphaEq f f' -> AlphaEq f' f.
Proof.
 revert f'.
 induction f as [h IH f LT] using height_ind.
 destruct f, f'; cbn in *; simpl_height;
   try (inversion_clear 1; auto).
 apply AEqQu with (z:=z); auto with set.
Qed.

Lemma AEq_freevars f f' :
  AlphaEq f f' -> Names.Equal (freevars f) (freevars f').
Proof.
 induction 1; cbn; auto with set.
 revert IHAlphaEq.
 destruct (NamesP.In_dec v (freevars f)) as [E|E];
  destruct (NamesP.In_dec v' (freevars f')) as [E'|E'];
  try (rewrite (rename_notin v z f E));
  try (rewrite (rename_notin v' z f' E'));
  repeat (rewrite freevars_rename_in by auto with set);
  cbn;
  rewrite <-!freevars_allvars in H.
 - (* namedec should suffice but take ages ?! *)
   intros EQ x. specialize (EQ x). namedec.
 - intros EQ x. specialize (EQ x). namedec.
 - intros EQ x. specialize (EQ x). namedec.
 - namedec.
Qed.

(** An adhoc helper lemma for the next one. *)

Lemma AEq_rename_aux f f' x x' v z z0 :
  ~Names.In z (Names.union (Names.add x (allvars f))
                         (Names.add v (allvars f'))) ->
  ~Names.In z0 (Names.union (allvars f)
                          (allvars (rename x' z f'))) ->
  AlphaEq (rename x z0 f) (rename v z0 (rename x' z f')) ->
  ~Names.In x' (freevars f').
Proof.
 intros Hz Hz0 EQ IN.
 assert (RenOk z0 f) by auto with set.
 assert (RenOk z f') by auto with set.
 assert (z0 <> z).
 { contradict Hz0. subst z0.
   nameiff. right.
   rewrite <- freevars_allvars.
   rewrite freevars_rename_in; auto. namedec. }
 assert (NI : ~Names.In z (freevars (rename x z0 f))).
 { rewrite freevars_rename_subset.
   rewrite freevars_allvars. namedec. }
 apply AEq_freevars in EQ.
 rewrite EQ in NI.
 contradict NI.
 rewrite <- freevars_rename_subset2.
 rewrite freevars_rename_in; namedec.
Qed.

(* The crucial lemma, utterly technical for something so obvious *)

Lemma AEq_rename_any f f' x x' z z' :
  ~Names.In z (Names.union (allvars f) (allvars f')) ->
  ~Names.In z' (Names.union (allvars f) (allvars f')) ->
  AlphaEq (rename x z f) (rename x' z f') ->
  AlphaEq (rename x z' f) (rename x' z' f').
Proof.
 revert f' x x' z z'.
 induction f as [h IH f LT] using height_ind.
 destruct f, f'; intros x x' z z' Hz Hz'; cbn in *; simpl_height;
  try (inversion 1; auto; fail).
 - inversion 1; subst.
   assert (E : map (Term.subst x z') l = map (Term.subst x' z') l0).
   { injection (term_subst_rename x x' z z' (Fun "" l) (Fun "" l0)).
     auto. namedec0. namedec0. cbn; f_equal; auto. }
   now rewrite E.
 - inversion 1; eauto.
 - inversion 1; subst; constructor; eapply IH; eauto; namedec0.
 - repeat (case eqbspec; cbn).
   + trivial.
   + intros NE <-. inversion_clear 1.
     assert (~Names.In x' (freevars f')).
     { eapply AEq_rename_aux; eauto. }
     rewrite !(rename_notin x') in * by trivial.
     apply AEqQu with z0; auto.
   + intros <- NE. inversion_clear 1.
     assert (~Names.In x (freevars f)).
     { apply AEq_sym in H1.
       eapply AEq_rename_aux; eauto; namedec0. }
     rewrite !(rename_notin x) in * by trivial.
     apply AEqQu with z0; auto.
   + intros NE NE'. inversion_clear 1.

     (* Let's pick a suitably fresh variable z1 *)

     set (vars :=
            Names.add x (Names.add x' (Names.add z (Names.add z'
             (Names.unions
               [ allvars (rename x z f);
                allvars (rename x' z f');
                allvars f; allvars f']))))).
     destruct (exist_fresh vars) as (z1,Hz1).
     simpl_fresh vars Hz1.

     (* Let's use z1 instead of z0 in the main hyp *)

     apply IH with (z':=z1) in H1; [ | auto | auto | namedec0].
     clear H0 z0.

     (* Let's use z1 in the conclusion. *)

     apply AEqQu with z1; auto.
     rewrite !allvars_rename; cbn; namedec0.
     revert H1.

     (* We now need to swap the substitutions to
        change z' with z thanks to the IH. *)

     rewrite !(rename_rename x), !(rename_rename x');
       auto; try (namedec0;fail).
     apply IH; auto;
     rewrite !allvars_rename; cbn; namedec0.
Qed.

Lemma AEq_trans f1 f2 f3 :
 AlphaEq f1 f2 -> AlphaEq f2 f3 -> AlphaEq f1 f3.
Proof.
 revert f2 f3.
 induction f1 as [h IH f1 LT] using height_ind.
 destruct f1, f2, f3; cbn in *; simpl_height;
  inversion_clear 1; inversion_clear 1; eauto.
 set (vars :=
        Names.unions [ (allvars f1); (allvars f2); (allvars f3) ]).
 destruct (exist_fresh vars) as (z1,Hz1). simpl_fresh vars Hz1.
 apply AEq_rename_any with (z':=z1) in H1; [ |namedec|namedec].
 apply AEq_rename_any with (z':=z1) in H3; [ |namedec|namedec].
 apply AEqQu with z1; eauto. namedec.
Qed.

Instance AEq_equiv : Equivalence AlphaEq.
Proof.
 split; [exact AEq_refl| exact AEq_sym | exact AEq_trans].
Qed.

Lemma AEqQu_iff q v v' f f' z :
  ~Names.In z (Names.union (allvars f) (allvars f')) ->
  AlphaEq (Quant q v f) (Quant q v' f') <->
  AlphaEq (rename v z f) (rename v' z f').
Proof.
 intros NI.
 split.
 - inversion 1; subst. eapply AEq_rename_any; eauto.
 - now apply AEqQu.
Qed.

Lemma AEq_rename f f' :
 AlphaEq f f' ->
 forall x y,
 RenOk y f -> RenOk y f' ->
 AlphaEq (rename x y f) (rename x y f').
Proof.
 revert f'.
 induction f as [h IH f LT] using height_ind.
 destruct f, f'; intros EQ x y IS1 IS2; inversion_clear EQ;
  cbn in *; simpl_height; auto.
 - constructor; intuition.
 - rename v0 into v'.
   rename H0 into EQ.
   clear q; rename q0 into q.
   assert (RenOk z f) by auto with set.
   assert (RenOk z f') by auto with set.
   repeat (case eqbspec; cbn); intros; auto.
   + subst v; subst v'.
     apply AEqQu with z; auto.
   + subst v. clear IS1.
     rewrite rename_notin; [ apply AEqQu with z; auto | ].
     { case (eqbspec x z).
       - intros ->; rewrite freevars_allvars; namedec.
       - intros NE.
         apply AEq_freevars in EQ.
         rewrite (freevars_rename_subset3 v' z), <- EQ.
         rewrite freevars_rename_subset. namedec. }
   + subst v'. clear IS2.
     rewrite rename_notin; [ apply AEqQu with z; auto | ].
     { case (eqbspec x z).
       - intros ->; rewrite freevars_allvars; namedec.
       - intros NE.
         apply AEq_freevars in EQ.
         rewrite (freevars_rename_subset3 v z), EQ.
         rewrite freevars_rename_subset. namedec. }
   + set (vars :=
            Names.add x (Names.add v (Names.add v' (Names.add y
              (Names.unions [allvars f; allvars f']))))).
     destruct (exist_fresh vars) as (z',Hz').
     simpl_fresh vars Hz'.
     apply AEq_rename_any with (z' := z') in EQ; [ |namedec|namedec].
     clear z H H0 H1.
     apply AEqQu with z'; [rewrite 2 allvars_rename; namedec|].
     rewrite 2 (rename_rename x) by auto with set.
     apply IH; auto; rewrite allvars_rename; namedec.
Qed.

Lemma AEqQu_nosubst f f' q v :
 AlphaEq f f' -> AlphaEq (Quant q v f) (Quant q v f').
Proof.
 intros.
 set (vars := Names.union (allvars f) (allvars f')).
 destruct (exist_fresh vars) as (z,Hz).
 apply AEqQu with z. exact Hz.
 apply AEq_rename; auto with set.
Qed.

Lemma AEqQu_rename f q v z :
 RenOk z f ->
 AlphaEq (Quant q v f) (Quant q z (rename v z f)).
Proof.
 intros R.
 set (vars := Names.add z (Names.add v (allvars f))).
 destruct (exist_fresh vars) as (z',Hz').
 apply AEqQu with z'.
 - rewrite allvars_rename. namedec.
 - case (eqbspec v z).
   + intros ->.
     rewrite (rename_notin z z); auto. reflexivity.
     rewrite freevars_allvars; auto.
   + intros NE.
     rewrite rename_chain; auto with set. reflexivity.
Qed.

Lemma AlphaEq_equiv f f' :
  αeq f f' = true <-> AlphaEq f f'.
Proof.
 unfold αeq.
 set (h := S _).
 assert (LT : height f < h) by (unfold h; auto with *).
 assert (LT' : height f' < h) by (unfold h; auto with *).
 clearbody h. revert f f' LT LT'.
 induction h as [|h IH]; [inversion 1|].
 destruct f, f'; simpl; intros LT LT'; simpl_height; try easy.
 - rewrite lazy_andb_iff, !eqb_eq.
   split.
   + now intros (<-,<-).
   + now inversion_clear 1.
 - rewrite IH by auto. split; auto. inversion_clear 1; auto.
 - rewrite !lazy_andb_iff, !eqb_eq, 2 IH by auto.
   split.
   + intros ((<-,?),?); auto.
   + now inversion_clear 1.
 - setfresh vars z Hz.
   rewrite !lazy_andb_iff, !eqb_eq, IH by auto with set.
   split.
   + intros (<-,?). apply AEqQu with z; auto with set.
   + inversion_clear 1. split; trivial.
     apply AEq_rename_any with z0; auto. namedec.
Qed.
