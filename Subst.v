
(** * Properties of substitutions for named formulas *)

(** The NatDed development, Pierre Letouzey, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Nam.
Import ListNotations.
Import Nam.Form.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Implicit Types x y z v : variable.

Lemma freevars_allvars f : Names.Subset (freevars f) (allvars f).
Proof.
 induction f; cbn; auto with set.
Qed.

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

(** RENAMING *)

(** For [rename x y f] to be meaningful, we ask that [y] isn't
    in [allvars f]. Actually, some simple properties over [rename]
    may even hold without this precondition. *)

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

(** Renaming in chain *)

Lemma rename_chain x y z f :
 ~Names.In y (allvars f) ->
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

(** FORMULA SUBSTITUTION *)

Ltac simpl_height :=
 match goal with
 | H : S _ < S _ |- _ =>
   apply Nat.succ_lt_mono in H; simpl_height
 | H : Nat.max _ _ < _ |- _ =>
   apply Nat.max_lub_lt_iff in H; destruct H; simpl_height
 | _ => idtac
 end.

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

(** Places where [subst] and [rename] do agree *)

Lemma rename_subst x y f :
  ~Names.In y (allvars f) -> rename x y f = subst x (Var y) f.
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
