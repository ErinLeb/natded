
(** Alternative definitions of substs and alpha for named formulas *)

Require Import RelationClasses Arith Omega Defs Proofs Nam.
Import ListNotations.
Import Nam.Form.
Import Nam.Form.Alt.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Local Coercion Var : variable >-> term.

(** Basic results about [Form.Alt.subst] *)

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
   repeat rewrite IHh; auto.
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
 destruct f; cbn -[fresh_var]; intros; simpl_height; f_equal; auto.
 case eqbspec; intros; auto.
 destruct negb eqn:E; f_equal; auto.
 rewrite (IHh h' v0) by auto.
 apply IHh; rewrite hsubst_height; auto.
Qed.

Lemma hsubst_subst v t f h :
  height f < h ->
  hsubst h v t f = subst v t f.
Proof.
 intros. apply hsubst_indep; auto with *.
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
      if negb (Vars.mem v out_vars) then
        Quant q v (subst x t f')
      else
        let z := fresh_var (vars_unions [allvars f; out_vars; Vars.singleton x])
      in
        Quant q z (subst x t (subst v z f'))
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
 - unfold subst. rewrite hsubst_height; auto with *.
Qed.

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
  | Quant _ x f => v = x \/ (~Vars.In x (Term.vars t)
                             /\ IsSimple v t f)
  end.

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
| SubQu2 q f f' x : x<>v -> ~Vars.In x (Term.vars t) ->
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
 - destruct f; cbn -[fresh_var];
   intros Hf IS; simpl_height; auto.
   + intuition.
   + case eqbspec.
     * intros ->; auto.
     * intros NE.
       destruct IS as [->|(NI,SI)]; [easy|].
       rewrite vars_mem_false; cbn; auto.
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
   rewrite vars_mem_false; auto.
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

(** A sufficient condition for simplicity: *)

Lemma noninter_IsSimple x t f :
  Vars.Empty (Vars.inter (allvars f) (Term.vars t)) -> IsSimple x t f.
Proof.
 induction f; cbn in *; auto.
 intros E; split; (apply IHf1 || apply IHf2); varsdec.
 intros E.
 case (eqbspec v x).
 - now left.
 - intros NE. right; split; try apply IHf; varsdec.
Qed.

(** Same, when t is a variable *)

Lemma notin_IsSimple (x z:variable) f :
  ~Vars.In z (allvars f) -> IsSimple x z f.
Proof.
 intros. apply noninter_IsSimple. cbn. varsdec.
Qed.

Hint Resolve notin_IsSimple.

(** No-op substitutions *)

Lemma term_subst_notin x u t :
 ~Vars.In x (Term.vars t) ->
 Term.subst x u t = t.
Proof.
 induction t as [v|f a IH] using term_ind'; cbn.
 - case eqbspec; auto. varsdec.
 - intros NI. f_equal. apply map_id_iff.
   intros t Ht. apply IH; auto. rewrite vars_unionmap_in in NI.
   contradict NI. now exists t.
Qed.

Lemma partialsubst_notin x t f :
 ~Vars.In x (freevars f) ->
 partialsubst x t f = f.
Proof.
 induction f; cbn; intros NI; f_equal; auto with set.
 - apply map_id_iff. intros a Ha. apply term_subst_notin.
   rewrite vars_unionmap_in in NI. contradict NI. now exists a.
 - case eqbspec; cbn; auto.
   intros NE. case Vars.mem; f_equal; auto with set.
Qed.

(** Free variables and substitutions *)

Lemma freevars_allvars f : Vars.Subset (freevars f) (allvars f).
Proof.
 induction f; cbn; auto with set.
Qed.

Lemma term_vars_subst x u t :
 Vars.Subset (Term.vars (Term.subst x u t))
             (Vars.union (Vars.remove x (Term.vars t)) (Term.vars u)).
Proof.
 induction t using term_ind'; cbn.
 - case eqbspec; cbn; auto with set.
 - intros v. rewrite vars_unionmap_in.
   intros (a & IN & IN'). rewrite in_map_iff in IN'.
   destruct IN' as (b & <- & IN').
   apply H in IN; trivial.
   revert IN.
   VarsF.set_iff. rewrite vars_unionmap_in in *.
   intros [(U,V)|W].
   + left. split; auto. now exists b.
   + now right.
Qed.

Lemma term_vars_subst_in x u t :
 Vars.In x (Term.vars t) ->
 Vars.Equal (Term.vars (Term.subst x u t))
            (Vars.union (Vars.remove x (Term.vars t)) (Term.vars u)).
Proof.
 revert t.
 fix IH 1; destruct t; cbn.
 - case eqbspec; cbn; auto with set.
 - revert l.
   fix IH' 1; destruct l; cbn.
   + varsdec.
   + destruct (VarsP.In_dec x (Term.vars t)) as [E|E];
     destruct (VarsP.In_dec x (vars_unionmap Term.vars l)) as [E'|E'].
     * intros _.
       fold (Term.subst x u t). rewrite (IH t E).
       rewrite (IH' l E'). varsdec.
     * intros _.
       assert (E'' : map (Term.substs [(x, u)]) l = l).
       { apply map_id_iff. intros a Ha.
         apply term_subst_notin. contradict E'.
         rewrite vars_unionmap_in. now exists a. }
       change Vars.elt with variable in *.
       rewrite E''.
       fold (Term.subst x u t). rewrite (IH t E).
       varsdec.
     * intros _.
       fold (Term.subst x u t).
       rewrite (term_subst_notin x u t) by trivial.
       rewrite (IH' l E'). varsdec.
     * VarsF.set_iff. tauto.
Qed.

Lemma term_vars_subst_in' x u t :
 Vars.In x (Term.vars t) ->
 Vars.Subset (Term.vars u) (Term.vars (Term.subst x u t)).
Proof.
 induction t using term_ind'; cbn.
 - case eqbspec; cbn; auto with set.
 - intros IN v Hv. rewrite vars_unionmap_in in *.
   destruct IN as (a & Ha & IN).
   exists (Term.subst x u a); split; auto using in_map.
   now apply (H a IN Ha).
Qed.

Lemma allvars_partialsubst x t f :
 Vars.Subset (allvars (partialsubst x t f))
             (Vars.union (allvars f) (Term.vars t)).
Proof.
 induction f; cbn; try varsdec.
 - generalize (term_vars_subst x t (Fun "" l)). cbn. varsdec.
 - destruct orb; cbn; varsdec.
Qed.

Lemma allvars_partialsubst_2 x t f :
 IsSimple x t f ->
 Vars.In x (freevars f) ->
 Vars.Subset (Term.vars t) (allvars (partialsubst x t f)).
Proof.
 induction f; cbn; intros IS; try varsdec.
 - apply (term_vars_subst_in' x t (Fun "" l)).
 - auto.
 - VarsF.set_iff. destruct IS as (IS1,IS2).
   intros [IN|IN].
   rewrite (IHf1 IS1 IN). varsdec.
   rewrite (IHf2 IS2 IN). varsdec.
 - case eqbspec; cbn. varsdec.
   VarsF.set_iff. intros NE (IN,_).
   destruct IS as [->|(NI,IS)]; [easy|].
   specialize (IHf IS IN).
   rewrite vars_mem_false by trivial. cbn. varsdec.
Qed.

Lemma freevars_partialsubst_in x t f :
 IsSimple x t f ->
 Vars.In x (freevars f) ->
 Vars.Equal (freevars (partialsubst x t f))
            (Vars.union (Vars.remove x (freevars f)) (Term.vars t)).
Proof.
 induction f; cbn; intros IS IN.
 - varsdec.
 - varsdec.
 - apply (term_vars_subst_in x t (Fun "" l)); auto.
 - auto.
 - destruct IS as (IS1,IS2).
   rewrite Vars.union_spec in IN.
   destruct (VarsP.In_dec x (freevars f1)) as [IN1|IN1];
    destruct (VarsP.In_dec x (freevars f2)) as [IN2|IN2];
    try rewrite (IHf1 IS1 IN1); try rewrite (IHf2 IS2 IN2);
    try rewrite (partialsubst_notin x t f2) by trivial;
    try rewrite (partialsubst_notin x t f1) by trivial;
    varsdec.
 - case eqbspec; cbn. varsdec.
   intros. destruct IS as [->|(NI,IS)]; [easy|].
   rewrite vars_mem_false by trivial.
   rewrite (IHf IS); varsdec.
Qed.


Lemma freevars_partialsubst_subset x t f :
 IsSimple x t f ->
 Vars.Subset (freevars (partialsubst x t f))
             (Vars.union (Vars.remove x (freevars f)) (Term.vars t)).
Proof.
 induction f; cbn; intros IS.
 - varsdec.
 - varsdec.
 - apply (term_vars_subst x t (Fun "" l)).
 - auto.
 - destruct IS as (IS1,IS2).
   specialize (IHf1 IS1). specialize (IHf2 IS2). varsdec.
 - case eqbspec; cbn. varsdec.
   intros. destruct IS as [->|(NI,IS)]; [easy|].
   specialize (IHf IS).
   rewrite vars_mem_false by trivial.
   cbn. varsdec.
Qed.

Lemma freevars_partialsubst_subset2 x t f :
  IsSimple x t f ->
  Vars.Subset (freevars f)
              (Vars.add x (freevars (partialsubst x t f))).
Proof.
 intros NE.
 destruct (VarsP.In_dec x (freevars f)).
 - rewrite freevars_partialsubst_in; auto with set.
 - rewrite partialsubst_notin; auto with set.
Qed.

Lemma freevars_partialsubst_subset3 x t f :
  IsSimple x t f ->
  Vars.Subset (Vars.remove x (freevars f))
              (freevars (partialsubst x t f)).
Proof.
 intros NE.
 rewrite (freevars_partialsubst_subset2 x t f); auto with set.
Qed.

(** Swapping substitutions *)

Lemma term_subst_subst x u y v t :
 x<>y -> ~Vars.In x (Term.vars v) ->
  Term.subst y v (Term.subst x u t) =
  Term.subst x (Term.subst y v u) (Term.subst y v t).
Proof.
 intros NE NI.
 induction t using term_ind'; cbn.
 - case eqbspec; [intros ->|intros NE'].
   + change Vars.elt with variable in *.
     rewrite <- eqb_neq in NE. rewrite NE. cbn.
     now rewrite eqb_refl.
   + case eqbspec; [intros ->|intros NE''].
     * cbn. rewrite eqb_refl.
       symmetry. now apply term_subst_notin.
     * cbn. rewrite <-eqb_neq in NE',NE''. now rewrite NE', NE''.
 - f_equal.
   rewrite !map_map.
   apply map_ext_in.
   auto.
Qed.

Lemma partialsubst_partialsubst x y u v f :
 x<>y -> ~Vars.In x (Term.vars v) ->
 IsSimple x u f ->
 IsSimple y v f ->
 partialsubst y v (partialsubst x u f) =
 partialsubst x (Term.subst y v u) (partialsubst y v f).
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
     assert (~Vars.In v0 (Term.vars (Term.subst y v u))).
     { rewrite term_vars_subst. varsdec. }
     repeat (rewrite vars_mem_false by trivial).
     auto.
Qed.

(** ALPHA EQUIVALENCE *)

(** An inductive definition, based on [partialsubst].
    We'll show later that it is equivalent to [Form.AlphaEq]
    and [Form.Alt.AlphaEq]. *)

Module Ind.

Inductive AlphaEq : formula -> formula -> Prop :=
| AEqTr : AlphaEq True True
| AEqFa : AlphaEq False False
| AEqPred p l : AlphaEq (Pred p l) (Pred p l)
| AEqNot f f' : AlphaEq f f' -> AlphaEq (Not f) (Not f')
| AEqOp o f1 f2 f1' f2' :
  AlphaEq f1 f1' -> AlphaEq f2 f2' ->
  AlphaEq (Op o f1 f2) (Op o f1' f2')
| AEqQu q v v' f f' (z:variable) :
  ~Vars.In z (Vars.union (allvars f) (allvars f')) ->
  AlphaEq (partialsubst v z f) (partialsubst v' z f') ->
  AlphaEq (Quant q v f) (Quant q v' f').

End Ind.
Import Ind.
Hint Constructors AlphaEq.

(** A weaker but faster version of varsdec *)

Ltac varsdec0 :=
  repeat (rewrite ?Vars.add_spec, ?Vars.union_spec,
                  ?Vars.remove_spec, ?Vars.singleton_spec in *);
  intuition auto.

Ltac simpl_fresh vars H :=
 unfold vars in H; cbn in H;
 rewrite ?Vars.add_spec, ?Vars.union_spec in H;
 repeat (apply Decidable.not_or in H; destruct H as (?,H));
 clear vars H.

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
 destruct (get_fresh_var (allvars f)) as (z,Hz).
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
  AlphaEq f f' -> Vars.Equal (freevars f) (freevars f').
Proof.
 induction 1; cbn; auto with set.
 revert IHAlphaEq.
 destruct (VarsP.In_dec v (freevars f)) as [E|E];
  destruct (VarsP.In_dec v' (freevars f')) as [E'|E'];
  try (rewrite (partialsubst_notin v z f E));
  try (rewrite (partialsubst_notin v' z f' E'));
  repeat (rewrite freevars_partialsubst_in by auto with set);
  cbn;
  rewrite <-!freevars_allvars in H.
 - (* varsdec should suffice but take ages ?! *)
   intros EQ x. specialize (EQ x). varsdec.
 - intros EQ x. specialize (EQ x). varsdec.
 - intros EQ x. specialize (EQ x). varsdec.
 - varsdec.
Qed.

Lemma term_subst_rename (x x' z z' : variable) t t':
  ~Vars.In z (Vars.union (Term.vars t) (Term.vars t')) ->
  ~Vars.In z' (Vars.union (Term.vars t) (Term.vars t')) ->
  Term.subst x z t = Term.subst x' z t'  ->
  Term.subst x z' t = Term.subst x' z' t'.
Proof.
 revert t t'.
 fix IH 1. destruct t, t'; intros Hz Hz'; cbn in *; try easy.
 - do 2 case eqbspec; intros H H'; subst; intros [=]; varsdec.
 - case eqbspec; intros _ [=].
 - case eqbspec; intros _ [=].
 - intros [= <- E]. f_equal. clear f.
   revert l l0 Hz Hz' E.
   fix IH' 1. destruct l, l0; intros Hz Hz'; cbn in *; try easy.
   intros [= E E']. f_equal.
   + apply IH; auto. varsdec. varsdec.
   + apply IH'; auto. varsdec. varsdec.
Qed.

(** An adhoc helper lemma for the next one. *)

Lemma AEq_rename_aux f f' (x x' v z z0 : variable) :
  ~Vars.In z (Vars.union (Vars.add x (allvars f))
                         (Vars.add v (allvars f'))) ->
  ~Vars.In z0 (Vars.union (allvars f)
                          (allvars (partialsubst x' z f'))) ->
  AlphaEq (partialsubst x z0 f)
          (partialsubst v z0 (partialsubst x' z f')) ->
  ~Vars.In x' (freevars f').
Proof.
 intros Hz Hz0 EQ IN.
 assert (IsSimple x z0 f) by auto with set.
 assert (IsSimple x' z f') by auto with set.
 assert (z0 <> z).
 { contradict Hz0. subst z0.
   VarsF.set_iff. right.
   rewrite <- freevars_allvars.
   rewrite freevars_partialsubst_in; auto. cbn. varsdec. }
 assert (NI : ~Vars.In z (freevars (partialsubst x z0 f))).
 { rewrite freevars_partialsubst_subset; auto. cbn.
   rewrite freevars_allvars. varsdec. }
 apply AEq_freevars in EQ.
 rewrite EQ in NI.
 contradict NI.
 rewrite <- freevars_partialsubst_subset3 by auto with set.
 rewrite freevars_partialsubst_in; auto with set.
Qed.

(* The crucial lemma, utterly technical for something so obvious *)

Lemma AEq_rename_any f f' (x x' z z' : variable) :
  ~Vars.In z (Vars.union (allvars f) (allvars f')) ->
  ~Vars.In z' (Vars.union (allvars f) (allvars f')) ->
  AlphaEq (partialsubst x z f) (partialsubst x' z f') ->
  AlphaEq (partialsubst x z' f) (partialsubst x' z' f').
Proof.
 revert f' x x' z z'.
 induction f as [h IH f LT] using height_ind.
 destruct f, f'; intros x x' z z' Hz Hz'; cbn in *; simpl_height;
  try (inversion 1; auto; fail).
 - inversion 1; subst.
   assert (E : map (Term.subst x z') l =
                map (Term.subst x' z') l0).
   { injection (term_subst_rename x x' z z' (Fun "" l) (Fun "" l0)).
     auto. varsdec0. varsdec0. cbn; f_equal; auto. }
   now rewrite E.
 - inversion 1; eauto.
 - inversion 1; subst; constructor; eapply IH; eauto; varsdec0.
 - rewrite !vars_mem_false by varsdec0.
   repeat (case eqbspec; cbn).
   + trivial.
   + intros NE <-. inversion_clear 1.
     assert (~Vars.In x' (freevars f')).
     { eapply AEq_rename_aux; eauto. }
     rewrite !(partialsubst_notin x') in * by trivial.
     apply AEqQu with z0; auto.
   + intros <- NE. inversion_clear 1.
     assert (~Vars.In x (freevars f)).
     { apply AEq_sym in H1.
       eapply AEq_rename_aux; eauto; varsdec0. }
     rewrite !(partialsubst_notin x) in * by trivial.
     apply AEqQu with z0; auto.
   + intros NE NE'. inversion_clear 1.

     (* Let's pick a suitably fresh variable z1 *)

     set (vars :=
            Vars.add x (Vars.add x' (Vars.add z (Vars.add z'
             (vars_unions
               [ allvars (partialsubst x z f);
                allvars (partialsubst x' z f');
                allvars f; allvars f']))))).
     destruct (get_fresh_var vars) as (z1,Hz1).
     simpl_fresh vars Hz1.

     (* Let's use z1 instead of z0 in the main hyp *)

     apply IH with (z':=z1) in H1; [ | auto | auto | varsdec0].
     clear H0 z0.

     (* Let's use z1 in the conclusion. *)

     apply AEqQu with z1; auto.
     rewrite !allvars_partialsubst; cbn; varsdec0.
     revert H1.

     (* We now need to swap the substitutions to
        change z' with z thanks to the IH. *)

     rewrite !(partialsubst_partialsubst x),
             !(partialsubst_partialsubst x'); auto;
     rewrite ?term_subst_notin; cbn;
     rewrite ?Vars.singleton_spec; auto;
     try apply notin_IsSimple; try (varsdec0;fail).

     apply IH; auto;
     rewrite !allvars_partialsubst; cbn; varsdec0.
Qed.

Lemma AEq_trans f1 f2 f3 :
 AlphaEq f1 f2 -> AlphaEq f2 f3 -> AlphaEq f1 f3.
Proof.
 revert f2 f3.
 induction f1 as [h IH f1 LT] using height_ind.
 destruct f1, f2, f3; cbn in *; simpl_height;
  inversion_clear 1; inversion_clear 1; eauto.
 set (vars :=
        vars_unions [ (allvars f1); (allvars f2); (allvars f3) ]).
 destruct (get_fresh_var vars) as (z1,Hz1). simpl_fresh vars Hz1.
 apply AEq_rename_any with (z':=z1) in H1; [ |varsdec|varsdec].
 apply AEq_rename_any with (z':=z1) in H3; [ |varsdec|varsdec].
 apply AEqQu with z1; eauto. varsdec.
Qed.

Instance AEq_equiv : Equivalence AlphaEq.
Proof.
 split; [exact AEq_refl| exact AEq_sym | exact AEq_trans].
Qed.

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
     rewrite vars_mem_false by trivial.
     assert (~Vars.In x (freevars f')).
     { case (eqbspec x z).
       - intros ->; rewrite freevars_allvars; varsdec.
       - intros NE.
         apply AEq_freevars in EQ.
         rewrite (freevars_partialsubst_subset2 v' z) by auto.
         rewrite <- EQ.
         rewrite freevars_partialsubst_subset by auto.
         cbn. clear EQ H. varsdec. }
     rewrite partialsubst_notin; auto.
     apply AEqQu with z; auto.
   + subst v'. clear IS2.
     destruct IS1 as [->|(NI,IS1)]; [easy|].
     rewrite vars_mem_false by trivial.
     assert (~Vars.In x (freevars f)).
     { case (eqbspec x z).
       - intros ->; rewrite freevars_allvars; varsdec.
       - intros NE.
         apply AEq_freevars in EQ.
         rewrite (freevars_partialsubst_subset2 v z) by auto.
         rewrite EQ.
         rewrite freevars_partialsubst_subset by auto.
         cbn. clear EQ H. varsdec. }
     rewrite partialsubst_notin; auto.
     apply AEqQu with z; auto.
   + destruct IS1 as [->|(NI1,IS1)]; [easy|].
     destruct IS2 as [->|(NI2,IS2)]; [easy|].
     rewrite !vars_mem_false by trivial.
     set (vars :=
            Vars.add x (Vars.add v (Vars.add v'
              (vars_unions
                 [ Term.vars t; allvars f; allvars f'])))).
     destruct (get_fresh_var vars) as (z',Hz').
     simpl_fresh vars Hz'.
     apply AEq_rename_any with (z' := z') in EQ;
       [ |varsdec|varsdec].
     clear z H H0 H1.
     apply AEqQu with z';
       [rewrite 2 allvars_partialsubst; varsdec|].
     rewrite 2 (partialsubst_partialsubst x); auto;
     try (rewrite !term_subst_notin by varsdec);
     try (apply IH; auto); cbn; try varsdec;
     try apply IsSimple_partialsubst; auto with set.
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

Lemma AEqQu_nosubst f f' q v :
 AlphaEq f f' -> AlphaEq (Quant q v f) (Quant q v f').
Proof.
 intros.
 set (vars := Vars.union (allvars f) (allvars f')).
 destruct (get_fresh_var vars) as (z,Hz).
 apply AEqQu with z. exact Hz.
 apply AEq_partialsubst; auto with set.
Qed.

Lemma AEqQu_rename0 f q (v z : variable) :
 IsSimple v z f -> ~Vars.In z (freevars f) ->
 AlphaEq (Quant q v f) (Quant q z (partialsubst v z f)).
Proof.
 intros IS NI.
 set (vars := Vars.add z (Vars.add v (allvars f))).
 destruct (get_fresh_var vars) as (z',Hz').
 apply AEqQu with z'.
 - rewrite allvars_partialsubst. cbn. varsdec.
 - case (eqbspec v z).
   + intros ->.
     rewrite (partialsubst_notin z z); auto. reflexivity.
   + intros NE.
     rewrite partialsubst_partialsubst; cbn; auto with set.
     now rewrite eqb_refl, (partialsubst_notin z).
Qed.

(** Same, with weaker but clearer precondition *)

Lemma AEqQu_rename f q (v z : variable) :
 ~Vars.In z (allvars f) ->
 AlphaEq (Quant q v f) (Quant q z (partialsubst v z f)).
Proof.
 intros NI. apply AEqQu_rename0; auto with set.
 rewrite freevars_allvars; varsdec.
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
  ~Vars.In v (Term.vars t) ->
  Subst x t f f' ->
  Subst x t (Quant q v f) (Quant q v f').
Proof.
  intros NE NI (f0 & EQ & IS).
  exists (Quant q v f0). auto using AEqQu_nosubst.
Qed.

Lemma Subst_Qu3 x t q (v z : variable) f f' g :
  x <> v ->
  ~Vars.In z (freevars f) ->
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
  intros x t [ ] LT; cbn -[fresh_var] in *; simpl_height.
 - apply Subst_True.
 - apply Subst_False.
 - apply Subst_Pred.
 - apply Subst_Not; auto.
 - apply Subst_Op; auto.
 - set (vars := Vars.union _ _).
   assert (Hz := fresh_var_ok vars).
   set (z := fresh_var _) in *. clearbody z.
   case eqbspec.
   + intros ->. apply Subst_Qu1.
   + intros NE.
     destruct (Vars.mem v (Term.vars t)) eqn:IN; cbn - [fresh_var].
     * clear IN.
       apply Subst_Qu3 with (hsubst h v z f); auto.
       { rewrite freevars_allvars. varsdec. }
       { apply Subst_Qu2; auto; try varsdec.
         apply IH. now rewrite hsubst_height. }
     * apply Subst_Qu2; auto.
       rewrite <- Vars.mem_spec. now rewrite IN.
Qed.

Lemma Subst_exists x t f : exists f', Subst x t f f'.
Proof.
 exists (subst x t f). apply Subst_subst.
Qed.

Lemma AlphaEq_equiv f f' :
  Alt.AlphaEq f f' <-> Ind.AlphaEq f f'.
Proof.
 unfold Alt.AlphaEq.
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
 - set (vars := Vars.union _ _).
   assert (Hz := fresh_var_ok vars).
   set (z := fresh_var vars) in *. clearbody z.
   rewrite <- !partialsubst_subst, !lazy_andb_iff, !eqb_eq, IH
     by auto with set.
   split.
   + intros (<-,?). apply AEqQu with z; auto with set.
   + inversion_clear 1. split; trivial.
     apply AEq_rename_any with z0; auto. varsdec.
Qed.

Lemma Subst_compat' x t f1 f2 f1' :
 AlphaEq f1 f2 -> Subst x t f1 f1' ->
 exists f2',  Subst x t f2 f2' /\ AlphaEq f1' f2'.
Proof.
 intros EQ SU.
 exists (subst x t f2).
 split. apply Subst_subst.
 eapply Subst_compat; eauto. apply Subst_subst.
Qed.

Require Import Morphisms RelationClasses.

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

Lemma subst_Qu1 x t q f :
 subst x t (Quant q x f) = Quant q x f.
Proof.
 rewrite subst_eqn. now rewrite eqb_refl.
Qed.
