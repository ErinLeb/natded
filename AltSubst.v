
(** * An simultaneous definition of substitution for named formulas *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Nam Alpha Equiv Meta.
Import ListNotations.
Import Nam.Form.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Module Subst.

Definition t := list (variable * term).

Definition invars (sub : t) :=
  List.fold_right (fun p vs => Names.add (fst p) vs) Names.empty sub.

Definition outvars (sub : t) :=
  Names.unionmap (fun '(_,t) => Term.vars t) sub.

Definition vars (sub : t) :=
  Names.union (invars sub) (outvars sub).

End Subst.

Module Alt.

(** Term substitution *)

Fixpoint term_substs (sub:Subst.t) t :=
  match t with
  | Var v => list_assoc_dft v sub t
  | Fun f args => Fun f (List.map (term_substs sub) args)
  end.

Definition term_subst x u t := term_substs [(x,u)] t.

(** Simultaneous substitution of many variables in a term.
    Capture of bounded variables is correctly handled. *)

Fixpoint substs (sub : Subst.t) f :=
 match f with
  | True | False => f
  | Pred p args => Pred p (List.map (term_substs sub) args)
  | Not f => Not (substs sub f)
  | Op o f f' => Op o (substs sub f) (substs sub f')
  | Quant q v f' =>
    let sub := list_unassoc v sub in
    let out_vars := Subst.outvars sub in
    if negb (Names.mem v out_vars) then
      Quant q v (substs sub f')
    else
      (* variable capture : we change v into a fresh variable first *)
      let z := fresh (Names.unions [allvars f; out_vars; Subst.invars sub])
      in
      Quant q z (substs ((v,Var z)::sub) f')
 end.

(** Substitution of a variable in a term :
    in [t], [v] is replaced by [u] *)

Definition subst v t f := substs [(v,t)] f.

(** Alpha equivalence *)

Fixpoint αeq_gen sub1 f1 sub2 f2 :=
  match f1, f2 with
  | True, True | False, False => true
  | Pred p1 args1, Pred p2 args2 =>
     (p1 =? p2) &&&
      (List.map (term_substs sub1) args1 =?
       List.map (term_substs sub2) args2)
  | Not f1, Not f2 => αeq_gen sub1 f1 sub2 f2
  | Op o1 f1 f1', Op o2 f2 f2' =>
    (o1 =? o2) &&&
    αeq_gen sub1 f1 sub2 f2 &&&
    αeq_gen sub1 f1' sub2 f2'
  | Quant q1 v1 f1', Quant q2 v2 f2' =>
    (q1 =? q2) &&&
    (let z := fresh
                (Names.unions
                   [allvars f1; Subst.vars sub1; allvars f2; Subst.vars sub2])
     in
     αeq_gen ((v1,Var z)::sub1) f1' ((v2,Var z)::sub2) f2')
  | _,_ => false
  end.

Definition αeq f1 f2 := αeq_gen [] f1 [] f2.

Definition AlphaEq f1 f2 := αeq f1 f2 = true.

End Alt.

(** Properties of [Subst.invars] and [Subst.outvars] *)

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
 Names.Subset (Term.vars (Alt.term_substs h t))
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
 Names.Subset (freevars (Alt.substs h f))
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

(** [Term.substs] may do nothing *)

Lemma term_substs_notin h t :
 Names.Empty (Names.inter (Term.vars t) (Subst.invars h)) ->
 Alt.term_substs h t = t.
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

(** ALPHA EQUIVALENCE *)

(** Let's prove that [Alt.αeq] is the same as [Nam.Form.αeq].
    We do that by showing that alpha-equivalent formulas are the
    ones that are equal via [nam2mix]. *)

(** The invariant used during the proof *)

Module AltAlphaInvariant.

Inductive Inv (vars:Names.t) : Subst.t -> Subst.t -> Prop :=
 | InvNil : Inv vars [] []
 | InvCons v v' z sub sub' :
   Inv vars sub sub' ->
   ~Names.In z vars ->
   ~Names.In z (Subst.vars sub) ->
   ~Names.In z (Subst.vars sub') ->
   Inv vars ((v,Var z)::sub) ((v',Var z)::sub').

End AltAlphaInvariant.
Import AltAlphaInvariant.

Hint Constructors Inv.

Lemma Inv_sym vars sub sub' :
 Inv vars sub sub' -> Inv vars sub' sub.
Proof.
 induction 1; auto.
Qed.

Lemma Inv_notIn sub sub' vars v :
 Inv vars sub sub' ->
  ~(Names.In v vars /\ Names.In v (Subst.outvars sub)).
Proof.
 induction 1; unfold Subst.vars in *; simpl; namedec.
Qed.

Lemma Inv_weak sub sub' vars vars' :
  Names.Subset vars' vars -> Inv vars sub sub' -> Inv vars' sub sub'.
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
  list_assoc v sub = Some (Var z) -> Names.In z (Subst.outvars sub).
Proof.
 induction sub as [|(v',t) sub IH]; try easy.
 simpl.
 case eqbspec.
 - intros <- [= ->]. simpl. namedec.
 - intros _ E. apply IH in E. simpl. namedec.
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
   unfold Subst.vars in *. namedec.
 - intros <- NE E [= <-]. apply list_assoc_some_in in E.
   unfold Subst.vars in *. namedec.
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
 Inv (Names.union (Term.vars t) (Term.vars t')) sub sub' ->
 Alt.term_substs sub t = Alt.term_substs sub' t' <->
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
       destruct (Inv_notIn _ _ _ v' inv). namedec.
     * intros <-.
       apply list_assoc_some_in in E'.
       apply Inv_sym in inv.
       destruct (Inv_notIn _ _ _ v inv). namedec.
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
     * apply IH; auto. eapply Inv_weak; eauto. namedec.
     * apply IH'; auto. eapply Inv_weak; eauto. namedec.
   + intros [= <- E]. f_equal.
     simpl in inv.
     clear f. revert a a' E inv.
     fix IH' 1. destruct a as [|t a], a' as [|t' a']; try easy.
     simpl.
     intros [= E E'] inv. f_equal.
     * apply IH; auto. eapply Inv_weak; eauto. namedec.
     * apply IH'; auto. eapply Inv_weak; eauto. namedec.
Qed.

Lemma term_substs_nil t :
 Alt.term_substs [] t = t.
Proof.
 induction t using term_ind'; simpl; f_equal; auto.
 apply map_id_iff; auto.
Qed.

Lemma substs_nil f :
 Alt.substs [] f = f.
Proof.
 induction f; cbn - [fresh]; f_equal; auto.
 apply map_id_iff. intros a _. apply term_substs_nil.
Qed.

Lemma nam2mix_term_inj t t' :
 nam2mix_term [] t = nam2mix_term [] t' <-> t = t'.
Proof.
 split; [|now intros ->].
 rewrite <- (nam2mix_term_ok [] []), !term_substs_nil; auto.
Qed.

Lemma nam2mix_canonical_gen sub sub' f f' :
 Inv (Names.union (allvars f) (allvars f')) sub sub' ->
 Alt.αeq_gen sub f sub' f' = true <->
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
   rewrite IHf1, IHf2 by (eapply Inv_weak; eauto; namedec).
   split; [intros ((<-,<-),<-)|intros [= <- <- <-]]; easy.
 - rewrite lazy_andb_iff, !eqb_eq.
   setfresh vars z Hz.
   rewrite IHf by (constructor; try (eapply Inv_weak; eauto); namedec).
   simpl.
   split; [intros (<-,<-) | intros [=]]; easy.
Qed.

Lemma nam2mix_canonical (f f' : Nam.formula) :
 nam2mix [] f = nam2mix [] f' <-> Alt.AlphaEq f f'.
Proof.
 symmetry. now apply nam2mix_canonical_gen.
Qed.

Lemma AlphaEq_alt f f' : Alt.AlphaEq f f' <-> AlphaEq f f'.
Proof.
 now rewrite <- nam2mix_canonical, Equiv.nam2mix_canonical.
Qed.

Lemma αeq_alt f f' : Alt.αeq f f' = Form.αeq f f'.
Proof.
 apply eq_true_iff_eq. rewrite AlphaEq_equiv. apply AlphaEq_alt.
Qed.

(** SUBSTS *)

(** We show that [Alt.subst] is equivalent to [Form.subst].
    For that, we'll use [nam2mix].
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
 nam2mix_term (map (chgVar h) stk) (Alt.term_substs (map putVar h) t) =
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
 nam2mix (map (chgVar h) stk) (Alt.substs (map putVar h) f) =
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
              (Alt.term_substs (map putVar h ++ [(x,u)]) t) =
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

Lemma nam2mix_altsubsts_aux1
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
    (Alt.substs ((v, Var z) :: g' ++ [(x, t)]) f) =
  nam2mix (map (chgVar ((v, z) :: g)) (v :: stk'))
    (Alt.substs (map putVar ((v, z) :: g) ++ [(x, t)]) f).
Proof.
 intros vars IV Hg Hg' Hz Hz' Hz'' CL stk'.
 unfold Subst.vars in *; simpl in *.
 rewrite chgVar_some with (z:=z) by (simpl; now rewrite eqb_refl).
 rewrite <-Hg'.
 set (f' := Alt.substs _ f).
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

Lemma form_altsubsts_aux2
  (x v : variable)(t : term)(f : formula)
  (stk : list variable)(h g : renaming) g' :
  let vars := Names.union (Names.add v (allvars f))
                         (Names.add x (Term.vars t)) in
  Inv vars h ->
  g = list_unassoc v h ->
  g' = map putVar g ->
  let f' := Alt.substs (g' ++ [(x,t)]) f in
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

Lemma nam2mix_altsubsts (stk:list variable) h (x:variable) t f:
 Inv (Names.unions [Names.of_list stk;
                   allvars f;
                   Names.add x (Term.vars t)]) h ->
 (forall a b , In (a,b) h -> In a stk) ->
 ~In x stk ->
 (forall v, In v stk -> ~Names.In (chgVar h v) (Term.vars t)) ->
 nam2mix (map (chgVar h) stk)
         (Alt.substs (map putVar h ++ [(x,t)]) f) =
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
                (Alt.substs (map putVar h) (Quant q x f))
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
       erewrite nam2mix_altsubsts_aux1; eauto; fold stk'; fold g.
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
       rewrite form_altsubsts_aux2 with (g:=g); auto.
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

(** And at last : *)

Lemma nam2mix_altsubst x t f:
 nam2mix [] (Alt.subst x t f) = nam2mix [] (subst x t f).
Proof.
 rewrite nam2mix0_subst_fsubst.
 apply (nam2mix_altsubsts [] []); simpl; intuition.
Qed.

Lemma subst_alt x t f:
 AlphaEq (Alt.subst x t f) (subst x t f).
Proof.
 apply Equiv.nam2mix_canonical.
 apply nam2mix_altsubst.
Qed.

Instance : Proper (eq ==> eq ==> AlphaEq ==> AlphaEq) Alt.subst.
Proof.
 intros x x' <- t t' <- f f' Hf.
 now rewrite !subst_alt, Hf.
Qed.
