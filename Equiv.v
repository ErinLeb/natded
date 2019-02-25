
(** Conversion from Named formulas to Locally Nameless formulas *)

Require Import RelationClasses Arith Omega Defs Proofs.
Require Nam Mix.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

Fixpoint nam2mix_term stack t :=
  match t with
  | Nam.Var v =>
    match list_index v stack with
    | None => Mix.FVar v
    | Some n => Mix.BVar n
    end
  | Nam.Fun f args =>
    Mix.Fun f (List.map (nam2mix_term stack) args)
  end.

Fixpoint nam2mix stack f :=
  match f with
  | Nam.True => Mix.True
  | Nam.False => Mix.False
  | Nam.Not f => Mix.Not (nam2mix stack f)
  | Nam.Op o f1 f2 =>
    Mix.Op o (nam2mix stack f1) (nam2mix stack f2)
  | Nam.Pred p args =>
    Mix.Pred p (List.map (nam2mix_term stack) args)
  | Nam.Quant q v f =>
    Mix.Quant q (nam2mix (v::stack) f)
  end.

Module Nam2MixProof.

Inductive Inv (vars:Vars.t) : Nam.subst -> Nam.subst -> Prop :=
 | InvNil : Inv vars [] []
 | InvCons v v' z sub sub' :
   Inv vars sub sub' ->
   ~Vars.In z vars ->
   ~Vars.In z (Nam.subvars sub) ->
   ~Vars.In z (Nam.subvars sub') ->
   Inv vars ((v,Nam.Var z)::sub) ((v',Nam.Var z)::sub').
Hint Constructors Inv.

Lemma Inv_sym vars sub sub' :
 Inv vars sub sub' -> Inv vars sub' sub.
Proof.
 induction 1; auto.
Qed.

Lemma Inv_notIn sub sub' vars v :
 Inv vars sub sub' ->
  ~(Vars.In v vars /\ Vars.In v (Nam.suboutvars sub)).
Proof.
 induction 1.
 - unfold Nam.subvars. simpl. varsdec.
 - unfold Nam.subvars in *. simpl. varsdec.
Qed.

Lemma Inv_weak sub sub' vars vars' :
  Vars.Subset vars' vars -> Inv vars sub sub' -> Inv vars' sub sub'.
Proof.
 induction 2; auto.
Qed.

Lemma Inv_listassoc_var vars sub sub' :
  Inv vars sub sub' ->
  forall v t, list_assoc v sub = Some t -> exists z, t = Nam.Var z.
Proof.
 induction 1.
 - easy.
 - simpl. intros x t.
   case eqbspec; eauto.
   intros -> [= <-]. now exists z.
Qed.

Lemma list_assoc_some_in v sub z :
  list_assoc v sub = Some (Nam.Var z) -> Vars.In z (Nam.suboutvars sub).
Proof.
 induction sub as [|(v',t) sub IH]; try easy.
 simpl.
 case eqbspec.
 - intros <- [= ->]. simpl. varsdec.
 - intros _ E. apply IH in E. simpl. varsdec.
Qed.

Lemma list_assoc_index vars v v' sub sub' z :
Inv vars sub sub' ->
list_assoc v sub = Some (Nam.Var z) ->
list_assoc v' sub' = Some (Nam.Var z) ->
exists k,
list_index v (map fst sub) = Some k /\
list_index v' (map fst sub') = Some k.
Proof.
 induction 1; try easy.
 simpl.
 do 2 case eqbspec.
 - intros. now exists 0.
 - intros NE <- [= <-] E. apply list_assoc_some_in in E.
   unfold Nam.subvars in *. varsdec.
 - intros <- NE E [= <-]. apply list_assoc_some_in in E.
   unfold Nam.subvars in *. varsdec.
 - intros _ _ E E'. destruct (IHInv E E') as (k & Hk & Hk').
   exists (S k). simpl in *. now rewrite Hk, Hk'.
Qed.

Lemma subinvars_in sub v :
  Vars.In v (Nam.subinvars sub) <-> In v (map fst sub).
Proof.
 induction sub as [|(x,t) sub IH]; simpl. varsdec.
 VarsF.set_iff. intuition.
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

Lemma list_assoc_index_none (sub:Nam.subst) v :
  list_assoc v sub = None <-> list_index v (map fst sub) = None.
Proof.
 induction sub as [|(x,t) sub IH]; simpl; auto.
 intuition.
 case eqbspec; try easy.
 intros NE. rewrite IH.
 destruct list_index; simpl; intuition congruence.
Qed.

Lemma nam2mix_term_ok sub sub' t t' :
 Inv (Vars.union (Nam.term_vars t) (Nam.term_vars t')) sub sub' ->
 Nam.term_substs sub t = Nam.term_substs sub' t' ->
 nam2mix_term (map fst sub) t = nam2mix_term (map fst sub') t'.
Proof.
 revert t t' sub sub'.
 fix IH 1. destruct t as [v|f a], t' as [v'|f' a']; intros sub sub' inv;
   simpl; rewrite ?list_assoc_dft_alt.
 - simpl in *.
   destruct (list_assoc v sub) eqn:E, (list_assoc v' sub') eqn:E'.
   + intros <-.
     destruct (Inv_listassoc_var _ _ _ inv v t E) as (z, ->).
     destruct (list_assoc_index _ v v' sub sub' z inv E E') as (k & Hk & Hk').
     simpl in Hk, Hk'.
     now rewrite Hk, Hk'.
   + intros ->.
     apply list_assoc_some_in in E.
     destruct (Inv_notIn _ _ _ v' inv). varsdec.
   + intros <-.
     apply list_assoc_some_in in E'.
     apply Inv_sym in inv.
     destruct (Inv_notIn _ _ _ v inv). varsdec.
   + intros [= <-].
     rewrite list_assoc_index_none in E, E'.
     simpl in *. now rewrite E, E'.
 - generalize (Inv_listassoc_var _ _ _ inv v).
   destruct list_assoc as [t|]; try easy.
   intros E. destruct (E t) as (v', ->); easy.
 - apply Inv_sym in inv.
   generalize (Inv_listassoc_var _ _ _ inv v').
   destruct list_assoc as [t'|]; try easy.
   intros E. destruct (E t') as (v, ->); easy.
 - intros [= <- E]. f_equal.
   simpl in inv.
   clear f. revert a a' E inv.
   fix IH' 1. destruct a as [|t a], a' as [|t' a']; try easy.
   simpl.
   intros [= E E'] inv. f_equal.
   + apply IH; auto.
     eapply Inv_weak; eauto. varsdec.
   + apply IH'; auto.
     eapply Inv_weak; eauto. varsdec.
Qed.

Lemma nam2mix_canonical_gen sub sub' f f' :
 Inv (Vars.union (Nam.allvars f) (Nam.allvars f')) sub sub' ->
 Nam.alpha_equiv_gen sub f sub' f' = true ->
 nam2mix (List.map fst sub) f = nam2mix (List.map fst sub') f'.
Proof.
 revert f' sub sub'.
 induction f; destruct f'; intros sub sub'; simpl; try easy.
 - case eqbspec; [ intros <- | easy ].
   case eqbspec; try discriminate.
   intros H inv _.
   f_equal.
   injection (nam2mix_term_ok sub sub' (Nam.Fun "" l) (Nam.Fun "" l0)); auto.
   simpl. now f_equal.
 - intros. f_equal. auto.
 - case eqbspec; [ intros <- | easy].
   rewrite lazy_andb_iff. intros E (H,H'); f_equal.
   + apply IHf1; auto. eapply Inv_weak; eauto; varsdec.
   + apply IHf2; auto. eapply Inv_weak; eauto; varsdec.
 - match goal with
     |- context [fresh_var ?vs] => set (vars := vs)
   end.
   case eqbspec; [intros <- | easy].
   intros inv H. f_equal. apply IHf in H; auto. clear H.
   assert (Fok := fresh_var_ok vars).
   constructor; try (eapply Inv_weak; eauto); varsdec.
Qed.

Lemma nam2mix_canonical f f' :
 Nam.AlphaEq f f' -> nam2mix [] f = nam2mix [] f'.
Proof.
 intros H.
 unfold Nam.AlphaEq, Nam.alpha_equiv in *.
 apply nam2mix_canonical_gen in H; auto.
Qed.

Lemma nam2mix_term_ok2 sub sub' t t' :
 Inv (Vars.union (Nam.term_vars t) (Nam.term_vars t')) sub sub' ->
 nam2mix_term (map fst sub) t = nam2mix_term (map fst sub') t' ->
 Nam.term_substs sub t = Nam.term_substs sub' t'.
Proof.
 revert t t' sub sub'.
 fix IH 1. destruct t as [v|f a], t' as [v'|f' a']; intros sub sub' inv;
   simpl; rewrite ?list_assoc_dft_alt.
 - simpl in *.
   destruct (list_index v) eqn:E, (list_index v') eqn:E';
   intros [= <-].
   + destruct (list_index_assoc _ _ _ _ _ _ inv E E') as (k & Hk & Hk').
     simpl in *. now rewrite Hk, Hk'.
   + rewrite <- list_assoc_index_none in E, E'.
     simpl in *. now rewrite E,E'.
 - destruct list_index; easy.
 - destruct list_index; easy.
 - intros [= <- E]. f_equal.
   simpl in inv.
   clear f. revert a a' E inv.
   fix IH' 1. destruct a as [|t a], a' as [|t' a']; try easy.
   simpl.
   intros [= E E'] inv. f_equal.
   + apply IH; auto.
     eapply Inv_weak; eauto. varsdec.
   + apply IH'; auto.
     eapply Inv_weak; eauto. varsdec.
Qed.

Lemma nam2mix_alpha_gen sub sub' f f' :
 Inv (Vars.union (Nam.allvars f) (Nam.allvars f')) sub sub' ->
 nam2mix (map fst sub) f = nam2mix (map fst sub') f' ->
 Nam.alpha_equiv_gen sub f sub' f' = true.
Proof.
 revert f' sub sub'.
 induction f; destruct f'; intros sub sub'; simpl; try easy.
 - case eqbspec; [ intros <- | congruence ].
   case eqbspec; auto.
   intros NE inv [=]. destruct NE.
   injection (nam2mix_term_ok2 sub sub' (Nam.Fun "" l) (Nam.Fun "" l0)); auto.
   simpl. now f_equal.
 - intros inv [=]. auto.
 - case eqbspec; [ intros <- | congruence].
   rewrite lazy_andb_iff. intros inv [=]. split.
   + apply IHf1; auto. eapply Inv_weak; eauto; varsdec.
   + apply IHf2; auto. eapply Inv_weak; eauto; varsdec.
 - match goal with
     |- context [fresh_var ?vs] => set (vars := vs)
   end.
   case eqbspec; [intros <- | congruence].
   intros inv [=]. apply IHf; auto.
   assert (Fok := fresh_var_ok vars).
   constructor; try (eapply Inv_weak; eauto); varsdec.
Qed.

Lemma nam2mix_alpha f f' :
  nam2mix [] f = nam2mix [] f' -> Nam.AlphaEq f f'.
Proof.
 intros. apply nam2mix_alpha_gen; auto.
Qed.

Lemma nam2mix_iff f f' :
 nam2mix [] f = nam2mix [] f' <-> Nam.AlphaEq f f'.
Proof.
 split; auto using nam2mix_alpha, Nam2MixProof.nam2mix_canonical.
Qed.

End Nam2MixProof.

Fixpoint mix2nam_term stack t :=
  match t with
  | Mix.FVar v => Nam.Var v
  | Mix.BVar n => Nam.Var (List.nth n stack "")
  | Mix.Fun f args =>
    Nam.Fun f (List.map (mix2nam_term stack) args)
  end.

Fixpoint to_vars l :=
 match l with
 | [] => Vars.empty
 | v::l => Vars.add v (to_vars l)
 end.

Lemma to_vars_in x l : List.In x l <-> Vars.In x (to_vars l).
Proof.
 induction l. simpl. varsdec.
 simpl. VarsF.set_iff. intuition.
Qed.

Fixpoint mix2nam stack f :=
  match f with
  | Mix.True => Nam.True
  | Mix.False => Nam.False
  | Mix.Not f => Nam.Not (mix2nam stack f)
  | Mix.Op o f1 f2 =>
    Nam.Op o (mix2nam stack f1) (mix2nam stack f2)
  | Mix.Pred p args =>
    Nam.Pred p (List.map (mix2nam_term stack) args)
  | Mix.Quant q f =>
    let v := fresh_var (Vars.union (to_vars stack) (Mix.fvars f)) in
    Nam.Quant q v (mix2nam (v::stack) f)
  end.

Lemma mix_nam_mix_term stack t :
 NoDup stack ->
 (Mix.level t <= List.length stack)%nat ->
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
 (Mix.level f <= List.length stack)%nat ->
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
     set (vars := Vars.union (to_vars stack) (Mix.fvars f)).
     assert (FR' := fresh_var_ok vars).
     contradict FR'.
     unfold vars at 2. VarsF.set_iff. left. now apply to_vars_in.
   + simpl. omega with *.
   + simpl.
     intros v [<-|IN].
     * set (vars := Vars.union (to_vars stack) (Mix.fvars f)).
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
  (Mix.level (nam2mix_term stack t) <= List.length stack)%nat.
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
  (Mix.level (nam2mix stack f) <= List.length stack)%nat.
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
  Nam.AlphaEq (mix2nam [] (nam2mix [] f)) f.
Proof.
 apply Nam2MixProof.nam2mix_iff.
 apply mix_nam_mix.
 apply nam2mix_closed.
Qed.

Lemma AlphaEq_equivalence :
  Equivalence Nam.AlphaEq.
Proof.
 constructor.
 - intros f. now apply Nam2MixProof.nam2mix_iff.
 - intros f f'. rewrite <-!Nam2MixProof.nam2mix_iff. auto.
 - intros f1 f2 f3. rewrite <-!Nam2MixProof.nam2mix_iff. apply eq_trans.
Qed.

Lemma nam2mix_eqb (f f' : Nam.formula) :
 (nam2mix [] f =? nam2mix [] f') = (f =? f').
Proof.
 case eqbspec; rewrite Nam2MixProof.nam2mix_iff.
 - apply eq_sym.
 - intros H. symmetry. exact (not_true_is_false _ H).
Qed.

(** Contexts *)

Definition nam2mix_ctx (c:Nam.context) : Mix.context :=
 List.map (nam2mix []) c.

Definition mix2nam_ctx (c:Mix.context) : Nam.context :=
 List.map (mix2nam []) c.

Lemma nam2mix_ctx_eqb (c c' : Nam.context) :
 (nam2mix_ctx c =? nam2mix_ctx c') = (c =? c').
Proof.
 revert c'.
 induction c; destruct c'; cbn; auto.
 rewrite nam2mix_eqb. case eqb; auto.
Qed.

(** Sequents *)

Definition nam2mix_seq '(Nam.Seq c f) : Mix.sequent :=
  Mix.Seq (nam2mix_ctx c) (nam2mix [] f).

Definition mix2nam_seq '(Mix.Seq c f) : Nam.sequent :=
  Nam.Seq (mix2nam_ctx c) (mix2nam [] f).

Lemma nam2mix_seq_eqb (s s' : Nam.sequent) :
 (nam2mix_seq s =? nam2mix_seq s') = (s =? s').
Proof.
 destruct s as (c,f), s' as (c',f'); cbn.
 now rewrite nam2mix_ctx_eqb, nam2mix_eqb.
Qed.


(** Rule kinds *)

Definition nam2mix_rule r :=
  match r with
  | Nam.Ax => Mix.Ax
  | Nam.Tr_i => Mix.Tr_i
  | Nam.Fa_e => Mix.Fa_e
  | Nam.Not_i => Mix.Not_i
  | Nam.Not_e => Mix.Not_e
  | Nam.And_i => Mix.And_i
  | Nam.And_e1 => Mix.And_e1
  | Nam.And_e2 => Mix.And_e2
  | Nam.Or_i1 => Mix.Or_i1
  | Nam.Or_i2 => Mix.Or_i2
  | Nam.Or_e => Mix.Or_e
  | Nam.Imp_i => Mix.Imp_i
  | Nam.Imp_e => Mix.Imp_e
  | Nam.All_i v => Mix.All_i v
  | Nam.All_e t => Mix.All_e (nam2mix_term [] t)
  | Nam.Ex_i t => Mix.Ex_i (nam2mix_term [] t)
  | Nam.Ex_e v => Mix.Ex_e v
  | Nam.Absu => Mix.Absu
  end.

Definition mix2nam_rule r :=
  match r with
  | Mix.Ax => Nam.Ax
  | Mix.Tr_i => Nam.Tr_i
  | Mix.Fa_e => Nam.Fa_e
  | Mix.Not_i => Nam.Not_i
  | Mix.Not_e => Nam.Not_e
  | Mix.And_i => Nam.And_i
  | Mix.And_e1 => Nam.And_e1
  | Mix.And_e2 => Nam.And_e2
  | Mix.Or_i1 => Nam.Or_i1
  | Mix.Or_i2 => Nam.Or_i2
  | Mix.Or_e => Nam.Or_e
  | Mix.Imp_i => Nam.Imp_i
  | Mix.Imp_e => Nam.Imp_e
  | Mix.All_i v => Nam.All_i v
  | Mix.All_e t => Nam.All_e (mix2nam_term [] t)
  | Mix.Ex_i t => Nam.Ex_i (mix2nam_term [] t)
  | Mix.Ex_e v => Nam.Ex_e v
  | Mix.Absu => Nam.Absu
  end.

(** Derivations *)

Fixpoint nam2mix_deriv (d:Nam.derivation) :=
  let '(Nam.Rule r s ds) := d in
  Mix.Rule
    (nam2mix_rule r)
    (nam2mix_seq s)
    (List.map nam2mix_deriv ds).

Fixpoint mix2nam_deriv (d:Mix.derivation) :=
  let '(Mix.Rule r s ds) := d in
  Nam.Rule
    (mix2nam_rule r)
    (mix2nam_seq s)
    (List.map mix2nam_deriv ds).

Ltac break :=
 rewrite <- ?andb_lazy_alt;
 match goal with
 | |- _ = match ?f ?x with _ => _ end => destruct x
 | |- _ = match ?x with _ => _ end => destruct x
 | |- match ?f (?g ?x) with _ => _ end = _ => destruct x
 | |- match ?f ?x with _ => _ end = _ => destruct x
 | |- match ?x with _ => _ end = _ => destruct x
 end.

Lemma lazy_andb_false (a:bool) : a &&& false = false.
Proof.
 now destruct a.
Qed.


Lemma nam2mix_subst v t f :
  nam2mix [] (Nam.formula_subst v t f) =
  Mix.bsubst 0 (nam2mix_term [] t) (nam2mix [v] f).
Proof.
Admitted. (* preuve ??? *)


Lemma nam2mix_deriv_valid_step logic (d:Nam.derivation) :
  Mix.valid_deriv_step logic (nam2mix_deriv d) =
  Nam.valid_deriv_step logic d.
Proof.
 destruct d as [[ ] s ds]; cbn.
 - repeat (break; cbn; auto).
   unfold nam2mix_ctx.
   induction c as [|A c IH]; cbn; auto.
   rewrite <- nam2mix_eqb.
   case eqbspec; auto.
 - repeat (break; cbn; auto).
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   now rewrite nam2mix_eqb, !nam2mix_ctx_eqb.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d, d0.
 - repeat (break; cbn; auto).
   now rewrite <- !nam2mix_seq_eqb.
 - repeat (break; cbn; auto).
   now rewrite <- !nam2mix_seq_eqb.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   rewrite <- nam2mix_ctx_eqb, <- !nam2mix_seq_eqb.
   now destruct d, d0.
 - repeat (break; cbn; auto).
   rewrite <- nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn - [Nam.alpha_equiv]; auto);
    rewrite ?andb_false_r; auto.
   rewrite <- nam2mix_ctx_eqb.
   case eqbspec; auto. intro Ec. simpl.
   rewrite <- nam2mix_eqb. cbn.
   apply eq_true_iff_eq. simpl.
   rewrite !andb_true_iff.
   rewrite !negb_true_iff, <- !not_true_iff_false.
   rewrite !Vars.mem_spec.
   rewrite !eqb_eq.
   split; intros (U,V); split.
   + change (Mix.FVar x) with (nam2mix_term [] (Nam.Var x)) in U.
     rewrite <- nam2mix_subst in U.
     (* f est f0 avec des x à la place des v, donc credible *)
       admit.
   + (* faut montrer que c equiv c0 -> memes variables libres *)
       admit.
   + rewrite U.
     change (Mix.FVar x) with (nam2mix_term [] (Nam.Var x)).
     rewrite <- nam2mix_subst.
     (* TODO:
        alpha_equiv (Nam.formula_subst x (Nam.Var x) f) f
       *)
       admit.
   + (* - memes variables libres dans contextes equivs
          - nam2mix [x] f0 n'a pas x comme variable libre... *)
       admit.
 - repeat (break; cbn; auto).
   rewrite !nam2mix_ctx_eqb. case eqb; simpl; auto.
   rewrite <- nam2mix_eqb.
   now rewrite <- nam2mix_subst.
 - repeat (break; cbn; auto).
   rewrite !nam2mix_ctx_eqb. case eqb; simpl; auto.
   rewrite <- nam2mix_eqb.
   now rewrite <- nam2mix_subst.
 - repeat (break; cbn - [Nam.alpha_equiv]; auto);
    rewrite ?andb_false_r; auto.
   rewrite <- nam2mix_seq_eqb, <- nam2mix_eqb. cbn.
   apply eq_true_iff_eq.
   rewrite !andb_true_iff.
   rewrite !negb_true_iff, <- !not_true_iff_false.
   rewrite !Vars.mem_spec.
   rewrite !eqb_eq.
   split.
   + intros (((U,V),W),X); repeat split.
     * rewrite <-V in U; exact U.
     * rewrite <- nam2mix_ctx_eqb. now apply eqb_eq.
     * admit. (* bsubst... *)
     * destruct s. cbn in *. injection U as U U'. admit.
   + intros ((U,(V,W)),Z); repeat split.
     * rewrite <- nam2mix_ctx_eqb in V. apply eqb_eq in V.
       rewrite U. f_equal; auto.
     * rewrite <- nam2mix_ctx_eqb in V. apply eqb_eq in V.
       rewrite V. auto.
     * rewrite W.
       change (Mix.FVar x) with (nam2mix_term [] (Nam.Var x)).
       rewrite <- nam2mix_subst.
       admit.
     * destruct s. cbn in *. injection U as U U'. admit.
 - repeat (break; cbn; auto).
   case eqb; simpl; auto.
   now rewrite <- nam2mix_seq_eqb.
Admitted.