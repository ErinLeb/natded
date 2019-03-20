
(** Equivalence between various substs and alpha for named formulas *)

Require Import Morphisms RelationClasses Arith Omega.
Require Import Defs Proofs Nam Alpha Meta Equiv.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Lemma subinvars_in sub v :
  Vars.In v (subinvars sub) <-> In v (map fst sub).
Proof.
 induction sub as [|(x,t) sub IH]; simpl. varsdec.
 VarsF.set_iff. intuition.
Qed.

Lemma subinvars_unassoc v h :
  Vars.Equal (subinvars (list_unassoc v h))
             (Vars.remove v (subinvars h)).
Proof.
 induction h as [|(x,u) h IH]; simpl.
 - varsdec.
 - case eqbspec; simpl.
   + intros ->. rewrite IH. varsdec.
   + intros NE. rewrite IH. varsdec.
Qed.

Lemma unassoc_app {A B}`{Eqb A} x (l1 l2 : list (A*B)) :
 list_unassoc x (l1++l2) = list_unassoc x l1 ++ list_unassoc x l2.
Proof.
 unfold list_unassoc.
 apply Vars.Raw.filter_app.
Qed.

Lemma unassoc_in {A B}`{EqbSpec A} x a b (l : list (A*B)) :
 In (a,b) (list_unassoc x l) <-> In (a,b) l /\ a <> x.
Proof.
 unfold list_unassoc.
 now rewrite filter_In, <- eqb_neq, negb_true_iff.
Qed.

Lemma subinvars_app h h' :
  Vars.Equal (subinvars (h++h')) (Vars.union (subinvars h) (subinvars h')).
Proof.
 induction h; simpl; auto with set.
Qed.

(** [nam2mix] and free variables *)

Lemma nam2mix_tvars stk t :
  Vars.Equal (Mix.fvars (nam2mix_term stk t))
             (Vars.diff (Nam.term_vars t) (vars_of_list stk)).
Proof.
 revert t.
 fix IH 1. destruct t as [v|f l]; cbn.
 - destruct list_index eqn:E; cbn.
   + assert (NE : list_index v stk <> None) by congruence.
     rewrite list_index_in in NE. rewrite <-vars_of_list_in in NE. varsdec.
   + rewrite list_index_notin, <-vars_of_list_in in E. varsdec.
 - clear f. revert l.
   fix IH' 1. destruct l as [|t l]; cbn; rewrite ?IH, ?IH'; varsdec.
Qed.

Lemma nam2mix_fvars stk f :
  Vars.Equal (Mix.fvars (nam2mix stk f))
             (Vars.diff (Nam.freevars f) (vars_of_list stk)).
Proof.
 revert stk.
 induction f; intros; cbn.
 - varsdec.
 - varsdec.
 - apply (nam2mix_tvars stk (Fun "" l)).
 - auto.
 - rewrite IHf1, IHf2; varsdec.
 - rewrite IHf. simpl. varsdec.
Qed.

(** [nam2mix] and modifying the stack *)

Lemma nam2mix_term_indep stk stk' t :
 (forall v, Vars.In v (term_vars t) ->
            list_index v stk = list_index v stk') ->
 nam2mix_term stk t = nam2mix_term stk' t.
Proof.
 induction t as [v|f l IH] using Nam.term_ind'; cbn; intros Ht.
 - rewrite Ht; auto with set.
 - f_equal. clear f. apply map_ext_iff. intros a Ha.
   apply IH; auto. intros v Hv. apply Ht.
   rewrite vars_unionmap_in. now exists a.
Qed.

Lemma nam2mix_indep stk stk' f :
 (forall v, Vars.In v (freevars f) ->
            list_index v stk = list_index v stk') ->
 nam2mix stk f = nam2mix stk' f.
Proof.
 revert stk stk'.
 induction f; simpl; intros stk stk' EQ; f_equal; auto with set.
 - injection (nam2mix_term_indep stk stk' (Fun "" l)); auto.
 - apply IHf. intros v' Hv'; simpl.
   case eqbspec; auto.
   intros NE. f_equal. apply EQ. varsdec.
Qed.

Lemma nam2mix_term_nostack stk t :
 (forall v, In v stk -> ~Vars.In v (term_vars t)) ->
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
 In x stk \/ ~Vars.In x (freevars f) ->
 In y stk \/ ~Vars.In y (freevars f) ->
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
 In x stk \/ ~Vars.In x (freevars f) ->
 In y stk \/ ~Vars.In y (freevars f) ->
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


(** [term_substs] may do nothing *)

Lemma term_substs_notin h t :
 Vars.Empty (Vars.inter (term_vars t) (subinvars h)) ->
 term_substs h t = t.
Proof.
 induction t as [v |f l IH] using term_ind'; intros EM; cbn in *.
 - rewrite list_assoc_dft_alt.
   assert (NI : ~In v (map fst h)).
   { rewrite <- subinvars_in. varsdec. }
   rewrite <- list_assoc_notin in NI. now rewrite NI.
 - f_equal. clear f.
   apply map_id_iff.
   intros a Ha. apply IH; auto. intros v. VarsF.set_iff. intros (Hv,Hv').
   apply (EM v). VarsF.set_iff. split; auto.
   rewrite vars_unionmap_in. now exists a.
Qed.

(* Unused for the moment *)
Lemma nam2mix_term_subst stk x u t:
 ~In x stk ->
 nam2mix_term stk (term_subst x u t) =
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

(* Unused for the moment *)
Lemma nam2mix_partialsubst stk x u f :
 ~In x stk ->
 (forall v, In v stk -> ~Vars.In v (term_vars u)) ->
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
     case eqbspec; auto. intros <-. varsdec.
   + intros NE.
     destruct IS as [-> | (NI,IS)]; [easy|].
     rewrite vars_mem_false by trivial.
     apply IHf; simpl; intuition auto; subst; eauto.
Qed.

Lemma nam2mix_term_subst' stk stk' x z t :
 ~In x stk ->
 ~In z stk ->
 ~Vars.In z (term_vars t) ->
 nam2mix_term (stk++z::stk') (term_subst x (Var z) t) =
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
       do 2 case eqbspec; auto. varsdec. intuition.
 - f_equal; clear f.
   rewrite !map_map.
   apply map_ext_in. intros t Ht. apply IH; auto.
   rewrite vars_unionmap_in in NI. contradict NI. now exists t.
Qed.

Lemma nam2mix_partialsubst' stk stk' x z f :
 ~In x stk ->
 ~In z stk ->
 ~Vars.In z (allvars f) ->
 nam2mix (stk++z::stk') (partialsubst x (Var z) f) =
 nam2mix (stk++x::stk') f.
Proof.
 revert stk.
 induction f; cbn; intros stk Hx Hz IS; f_equal; auto.
 - injection (nam2mix_term_subst' stk stk' x z (Fun "" l)); easy.
 - intuition.
 - intuition.
 - rewrite vars_mem_false by varsdec.
   case eqbspec; cbn.
   + intros <-.
     symmetry.
     apply (nam2mix_shadowstack' (x::stk)). simpl; auto.
     right. rewrite freevars_allvars. varsdec.
   + intros NE.
     apply (IHf (v::stk)).
     simpl. intuition.
     simpl. intuition.
     varsdec.
Qed.

Lemma AlphaEq_nam2mix_gen stk f f' :
 Alpha.AlphaEq f f' -> nam2mix stk f = nam2mix stk f'.
Proof.
 intros H. revert stk.
 induction H; cbn; intros stk; f_equal; auto.
 generalize (IHAlphaEq (z::stk)).
 rewrite (nam2mix_partialsubst' [] stk v z) by (auto; varsdec).
 rewrite (nam2mix_partialsubst' [] stk v' z) by (auto; varsdec).
 auto.
Qed.

(* Unused for the moment *)
Lemma nam2mix0_partialsubst x u f :
 IsSimple x u f ->
 nam2mix [] (partialsubst x u f) =
  Mix.fsubst x (nam2mix_term [] u) (nam2mix [] f).
Proof.
 apply nam2mix_partialsubst; auto.
Qed.

Lemma term_subst_bsubst stk (x z:variable) t :
 ~In x stk ->
 ~In z stk ->
 ~Vars.In z (term_vars t) ->
 nam2mix_term stk (term_subst x (Var z) t) =
  Mix.bsubst (length stk) (Mix.FVar z) (nam2mix_term (stk++[x]) t).
Proof.
  induction t as [v|f l IH] using term_ind'; intros X Z1 Z2; cbn in *.
 - case eqbspec.
   + intros ->. cbn.
     rewrite <-list_index_notin in Z1. rewrite Z1.
     rewrite list_index_app_r; auto. cbn. rewrite eqb_refl. cbn.
     rewrite Nat.add_0_r. now rewrite eqb_refl.
   + intros NE. cbn.
     rewrite list_index_app_l' by (simpl; intuition).
     destruct (list_index v stk) eqn:E; cbn; auto.
     apply list_index_lt_length in E.
     case eqbspec; intros; subst; auto; omega.
 - f_equal; clear f.
   rewrite !map_map.
   apply map_ext_in. intros t Ht. apply IH; auto.
   contradict Z2. rewrite vars_unionmap_in. now exists t.
Qed.

Lemma partialsubst_bsubst stk x z f :
 ~In x stk ->
 ~In z stk ->
 ~Vars.In z (allvars f) ->
 nam2mix stk (partialsubst x (Var z) f) =
  Mix.bsubst (length stk) (Mix.FVar z) (nam2mix (stk++[x]) f).
Proof.
 revert stk.
 induction f; cbn; intros stk X Z1 Z2; f_equal; auto.
 - injection (term_subst_bsubst stk x z (Fun "" l)); auto.
 - apply IHf1; auto. varsdec0.
 - apply IHf2; auto. varsdec0.
 - fold (v =? z)%string. change (v =? z)%string with (v =? z).
   case eqbspec; cbn.
   + intros <-.
     change (x::stk++[x]) with ((x::stk)++[x]).
     rewrite nam2mix_shadowstack by (simpl; auto).
     symmetry.
     apply form_level_bsubst_id.
     now rewrite nam2mix_level.
   + intros NE.
     rewrite vars_mem_false by varsdec0.
     apply IHf; simpl; intuition.
Qed.

Lemma partialsubst_bsubst0 x z f :
 ~Vars.In z (allvars f) ->
 nam2mix [] (partialsubst x (Var z) f) =
  Mix.bsubst 0 (Mix.FVar z) (nam2mix [x] f).
Proof.
 apply partialsubst_bsubst; auto.
Qed.

Lemma nam2mix_rename_iff z v v' f f' :
  ~ Vars.In z (Vars.union (allvars f) (allvars f')) ->
  nam2mix [] (partialsubst v (Var z) f) =
  nam2mix [] (partialsubst v' (Var z) f')
  <->
  nam2mix [v] f = nam2mix [v'] f'.
Proof.
 intros Hz.
 rewrite 2 partialsubst_bsubst0 by varsdec.
 split.
 - intros H. apply bsubst_fresh_inj in H; auto.
   rewrite !nam2mix_fvars. cbn. rewrite !freevars_allvars. varsdec.
 - now intros ->.
Qed.

Lemma nam2mix_term_inj t t' : nam2mix_term [] t = nam2mix_term [] t' -> t = t'.
Proof.
 intro E.
 apply (Nam2MixProof.nam2mix_term_ok2 [] []) in E; auto.
 rewrite !term_substs_notin in E; cbn; auto with set.
Qed.

Lemma nam2mix_AlphaEq f f' :
 Alpha.AlphaEq f f' <-> nam2mix [] f = nam2mix [] f'.
Proof.
 split.
 - induction 1; cbn; f_equal; auto.
   apply (nam2mix_rename_iff z); auto.
 - set (h := S (Nat.max (form_height f) (form_height f'))).
   assert (LT : form_height f < h) by (unfold h; auto with *).
   assert (LT' : form_height f' < h) by (unfold h; auto with *).
   clearbody h. revert f f' LT LT'.
   induction h as [|h IH]; [inversion 1|].
   destruct f, f'; simpl; intros LT LT'; simpl_height; try easy.
   + intros [= <- E].
     injection (nam2mix_term_inj (Fun "" l) (Fun "" l0)) as <-; cbn; auto.
     now f_equal.
   + intros [= E]; auto.
   + intros [= <- E1 E2]; auto.
   + intros [= <- E].
     destruct (get_fresh_var (Vars.union (allvars f) (allvars f'))) as (z,Hz).
     apply AEqQu with z; auto.
     apply IH; try rewrite partialsubst_height; auto.
     apply nam2mix_rename_iff; auto.
Qed.

Lemma AlphaEq_alt f f' : Nam.AlphaEq f f' <-> Alpha.AlphaEq f f'.
Proof.
 now rewrite nam2mix_AlphaEq, Nam2MixProof.nam2mix_iff.
Qed.

Lemma alpha_equiv_alt f f' : Nam.alpha_equiv f f' = Alpha.alpha_equiv f f'.
Proof.
 apply eq_true_iff_eq. fold (Nam.AlphaEq f f'). rewrite alpha_equiv_ok.
 apply AlphaEq_alt.
Qed.


(** SUBST *)

Lemma nam2mix_Subst x u f f' :
 Subst x u f f' ->
 nam2mix [] f' = Mix.fsubst x (nam2mix_term [] u) (nam2mix [] f).
Proof.
 intros (f0 & EQ & SI).
 apply nam2mix_AlphaEq in EQ. rewrite EQ.
 apply SimpleSubst_carac in SI. destruct SI as (<- & IS).
 apply nam2mix0_partialsubst; auto.
Qed.

Lemma nam2mix_subst x u f :
 nam2mix [] (form_subst x u f) =
  Mix.fsubst x (nam2mix_term [] u) (nam2mix [] f).
Proof.
 apply nam2mix_Subst.
 apply Subst_subst.
Qed.

Lemma term_substs_ext h h' t :
 (forall v, list_assoc_dft v h (Var v) =
            list_assoc_dft v h' (Var v)) ->
 term_substs h t = term_substs h' t.
Proof.
 intros EQ.
 induction t as [v|f l IH] using term_ind'; cbn; auto.
 f_equal. apply map_ext_iff; auto.
Qed.

Lemma form_substs_deepswap h h' x1 x2 t1 t2 f :
 x1 <> x2 ->
 form_substs (h++(x1,t1)::(x2,t2)::h') f =
 form_substs (h++(x2,t2)::(x1,t1)::h') f.
Proof.
 revert h h'.
 induction f; cbn; intros h h' NE; f_equal; auto.
 - injection (term_substs_ext (h++(x1,t1)::(x2,t2)::h')
                              (h++(x2,t2)::(x1,t1)::h')
                              (Fun "" l)); auto.
   intros.
   induction h as [|(a,b) h IH]; cbn; auto.
   + repeat case eqbspec; auto. congruence.
   + case eqbspec; auto.
 - rewrite !unassoc_app in *. cbn.
   set (g := list_unassoc v h).
   set (g' := list_unassoc v h').
   repeat case eqbspec; cbn; try easy.
   intros NE1 NE2.
   assert (OUT : Vars.Equal (suboutvars (g++(x1,t1)::(x2,t2)::g'))
                          (suboutvars (g++(x2,t2)::(x1,t1)::g'))).
   { unfold suboutvars.
     rewrite !vars_unionmap_app. cbn. varsdec. }
   rewrite OUT.
   destruct (Vars.mem _ _) eqn:EQ; cbn; [ | f_equal; auto].
   set (vars1 := Vars.union _ _).
   set (vars2 := Vars.union _ _).
   assert (VARS : Vars.Equal vars1 vars2).
   { unfold vars1, vars2; clear vars1 vars2.
     f_equiv. f_equiv. apply OUT. f_equiv.
     rewrite !subinvars_app. simpl. varsdec. }
   clearbody vars1 vars2.
   replace (fresh_var vars2) with (fresh_var vars1) by now rewrite <- VARS.
   f_equal. apply (IHf ((v,Var _)::g)); auto.
Qed.

Lemma form_substs_swap x1 x2 t1 t2 h f :
 x1 <> x2 ->
 form_substs ((x1,t1)::(x2,t2)::h) f =
 form_substs ((x2,t2)::(x1,t1)::h) f.
Proof.
apply (form_substs_deepswap [] h).
Qed.


(*
Definition foldsubst (h:subst) :=
  fold_left (fun a '(x,u) => form_subst x u a) h.

Definition substfoldr (h:subst) f :=
  fold_right (fun '(x,u) => form_subst x u) f h.

Lemma foldsubst_True h :
  foldsubst h True = True.
Proof.
 induction h as [|(v,t) h IH]; simpl; auto.
Qed.

Lemma foldsubst_False h :
  foldsubst h False = False.
Proof.
 induction h as [|(v,t) h IH]; simpl; auto.
Qed.

Lemma foldsubst_Pred p l h :
  foldsubst h (Pred p l) =
  Pred p (map (fold_left (fun a '(x,u) => term_subst x u a) h) l).
Proof.
 revert p l.
 induction h as [|(v,t) h IH]; simpl; intros.
 - f_equal. symmetry. now apply map_id_iff.
 - rewrite form_subst_eqn. rewrite IH. f_equal. now rewrite map_map.
Qed.

Lemma foldsubst_Not f h :
 foldsubst h (Not f) = Not (foldsubst h f).
Proof.
 revert f.
 induction h as [|(v,t) h IH]; simpl; intros; auto.
 now rewrite form_subst_eqn.
Qed.

Lemma foldsubst_Op o f1 f2 h :
 foldsubst h (Op o f1 f2) = Op o (foldsubst h f1) (foldsubst h f2).
Proof.
 revert f1 f2.
 induction h as [|(v,t) h IH]; simpl; intros; auto.
 now rewrite form_subst_eqn.
Qed.

Fixpoint Sequential h :=
 match h with
 | [] => Logic.True
 | (x,u) :: h => Vars.Empty (Vars.inter (term_vars u) (subinvars h))
                 /\ Sequential h
 end.

Lemma term_substs_cons x u h t :
 Vars.Empty (Vars.inter (term_vars u) (subinvars h)) ->
 term_substs ((x,u)::h) t = term_substs h (term_subst x u t).
Proof.
 induction t as [v |f l IH] using term_ind'; intros EM; cbn in *.
 - case eqbspec; auto.
   intros ->. symmetry. now apply term_substs_notin.
 - f_equal. clear f.
   rewrite map_map.
   apply map_ext_iff.
   intros a Ha. apply IH; auto.
Qed.

Lemma term_substs_subst h t :
 Sequential h ->
 term_substs h t = fold_left (fun a '(x,u) => term_subst x u a) h t.
Proof.
 revert t.
 induction h as [|(x,u) h IH]; cbn; intros t SE.
 - apply term_substs_notin. cbn. varsdec.
 - destruct SE as (EM,SE).
   rewrite term_substs_cons; auto.
Qed.
*)

Lemma form_substs_nil f :
 form_substs [] f = f.
Proof.
 induction f; cbn - [fresh_var]; f_equal; auto.
 apply map_id_iff. intros a _. apply term_substs_notin. cbn. varsdec.
Qed.

Lemma simple_substs x t f :
 IsSimple x t f ->
 form_substs [(x,t)] f = partialsubst x t f.
Proof.
 induction f; cbn; intros IS; auto.
 - f_equal; auto.
 - f_equal; intuition.
 - case eqbspec; simpl.
   + intros _. f_equal. apply form_substs_nil.
   + intros NE. destruct IS as [->|(NI,IS)]; [easy|].
     rewrite vars_mem_false by varsdec. simpl.
     rewrite vars_mem_false by varsdec. f_equal; auto.
Qed.


Lemma Subst_compat' x t f1 f2 f1' :
 AlphaEq f1 f2 -> Subst x t f1 f1' ->
 exists f2',  Subst x t f2 f2' /\ AlphaEq f1' f2'.
Proof.
 intros EQ SU.
 exists (form_subst x t f2).
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

Instance : Proper (eq ==> eq ==> AlphaEq ==> AlphaEq) form_subst.
Proof.
 intros x x' <- t t' <- f f' Hf.
 apply (Subst_compat x t f f'); auto using Subst_subst.
Qed.

(*
(** Unicity rules for Subst *)

Lemma Subst_True_iff x t f : Subst x t True f <-> f = True.
Proof.
 split; [|intros ->; apply Subst_True].
 intros (f0 & EQ & SI). inversion EQ; subst. now inversion SI.
Qed.

Lemma Subst_False_iff x t f : Subst x t False f <-> f = False.
Proof.
 split; [|intros ->; apply Subst_False].
 intros (f0 & EQ & SI). inversion EQ; subst. now inversion SI.
Qed.

Lemma Subst_Pred_iff x t f p l :
  Subst x t (Pred p l) f <-> f = partialsubst x t (Pred p l).
Proof.
 split; [|intros ->; apply Subst_Pred].
 intros (f0 & EQ & SI). inversion EQ; subst. now inversion SI.
Qed.

Lemma Subst_Not_iff x t f f' :
  Subst x t (~f) f' <->
   exists f0,  f' = (~f0)%form /\ Subst x t f f0.
Proof.
 split; [|intros (f0 & -> & SU); now apply Subst_Not].
 intros (f0 & EQ & SI).
 inversion EQ; subst. inversion SI; subst. firstorder.
Qed.

Lemma Subst_Op_iff x t o f1 f2 f' :
  Subst x t (Op o f1 f2) f' <->
   exists f1' f2',
    f' = Op o f1' f2' /\ Subst x t f1 f1' /\ Subst x t f2 f2'.
Proof.
 split; [|intros (f1' & f2' & -> & SU); now apply Subst_Op].
 intros (f0 & EQ & SI).
 inversion EQ; subst. inversion SI; subst. firstorder.
Qed.
*)

Lemma form_subst_Qu1 x t q f :
 form_subst x t (Quant q x f) = Quant q x f.
Proof.
 rewrite form_subst_eqn. now rewrite eqb_refl.
Qed.


Lemma subst_subst x y u v f :
 x<>y -> ~Vars.In x (term_vars v) ->
 AlphaEq (form_subst y v (form_subst x u f))
         (form_subst x (term_subst y v u) (form_subst y v f)).
Proof.
 intros NE NI.
 apply nam2mix_AlphaEq.
 rewrite !nam2mix_subst.
 rewrite nam2mix_term_subst by auto.
 apply form_fsubst_fsubst; auto.
 rewrite nam2mix_tvars. cbn. varsdec.
Qed.

Lemma nam2mix_subst_subst stk x y u v f :
 x<>y -> ~Vars.In x (term_vars v) ->
 nam2mix stk (form_subst y v (form_subst x u f)) =
 nam2mix stk (form_subst x (term_subst y v u) (form_subst y v f)).
Proof.
 intros.
 apply AlphaEq_nam2mix_gen.
 apply subst_subst; auto.
Qed.


Lemma nam2mix_subst_gen stk x u f :
 ~In x stk ->
 (forall v, In v stk -> ~Vars.In v (term_vars u)) ->
 nam2mix stk (form_subst x u f) =
 Mix.fsubst x (nam2mix_term [] u) (nam2mix stk f).
Proof.
 set (h:=S (form_height f)).
 assert (LT : form_height f < h) by auto with *.
 clearbody h.
 revert f stk LT.
 induction h as [|h IH]; [inversion 1|].
 destruct f; intros stk LT NI II; rewrite form_subst_eqn;
  cbn -[form_subst] in *; simpl_height; f_equal; auto.
 - injection (nam2mix_partialsubst stk x u (Pred "" l)); simpl; auto.
 - case eqbspec.
   + intros <-. cbn.
     f_equal.
     unfold Mix.fsubst.
     symmetry. apply form_vmap_id. intros v Hv.
     unfold Mix.varsubst.
     rewrite nam2mix_fvars in Hv. cbn in Hv.
     case eqbspec; auto. varsdec.
   + intros NE.
     destruct Vars.mem eqn:E; cbn -[form_subst].
     * f_equal.
       set (vars := Vars.union _ _).
       assert (Hz := fresh_var_ok vars).
       set (z := fresh_var _) in *.
       rewrite IH;
         [ | now rewrite form_subst_height
           | simpl; intuition
           | simpl; intros v0 [<-|Hv0]; auto; varsdec ].
       f_equal.
       rewrite <- partialsubst_subst by auto with set.
       apply (nam2mix_partialsubst' [] stk); simpl; auto with set.
     * f_equal.
       apply IH; auto.
       simpl. intuition.
       rewrite <-not_true_iff_false, Vars.mem_spec in E.
       simpl. intros z [<-|IN]; auto.
Qed.

Lemma form_subst_QuGen x t q v f z :
 x<>v ->
 ~Vars.In z (Vars.add x (Vars.union (allvars f) (term_vars t))) ->
 AlphaEq (form_subst x t (Quant q v f))
         (Quant q z (form_subst x t (form_subst v (Var z) f))).
Proof.
 intros NE NI.
 apply nam2mix_AlphaEq. cbn - [form_subst].
 rewrite !nam2mix_subst. cbn - [form_subst].
 f_equal.
 rewrite nam2mix_subst_gen by (simpl; varsdec).
 f_equal. symmetry.
 rewrite <- partialsubst_subst by auto with set.
 apply (nam2mix_partialsubst' [] []); auto with set.
Qed.

Lemma nam2mix_subst_QuGen stk x t q v f z :
 x<>v ->
 ~Vars.In z (Vars.add x (Vars.union (allvars f) (term_vars t))) ->
 nam2mix stk (form_subst x t (Quant q v f)) =
 nam2mix stk (Quant q z (form_subst x t (form_subst v (Var z) f))).
Proof.
 intros.
 apply AlphaEq_nam2mix_gen. apply form_subst_QuGen; auto.
Qed.


Definition renaming := list (variable*variable).

Definition putVar : variable*variable -> variable*Nam.term :=
 fun '(a,b) => (a,Var b).

Definition chgVar : renaming -> variable -> variable :=
  fun h v => list_assoc_dft v h v.

Fixpoint Inv vs (h:renaming) :=
  match h with
  | [] => Logic.True
  | (v,z)::h => ~Vars.In z vs /\
                (forall a b, In (a,b) h -> z<>a/\z<>b) /\
                Inv vs h
  end.

Lemma Inv_subset vs vs' h :
  Vars.Subset vs vs' -> Inv vs' h -> Inv vs h.
Proof.
 induction h as [|(v,z) h IH]; simpl; intuition.
Qed.

Lemma Inv_notin vs (h:renaming) v z :
  Inv vs h -> list_assoc v h = Some z -> ~Vars.In z vs.
Proof.
 induction h as [|(a,b) h IH]; simpl; try easy.
 - intros (H & H' & IV).
   case eqbspec; auto.
   now intros <- [= ->].
Qed.

Lemma Inv_notin' vs (h:renaming) (v x:variable) :
  Inv vs h -> (Vars.In x vs \/ list_assoc v h = Some x) ->
  ~Vars.In x (suboutvars (map putVar (list_unassoc v h))).
Proof.
 intros IV.
 induction h as [|(a,b) h IH]; simpl in *; auto.
 - varsdec.
 - destruct IV as (H & H' & IV).
   rewrite eqb_sym.
   case eqbspec; simpl.
   + intros -> [IN|[= ->]]. intuition.
     unfold suboutvars. rewrite vars_unionmap_in.
     intros ((a,t) & IN & IN').
     rewrite in_map_iff in IN'.
     destruct IN' as ((a',b) & [= -> <-] & IN').
     rewrite unassoc_in in IN'.
     simpl in IN. rewrite Vars.singleton_spec in IN.
     destruct (H' a b); intuition.
   + intros NE [IN|SO];
      rewrite Vars.union_spec, Vars.singleton_spec.
     * intuition.
     * intros [<-|IN]; [|intuition].
       apply list_assoc_in2 in SO. now apply H' in SO.
Qed.

Lemma Inv_inj vs (h:renaming) x y z :
 Inv vs h ->
 list_assoc x h = Some z -> list_assoc y h = Some z -> x = y.
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
  Vars.In x vs -> Vars.In y vs ->
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

Lemma term_substs_vars h t :
 Vars.Subset (term_vars (term_substs h t))
             (Vars.union (Vars.diff (term_vars t) (subinvars h))
                         (suboutvars h)).
Proof.
 revert t.
 fix IH 1. destruct t as [v|f l]; cbn.
 - rewrite list_assoc_dft_alt.
   assert (H := list_assoc_in2 h v).
   assert (H' := list_assoc_notin h v).
   destruct (list_assoc v h).
   + specialize (H t).
     unfold suboutvars.
     intros y Hy.
     rewrite Vars.union_spec, vars_unionmap_in.
     right. exists (v,t); auto.
   + simpl. intros y. rewrite Vars.singleton_spec. intros ->.
     VarsF.set_iff. left; split; auto.
     rewrite subinvars_in; intuition.
 - clear f. revert l.
   fix IH' 1. destruct l as [|t l]; cbn -[Vars.diff].
   + varsdec.
   + specialize (IH t). specialize (IH' l). varsdec.
Qed.

Lemma suboutvars_unassoc v h :
 Vars.Subset (suboutvars (list_unassoc v h)) (suboutvars h).
Proof.
 induction h as [|(x,t) h IH]; simpl.
 - varsdec.
 - case eqbspec; simpl; varsdec.
Qed.

Lemma form_substs_freevars h f :
 Vars.Subset (freevars (form_substs h f))
             (Vars.union (Vars.diff (freevars f) (subinvars h))
                         (suboutvars h)).
Proof.
 revert h.
 induction f; cbn -[subinvars suboutvars Vars.diff]; intros; auto.
 - varsdec.
 - varsdec.
 - apply (term_substs_vars h (Fun "" l)).
 - rewrite IHf1, IHf2. varsdec.
 - destruct (Vars.mem _ _) eqn:E; simpl.
   + set (vars := Vars.union _ _).
     assert (Hz := fresh_var_ok vars).
     set (z := fresh_var vars) in *.
     rewrite IHf; simpl.
     rewrite subinvars_unassoc, suboutvars_unassoc.
     varsdec.
   + rewrite IHf; simpl.
     rewrite subinvars_unassoc, suboutvars_unassoc.
     varsdec.
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

Lemma cons_app {A} (x:A) l : x::l = [x]++l.
Proof.
 reflexivity.
Qed.

Lemma nam2mix_substs_rename_aux stk stk' v (h:renaming) f :
  let g := list_unassoc v h in
  In (chgVar h v) stk \/ ~Vars.In (chgVar h v) (freevars f) ->
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
  Inv (Vars.union (vars_of_list stk) (Vars.singleton v)) h ->
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
     assert (H' : Inv (Vars.union (vars_of_list stk) (Vars.singleton v)) h).
     { eapply Inv_subset; eauto. varsdec. }
     specialize (IHstk H' H).
     destruct (list_index z (map (chgVar h) stk)),
              (list_index v stk); simpl; try easy.
     injection IHstk as ->; auto.
Qed.

Lemma nam2mix_term_chgVar_none stk (h:renaming) (v:variable) :
  Inv (Vars.union (vars_of_list stk) (Vars.singleton v)) h ->
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
     assert (H : Inv (Vars.union (vars_of_list stk) (Vars.singleton v)) h).
     { eapply Inv_subset; eauto. varsdec. }
     specialize (IHstk H).
     destruct (list_index v (map (chgVar h) stk)),
              (list_index v stk); simpl; try easy.
     injection IHstk as ->; auto.
Qed.

Lemma nam2mix_term_substs_rename stk (h:renaming) t :
 Inv (Vars.union (vars_of_list stk) (term_vars t)) h ->
 (forall a b, In (a,b) h -> In a stk) ->
 nam2mix_term (map (chgVar h) stk) (term_substs (map putVar h) t) =
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
   apply IH; auto. eapply Inv_subset; eauto. varsdec.
   apply IH'; auto. eapply Inv_subset; eauto. varsdec.
Qed.

Lemma nam2mix_substs_rename stk (h:renaming) f:
 Inv (Vars.union (vars_of_list stk) (allvars f)) h ->
 (forall a b, In (a,b) h -> In a stk) ->
 nam2mix (map (chgVar h) stk) (form_substs (map putVar h) f) =
 nam2mix stk f.
Proof.
 revert stk h.
 induction f; intros stk h IV SU; cbn in *; auto.
 - f_equal.
   injection (nam2mix_term_substs_rename stk h (Fun "" l)); auto.
 - f_equal; auto.
 - f_equal. apply IHf1; auto. eapply Inv_subset; eauto. varsdec.
   apply IHf2; auto. eapply Inv_subset; eauto. varsdec.
 - set (g' := list_unassoc v (map putVar h)).
   set (g := list_unassoc v h).
   assert (~Vars.In v (suboutvars g')).
   { unfold g'. rewrite unassoc_putVar.
     eapply Inv_notin'; eauto. left; varsdec. }
   rewrite vars_mem_false by trivial; simpl.
   f_equal.
   rewrite <- IHf with (h:=g).
   2:{ apply Inv_unassoc.
       eapply Inv_subset; eauto. simpl; varsdec. }
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
   rewrite form_substs_freevars, freevars_allvars.
   destruct (list_assoc v h) as [z|] eqn:Hz.
   + right.
     rewrite (chgVar_some _ _ _ Hz).
     assert (IV2 := Inv_notin _ _ _ _ IV Hz).
     assert (IV3 := Inv_notin' _ _ _ _ IV (or_intror _ Hz)).
     rewrite <- unassoc_putVar in IV3. fold g' in IV3.
     varsdec.
   + left; left. symmetry. now apply chgVar_none.
Qed.

Lemma list_assoc_app_l {A B}`{EqbSpec A}
 (l l' : list (A*B)) x :
 In x (map fst l) -> list_assoc x (l++l') = list_assoc x l.
Proof.
 induction l as [|(a,b) l IH]; simpl; try easy.
 - case eqbspec; auto.
   intros NE [->|IN]; [easy|auto].
Qed.

Lemma list_assoc_app_r {A B}`{EqbSpec A}
 (l l' : list (A*B)) x :
 ~In x (map fst l) -> list_assoc x (l++l') = list_assoc x l'.
Proof.
 induction l as [|(a,b) l IH]; simpl; try easy.
 - case eqbspec; auto. intros <-. intuition.
Qed.

Lemma nam2mix_term_substs stk h x u t:
 Inv (vars_unions [vars_of_list stk;
                   term_vars t;
                   Vars.add x (term_vars u)]) h ->
 (forall a b , In (a,b) h -> In a stk) ->
 ~In x stk ->
 (forall v, In v stk -> ~Vars.In (chgVar h v) (term_vars u)) ->
 nam2mix_term (map (chgVar h) stk)
              (term_substs (map putVar h ++ [(x,u)]) t) =
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
     intros ->; auto; [ | eapply Inv_subset; eauto; varsdec].
     rewrite <- list_index_in in IN'.
     now destruct (list_index v stk).
   + assert (~In v (map fst (map putVar h))).
     { rewrite map_map. rewrite in_map_iff in *.
       intros ((a,b) & EQ & IN). apply NI'. now exists (a,b). }
     rewrite list_assoc_app_r by auto.
     simpl. case eqbspec; simpl.
     * intros <-. apply list_index_notin in NI.
       change Vars.elt with variable in *.
       rewrite NI. cbn. unfold Mix.varsubst. rewrite eqb_refl.
       apply nam2mix_term_nostack.
       intros y. rewrite in_map_iff. intros (x & <- & Hx); auto.
     * intros NE.
       generalize (nam2mix_term_chgVar_none stk h v).
       simpl.
       intros ->; auto.
       2:{ eapply Inv_subset; eauto. varsdec. }
       2:{ now apply list_assoc_notin. }
       unfold Mix.fsubst.
       rewrite term_vmap_id; auto.
       intros y. unfold Mix.varsubst.
       destruct (list_index v stk); cbn; VarsF.set_iff; intuition.
 - f_equal. clear f.
   revert l IV.
   fix IH' 1. destruct l as [|t l]; cbn; intros IV; auto.
   f_equal.
   apply IH; auto. eapply Inv_subset; eauto. simpl. varsdec.
   apply IH'; auto. eapply Inv_subset; eauto. simpl. varsdec.
Qed.

Lemma nam2mix_substs stk h x t f:
 Inv (vars_unions [vars_of_list stk;
                   allvars f;
                   Vars.add x (term_vars t)]) h ->
 (forall a b , In (a,b) h -> In a stk) ->
 ~In x stk ->
 (forall v, In v stk -> ~Vars.In (chgVar h v) (term_vars t)) ->
 nam2mix (map (chgVar h) stk)
         (form_substs (map putVar h ++ [(x,t)]) f) =
 Mix.fsubst x (nam2mix_term [] t) (nam2mix stk f).
Proof.
 revert stk h.
 induction f; intros stk h IV SU NI CL; cbn in *; auto.
 - f_equal.
   injection (nam2mix_term_substs stk h x t (Fun "" l)); auto.
 - f_equal; auto.
 - f_equal. apply IHf1; auto. eapply Inv_subset; eauto. varsdec.
   apply IHf2; auto. eapply Inv_subset; eauto. varsdec.
 - rewrite !unassoc_app. cbn.
   set (g' := list_unassoc v (map putVar h)).
   set (g := list_unassoc v h).
   case eqbspec; cbn.
   + intros <-.
     rewrite app_nil_r.
     unfold Mix.fsubst.
     rewrite form_vmap_id.
     2:{ intros v. unfold Mix.varsubst. case eqbspec; auto.
         intros <-. rewrite nam2mix_fvars. simpl. varsdec. }
     change
       (nam2mix (map (chgVar h) stk)
                (form_substs (map putVar h) (Quant q x f))
        = nam2mix stk (Quant q x f)).
     apply nam2mix_substs_rename; auto.
     eapply Inv_subset; eauto. cbn. varsdec.
   + intros NE.
     destruct (Vars.mem _ _) eqn:MM; cbn -[form_subst]; f_equal.
     * set (vars := Vars.union _ _).
       assert (Hz := fresh_var_ok vars).
       set (z := fresh_var vars) in *. clearbody z.
       rewrite Vars.mem_spec in MM.
(*
       assert (NI' : ~Vars.In v (suboutvars g')).
       { unfold g'.
         revert IV. clear.
         induction h as [|(a,b) h IH]; simpl; auto.
         - varsdec.
         - case eqbspec; simpl. intros <-. intro. intuition.
           intros NE. rewrite Vars.union_spec. intuition. }
       assert (IN : Vars.In v (term_vars t)).
       { clear -MM NI' NE. unfold suboutvars in *.
         rewrite vars_unionmap_app in MM. cbn in MM. varsdec. }
       rewrite <-Vars.mem_spec in IN. rewrite IN. simpl.
       set (vars' := Vars.union _ (Vars.union (term_vars t) _)) in *.
       assert (Hz' := fresh_var_ok vars').
       set (z' := fresh_var vars') in *.
*)
       set (vars0 := Vars.union vars (vars_of_list stk)).
       assert (Hz0 := fresh_var_ok vars0).
       set (z0 := fresh_var vars0) in *. clearbody z0.
       set (stk' := map (fun a => if a =? z then z0 else a) stk).
       assert
         (nam2mix (z :: map (chgVar h) stk)
                  (form_substs ((v,Var z)::g' ++ [(x,t)]) f) =
          nam2mix (map (chgVar ((v,z)::g)) (v::stk'))
                  (form_substs (map putVar ((v,z)::g) ++ [(x,t)]) f)).
       { admit. }
       change Vars.elt with variable in *.
       rewrite H.
(*
       assert ((v,Var z) :: list_unassoc v (map putVar h) =
               map putVar ((v,z)::list_unassoc v h)).
       { clear. simpl. f_equal.
         induction h as [|(a,b) h IH]; simpl; auto.
         case eqbspec; simpl; auto.
         intros _. f_equal; auto. }
       rewrite app_comm_cons.
       rewrite H0.
*)
       rewrite IHf.
       { f_equal.
         unfold stk'.
         apply (nam2mix_shadowstack_map [v] stk);
          right; rewrite freevars_allvars; varsdec. }
       { simpl. split; [|split].
         - admit.
         - intros a b. admit.
         - admit. }
       { intros a b [[= -> ->]|IN]; simpl; auto.
         assert (Vars.In a (subinvars g')).
         { unfold g'.
           rewrite subinvars_in. rewrite unassoc_putVar.
           rewrite map_map. apply in_map_iff. now exists (a,b). }
         assert (a <> z).
         { intros ->.
           unfold vars in Hz.
           rewrite subinvars_app in Hz. varsdec0. }
         unfold g in IN. rewrite unassoc_in in IN. right.
         unfold stk'. rewrite in_map_iff.
         exists a.
         case eqbspec; try easy. split; auto. eapply SU. apply IN. }
       { intros [->|IN]; [easy|]. unfold stk' in IN. rewrite in_map_iff in IN.
         destruct IN as (x0 & EQ & IN).
         revert EQ.
         case eqbspec.
         - intros -> ->.
           unfold vars0,vars in Hz0.
           rewrite subinvars_app in Hz0. simpl in Hz0. varsdec0.
         - intros _ ->; auto. }
       { intros v0 [<-|IN].
         - unfold chgVar. simpl. rewrite eqb_refl.
           unfold vars, suboutvars in Hz.
           rewrite vars_unionmap_app in Hz. cbn in Hz.
           varsdec0.
         - unfold stk' in IN. rewrite in_map_iff in IN.
           destruct IN as (x0 & EQ & IN).
           revert EQ.
           case eqbspec.
           + intros -> <-.
             rewrite chgVar_none.
             * unfold vars0, vars, suboutvars in Hz0.
               rewrite vars_unionmap_app in Hz0. simpl in Hz0.
               varsdec0.
             * simpl. case eqbspec.
               { intros <-. unfold vars0, vars in Hz0. varsdec0. }
               { intros _.
                 assert (NO : list_assoc z0 g' = None).
                 { apply list_assoc_notin.
                   rewrite <- subinvars_in.
                   unfold vars0, vars in Hz0.
                   rewrite subinvars_app in Hz0. simpl in Hz0.
                   varsdec0. }
                 revert NO.
                 unfold g'. rewrite unassoc_putVar. fold g.
                 rewrite assoc_putVar.
                 now destruct (list_assoc z0 g). }
           + intros NE' ->.
             unfold chgVar. simpl.
             case eqbspec.
             * intros _.
               unfold vars, suboutvars in Hz.
               rewrite vars_unionmap_app in Hz. simpl in Hz. varsdec0.
             * intros NE''.
               fold (chgVar g v0). unfold g.
               rewrite chgVar_unassoc_else by auto.
               now apply CL. }
     * assert (~Vars.In v (term_vars t)).
       { clear -MM NE. unfold suboutvars in *.
         rewrite vars_unionmap_app in MM. cbn in MM.
         rewrite <-not_true_iff_false, Vars.mem_spec in MM.
         varsdec. }
       assert
         (nam2mix (v :: map (chgVar h) stk)
                  (form_substs (g' ++ [(x,t)]) f) =
          nam2mix (map (chgVar g) (v::stk))
                  (form_substs (map putVar g ++ [(x,t)]) f)).
       { admit. }
       change Vars.elt with variable in *.
       rewrite H0.
       apply IHf.
       { apply Inv_unassoc.
         eapply Inv_subset; eauto. simpl. varsdec. }
       { intros a b. unfold g.
         rewrite unassoc_in. intros (IN,_); simpl; eauto. }
       { simpl. intros [->|IN]; intuition. }
       { intros v0.
         case (eqbspec v0 v).
         - intros -> _.
           unfold g. now rewrite chgVar_unassoc_at.
         - intros NE' [->|IN]; [easy|].
           unfold g. rewrite chgVar_unassoc_else; auto. }
Admitted.

Lemma nam2mix_substs_init x t f:
 nam2mix [] (form_substs [(x,t)] f) =
 nam2mix [] (form_subst x t f).
Proof.
 rewrite nam2mix_subst.
 apply (nam2mix_substs [] []); simpl; intuition.
Qed.

Lemma substs_subst x t f:
 AlphaEq (form_substs [(x,t)] f) (form_subst x t f).
Proof.
 apply nam2mix_AlphaEq.
 apply nam2mix_substs_init.
Qed.
