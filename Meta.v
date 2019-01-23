
(** Some Meta-properties (proved on the Mix encoding) *)

Require Import RelationClasses Arith Omega Defs Proofs Mix.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

Lemma closed_bsubst n u t :
 term_closed t = true -> term_bsubst n u t = t.
Proof.
 unfold term_closed.
 case Nat.eqb_spec; [ intros H _ | easy ].
 revert t H.
 fix IH 1. destruct t; simpl; try easy.
 intros H. f_equal. clear f.
 revert l H.
 fix IH' 1. destruct l; simpl; try easy.
 intros H. f_equal. apply IH. omega with *. apply IH'. omega with *.
Qed.

Lemma freevars_fsubst v u t :
 ~Vars.In v (term_fvars t) -> term_fsubst v u t = t.
Proof.
 revert t.
 fix IH 1. destruct t; simpl; trivial.
 - case string_eqb_spec; trivial. intros <-. varsdec.
 - intros H. f_equal. clear f.
   revert l H.
   fix IH' 1. destruct l; simpl; trivial.
   intros H. f_equal. apply IH. varsdec. apply IH'. varsdec.
Qed.

Lemma term_fsubst_bsubst v t n u T :
  ~Vars.In v (term_fvars u) ->
  term_closed t = true ->
  term_fsubst v t (term_bsubst n u T) =
  term_bsubst n u (term_fsubst v t T).
Proof.
 revert T. fix IH 1. destruct T; simpl; intros.
 - case string_eqb_spec; simpl; auto.
   intros <-. now rewrite closed_bsubst.
 - case Nat.eqb_spec; simpl; auto.
   intros _. now apply freevars_fsubst.
 - f_equal. clear f.
   revert l. fix IH' 1. destruct l; simpl; trivial.
   f_equal. now apply IH. now apply IH'.
Qed.

Lemma fsubst_bsubst v t n u f :
  ~Vars.In v (term_fvars u) ->
  term_closed t = true ->
  form_fsubst v t (form_bsubst n u f) =
  form_bsubst n u (form_fsubst v t f).
Proof.
 revert n.
 induction f; simpl; intros; f_equal; auto.
 injection (term_fsubst_bsubst v t n u (Fun "" l)); auto.
Qed.


Definition subst := list (variable * term).

Definition subinvars (sub : subst) :=
  List.fold_right (fun p vs => Vars.add (fst p) vs) Vars.empty sub.

Definition suboutvars (sub : subst) :=
  vars_flatmap (fun '(_,t) => term_fvars t) sub.

Definition subvars (sub : subst) :=
  Vars.union (subinvars sub) (suboutvars sub).

Definition sub_closed (sub : subst) :=
  forallb (fun '(_,t) => term_closed t) sub.

Lemma fresh_fsubsts sub s z :
  Vars.In z (freevars_seq (seq_fsubsts sub s)) ->
  Vars.In z (Vars.union (freevars_seq s) (subvars sub)).
Proof.
destruct s as (c,f). simpl.
unfold freevars_seq.
Admitted.

Lemma form_fsubsts_notIn sub x t A :
 ~Vars.In x (freevars A) ->
 form_fsubsts ((x, t) :: sub) A = form_fsubsts sub A.
Proof.
Admitted.

Lemma ctx_fsubsts_notIn sub x t Γ:
 ~Vars.In x (freevars_ctx Γ) ->
 ctx_fsubsts ((x,t)::sub) Γ = ctx_fsubsts sub Γ.
Proof.
Admitted.

Lemma term_fsubsts_bsubst sub n u t :
 sub_closed sub = true ->
 term_fsubsts sub (term_bsubst n u t) =
  term_bsubst n (term_fsubsts sub u) (term_fsubsts sub t).
Proof.
 intros CL.
 revert t.
 fix IH 1. destruct t; simpl; auto.
 - destruct (list_assoc v sub) eqn:E; simpl; auto.
   symmetry. apply closed_bsubst.
   (* TODO sub lemma... *)
   clear IH.
   induction sub as [|(x,w) sub IH]; simpl in *; try easy.
   rewrite andb_true_iff in *.
   revert E. case string_eqb_spec.
   + intros <- [= ->]. easy.
   + intuition.
 - case Nat.eqb_spec; simpl; auto.
 - f_equal. clear f.
   revert l. fix IH' 1. destruct l; simpl; auto.
   f_equal. apply IH. apply IH'.
Qed.

Lemma fsubsts_bsubst sub n u A :
 sub_closed sub = true ->
 form_fsubsts sub (form_bsubst n u A) =
  form_bsubst n (term_fsubsts sub u) (form_fsubsts sub A).
Proof.
 intros CL. revert n.
 induction A; simpl; intros n; f_equal; auto.
 injection (term_fsubsts_bsubst sub n u (Fun "" l)); auto.
Qed.

Lemma fsubst_bsubst_adhoc sub x t A :
 sub_closed ((x,t)::sub) = true ->
 ~Vars.In x (freevars A) ->
 form_fsubsts ((x,t)::sub) (form_bsubst 0 (FVar x) A) =
 form_bsubst 0 t (form_fsubsts sub A).
Proof.
 intros.
 rewrite fsubsts_bsubst by trivial.
 simpl. case string_eqb_spec; [intros _ |easy].
 f_equal.
 now apply form_fsubsts_notIn.
Qed.

Lemma Pr_fsubsts logic s :
  Pr logic s ->
  forall sub, sub_closed sub = true ->
  Pr logic (seq_fsubsts sub s).
Proof.
 induction 1; simpl in *; intros; auto.
 - apply R_Ax. unfold ctx_fsubsts.
   now apply in_map.
 - apply R_Not_e with (form_fsubsts sub A); auto.
 - apply R_And_e1 with (form_fsubsts sub B); auto.
 - apply R_And_e2 with (form_fsubsts sub A); auto.
 - apply R_Or_e with (form_fsubsts sub A) (form_fsubsts sub B); auto.
 - apply R_Imp_e with (form_fsubsts sub A); auto.
 - set (vars := Vars.union (freevars_seq (Γ⊢A)) (subvars sub)).
   set (z := fresh_var vars).
   apply R_All_i with z.
   + intros H'. apply (fresh_fsubsts sub (Γ⊢A) z) in H'.
     apply (fresh_var_ok vars). exact H'.
   + specialize (IHPr ((x,FVar z)::sub)).
     rewrite ctx_fsubsts_notIn in IHPr by varsdec.
     rewrite <- fsubst_bsubst_adhoc with (x:=x); auto. varsdec.
 - rewrite fsubsts_bsubst by auto.
   apply R_All_e; auto.
 - specialize (IHPr sub).
   rewrite fsubsts_bsubst in IHPr by auto.
   apply R_Ex_i with (term_fsubsts sub t); auto.
 - set (vars := Vars.union (freevars_seq (A::Γ⊢B)) (subvars sub)).
   set (z := fresh_var vars).
   apply R_Ex_e with z (form_fsubsts sub A).
   + intros H'. apply (fresh_fsubsts sub (A::Γ⊢B) z) in H'.
     apply (fresh_var_ok vars). exact H'.
   + now apply IHPr1.
   + specialize (IHPr2 ((x,FVar z)::sub)).
     rewrite ctx_fsubsts_notIn in IHPr2 by varsdec.
     rewrite fsubst_bsubst_adhoc in IHPr2; auto; try varsdec.
     rewrite form_fsubsts_notIn in IHPr2 by varsdec.
     auto.
 - apply R_Absu with l. auto.
Qed.

Definition Subset {A} (l l': list A) :=
  forall a, In a l -> In a l'.

Inductive SubsetSeq : sequent -> sequent -> Prop :=
 | SubSeq Γ Γ' A : Subset Γ Γ' -> SubsetSeq (Γ⊢A) (Γ'⊢A).
Hint Constructors SubsetSeq.

Lemma Subset_cons {A} (l l': list A) x :
  Subset l l' -> Subset (x::l) (x::l').
Proof.
 intros H y [Hy|Hy]; simpl; auto.
Qed.
Hint Resolve Subset_cons.

Lemma Pr_weakening logic s s' :
  Pr logic s ->
  SubsetSeq s s' ->
  Pr logic s'.
Proof.
 intros H. revert s'.
 induction H; inversion_clear 1; auto.
 - apply R_Not_e with A; auto.
 - apply R_And_e1 with B; auto.
 - apply R_And_e2 with A; auto.
 - apply R_Or_e with A B; auto.
 - apply R_Imp_e with A; auto.
 - admit. (*now apply R_All_i with x.*)
 - admit. (*now apply R_Ex_i with t.*)
 - admit. (*now apply R_Ex_e with x A.*)
 - admit.
Admitted.
