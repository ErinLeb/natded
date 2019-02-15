
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
 case eqbspec; [ intros H _ | easy ].
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
 - case eqbspec; trivial. intros <-. varsdec.
 - intros H. f_equal. clear f.
   revert l H.
   fix IH' 1. destruct l; simpl; trivial.
   intros H. f_equal. apply IH. varsdec. apply IH'. varsdec.
Qed.

(*
Lemma term_fsubst_bsubst v t n u T :
  ~Vars.In v (term_fvars u) ->
  term_closed t = true ->
  term_fsubst v t (term_bsubst n u T) =
  term_bsubst n u (term_fsubst v t T).
Proof.
 revert T. fix IH 1. destruct T; simpl; intros.
 - case eqbspec; simpl; auto.
   intros <-. now rewrite closed_bsubst.
 - case eqbspec; simpl; auto.
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
*)

Definition subinvars (sub : subst) :=
  List.fold_right (fun p vs => Vars.add (fst p) vs) Vars.empty sub.

Definition suboutvars (sub : subst) :=
  vars_flatmap (fun '(_,t) => term_fvars t) sub.

Definition subvars (sub : subst) :=
  Vars.union (subinvars sub) (suboutvars sub).

Definition sub_closed (sub : subst) :=
  forallb (fun '(_,t) => term_closed t) sub.

Lemma list_assoc_suboutvars sub t v :
 list_assoc v sub = Some t ->
 Vars.Subset (term_fvars t) (suboutvars sub).
Proof.
 induction sub as [|(x,u) sub IH]; simpl.
 - easy.
 - case eqbspec.
   + intros <- [= ->]. varsdec.
   + intros NE H. specialize (IH H). varsdec.
Qed.

Lemma term_fresh_fsubsts sub t :
  Vars.Subset (term_fvars (term_fsubsts sub t))
              (Vars.union (term_fvars t) (subvars sub)).
Proof.
 revert t.
 fix IH 1. destruct t; simpl.
 - destruct (list_assoc v sub) eqn:E; simpl; [ | varsdec].
   unfold subvars. apply list_assoc_suboutvars in E. varsdec.
 - varsdec.
 - clear f. revert l. fix IH' 1. destruct l; simpl.
   + varsdec.
   + specialize (IH t). specialize (IH' l). varsdec.
Qed.

Lemma fresh_fsubsts sub f :
  Vars.Subset (freevars (form_fsubsts sub f))
              (Vars.union (freevars f) (subvars sub)).
Proof.
 induction f; simpl; auto; try varsdec.
 apply (term_fresh_fsubsts sub (Fun "" l)).
Qed.

Lemma fresh_fsubsts_ctx sub c :
  Vars.Subset (freevars_ctx (ctx_fsubsts sub c))
              (Vars.union (freevars_ctx c) (subvars sub)).
Proof.
 induction c as [|f c IH]; simpl.
 - varsdec.
 - generalize (fresh_fsubsts sub f). varsdec.
Qed.

Lemma fresh_fsubsts_seq sub s :
  Vars.Subset (freevars_seq (seq_fsubsts sub s))
              (Vars.union (freevars_seq s) (subvars sub)).
Proof.
 destruct s as (c,f). simpl.
 generalize (fresh_fsubsts_ctx sub c) (fresh_fsubsts sub f).
 varsdec.
Qed.

Lemma term_fsubsts_notIn sub x u t :
 ~Vars.In x (term_fvars t) ->
 term_fsubsts ((x, u) :: sub) t = term_fsubsts sub t.
Proof.
 revert t.
 fix IH 1. destruct t; simpl; auto.
 - case eqbspec; auto. varsdec.
 - intros NI. f_equal. clear f.
   revert l NI.
   fix IH' 1. destruct l; simpl; auto.
   intros NI. f_equal. apply IH; varsdec. apply IH'; varsdec.
Qed.

Lemma form_fsubsts_notIn sub x u A :
 ~Vars.In x (freevars A) ->
 form_fsubsts ((x, u) :: sub) A = form_fsubsts sub A.
Proof.
 induction A; simpl; intro NI; f_equal; auto.
 - now injection (term_fsubsts_notIn sub x u (Fun "" l)).
 - apply IHA1. varsdec.
 - apply IHA2. varsdec.
Qed.

Lemma ctx_fsubsts_notIn sub x u c:
 ~Vars.In x (freevars_ctx c) ->
 ctx_fsubsts ((x,u)::sub) c = ctx_fsubsts sub c.
Proof.
 induction c; simpl; intro NI; f_equal; auto.
 apply form_fsubsts_notIn. varsdec.
 apply IHc. varsdec.
Qed.

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
   apply list_assoc_in2 in E.
   unfold sub_closed in CL. rewrite forallb_forall in CL.
   now apply (CL (v,t)).
 - case eqbspec; simpl; auto.
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

Lemma fsubsts_bsubst_adhoc sub x t A :
 sub_closed ((x,t)::sub) = true ->
 ~Vars.In x (freevars A) ->
 form_fsubsts ((x,t)::sub) (form_bsubst 0 (FVar x) A) =
 form_bsubst 0 t (form_fsubsts sub A).
Proof.
 intros.
 rewrite fsubsts_bsubst by trivial.
 simpl. case eqbspec; [intros _ |easy].
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
   + intros H'. apply (fresh_fsubsts_seq sub (Γ⊢A)) in H'.
     apply (fresh_var_ok vars). exact H'.
   + specialize (IHPr ((x,FVar z)::sub)).
     rewrite ctx_fsubsts_notIn in IHPr by varsdec.
     rewrite <- fsubsts_bsubst_adhoc with (x:=x); auto. varsdec.
 - rewrite fsubsts_bsubst by auto.
   apply R_All_e; auto.
 - specialize (IHPr sub).
   rewrite fsubsts_bsubst in IHPr by auto.
   apply R_Ex_i with (term_fsubsts sub t); auto.
 - set (vars := Vars.union (freevars_seq (A::Γ⊢B)) (subvars sub)).
   set (z := fresh_var vars).
   apply R_Ex_e with z (form_fsubsts sub A).
   + intros H'. apply (fresh_fsubsts_seq sub (A::Γ⊢B) z) in H'.
     apply (fresh_var_ok vars). exact H'.
   + now apply IHPr1.
   + specialize (IHPr2 ((x,FVar z)::sub)).
     rewrite ctx_fsubsts_notIn in IHPr2 by varsdec.
     rewrite fsubsts_bsubst_adhoc in IHPr2; auto; try varsdec.
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
