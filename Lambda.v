
(** * A link with Lambda Calculus *)

(** The NatDed development, Pierre Letouzey, Samuel Ben Hamou, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Utils Defs Mix Meta.
Import ListNotations.
Local Open Scope list.
Local Open Scope eqb_scope.

Inductive term :=
  | Var : nat -> term
  | App : term -> term -> term
  | Abs : term -> term
  | One : term
  | Nabla : term -> term
  | Couple : term -> term -> term
  | Pi1 : term -> term
  | Pi2 : term -> term
  | Case : term -> term -> term -> term
  | I1 : term -> term
  | I2 : term -> term.

Inductive type :=
  | Arr : type -> type -> type
  | Atom : name -> type
  | Bot : type
  | Unit : type
  | And : type -> type -> type
  | Or : type -> type -> type.

Definition context := list type.

Inductive typed : context -> term -> type -> Prop :=
  | Type_Var : forall Γ τ n, nth_error Γ n = Some τ -> typed Γ (Var n) τ
  | Type_App : forall Γ u v σ τ, typed Γ u (Arr σ τ) -> typed Γ v σ -> typed Γ (App u v) τ
  | Type_Abs : forall Γ u σ τ,  typed (σ :: Γ) u τ -> typed Γ (Abs u) (Arr σ τ)
  | Type_One : forall Γ, typed Γ One Unit
  | Type_Nabla : forall Γ u τ, typed Γ u Bot -> typed Γ (Nabla u) τ
  | Type_Couple : forall Γ u v σ τ, typed Γ u σ -> typed Γ v τ ->
                                    typed Γ (Couple u v) (And σ τ)
  | Type_Pi1 : forall Γ u σ τ, typed Γ u (And σ τ) -> typed Γ (Pi1 u) σ
  | Type_Pi2 : forall Γ u σ τ, typed Γ u (And σ τ) -> typed Γ (Pi2 u) τ
  | Type_Case : forall Γ u v1 v2 τ1 τ2 σ, typed Γ u (Or τ1 τ2) -> typed (τ1 :: Γ) v1 σ ->
                                          typed (τ2 :: Γ) v2 σ -> typed Γ (Case u v1 v2) σ
  | Type_I1 : forall Γ u σ τ, typed Γ u σ -> typed Γ (I1 u) (Or σ τ)
  | Type_I2 : forall Γ u σ τ, typed Γ u τ -> typed Γ (I2 u) (Or σ τ).

Hint Constructors typed.

Notation "u @ v" := (App u v) (at level 20) : lambda_scope.
Notation "∇ u" := (Nabla u) (at level 20) : lambda_scope.
(*Notation "u , v" := (Couple u v) (at level 20) : lambda_scope. *)
Notation "σ -> τ" := (Arr σ τ) : lambda_scope.
Notation "σ /\ τ" := (And σ τ) : lambda_scope.
Notation "σ \/ τ" := (Or σ τ) : lambda_scope.
Notation "# n" := (Var n) (at level 20, format "# n") : lambda_scope.

Delimit Scope lambda_scope with lam.
Bind Scope lambda_scope with term.

Open Scope lambda_scope.

Coercion Var : nat >-> term.
Check Abs 0 @ 0.

Fixpoint to_form (t : type) : formula :=
  match t with
    | Arr u v => ((to_form u) -> (to_form v))%form
    | Atom a => Pred a []
    | Unit => True
    | Bot => False
    | And u v => ((to_form u) /\ (to_form v))%form
    | Or u v => ((to_form u) \/ (to_form v))%form
  end.

Definition to_ctxt (Γ : context) := List.map to_form Γ.

Theorem CurryHoward Γ u τ :
  typed Γ u τ -> Pr Intuiti (to_ctxt Γ ⊢ to_form τ).
Proof.
  induction 1; cbn.
  - apply R_Ax.
    apply in_map.
    apply nth_error_In with (n := n); auto.
  - apply R_Imp_e with (A := to_form σ); intuition.
  - apply R_Imp_i. intuition.
  - apply R_Tr_i.
  - apply R_Fa_e. intuition.
  - apply R_And_i; intuition.
  - apply R_And_e1 with (B := to_form τ). intuition.
  - apply R_And_e2 with (A := to_form σ). intuition.
  - eapply R_Or_e; eauto.
  - now apply R_Or_i1.
  - now apply R_Or_i2.
Qed.

Lemma ex : Pr Intuiti ([] ⊢ (Pred "A" [] /\ Pred "B" []) -> (Pred "A" [] \/ Pred "B" [])).
Proof.
  set (typ := Atom "A" /\ Atom "B" -> Atom "A" \/ Atom "B").
  change (Pr J (to_ctxt [] ⊢ to_form typ)).
  apply CurryHoward with (u := (Abs (I1 (Pi1 (#0))))).
  unfold typ.
  apply Type_Abs.
  apply Type_I1.
  apply Type_Pi1 with (τ := Atom "B").
  apply Type_Var.
  easy.
Qed.

Instance eqb_type : Eqb type :=
 fix eqb_type (u v:type) :=
   match u, v with
   | Unit, Unit | Bot, Bot => true
   | Atom a, Atom b => a =? b
   | Arr u1 u2, Arr v1 v2
   | And u1 u2, And v1 v2
   | Or u1 u2, Or v1 v2 => eqb_type u1 v1 && eqb_type u2 v2
   | _, _ => false
   end.

Instance eqbspec_type : EqbSpec type.
Proof.
 red. induction x; destruct y; cbn; try constructor; try easy.
 - destruct (IHx1 y1), (IHx2 y2); cbn; constructor; congruence.
 - case eqbspec; constructor; congruence.
 - destruct (IHx1 y1), (IHx2 y2); cbn; constructor; congruence.
 - destruct (IHx1 y1), (IHx2 y2); cbn; constructor; congruence.
Qed.

Lemma list_index_nth_error {A} `(EqbSpec A) n x l :
  list_index x l = Some n -> nth_error l n = Some x.
Proof.
 revert n. induction l; intros n; cbn; try easy.
 case eqbspec. now intros -> [= <-].
 intros N. destruct (list_index x l); try easy. cbn.
 intros [= <-]. cbn; auto.
Qed.

Fixpoint of_form (f : formula) : type :=
  match f with
  | True => Unit
  | False => Bot
  | Pred a _ => Atom a
  | Not A => Arr (of_form A) Bot
  | (A->B) => Arr (of_form A) (of_form B)
  | (A/\B) => And (of_form A) (of_form B)
  | (A\/B) => Or (of_form A) (of_form B)
  | Quant _ A => of_form A
  end%form.

Definition of_ctxt (Γ : Mix.context) := List.map of_form Γ.

Lemma of_to_form T : of_form (to_form T) = T.
Proof.
 induction T; cbn; now f_equal.
Qed.

Lemma of_form_bsubst n t A :
 of_form (bsubst n t A) = of_form A.
Proof.
 revert n t; induction A; cbn; intros; auto.
 - now f_equal.
 - destruct o; f_equal; auto.
Qed.

Theorem CurryHoward_recip seq :
  Pr Intuiti seq ->
  let '(Γ ⊢ A) := seq in exists u, typed (of_ctxt Γ) u (of_form A).
Proof.
 induction 1; cbn in *.
 - unfold of_ctxt.
   apply (in_map of_form) in H.
   rewrite <- list_index_in in H.
   destruct (list_index (of_form A) (map of_form Γ)) eqn:E; try easy.
   exists (Var n). constructor.
   apply list_index_nth_error; eauto with *.
 - exists One; auto.
 - destruct IHPr as (u,P). exists (Nabla u); auto.
 - destruct IHPr as (u,P). exists (Abs u); auto.
 - destruct IHPr1 as (u,P), IHPr2 as (v,Q). exists (v @ u); eauto.
 - destruct IHPr1 as (u,P), IHPr2 as (v,Q). exists (Couple u v); eauto.
 - destruct IHPr as (u,P). exists (Pi1 u); eauto.
 - destruct IHPr as (u,P). exists (Pi2 u); eauto.
 - destruct IHPr as (u,P). exists (I1 u); auto.
 - destruct IHPr as (u,P). exists (I2 u); auto.
 - destruct IHPr1 as (u,P), IHPr2 as (v,Q), IHPr3 as (w,R).
   exists (Case u v w); eauto.
 - destruct IHPr as (u,P). exists (Abs u); auto.
 - destruct IHPr1 as (u,P), IHPr2 as (v,Q). exists (u @ v); eauto.
 - destruct IHPr as (u,P). rewrite of_form_bsubst in P.
   now exists u.
 - destruct IHPr as (u,P). exists u. now rewrite of_form_bsubst.
 - destruct IHPr as (u,P). exists u. now rewrite of_form_bsubst in P.
 - destruct IHPr1 as (u,P), IHPr2 as (v,Q).
   rewrite of_form_bsubst in Q. exists (Abs v @ u); eauto.
 - easy.
Qed.

Theorem CurryHoward_recip' Γ A :
  Pr Intuiti (Γ ⊢ A) -> exists u, typed (of_ctxt Γ) u (of_form A).
Proof.
 apply CurryHoward_recip.
Qed.
