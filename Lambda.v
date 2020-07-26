
(* A link with Lambda Calculus. *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs Mix List.
Import ListNotations.
Open Scope list.

Inductive term :=
  | Var : nat -> term
  | App : term -> term -> term
  | Abs : term -> term
  | Nabla : term -> term
  | Couple : term -> term -> term
  | Pi1 : term -> term
  | Pi2 : term -> term.

Inductive type :=
  | Arr : type -> type -> type
  | Atom : name -> type
  | Bot : type
  | And : type -> type -> type.

Definition context := list type.

Inductive typed : context -> term -> type -> Prop :=
  | Type_Var : forall Γ τ n, nth_error Γ n = Some τ -> typed Γ (Var n) τ
  | Type_App : forall Γ u v σ τ, typed Γ u (Arr σ τ) -> typed Γ v σ -> typed Γ (App u v) τ
  | Type_Abs : forall Γ u σ τ,  typed (σ :: Γ) u τ -> typed Γ (Abs u) (Arr σ τ)
  | Type_Nabla : forall Γ u τ, typed Γ u Bot -> typed Γ (Nabla u) τ
  | Type_Couple : forall Γ u v σ τ, typed Γ u σ -> typed Γ v τ -> typed Γ (Couple u v) (And σ τ)
  | Type_Pi1 : forall Γ u σ τ, typed Γ u (And σ τ) -> typed Γ (Pi1 u) σ
  | Type_Pi2 : forall Γ u σ τ, typed Γ u (And σ τ) -> typed Γ (Pi2 u) τ.

Notation "u @ v" := (App u v) (at level 20) : lambda_scope.
Notation "∇ u" := (Nabla u) (at level 20) : lambda_scope.
Notation "u , v" := (Couple u v) (at level 20) : lambda_scope.
Notation "σ -> τ" := (Arr σ τ) : lambda_scope.
Notation "σ /\ τ" := (And σ τ) : lambda_scope.
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
    | Bot => False
    | And u v => ((to_form u) /\ (to_form v))%form
  end.

Definition to_ctxt (Γ : context) := List.map to_form Γ.

Lemma In_in τ Γ :
  In τ Γ -> In (to_form τ) (to_ctxt Γ).
Proof.
  induction Γ.
  - intros. inversion H.
  - intros.
    assert (a :: Γ = [a] ++ Γ). { easy. }
    rewrite H0 in H. clear H0.
    apply in_app_or in H.
    destruct H.
    + inversion H; [ | inversion H0 ].
      unfold to_ctxt. rewrite List.map_cons.
      rewrite H0.
      apply in_eq.
    + unfold to_ctxt. rewrite List.map_cons.
      apply in_cons.
      apply IHΓ. assumption.
Qed.

Theorem CurryHoward Γ u τ :
  typed Γ u τ -> Pr Intuiti (to_ctxt Γ ⊢ to_form τ).
Proof.
  revert Γ. revert τ.
  induction u.
  - intros.
    inversion H. clear Γ0 τ0 n0 H1 H0 H3.
    apply R_Ax.
    apply In_in.
    apply nth_error_In with (n := n); auto.
  - intros.
    inversion H. clear H2 H0 H1 H4.
    apply R_Imp_e with (A := to_form σ).
    + specialize IHu1 with (τ := σ -> τ) (Γ := Γ).
      cbn in IHu1.
      intuition.
    + specialize IHu2 with (τ := σ) (Γ := Γ).
      intuition.
  - intros.
    inversion H. clear Γ0 u0 H1 H0.
    rewrite<- H3 in H. clear H3.
    specialize IHu with (τ := τ0) (Γ := σ :: Γ).
    cbn. apply R_Imp_i.
    intuition.
  - intros.
    inversion H. clear Γ0 u0 τ0 H1 H0 H3.
    specialize IHu with (τ := Bot) (Γ := Γ). cbn in IHu.
    apply R_Fa_e.
    intuition.
  - intros.
    inversion H. clear Γ0 H2 H0 H1.
    rewrite<- H4 in H. clear H4.
    cbn. apply R_And_i.
    + specialize IHu1 with (τ := σ) (Γ := Γ).
      intuition.
    + specialize IHu1 with (τ := τ) (Γ := Γ).
      intuition.
  - intros.
    inversion H. clear Γ0 u0 σ H1 H0 H3.
    apply R_And_e1 with (B := to_form τ0).
    specialize IHu with (τ := τ /\ τ0) (Γ := Γ).
    intuition.
  - intros.
    inversion H. clear Γ0 u0 τ0 H1 H0 H3.
    apply R_And_e2 with (A := to_form σ).
    specialize IHu with (τ := σ /\ τ) (Γ := Γ).
    intuition.
Qed.