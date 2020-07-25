
(* A link with Lambda Calculus. *)

Require Import Defs Mix List.
Import ListNotations.

Open Scope list.

Inductive term :=
  | Var : nat -> term
  | App : term -> term -> term
  | Abs : term -> term.

Inductive type :=
  | Arr : type -> type -> type
  | Atom : name -> type.

Definition context := list type.

Inductive typed : context -> term -> type -> Prop :=
  | Type_Ax : forall Γ τ n, nth_error Γ n = Some τ -> typed Γ (Var n) τ
  | Type_App : forall Γ u v σ μ, typed Γ u (Arr σ μ) -> typed Γ v σ -> typed Γ (App u v) μ
  | Type_Abs : forall Γ u σ μ,  typed (σ :: Γ) u μ -> typed Γ (Abs u) (Arr σ μ).

Notation "u @ v" := (App u v) (at level 20) : lambda_scope.
Notation "σ -> μ" := (Arr σ μ) : lambda_scope.
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
    specialize IHu with (τ := μ) (Γ := σ :: Γ).
    cbn. apply R_Imp_i.
    intuition.
Qed.