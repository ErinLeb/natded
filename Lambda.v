
(** * A link with Lambda Calculus *)

(** The NatDed development, Pierre Letouzey, Samuel Ben Hamou, 2019-2020.
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
  | Pi2 : term -> term
  | Case : term -> term -> term -> term
  | I1 : term -> term
  | I2 : term -> term.

Inductive type :=
  | Arr : type -> type -> type
  | Atom : name -> type
  | Bot : type
  | And : type -> type -> type
  | Or : type -> type -> type.

Definition context := list type.

Inductive typed : context -> term -> type -> Prop :=
  | Type_Var : forall Γ τ n, nth_error Γ n = Some τ -> typed Γ (Var n) τ
  | Type_App : forall Γ u v σ τ, typed Γ u (Arr σ τ) -> typed Γ v σ -> typed Γ (App u v) τ
  | Type_Abs : forall Γ u σ τ,  typed (σ :: Γ) u τ -> typed Γ (Abs u) (Arr σ τ)
  | Type_Nabla : forall Γ u τ, typed Γ u Bot -> typed Γ (Nabla u) τ
  | Type_Couple : forall Γ u v σ τ, typed Γ u σ -> typed Γ v τ ->
                                    typed Γ (Couple u v) (And σ τ)
  | Type_Pi1 : forall Γ u σ τ, typed Γ u (And σ τ) -> typed Γ (Pi1 u) σ
  | Type_Pi2 : forall Γ u σ τ, typed Γ u (And σ τ) -> typed Γ (Pi2 u) τ
  | Type_Case : forall Γ u v1 v2 τ1 τ2 σ, typed Γ u (Or τ1 τ2) -> typed (τ1 :: Γ) v1 σ ->
                                          typed (τ2 :: Γ) v2 σ -> typed Γ (Case u v1 v2) σ
  | Type_I1 : forall Γ u σ τ, typed Γ u σ -> typed Γ (I1 u) (Or σ τ)
  | Type_I2 : forall Γ u σ τ, typed Γ u τ -> typed Γ (I2 u) (Or σ τ).

Notation "u @ v" := (App u v) (at level 20) : lambda_scope.
Notation "∇ u" := (Nabla u) (at level 20) : lambda_scope.
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
    | Bot => False
    | And u v => ((to_form u) /\ (to_form v))%form
    | Or u v => ((to_form u) \/ (to_form v))%form
  end.

Definition to_ctxt (Γ : context) := List.map to_form Γ.

Theorem CurryHoward Γ u τ :
  typed Γ u τ -> Pr Intuiti (to_ctxt Γ ⊢ to_form τ).
Proof.
  induction 1.
  - apply R_Ax.
    apply in_map.
    apply nth_error_In with (n := n); auto.
  - apply R_Imp_e with (A := to_form σ); intuition.
  - apply R_Imp_i. intuition.
  - apply R_Fa_e. intuition.
  - apply R_And_i; intuition.
  - apply R_And_e1 with (B := to_form τ). intuition.
  - apply R_And_e2 with (A := to_form σ). intuition.
  - apply R_Or_e with (A := to_form τ1) (B := to_form τ2); intuition.
  - apply R_Or_i1 with (B := to_form τ). intuition.
  - apply R_Or_i2 with (A := to_form σ). intuition.
Qed.

Lemma ex : Pr Intuiti ([] ⊢ (Pred "A" [] /\ Pred "B" []) -> (Pred "A" [] \/ Pred "B" [])).
Proof.
  set (A := Pred "A" []). set (B := Pred "B" []).
  set (form := (_ -> _)%form). set (typ := Atom "A" /\ Atom "B" -> Atom "A" \/ Atom "B").
  assert (to_form typ = form).
  { intuition. }
  rewrite<- H.
  assert (to_ctxt [] = []).
  { intuition. }
  rewrite<- H0.
  apply CurryHoward with (u := (Abs (I1 (Pi1 (#0))))).
  unfold typ.
  apply Type_Abs.
  apply Type_I1.
  apply Type_Pi1 with (τ := Atom "B").
  apply Type_Var.
  intuition.
Qed.
