
(** * Some examples of proofs in the Mix encoding *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Meta.
Import ListNotations.

Local Open Scope form.

(** Some usual proofs *)

Lemma DoubleNeg_i logic A : Pr logic ([A] ⊢ ~~A).
Proof.
 apply R_Not_i.
 apply R_Not_e with A; [apply Pr_pop, R'_Ax|apply R'_Ax].
Qed.

Lemma Excluded_Middle_core logic A :
 Pr logic ([] ⊢ ~~(A\/~A)).
Proof.
 apply R_Not_i.
 apply R_Not_e with (A\/~A); [|apply R'_Ax].
 apply R_Or_i2.
 apply R_Not_i.
 apply R_Not_e with (A\/~A); [|apply Pr_pop, R'_Ax ].
 apply R_Or_i1.
 apply R'_Ax.
Qed.

Lemma Contra logic Γ A B :
 Pr logic (Γ ⊢ A -> B) -> Pr logic (Γ ⊢ ~B -> ~A).
Proof.
 intros.
 apply R_Imp_i.
 apply R_Not_i. apply R_Not_e with B.
 - eapply R_Imp_e.
   + apply Pr_pop, Pr_pop. exact H.
   + apply R'_Ax.
 - apply Pr_pop, R'_Ax.
Qed.

Lemma ContraIff logic Γ A B :
 Pr logic (Γ ⊢ A <-> B) -> Pr logic (Γ ⊢ ~A <-> ~B).
Proof.
 intros.
 apply R_And_i.
 - apply Contra. eapply R_And_e2. apply H.
 - apply Contra. eapply R_And_e1. apply H.
Qed.

Lemma AndImp Γ logic A B A' B' :
 Pr logic (Γ ⊢ A -> B) ->
 Pr logic (Γ ⊢ A' -> B') ->
 Pr logic (Γ ⊢ A /\ A' -> B /\ B').
Proof.
 intros H H'.
 apply R_Imp_i.
 apply R'_And_e, R_And_i.
 - eapply R_Imp_e; try apply R'_Ax. apply Pr_pop, Pr_pop, H.
 - apply Pr_pop. eapply R_Imp_e; try apply R'_Ax. apply Pr_pop, H'.
Qed.

Lemma AndIff Γ logic A B A' B' :
 Pr logic (Γ ⊢ A <-> B) ->
 Pr logic (Γ ⊢ A' <-> B') ->
 Pr logic (Γ ⊢ A /\ A' <-> B /\ B').
Proof.
 intros H H'.
 apply R_And_i; apply AndImp.
 - eapply R_And_e1, H.
 - eapply R_And_e1, H'.
 - eapply R_And_e2, H.
 - eapply R_And_e2, H'.
Qed.

Lemma OrImp Γ logic A B A' B' :
 Pr logic (Γ ⊢ A -> B) ->
 Pr logic (Γ ⊢ A' -> B') ->
 Pr logic (Γ ⊢ A \/ A' -> B \/ B').
Proof.
 intros H H'.
 apply R_Imp_i.
 apply R'_Or_e.
 - apply R_Or_i1. eapply R_Imp_e; try apply R'_Ax. apply Pr_pop, H.
 - apply R_Or_i2. eapply R_Imp_e; try apply R'_Ax. apply Pr_pop, H'.
Qed.

Lemma OrIff Γ logic A B A' B' :
 Pr logic (Γ ⊢ A <-> B) ->
 Pr logic (Γ ⊢ A' <-> B') ->
 Pr logic (Γ ⊢ A \/ A' <-> B \/ B').
Proof.
 intros H H'.
 apply R_And_i; apply OrImp.
 - eapply R_And_e1, H.
 - eapply R_And_e1, H'.
 - eapply R_And_e2, H.
 - eapply R_And_e2, H'.
Qed.

Lemma ImpImp Γ logic A B A' B' :
 Pr logic (Γ ⊢ B -> A) ->
 Pr logic (Γ ⊢ A' -> B') ->
 Pr logic (Γ ⊢ (A -> A') -> (B -> B')).
Proof.
 intros H H'.
 apply R_Imp_i, R_Imp_i.
 eapply R_Imp_e. apply Pr_pop, Pr_pop, H'.
 eapply R_Imp_e. apply Pr_pop, R'_Ax.
 eapply R_Imp_e. apply Pr_pop, Pr_pop, H. apply R'_Ax.
Qed.

Lemma ImpIff Γ logic A B A' B' :
 Pr logic (Γ ⊢ A <-> B) ->
 Pr logic (Γ ⊢ A' <-> B') ->
 Pr logic (Γ ⊢ (A -> A') <-> (B -> B')).
Proof.
 intros H H'.
 apply R_And_i; apply ImpImp.
 - eapply R_And_e2, H.
 - eapply R_And_e1, H'.
 - eapply R_And_e1, H.
 - eapply R_And_e2, H'.
Qed.

Lemma OpIff Γ logic A B A' B' o :
 Pr logic (Γ ⊢ A <-> B) ->
 Pr logic (Γ ⊢ A' <-> B') ->
 Pr logic (Γ ⊢ Op o A A' <-> Op o B B').
Proof.
 intros H H'. destruct o.
 now apply AndIff. now apply OrIff. now apply ImpIff.
Qed.

Lemma QuantIff logic Γ A B q :
 Pr logic (Γ ⊢ ∀ (A <-> B)) ->
 Pr logic (Γ ⊢ Quant q A <-> Quant q B).
Proof.
 intros H.
 apply R_And_i; apply R_Imp_i.
 - destruct q.
   + set (s := _⊢_). unfold s.
     destruct (exist_fresh (fvars s)) as (v,Hv).
     apply R_All_i with (x:=v); auto.
     apply R_All_e with (t := FVar v) in H. cbn in H.
     apply R_And_e1 in H.
     eapply R_Imp_e. apply Pr_pop. exact H.
     apply R_All_e, R'_Ax.
   + set (s := _⊢_). unfold s.
     destruct (exist_fresh (fvars s)) as (v,Hv).
     apply R'_Ex_e with (x:=v); auto.
     apply R_Ex_i with (t:=FVar v).
     apply R_All_e with (t := FVar v) in H. cbn in H.
     apply R_And_e1 in H.
     eapply R_Imp_e. apply Pr_pop. exact H.
     apply R'_Ax.
 - destruct q.
   + set (s := _⊢_). unfold s.
     destruct (exist_fresh (fvars s)) as (v,Hv).
     apply R_All_i with (x:=v); auto.
     apply R_All_e with (t := FVar v) in H. cbn in H.
     apply R_And_e2 in H.
     eapply R_Imp_e. apply Pr_pop. exact H.
     apply R_All_e, R'_Ax.
   + set (s := _⊢_). unfold s.
     destruct (exist_fresh (fvars s)) as (v,Hv).
     apply R'_Ex_e with (x:=v); auto.
     apply R_Ex_i with (t:=FVar v).
     apply R_All_e with (t := FVar v) in H. cbn in H.
     apply R_And_e2 in H.
     eapply R_Imp_e. apply Pr_pop. exact H.
     apply R'_Ax.
Qed.

Lemma NotEx_AllNot logic Γ A :
 Pr logic (Γ ⊢ ~∃A) <-> Pr logic (Γ ⊢ ∀~A).
Proof.
 destruct (exist_fresh (fvars (Γ ⊢ A))) as (x,Hx).
 split.
 - intros NE.
   apply R_All_i with x; cbn - [Names.union] in *. namedec.
   apply R_Not_i.
   apply R_Not_e with (∃A)%form; [|now apply Pr_pop].
   apply R_Ex_i with (FVar x); auto using R'_Ax.
 - intros AN.
   apply R_Not_i.
   apply R'_Ex_e with x. cbn in *. namedec.
   eapply R_Not_e; [apply R'_Ax|].
   apply Pr_pop. now apply R_All_e with (t:=FVar x) in AN.
Qed.

(** A few classical proofs *)

Lemma DoubleNeg A :
 Pr K ([] ⊢ ~~A -> A).
Proof.
 apply R_Imp_i.
 apply R_Absu; trivial.
 apply R_Not_e with (~A); apply R_Ax; cbn; auto.
Qed.

Lemma Excluded_Middle A :
 Pr K ([] ⊢ A\/~A).
Proof.
 apply R_Imp_e with (~~(A\/~A)).
 - apply DoubleNeg.
 - apply Excluded_Middle_core.
Qed.

Lemma Peirce A B :
 Pr K ([] ⊢ ((A->B)->A)->A).
Proof.
 apply R_Imp_i.
 apply R_Absu; trivial.
 apply R_Not_e with A; [|apply R'_Ax].
 apply Pr_swap.
 apply R'_Imp_e.
 apply R_Imp_i.
 apply R_Fa_e.
 apply R_Not_e with A; apply R_Ax; cbn; auto.
Qed.

(** Conversely, with these classical laws, we could
    simulate the "Reductio ad absurdum" rule.
    We do this in any logic (which amounts to say intuititionistic) *)

Lemma DoubleNeg_to_Absurdum l Γ A :
 Pr l (Γ ⊢ ~~A->A) ->
 Pr l ((~A) :: Γ ⊢ False) -> Pr l (Γ ⊢ A).
Proof.
 intros DNEG HYP.
 apply R_Imp_e with (~ ~ A).
 - apply DNEG.
 - apply R_Not_i, HYP.
Qed.

Lemma ExcludedMiddle_to_Absurdum l Γ A :
 Pr l (Γ ⊢ A \/ ~A) ->
 Pr l ((~A) :: Γ ⊢ False) -> Pr l (Γ ⊢ A).
Proof.
 intros EM HYP.
 apply R_Or_e with A (~ A).
 - apply EM.
 - apply R'_Ax.
 - apply R_Fa_e. apply HYP.
Qed.

Lemma Pierce_to_Absurdum l Γ A :
 (forall B, Pr l (Γ ⊢ ((A->B)->A)->A)) ->
 Pr l ((~A) :: Γ ⊢ False) -> Pr l (Γ ⊢ A).
Proof.
 intros PEI HYP.
 apply R_Imp_e with ((A->False)->A).
 - apply PEI.
 - apply R_Imp_i.
   apply R_Fa_e.
   apply R_Imp_e with (~A).
   apply Pr_pop.
   apply R_Imp_i; assumption.
   apply R_Not_i.
   apply R_Imp_e with A; apply R_Ax; simpl; auto.
Qed.

Lemma NotExNot Γ A :
 Pr K (Γ ⊢ ~∃~A) <-> Pr K (Γ ⊢ ∀A).
Proof.
 destruct (exist_fresh (fvars (Γ ⊢ A))) as (x,Hx).
 split.
 - intros NEN.
   apply R_All_i with x; cbn - [Names.union] in *. namedec.
   apply R_Absu; auto.
   apply R_Not_e with (∃~A); [|now apply Pr_pop].
   apply R_Ex_i with (FVar x); auto using R'_Ax.
 - intros ALL.
   apply R_Not_i.
   apply R'_Ex_e with x; cbn in *. namedec.
   eapply R_Not_e; [|eapply R'_Ax].
   apply Pr_pop. eapply R_All_e with (t:=FVar x); eauto.
Qed.

Lemma Kontra Γ A B :
 Pr K (Γ ⊢ A -> B) <-> Pr K (Γ ⊢ ~B -> ~A).
Proof.
 split.
 - apply Contra.
 - intros H. apply R_Imp_i. apply R_Absu; auto.
   apply R_Not_e with A.
   + apply Pr_pop, R'_Ax.
   + eapply R_Imp_e.
     * apply Pr_pop, Pr_pop, H.
     * apply R'_Ax.
Qed.

Lemma KontraIff Γ A B :
 Pr K (Γ ⊢ A <-> B) <-> Pr K (Γ ⊢ ~A <-> ~B).
Proof.
 split.
 - apply ContraIff.
 - intros H. apply R_And_i; apply Kontra.
   eapply R_And_e2; eauto. eapply R_And_e1; eauto.
Qed.

(** a tautology used during Henkin extensions in [Theory.v] *)
Lemma ExEx A :
 level A <= 1 ->
 Pr K ([] ⊢ ∃ ((∃ A) -> A)).
Proof.
 intros HA.
 destruct (exist_fresh (fvars A)) as (x,Hx).
 apply R_Or_e with (∃ A) (~∃ A).
 - apply Excluded_Middle.
 - apply R'_Ex_e with x; cbn; try namedec.
   apply R_Ex_i with (FVar x); auto. cbn.
   apply R_Imp_i, Pr_pop, R'_Ax.
 - apply R_Ex_i with (FVar x); auto. cbn.
   rewrite form_level_bsubst_id; auto.
   apply R_Imp_i.
   apply R_Fa_e.
   apply R_Not_e with (∃ A); apply R_Ax; simpl; auto.
Qed.

(** One example of classic law through its derivation *)

Definition Excluded_Middle_core_deriv A :=
 Rule Not_i ([] ⊢ ~~(A\/~A))
  [Rule Not_e ([~(A\/~A)] ⊢ False)
    [Rule Or_i2 ([~(A\/~A)] ⊢ A\/~A)
      [Rule Not_i ([~(A\/~A)] ⊢ ~A)
        [Rule Not_e ([A;~(A\/~A)] ⊢ False)
          [Rule Or_i1 ([A;~(A\/~A)] ⊢ A\/~A)
            [Rule Ax ([A;~(A\/~A)] ⊢ A) []];
           Rule Ax ([A;~(A\/~A)] ⊢ ~(A\/~A)) []]]];
     Rule Ax ([~(A\/~A)] ⊢ ~(A\/~A)) []]]%form.

Lemma Excluded_Middle_core_valid logic A :
 Valid logic (Excluded_Middle_core_deriv A).
Proof.
 unfold Excluded_Middle_core_deriv.
 repeat (econstructor; eauto; unfold In; intuition).
Qed.

Definition Excluded_Middle_deriv A :=
 Rule Absu ([] ⊢ A\/~A)
  (let '(Rule _ _ ds) := Excluded_Middle_core_deriv A in ds).

Lemma Excluded_Middle_valid A :
 Valid K (Excluded_Middle_deriv A).
Proof.
 unfold Excluded_Middle_deriv.
 unfold Excluded_Middle_core_deriv.
 repeat (econstructor; eauto; unfold In; intuition).
Qed.

(* A few examples of proofs in NJ1 and NK1 (Samuel). *)

Lemma ex1 f1 f2 : Provable J ([] ⊢ (f1 /\ f2) -> (f1 \/ f2)).
Proof.
  apply Provable_alt.
  apply R_Imp_i.
  apply R_Or_i1.
  apply R_And_e1 with (B := f2).
  apply R_Ax.
  apply in_eq.
Qed.

Lemma ex2 f1 f2 f3 : Provable J ([] ⊢ (f1 -> f2 -> f3) <-> (f1 /\ f2 -> f3)).
Proof.
  apply Provable_alt.
  apply R_And_i.
  + apply R_Imp_i.
    apply R_Imp_i.
    apply R_Imp_e with (A := f2).
    - apply R_Imp_e with (A := f1).
      * apply R_Ax. apply in_cons. apply in_eq.
      * apply R_And_e1 with (B := f2). apply R_Ax. apply in_eq.
    - apply R_And_e2 with (A := f1). apply R_Ax. apply in_eq.
  + apply R_Imp_i.
    apply R_Imp_i.
    apply R_Imp_i.
    apply R_Imp_e with (A := (f1 /\ f2)%form).
    - apply R_Ax. apply in_cons. apply in_cons. apply in_eq.
    - apply R_And_i; apply R_Ax.
      * apply in_cons. apply in_eq.
      * apply in_eq.
Qed.

Lemma RAA f1 Γ : Pr K (Γ ⊢ ~~f1) -> Pr K (Γ ⊢ f1).
Proof.
  intro.
  apply R_Absu.
  + reflexivity.
  + apply R_Not_e with (A := (~ f1)%form).
    - apply R_Ax. apply in_eq.
    - apply Pr_pop. exact H.
Qed.

Lemma DeMorgan f1 f2 Γ : Pr K (Γ ⊢ ~(~f1 /\ f2)) -> Pr K (Γ ⊢ ~~(f1 \/ ~f2)).
Proof.
  intro.
  apply R_Not_i.
  apply R_Not_e with (A := (~f1 /\ f2)%form).
  + apply RAA with (f1 := (~f1 /\ f2)%form).
    apply R_Not_i.
    apply R_Not_e with (A := (f1\/~f2)%form).
    - apply R_Or_i1.
      apply RAA.
      apply R_Not_i.
      apply R_Not_e with (A := (f1\/~f2)%form).
      * apply R_Or_i2. apply R_Not_i. apply R_Not_e with (A := (~f1 /\ f2)%form).
        ++ apply R_And_i.
           -- apply R_Ax. apply in_cons. apply in_eq.
           -- apply R_Ax. apply in_eq.
        ++ apply R_Ax. apply in_cons. apply in_cons. apply in_eq.
      * apply R_Ax. apply in_cons. apply in_cons. apply in_eq.
    - apply R_Ax. apply in_cons. apply in_eq.
  + apply Pr_pop. exact H.
Qed.

Lemma ExcludedMiddle f1 : Provable K ([] ⊢ f1 \/ ~f1).
Proof.
  apply Provable_alt.
  apply RAA.
  apply DeMorgan with (f2 := f1) (Γ := []).
  apply R_Not_i.
  apply R_Not_e with (A := f1).
  + apply R_And_e2 with (A := (~f1)%form). apply R_Ax. apply in_eq.
  + apply R_And_e1 with (B := f1). apply R_Ax. apply in_eq.
Qed.
