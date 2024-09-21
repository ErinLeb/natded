
(** * Natural deduction, with a Locally Nameless encoding *)

(** The NatDed development, Pierre Letouzey, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs.
Require DecimalString.
Require Import Mix.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope eqb_scope.
(** We use here a Locally nameless representation of terms.
    See for instance http://www.chargueraud.org/research/2009/ln/main.pdf
*)

Definition valid_deriv_step logic '(Rule r s ld) :=
  match r, s, List.map claim ld with
  | Ax,     (Γ ⊢ A), [] => list_mem A Γ
  | Tr_i,   (_ ⊢ True), [] => true
  | Fa_e,   (Γ ⊢ _), [s] => (negb (logic =? M)) &&& (s =? (Γ ⊢ False) )
  | Not_i,  (Γ ⊢ Not A), [s] => s =? (A::Γ ⊢ False)
  | Not_e,  (Γ ⊢ False), [Γ1 ⊢ A; Γ2 ⊢ Not A'] =>
    (A =? A') &&& (Γ =? Γ1) &&& (Γ =? Γ2)
  | And_i,  (Γ ⊢ A/\B), [s1; s2] =>
    (s1 =? (Γ ⊢ A)) &&& (s2 =? (Γ ⊢ B))
  | And_e1, s, [Γ ⊢ A/\_] => s =? (Γ ⊢ A)
  | And_e2, s, [Γ ⊢ _/\B] => s =? (Γ ⊢ B)
  | Or_i1,  (Γ ⊢ A\/_), [s] => s =? (Γ ⊢ A)
  | Or_i2,  (Γ ⊢ _\/B), [s] => s =? (Γ ⊢ B)
  | Or_e,   (Γ ⊢ C), [Γ' ⊢ A\/B; s2; s3] =>
     (Γ=?Γ') &&& (s2 =? (A::Γ ⊢ C)) &&& (s3 =? (B::Γ ⊢ C))
  | Imp_i,  (Γ ⊢ A->B), [s] => s =? (A::Γ ⊢ B)
  | Imp_e,  s, [Γ ⊢ A->B;s2] =>
     (s =? (Γ ⊢ B)) &&& (s2 =? (Γ ⊢ A))
  | All_i x,  (Γ⊢∀A), [Γ' ⊢ A'] =>
     (Γ =? Γ') &&& (A' =? bsubst 0 (FVar x) A)
     &&& negb (Names.mem x (fvars (Γ⊢A)))
  | All_e t, (Γ ⊢ B), [Γ'⊢ ∀A] =>
    (Γ =? Γ') &&& (B =? bsubst 0 t A)
  | Ex_i t,  (Γ ⊢ ∃A), [Γ'⊢B] =>
    (Γ =? Γ') &&& (B =? bsubst 0 t A)
  | Ex_e x,  s, [Γ⊢∃A; A'::Γ'⊢B] =>
     (s =? (Γ ⊢ B)) &&& (Γ' =? Γ)
     &&& (A' =? bsubst 0 (FVar x) A)
     &&& negb (Names.mem x (fvars (A::Γ⊢B)))
  | Absu, s, [Not A::Γ ⊢ False] =>
    (logic =? K) &&& (s =? (Γ ⊢ A))
  | _,_,_ => false
  end.

Fixpoint valid_deriv logic d :=
  valid_deriv_step logic d &&&
   (let '(Rule _ _ ld) := d in
    List.forallb (valid_deriv logic) ld).

(** Some examples of derivations *)

Definition deriv_example :=
  let A := Pred "A" [] in
  Rule Imp_i ([]⊢A->A) [Rule Ax ([A]⊢A) []].

Compute valid_deriv J deriv_example.
Compute valid_deriv M deriv_example.

Definition example_gen (A:formula) :=
  Rule Imp_i ([]⊢A->A) [Rule Ax ([A]⊢A) []].

Compute valid_deriv J (example_gen (Pred "A" [])).

Definition example2 (A B : term->formula):=
  (Rule Imp_i ([]⊢(∀A(#0)/\B(#0))->(∀A(#0))/\(∀B(#0)))
    (let C := (∀(A(#0)/\B(#0))) in
     [Rule And_i ([C] ⊢ (∀A(#0))/\(∀B(#0)))
       [Rule (All_i "x") ([C]⊢∀A(#0))
         [Rule And_e1 ([C]⊢A(FVar "x"))
           [Rule (All_e (FVar "x")) ([C]⊢ A(FVar "x")/\B(FVar "x"))
             [Rule Ax ([C]⊢C) []]]]
        ;
        Rule (All_i "x") ([C]⊢∀B(#0))
         [Rule And_e2 ([C]⊢B(FVar "x"))
           [Rule (All_e (FVar "x")) ([C]⊢A(FVar "x")/\B(FVar "x"))
             [Rule Ax ([C]⊢C) []]]]]]))%form.

Compute valid_deriv Intuiti
         (example2 (fun x => Pred "A" [x])
                   (fun x => Pred "B" [x])).

Definition em (A:formula) :=
  Rule Absu ([]⊢A\/~A)
    [Rule Not_e ([~(A\/~A)]⊢False)
       [Rule Or_i2 ([~(A\/~A)]⊢A\/~A)
         [Rule Not_i ([~(A\/~A)]⊢~A)
           [Rule Not_e ([A;~(A\/~A)]⊢False)
             [Rule Or_i1 ([A;~(A\/~A)]⊢A\/~A)
               [Rule Ax ([A;~(A\/~A)]⊢A) []]
              ;
              Rule Ax ([A;~(A\/~A)]⊢~(A\/~A)) []]]]
        ;
        Rule Ax ([~(A\/~A)]⊢~(A\/~A)) []]]%form.

Compute valid_deriv K (em (Pred "A" [])).
Compute valid_deriv J (em (Pred "A" [])).
Compute valid_deriv M (em (Pred "A" [])).

(** Example of free alpha-renaming during a proof,
    (not provable without alpha-renaming) *)

Definition captcha :=
  let A := fun x => Pred "A" [x] in
  Rule (All_i "z") ([A(FVar "x")]⊢∀(A(#0)->A(#0)))%form
   [Rule Imp_i ([A(FVar "x")]⊢A(FVar "z")->A(FVar "z"))
     [Rule Ax ([A(FVar "z");A(FVar "x")]⊢A(FVar "z")) []]].

Compute valid_deriv J captcha.

Definition captcha_bug :=
  let A := fun x => Pred "A" [x] in
  Rule (All_i "x") ([A(FVar "x")]⊢∀(A(#0)->A(#0)))%form
   [Rule Imp_i ([A(FVar "x")]⊢A(FVar "x")->A(FVar "x"))
    [Rule Ax ([A(FVar "x");A(FVar "x")]⊢A(FVar "x")) []]].

Compute valid_deriv J captcha_bug.


(**Examples of derivations not valid for minimal logic**)

Definition False_example :=
let A := Pred "A" [] in 
(Rule Fa_e ([A; ~A] ⊢ A) [
  Rule Not_e ([A; ~A] ⊢ False) [
    Rule Ax ([A; ~A] ⊢ A) [];
    Rule Ax ([A; ~A] ⊢ ~A) []]])%form.

Compute valid_deriv M False_example. (*False*)
Compute valid_deriv J False_example. (*True*)
Compute valid_deriv K False_example. (*True*)

Definition not_minimal :=
let A := Pred "A" [] in
let B := Pred "B" [] in
  Rule Imp_i ([] ⊢ (~A\/B -> (A->B))) [
    Rule Imp_i ([~A\/B] ⊢ (A->B)) [
      Rule Or_e ([A; ~A\/B] ⊢ B ) [
        Rule Ax ([A; ~A\/B]⊢ ~A\/B) [];
        Rule Fa_e ([~A; A; ~A\/B] ⊢ B) [
            Rule Not_e ([~A; A; ~A\/B] ⊢ False) [
              Rule Ax ([~A; A; ~A\/B] ⊢ A) [];
              Rule Ax ([~A; A; ~A\/B] ⊢ ~A) []]];
         Rule Ax ([B; A; ~A\/B] ⊢ B) []]]]%form. 

Compute valid_deriv M not_minimal. 
Compute valid_deriv J not_minimal.
Compute valid_deriv K not_minimal.

(** An inductive counterpart to valid_deriv, easier to use in proofs *)

Inductive Valid (l:logic) : derivation -> Prop :=
 | V_Ax Γ A : In A Γ -> Valid l (Rule Ax (Γ ⊢ A) [])
 | V_Tr_i Γ : Valid l (Rule Tr_i (Γ ⊢ True) [])
 | V_Fa_e d Γ A :
    l<>M ->
     Valid l d -> Claim d (Γ ⊢ False) ->
     Valid l (Rule Fa_e (Γ ⊢ A) [d])
 | V_Not_i d Γ A :
     Valid l d -> Claim d (A::Γ ⊢ False) ->
     Valid l (Rule Not_i (Γ ⊢ ~A) [d])
 | V_Not_e d1 d2 Γ A :
     Valid l d1 -> Valid l d2 ->
     Claim d1 (Γ ⊢ A) -> Claim d2 (Γ ⊢ ~A) ->
     Valid l (Rule Not_e (Γ ⊢ False) [d1;d2])
 | V_And_i d1 d2 Γ A B :
     Valid l d1 -> Valid l d2 ->
     Claim d1 (Γ ⊢ A) -> Claim d2 (Γ ⊢ B) ->
     Valid l (Rule And_i (Γ ⊢ A/\B) [d1;d2])
 | V_And_e1 d Γ A B :
     Valid l d -> Claim d (Γ ⊢ A/\B) ->
     Valid l (Rule And_e1 (Γ ⊢ A) [d])
 | V_And_e2 d Γ A B :
     Valid l d -> Claim d (Γ ⊢ A/\B) ->
     Valid l (Rule And_e2 (Γ ⊢ B) [d])
 | V_Or_i1 d Γ A B :
     Valid l d -> Claim d (Γ ⊢ A) ->
     Valid l (Rule Or_i1 (Γ ⊢ A\/B) [d])
 | V_Or_i2 d Γ A B :
     Valid l d -> Claim d (Γ ⊢ B) ->
     Valid l (Rule Or_i2 (Γ ⊢ A\/B) [d])
 | V_Or_e d1 d2 d3 Γ A B C :
     Valid l d1 -> Valid l d2 -> Valid l d3 ->
     Claim d1 (Γ ⊢ A\/B) -> Claim d2 (A::Γ ⊢ C) -> Claim d3 (B::Γ ⊢ C) ->
     Valid l (Rule Or_e (Γ ⊢ C) [d1;d2;d3])
 | V_Imp_i d Γ A B :
     Valid l d -> Claim d (A::Γ ⊢ B) ->
     Valid l (Rule Imp_i (Γ ⊢ A->B) [d])
 | V_Imp_e d1 d2 Γ A B :
     Valid l d1 -> Valid l d2 ->
     Claim d1 (Γ ⊢ A->B) -> Claim d2 (Γ ⊢ A) ->
     Valid l (Rule Imp_e (Γ ⊢ B) [d1;d2])
 | V_All_i x d Γ A :
     ~Names.In x (fvars (Γ ⊢ A)) ->
     Valid l d -> Claim d (Γ ⊢ bsubst 0 (FVar x) A) ->
     Valid l (Rule (All_i x) (Γ ⊢ ∀A) [d])
 | V_All_e t d Γ A :
     Valid l d -> Claim d (Γ ⊢ ∀A) ->
     Valid l (Rule (All_e t) (Γ ⊢ bsubst 0 t A) [d])
 | V_Ex_i t d Γ A :
     Valid l d -> Claim d (Γ ⊢ bsubst 0 t A) ->
     Valid l (Rule (Ex_i t) (Γ ⊢ ∃A) [d])
 | V_Ex_e x d1 d2 Γ A B :
     ~Names.In x (fvars (A::Γ⊢B)) ->
     Valid l d1 -> Valid l d2 ->
     Claim d1 (Γ ⊢ ∃A) -> Claim d2 ((bsubst 0 (FVar x) A)::Γ ⊢ B) ->
     Valid l (Rule (Ex_e x) (Γ ⊢ B) [d1;d2])
 | V_Absu d Γ A :
     l=K ->
     Valid l d -> Claim d (Not A :: Γ ⊢ False) ->
     Valid l (Rule Absu (Γ ⊢ A) [d]).

Hint Constructors Valid.

(** Let's prove now that [valid_deriv] is equivalent to [Valid] *)

Ltac break :=
 match goal with
 | H : match _ with true => _ | false => _ end = true |- _ =>
   rewrite !lazy_andb_iff in H
 | H : match claim ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | H : match map _ ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | H : match ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | _ => idtac
 end.

Ltac mytac :=
 cbn in *;
 break;
 rewrite ?andb_true_r, ?andb_true_iff, ?lazy_andb_iff in *;
 repeat match goal with H : _ /\ _ |- _ => destruct H end;
 repeat match goal with IH : Forall _ _  |- _ => inversion_clear IH end;
 rewrite ?@eqb_eq in * by auto with typeclass_instances.

Ltac rewr :=
 unfold Claim, BClosed in *;
 match goal with
 | H: _ = _ |- _ => rewrite H in *; clear H; rewr
 | _ => rewrite ?eqb_refl
 end.

Lemma Valid_equiv l d : valid_deriv l d = true <-> Valid l d.
Proof.
(* split.
 - induction d as [r s ds IH] using derivation_ind'.
   cbn - [valid_deriv_step]. rewrite lazy_andb_iff. intros (H,H').
   assert (IH' : Forall (fun d => Valid l d) ds).
   { rewrite Forall_forall, forallb_forall in *. auto. }
   clear IH H'.
   mytac; subst; eauto.
   + now apply V_Ax, list_mem_in.
   + apply V_All_i; auto.
     rewrite <- Names.mem_spec. cbn. intros EQ. now rewrite EQ in *.
   + apply V_Ex_e with f; auto.
     rewrite <- Names.mem_spec. cbn. intros EQ. now rewrite EQ in *.
 - induction 1; simpl; rewr; auto.
   + apply list_mem_in in H. now rewrite H.
   + rewrite <- Names.mem_spec in H. destruct Names.mem; auto.
   + rewrite <- Names.mem_spec in H. destruct Names.mem; auto.
Qed.*)
Admitted.

(** A notion of provability, directly on a sequent *)

Definition Provable logic (s : sequent) :=
  exists d, Valid logic d /\ Claim d s.

Lemma thm_example :
  let A := Pred "A" [] in
  Provable J ([]⊢A->A).
Proof.
 exists deriv_example. now rewrite <- Valid_equiv.
Qed.


(** A provability notion directly on sequents, without derivations.
    Pros: lighter
    Cons: no easy way to express meta-theoretical facts about the proof
          itself (e.g. free or bounded variables used during the proof). *)

Inductive Pr (l:logic) : sequent -> Prop :=
 | R_Ax Γ A : In A Γ -> Pr l (Γ ⊢ A)
 | R_Tr_i Γ : Pr l (Γ ⊢ True)
 | R_Fa_e Γ A : l<>M -> Pr l (Γ ⊢ False) ->
                  Pr l (Γ ⊢ A)
 | R_Not_i Γ A : Pr l (A::Γ ⊢ False) ->
                   Pr l (Γ ⊢ ~A)
 | R_Not_e Γ A : Pr l (Γ ⊢ A) -> Pr l (Γ ⊢ ~A) ->
                   Pr l (Γ ⊢ False)
 | R_And_i Γ A B : Pr l (Γ ⊢ A) -> Pr l (Γ ⊢ B) ->
                   Pr l (Γ ⊢ A/\B)
 | R_And_e1 Γ A B : Pr l (Γ ⊢ A/\B) ->
                    Pr l (Γ ⊢ A)
 | R_And_e2 Γ A B : Pr l (Γ ⊢ A/\B) ->
                    Pr l (Γ ⊢ B)
 | R_Or_i1 Γ A B : Pr l (Γ ⊢ A) ->
                   Pr l (Γ ⊢ A\/B)
 | R_Or_i2 Γ A B : Pr l (Γ ⊢ B) ->
                   Pr l (Γ ⊢ A\/B)
 | R_Or_e Γ A B C :
     Pr l (Γ ⊢ A\/B) -> Pr l (A::Γ ⊢ C) -> Pr l (B::Γ ⊢ C) ->
     Pr l (Γ ⊢ C)
 | R_Imp_i Γ A B : Pr l (A::Γ ⊢ B) ->
                     Pr l (Γ ⊢ A->B)
 | R_Imp_e Γ A B : Pr l (Γ ⊢ A->B) -> Pr l (Γ ⊢ A) ->
                   Pr l (Γ ⊢ B)
 | R_All_i x Γ A : ~Names.In x (fvars (Γ ⊢ A)) ->
                   Pr l (Γ ⊢ bsubst 0 (FVar x) A) ->
                   Pr l (Γ ⊢ ∀A)
 | R_All_e t Γ A : Pr l (Γ ⊢ ∀A) -> Pr l (Γ ⊢ bsubst 0 t A)
 | R_Ex_i t Γ A : Pr l (Γ ⊢ bsubst 0 t A) -> Pr l (Γ ⊢ ∃A)
 | R_Ex_e x Γ A B : ~Names.In x (fvars (A::Γ⊢B)) ->
      Pr l (Γ ⊢ ∃A) -> Pr l ((bsubst 0 (FVar x) A)::Γ ⊢ B) ->
      Pr l (Γ ⊢ B)
 | R_Absu Γ A : l=K -> Pr l (Not A :: Γ ⊢ False) ->
                  Pr l (Γ ⊢ A).
Hint Constructors Pr.

Lemma Valid_Pr lg d :
  Valid lg d -> Pr lg (claim d).
Proof.
 induction 1; cbn in *; rewr; eauto 2.
Qed.


(* Some useful statements. *)

Lemma Pr_intuit_classic s : Pr J s -> Pr K s.
Proof.
 induction 1; eauto 2.
 apply R_Fa_e; easy.
Qed.

Lemma Pr_minimal_intuit s : Pr M s -> Pr J s.
Proof.
 induction 1; eauto 2; try easy. 
 (*unfold not in H.
 destruct H; easy. easy. *)
Qed.

Lemma Pr_minimal_any lg s : Pr M s -> Pr lg s.
Proof.
 destruct lg; trivial. 
  - intros. apply Pr_intuit_classic, Pr_minimal_intuit. trivial. 
  - apply Pr_minimal_intuit.
Qed.

Lemma Pr_any_classic lg s : Pr lg s -> Pr K s.
Proof.
 destruct lg. trivial. apply Pr_intuit_classic.
 apply Pr_minimal_any.
Qed.