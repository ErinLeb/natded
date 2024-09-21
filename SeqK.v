(** * Sequent Calculus *)

(** The NatDed development, Pierre Letouzey, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs List Permutation.
Require Import Mix Meta SeqJ.
Require DecimalString.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Open Scope eqb_scope.


(** We use here a Locally nameless representation of terms.
    See for instance http://www.chargueraud.org/research/2009/ln/main.pdf
*)

(** Derivation *)

Inductive rule_kind :=
  | Ax
  | Fa_g
  | Aff_g
  | Aff_d
  | Contr_g
  | Contr_d
  | And_g | And_d 
  | Or_g | Or_d 
  | Imp_g | Imp_d
  | Not_g | Not_d  
  | All_g (wit:term)| All_d (v:variable)
  | Ex_g (v:variable) | Ex_d (wit:term)
  | Cut.

Inductive derivation :=
  | Rule : rule_kind -> sequent -> list derivation -> derivation.

(** The final sequent of a derivation *)

Definition claim '(Rule _ s _) := s.

(* Concatenates two lists *)
Fixpoint concat {X : Type} (l1 l2 : list X) : list X :=
match l1 with 
|[] => l2
|h::t => concat t (h::l2)
end.


(*TODO : examples and properties on list functions*)

Definition valid_deriv_step_LK '(Rule r s ld) :=
  match r, s,  List.map claim ld with
  | Ax,      ([A] ⊢ [A']),          []   => form_eqb A A' 
  | Fa_g,    (Γ ⊢ []),              []   => true
  | Aff_g,   (A::Γ ⊢ Δ),            [Γ' ⊢ Δ']   => (Γ' =? Γ) &&& (Δ' =? Δ)
  | Aff_d,   (Γ ⊢ A::Δ),            [Γ' ⊢ Δ']   => (Γ' =? Γ) &&& (Δ' =? Δ)
  | Contr_g, (A::Γ ⊢ Δ),            [Γ' ⊢ Δ']   => (Γ' =? A::A::Γ) &&& (Δ' =? Δ)
  | Contr_d, (Γ ⊢ A::Δ),            [s]   => s =?  (Γ ⊢ A::A::Δ)
  | And_g,   ((Op And A B)::Γ ⊢ Δ), [s]   => s =? (A::B::Γ ⊢ Δ)
  | And_d,   (Γ ⊢ (Op And A B)::Δ), [s1;s2]   => (s1 =? (Γ ⊢ A::Δ)) &&& (s2 =? (Γ ⊢ B::Δ))
  | Or_g,    ((Op Or A B)::Γ ⊢ Δ),  [s1; s2]   => (s1 =? (A::Γ ⊢ Δ))  &&& (s2 =? (B::Γ ⊢ Δ))
  | Or_d,    (Γ ⊢ (Op Or A B)::Δ),  [s]   => s =? (Γ ⊢ A::B::Δ)
  | Imp_g,   ((Op Impl A B)::Γ ⊢ Δ), [s1; s2]   => (s1 =? (Γ ⊢ A::Δ)) &&& (s2 =? (B::Γ ⊢ Δ))
  | Imp_d,   (Γ ⊢ (Op Impl A B)::Δ), [s]   => s =? (A::Γ ⊢ B::Δ)
  | Not_g,   ((Not A)::Γ ⊢ Δ),      [s]   => s =? (Γ ⊢ A::Δ)
  | Not_d,   (Γ ⊢ (Not A)::Δ),      [s]   => s =? (A::Γ ⊢ Δ)
  | All_g t, ((Quant All A)::Γ ⊢ Δ),[B::Γ' ⊢ Δ']   => (B =? bsubst 0 t A) &&& (Γ' =? Γ) &&& (Δ' =? Δ)
  | All_d x, (Γ ⊢ (Quant All A)::Δ),[s]   => (s =? (Γ ⊢ A::Δ)) &&& (negb (Names.mem x (fvars (Γ ⊢ Δ))))
  | Ex_g x,  ((Quant Ex A)::Γ ⊢ Δ), [s]   => (s =? (A::Γ ⊢ Δ)) &&& (negb (Names.mem x (fvars (Γ ⊢ Δ))))
  | Ex_d t,  (Γ ⊢ (Quant Ex A)::Δ), [Γ' ⊢ B::Δ']   =>  (B =? bsubst 0 t A) &&& (Γ' =? Γ) &&& (Δ' =? Δ)
  | Cut,     (p ⊢ c),               [(Γ ⊢ A::Δ); (Γ' ⊢ A'::Δ')]   => (A =? A') &&& (p =? Γ ++ Γ') &&& (c =? Δ ++ Δ')
  | _,_,_   => false
  end.


Fixpoint valid_deriv_LK d := valid_deriv_step_LK d &&&
   (let '(Rule _ _ ld) := d in
    List.forallb (valid_deriv_LK) ld).

(** Some examples of derivations *)

Definition double_implies :=
let A := Pred "A" [] in
let B := Pred "B" [] in
Rule Imp_d ([] ⊢ [Op Impl A (Op Impl B A)]) [
  Rule Imp_d ([A] ⊢ [Op Impl B A]) [
    Rule Aff_g ([B;A] ⊢ [A]) [
      Rule Ax ([A] ⊢ [A]) []]]].

Compute valid_deriv_LK double_implies.

Definition Claim d s := claim d = s.
Arguments Claim _ _ /.
Hint Extern 1 (Claim _ _) => cbn.

Inductive Pr_LK : sequent -> Prop :=
 | R_Ax A : Pr_LK (A ⊢ A)
 | R_Fa_g : Pr_LK ([False] ⊢ [])
 | R_Tr_d : Pr_LK ([] ⊢ [True])
 | R_Aff Γ Γ' Δ Δ'  : ListSubset Γ Γ'-> ListSubset Δ Δ' -> Pr_LK (Γ ⊢ Δ) -> Pr_LK (Γ' ⊢ Δ')
 | R_And_d Γ Δ A B : Pr_LK (Γ ⊢ A::Δ) -> Pr_LK (Γ ⊢ B::Δ) -> Pr_LK (Γ ⊢ (Op And A B)::Δ)
 | R_And_g Γ Δ A B : Pr_LK (A::B::Γ ⊢ Δ) -> Pr_LK ((Op And A B)::Γ ⊢ Δ)
 | R_Or_g Γ Δ A B : Pr_LK (A::Γ ⊢ Δ) -> Pr_LK (B::Γ ⊢ Δ) -> Pr_LK ((Op Or A B)::Γ ⊢ Δ)
 | R_Or_d Γ Δ A B : Pr_LK (Γ ⊢ A::B::Δ) -> Pr_LK (Γ ⊢ (Op Or A B)::Δ)
 | R_Imp_g Γ Δ A B : Pr_LK (Γ ⊢ A::Δ) -> Pr_LK (B::Γ ⊢ Δ) -> Pr_LK ((Op Impl A B)::Γ ⊢ Δ) 
 | R_Imp_d Γ Δ A B : Pr_LK (A::Γ ⊢ B::Δ) -> Pr_LK (Γ ⊢ (Op Impl A B)::Δ)
 | R_Not_g Γ Δ A : Pr_LK (Γ ⊢ A::Δ) -> Pr_LK (Not A::Γ ⊢ Δ)
 | R_Not_d Γ Δ A : Pr_LK (A::Γ ⊢ Δ) -> Pr_LK (Γ ⊢ Not A::Δ)
 | R_All_g t Γ Δ A : Pr_LK ((bsubst 0 t A)::Γ ⊢ Δ) -> Pr_LK ((Quant All A)::Γ ⊢ Δ)
 | R_All_d x Γ Δ A : ~Names.In x (fvars (Γ ⊢ A::Δ)) -> Pr_LK (Γ ⊢ (bsubst 0 (FVar x) A)::Δ) -> Pr_LK (Γ ⊢ (Quant All A)::Δ)
 | R_Ex_g x Γ Δ A : ~Names.In x (fvars (A::Γ ⊢ Δ)) -> Pr_LK ((bsubst 0 (FVar x) A)::Γ ⊢ Δ) -> Pr_LK ((Quant Ex A)::Γ ⊢ Δ)
 | R_Ex_d t Γ Δ A : Pr_LK (Γ ⊢ (bsubst 0 t A)::Δ) -> Pr_LK (Γ ⊢ (Quant Ex A)::Δ)
 | R_Cut Γ Γ' Δ Δ' A : Pr_LK (Γ ⊢ A::Δ)-> Pr_LK (A::Γ' ⊢ Δ') -> Pr_LK ( Γ ++ Γ' ⊢ Δ ++ Δ').

Hint Constructors Pr_LK.

Lemma R_Aff_d' : forall G A C, Pr_LK (G ⊢ [A]) -> In A C -> Pr_LK (G ⊢ C).
Proof.
intros. eapply R_Aff; eauto.
red. intuition.
red. simpl. intuition. subst. easy.
Qed.

Lemma LJ_implies_LK : forall s, Pr_LJ s -> Pr_LK s.
Proof.
intros. induction H; eauto.
- eapply R_Aff; eauto. red. intuition.
- eapply R_Aff; eauto; red; intuition.
- eapply R_Or_d. eapply R_Aff; eauto; red; simpl; intuition. 
- eapply R_Or_d. eapply R_Aff; eauto; red; simpl; intuition. 
- eapply R_Imp_g. eapply R_Aff_d'. apply IHPr_LJ1. simpl. intuition. apply IHPr_LJ2.
- apply (R_Aff (Γ++Γ) Γ ([]++B) B). red. intros. rewrite in_app_iff in *. intuition.
  simpl. red. intuition.
  eapply R_Cut; eauto.
Qed.

(*TODO : prove Pr_LK <=> Pr K *)
