(** * Sequent Calculus *)

(** The NatDed development, Pierre Letouzey, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs List Permutation.
Require Import Mix Meta.
Require DecimalString.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope nat_scope.
Local Open Scope eqb_scope.

(** We use here a Locally nameless representation of terms.
    See for instance http://www.chargueraud.org/research/2009/ln/main.pdf
*)

(** Sequent *)

(* In sequent calculus, the conclusion is not just one formula but a disjunction of formula, 
e.g a list of formulas in which at least one is true. *)
Inductive sequent :=
| Seq : context -> context -> sequent.

Infix "⊢" := Seq (at level 100).

Definition print_seq '(Γ ⊢ Δ) :=
  print_ctx Γ ++ " ⊢ " ++ print_ctx Δ.

Instance check_seq : Check sequent :=
 fun sign '(Γ ⊢ A) => check sign Γ &&& check sign A.

Instance bsubst_seq : BSubst sequent :=
 fun n u '(Γ ⊢ A) => (bsubst n u Γ ⊢ bsubst n u A).

Instance level_seq : Level sequent :=
 fun '(Γ ⊢ A) => Nat.max (level Γ) (level A).

Instance seq_fvars : FVars sequent :=
 fun '(Γ ⊢ A) => Names.union (fvars Γ) (fvars A).

Instance seq_vmap : VMap sequent :=
 fun h '(Γ ⊢ A) => (vmap h Γ ⊢ vmap h A).

Instance seq_eqb : Eqb sequent :=
 fun '(Γ1 ⊢ A1) '(Γ2 ⊢ A2) => (Γ1 =? Γ2) &&& (A1 =? A2).

(** Derivation *)

Inductive rule_kind :=
  | Ax
  | Fa_g
  | Aff_g
  | Aff_d
  | Contr_g
  | Contr_d
  | And_g | And_d 
  | Or_g | Or_d1 | Or_d2 
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

(*TODO : another definition might be better *)
Definition is_concl_LJ (l : context) : bool :=
match l with 
| x::y::t => false
| _ => true
end.

(* Examples *)
Compute is_concl_LJ [].

Definition ex_concl_true := 
let A := Pred "A" [] in [A].

Definition ex_concl_false := 
let A := Pred "A" [] in [A;A].

Compute is_concl_LJ ex_concl_true.
Compute is_concl_LJ ex_concl_false.

Definition valid_deriv_step_LJ '(Rule r s ld) :=
  match r, s,  List.map claim ld with
  | Ax,      ([A] ⊢ [A']),          []   => form_eqb A A' 
  | Fa_g,    (Γ ⊢ []),              []   => true
  | Aff_g,   (A::Γ ⊢ B),            [Γ' ⊢ B']   => (is_concl_LJ B) &&& (Γ' =? Γ) &&& (B =? B') 
  | Aff_d,   (Γ ⊢ [A]),             [Γ' ⊢ []]   => (Γ' =? Γ) 
  | Contr_g, (A::Γ ⊢ B),            [Γ' ⊢ B']   => (is_concl_LJ B) &&& (Γ' =? A::A::Γ) &&& (B' =? B)
  | And_g,   ((Op And A B)::Γ ⊢ C), [s]   => (is_concl_LJ C) &&& (s =? (A::B::Γ ⊢ C))
  | And_d,   (Γ ⊢ [Op And A B]),    [s1;s2]   => (s1 =? (Γ ⊢ [A])) &&& (s2 =? (Γ ⊢ [B]))
  | Or_g,    ((Op Or A B)::Γ ⊢ C),  [s1; s2]   => (is_concl_LJ C) &&& (s1 =? (A::Γ ⊢ C))  &&& (s2 =? (B::Γ ⊢ C))
  | Or_d1,   (Γ ⊢ [Op Or A B]),    [s]   => s =? (Γ ⊢ [A])
  | Or_d2,   (Γ ⊢ [Op Or A B]),    [s]   => s =? (Γ ⊢ [B])
  | Imp_g,   ((Op Impl A B)::Γ ⊢ C),[s1; s2]   => (is_concl_LJ C) &&& (s1 =? (Γ ⊢ [A])) &&& (s2 =? (B::Γ ⊢ C))
  | Imp_d,   (Γ ⊢ [Op Impl A B]),  [s]   => s =? (A::Γ ⊢ [B])
  | Not_g,   ((Not A)::Γ ⊢ []),     [s]   => s =? (Γ ⊢ [A])
  | Not_d,   (Γ ⊢ [Not A]),         [s]   => s =? (A::Γ ⊢ [])
  | All_g t, ((Quant All A)::Γ ⊢ C),[B::Γ' ⊢ C']   => (is_concl_LJ C) &&& (B =? bsubst 0 t A) &&& (Γ' =? Γ) &&& (C' =? C)
  | All_d x, (Γ ⊢ [Quant All A]),[s]   => (s =? (Γ ⊢ [A])) &&& (negb (Names.mem x (fvars Γ)))
  | Ex_g x,  ((Quant Ex A)::Γ ⊢ C), [s]   => (is_concl_LJ C) &&& (s =? (A::Γ ⊢ C)) &&& (negb (Names.mem x (fvars (Γ ⊢ C))))
  | Ex_d t,  (Γ ⊢ [Quant Ex A]), [Γ' ⊢ [B]]   =>  (B =? bsubst 0 t A) &&& (Γ' =? Γ)
  | Cut,     (Γ ⊢ B),               [(Γ' ⊢ [A]); (Γ'' ⊢ B')]   => (is_concl_LJ B) &&& (Γ' =? Γ) &&& (Γ'' =? A::Γ) &&& (B =? B')
  | _,_,_   => false
 end.

Fixpoint valid_deriv_LJ d := valid_deriv_step_LJ d &&&
   (let '(Rule _ _ ld) := d in
    List.forallb (valid_deriv_LJ) ld).

(** Some examples of derivations *)

Definition double_implies :=
let A := Pred "A" [] in
let B := Pred "B" [] in
Rule Imp_d ([] ⊢ [Op Impl A (Op Impl B A)]) [
  Rule Imp_d ([A] ⊢ [Op Impl B A]) [
    Rule Aff_g ([B;A] ⊢ [A]) [
      Rule Ax ([A] ⊢ [A]) []]]].

Compute valid_deriv_LJ double_implies.

(*TODO Prove valid_deriv_LJ => valid_deriv_LK *)

Definition Claim d s := claim d = s.
Arguments Claim _ _ /.
Hint Extern 1 (Claim _ _) => cbn.

Inductive Pr_LJ : sequent -> Prop :=
 | R_Ax A : Pr_LJ ([A] ⊢ [A])
 | R_Fa_g : Pr_LJ ([False] ⊢ [])
 | R_Tr_d : Pr_LJ ([] ⊢ [True])
 | R_Aff_g Γ Γ' D : ListSubset Γ Γ' -> Pr_LJ (Γ ⊢ D) -> Pr_LJ (Γ' ⊢ D) 
 | R_Aff_d Γ A : Pr_LJ (Γ ⊢ []) -> Pr_LJ (Γ ⊢ [A])
 | R_And_g Γ A B C : Pr_LJ (A::B::Γ ⊢ C) -> Pr_LJ ((A/\B)%form::Γ ⊢ C)
 | R_And_d Γ A B : Pr_LJ (Γ ⊢ [A]) -> Pr_LJ (Γ ⊢ [B]) -> Pr_LJ (Γ ⊢ [(Op And A B)])
 | R_Or_g Γ A B C : Pr_LJ (A::Γ ⊢ C) -> Pr_LJ (B::Γ ⊢ C) -> Pr_LJ ((Op Or A B)::Γ ⊢ C)
 | R_Or_d1 Γ A B : Pr_LJ (Γ ⊢ [A]) -> Pr_LJ(Γ ⊢ [Op Or A B])
 | R_Or_d2 Γ A B : Pr_LJ (Γ ⊢ [B]) -> Pr_LJ(Γ ⊢ [Op Or A B])
 | R_Imp_g Γ A B C : Pr_LJ (Γ ⊢ [A]) -> Pr_LJ (B::Γ ⊢ C) -> Pr_LJ ((Op Impl A B)::Γ ⊢ C)
 | R_Imp_d Γ A B : Pr_LJ (A::Γ ⊢ [B]) -> Pr_LJ (Γ ⊢ [Op Impl A B])
 | R_Not_g Γ A : Pr_LJ (Γ ⊢ [A]) -> Pr_LJ ((Not A)::Γ ⊢ [])
 | R_Not_d Γ A : Pr_LJ (A::Γ ⊢ []) -> Pr_LJ (Γ ⊢ [Not A])
 | R_All_g t Γ A C : Pr_LJ ((bsubst 0 t A)::Γ ⊢ C) -> Pr_LJ ((Quant All A)::Γ ⊢ C)
 | R_All_d x Γ A : ~Names.In x (fvars (Γ ⊢ [A])) -> Pr_LJ (Γ ⊢ [bsubst 0 (FVar x) A]) -> Pr_LJ (Γ ⊢ [Quant All A])
 | R_Ex_g x Γ A C : ~Names.In x (fvars (A::Γ ⊢ C)) -> Pr_LJ ((bsubst 0 (FVar x) A)::Γ ⊢ C) -> Pr_LJ ((Quant Ex A)::Γ ⊢ C)
 | R_Ex_d t Γ A : Pr_LJ (Γ ⊢ [bsubst 0 t A]) -> Pr_LJ (Γ ⊢ [Quant Ex A])
 | R_Cut Γ A B : Pr_LJ (Γ ⊢ [A]) -> Pr_LJ (A::Γ ⊢ B) -> Pr_LJ (Γ ⊢ B)
.

Hint Constructors Pr_LJ.
Definition prem (s : sequent) := match s with 
| (Γ ⊢ Δ) => Γ
end.
 
Definition concl (s : sequent) := match s with 
| (Γ ⊢ Δ) => Δ
end.

Lemma eq_prem_seq : forall Γ Γ' Δ Δ', (Γ ⊢ Δ) = (Γ' ⊢ Δ') ->  prem(Γ ⊢ Δ) =  prem(Γ' ⊢ Δ').
Proof.
intros. rewrite H. easy.
Qed.

Lemma eq_concl_seq : forall Γ Γ' Δ Δ', (Γ ⊢ Δ) = (Γ' ⊢ Δ') ->  concl(Γ ⊢ Δ) =  concl(Γ' ⊢ Δ').
Proof.
intros. rewrite H. easy.
Qed.

Lemma eq_seq : forall s s', prem s = prem s' -> concl s = concl s' -> s = s'.
Proof. intros. destruct s. destruct s'. simpl in H. simpl in H0.
rewrite H. rewrite H0. easy.
Qed.

Definition is_concl_LJ' (c : context): Prop :=
match c with 
| x::y::t => Logic.False
| _ => Logic.True
end.

Lemma length_concl_LJ : forall Γ Δ, Pr_LJ (Γ ⊢ Δ) -> is_concl_LJ' Δ.
Proof.
intros. remember (Γ ⊢ Δ) as s in H. revert Γ Δ Heqs. induction H; 
intros ? ? [= <- <-]; simpl; eauto.
Qed.

Lemma concl_false : forall Γ, Pr_LJ (Γ ⊢ [False]) <-> Pr_LJ (Γ ⊢ []).
Proof.
intros Γ. 
split. 
- intros. eapply R_Cut. apply H. eapply R_Aff_g. 2: apply R_Fa_g. intros a [<- | []]. intuition.
- intros. apply R_Aff_d. easy.
Qed.

Lemma concl_false_g : forall Γ, Pr_LJ (Γ ⊢ [False]) -> Pr_LJ (Γ ⊢ []).
Proof.
intros Γ. apply concl_false.
Qed.

Hint Resolve concl_false_g.

Lemma R_Ax' : forall Γ A, In A Γ -> Pr_LJ (Γ ⊢ [A]).
Proof.
intros. eapply R_Aff_g. 2 : apply R_Ax. unfold ListSubset. now intros a [<-|[]].
Qed. 

Lemma elim_and_g : forall Γ A B, Pr_LJ (Γ ⊢ [A/\B]%form) -> Pr_LJ (Γ ⊢ [A]).
Proof. 
intros.
apply R_Cut with (A/\B)%form. apply H. apply R_And_g. apply R_Ax'. intuition.
Qed.

Lemma elim_and_d : forall Γ A B, Pr_LJ (Γ ⊢ [A/\B]%form) -> Pr_LJ (Γ ⊢ [B]).
Proof.
intros.
apply R_Cut with (A/\B)%form. apply H. apply R_And_g. apply R_Ax'. intuition.
Qed.

Lemma elim_impl : forall Γ A B, 
  Pr_LJ (Γ ⊢ [A->B]%form) -> Pr_LJ (Γ ⊢ [A]) -> Pr_LJ (Γ ⊢ [B]).
Proof.
intros. apply R_Cut with (A->B)%form. apply H. 
apply R_Imp_g. apply H0. apply R_Ax'. intuition.
Qed.

Definition convert_to_LJ (s : Mix.sequent) : sequent := match s with 
|Mix.Seq Γ A => Γ ⊢ [A]
end.

Fixpoint convert_concl (l : list formula) : formula :=
match l with 
|[] => False
|[x] => x
|x::t => Op Or x (convert_concl t)
end.

Fixpoint convert_concl' (l : list formula) : formula :=
match l with 
|[] => False
|x::t => Op Or x (convert_concl' t)
end.

Lemma equiv_convert_concl : forall G, 
Names.Equal (fvars (convert_concl G)) (fvars (convert_concl' G)).
Proof.
induction G; simpl. reflexivity.
destruct G.
simpl. unfold fvars. simpl. rewrite NameProofs.NamesP.empty_union_2. easy.
apply Names.empty_spec.
unfold fvars in *. simpl in *. rewrite IHG. easy.
Qed.

Definition convert_from_LJ (s : sequent) : Mix.sequent := 
match s with 
| Seq Γ A => Mix.Seq Γ (convert_concl A)
end.

(*TODO : add examples and properties on conversions *)

Lemma fvars_context_form : forall Γ A x, 
   Names.In x (fvars (Γ ⊢ [A])) <-> Names.In x (fvars (Mix.Seq Γ A)).
Proof.
intros.
split; intros eq.
- unfold fvars in *. simpl in *. unfold fvars in eq. simpl in eq. 
rewrite (NameProofs.NamesP.empty_union_2 (fvars A)) in eq. easy.
apply Names.empty_spec.
- simpl in *. unfold fvars in *; simpl in *. unfold fvars. simpl.
rewrite (NameProofs.NamesP.empty_union_2 (fvars A)). easy. apply Names.empty_spec.
Qed.

Lemma fvar_convert : forall G, Names.Equal (fvars G) (fvars (convert_concl G)).
Proof.
intros G. rewrite equiv_convert_concl.
induction G; simpl.
- unfold fvars. simpl. reflexivity.
- unfold fvars in *. simpl. rewrite IHG. easy.
Qed.

Theorem natded_to_seq : forall (s : Mix.sequent) l, 
 Pr l s -> l = J -> Pr_LJ (convert_to_LJ s).
Proof.
intros. induction H; subst l; simpl; eauto.
- apply R_Ax'. apply H.
- eapply R_Aff_g. 2 : apply R_Tr_d. easy.
- eapply elim_and_g. apply IHPr.
- eapply elim_and_d. apply IHPr.
- eapply elim_impl; eauto.
- eapply R_All_d. rewrite fvars_context_form. apply H. simpl in IHPr. easy.
- eapply R_Cut. apply IHPr. eapply R_All_g. apply R_Ax'. intuition.
- eapply R_Cut. apply IHPr1. eapply R_Ex_g. rewrite fvars_context_form. 
  apply H. simpl in IHPr2. easy.
- discriminate.
Qed.

Theorem seq_to_natded : forall s, Pr_LJ s -> Pr J (convert_from_LJ s).
Proof.
intros. induction H; simpl in *; eauto 3. 
- eapply Mix.R_Ax. red. intuition.
- eapply Mix.R_Ax. red. intuition.
- eapply Pr_weakening; eauto.
- eapply R'_And_e. easy.
- eapply R'_Or_e; easy.
- apply Mix.R_Imp_e with B.
  + apply Mix.R_Imp_i. eapply Pr_weakening; eauto. 
    constructor. red. simpl. intuition. 
  + apply Mix.R_Imp_e with A. apply Mix.R_Ax. intuition. 
    eapply Pr_weakening. apply IHPr_LJ1. constructor. red. intuition.
- eapply Mix.R_Not_e with A. eapply Pr_weakening. apply IHPr_LJ. 
  constructor. red. intuition.
  apply Mix.R_Ax. intuition.
- eapply R'_All_e; eauto.
- eapply Mix.R_All_i; eauto. rewrite <- fvars_context_form; easy.
- eapply R'_Ex_e; eauto. rewrite  <- fvars_context_form.
  unfold fvars. simpl. unfold fvars. simpl. rewrite  <- fvar_convert.
  rewrite (NameProofs.NamesP.empty_union_2 (fvars C)). apply H.
  apply Names.empty_spec.
Qed.

(*TODO : convert involutive *)
(*TODO : thm equivalence *)