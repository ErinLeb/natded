(** * The Zermelo Fraenkel set theory and its Coq model *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Meta Theories PreModels Models.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

(** On the necessity of a non trivial set theory : Russell's paradox. *)

(*  The naive set theory consists of the non restricted comprehension axiom schema :
    ∀ x1, ..., ∀ xn, ∃ a, ∀ y (y ∈ a <-> A),
      forall formula A whose free variables are amongst x1, ..., xn, y. *)

Notation "x ∈ y" := (Pred "∈" [x;y]) (at level 70) : formula_scope.

Open Scope string_scope.
Open Scope formula_scope.

(* It is easy to notice that ∃ a ∀ x (x ∈ a <-> ~(x ∈ x)) is (almost) an instance of the
   comprehension axiom schema : it suffices to let A = ~ (a ∈ a). *)
Lemma Russell : Pr Intuiti ([ ∃∀ (#0 ∈ #1 <-> ~(#0 ∈ #0)) ] ⊢ False).
Proof.
  apply R'_Ex_e with (x := "a"); auto.
  + cbn - [Names.union]. intro. inversion H.
  + cbn. set  (A := FVar "a"). fold (#0 ∈ A <-> ~ #0 ∈ #0)%form.
    set (comp := ∀ _ <-> _).
    set (Γ := [comp]).
    assert (Pr Intuiti (Γ ⊢ ~ A ∈ A)).
    {
      apply R_Not_i.
      set (Γ' := (_ :: Γ)).
      apply R_Not_e with (A := A ∈ A).
      * apply R_Ax. compute; intuition.
      * apply R_Imp_e with (A := A ∈ A).
        ++ apply R_And_e1 with (B := (~ A ∈ A -> A ∈ A)).
           assert (Pr Intuiti (Γ' ⊢ comp)). { apply R_Ax. compute; intuition. }
           apply R_All_e with (t := A) in H; auto.
        ++ apply R_Ax. compute; intuition.
    }     
    apply R_Not_e with (A := A ∈ A); auto.
    apply R_Imp_e with (A := ~ A ∈ A); auto.
    - apply R_And_e2 with (A := (A ∈ A -> ~ A ∈ A)).
      assert (Pr Intuiti (Γ ⊢ comp)). { apply R_Ax. compute; intuition. }
      apply R_All_e with (t := A) in H0; auto.
Qed.

(* Russell's paradox therefore shows that the naive set theory is inconsistent.
   We are to try to fix it, using ZF(C) theory, which has not been proved inconstitent so far
   (neither has it been proved consistent though).
   Actually, were we to intend to prove that ZF is consistent, Godel's second theorem tells us that
   we would have to do it in a stronger theory, which we would have to prove to be consitent too
   (in a stronger theory too), and so on... *)

(** The ZF axioms *)

Close Scope string_scope.
Definition ZFSign := Finite.to_infinite zf_sign.

Notation "x = y" := (Pred "=" [x;y]) : formula_scope.
Notation "x ∈ y" := (Pred "∈" [x;y]) (at level 70) : formula_scope.

Module ZFAx.
Local Open Scope formula_scope.

Definition eq_refl := ∀ (#0 = #0).
Definition eq_sym := ∀∀ (#1 = #0 -> #0 = #1).
Definition eq_trans := ∀∀∀ (#2 = #1 /\ #1 = #0 -> #2 = #0).
Definition compat_left := ∀∀∀ (#0 = #1 /\ #0 ∈ #2 -> #1 ∈ #2).
Definition compat_right := ∀∀∀ (#0 ∈ #1 /\ #1 = #2 -> #0 ∈ #2).

Definition ext := ∀∀ (∀ (#0 ∈ #2 <-> #0 ∈ #1) -> #2 = #1).
Definition pairing := ∀∀∃∀ (#0 ∈ #1 <-> #0 = #3 \/ #0 = #2).
Definition union := ∀∃∀ (#0 ∈ #1 <-> ∃ (#0 ∈ #3 /\ #1 ∈ #0)).
Definition powerset := ∀∃∀ (#0 ∈ #1 <-> ∀ (#0 ∈ #1 -> #0 ∈ #3)).
Definition infinity := ∃ (∃ (#0 ∈ #1 /\ ∀ ~(#0 ∈ #1)) /\ ∀ (#0 ∈ #1 -> (∃ (#0 ∈ #2 /\ (∀ (#0 ∈ #1 <-> #0 = #2 \/ #0 ∈ #2)))))).

Definition axioms_list :=
 [ eq_refl; eq_sym; eq_trans; compat_left; compat_right; ext; pairing; union; powerset; infinity ].

Fixpoint occur_term n t :=
  match t with
  | BVar m => n =? m
  | FVar _ => false
  | Fun _ l => existsb (occur_term n) l
  end.

Fixpoint occur_form n f :=
  match f with
    | True | False => false
    | Pred _ l => existsb (occur_term n) l
    | Not f' => occur_form n f'
    | Op _ f1 f2 => (occur_form n f1) &&& (occur_form n f2)
    | Quant _ f' => occur_form (S n) f'
  end.

(* POUR SEPARATION:
  dB dans A :  0=>x 1=>a n>=2:z_i
  dB dans (lift_above 1 A) 0=>x ... 2=>a (n>=3:z_i) *)
Definition separation_schema A :=
  nForall
    ((level A) - 2)
    (∀∃∀ (#0 ∈ #1 <-> (#0 ∈ #2 /\ lift_form_above 1 A))).

Definition exists_uniq A :=
∃ (A /\ ∀ (lift_form_above 1 A -> #0 = #1)).

(* POUR REPLACEMENT:
   dB dans A :  0=>y 1=>x 2=>a n>=3:z_i
   dB dans (lift_above 2 A) 0=>y 1=>x ... 3=>a (n>=4:z_i) *)
Definition replacement_schema A :=
  nForall
    ((level A) - 3)
    (∀ (∀ (#0 ∈ #1 -> exists_uniq A)) ->
       ∃∀ (#0 ∈ #2 -> ∃ (#0 ∈ #3 /\ lift_form_above 2 A))).

Local Close Scope formula_scope.

Definition IsAx A :=
  List.In A axioms_list \/
  (exists B, A = separation_schema B /\
             check ZFSign B = true /\
             FClosed B)
  \/
  (exists B, A = replacement_schema B /\
             check ZFSign B = true /\
             FClosed B).

Lemma aux A B : level (A <-> B)%form = Nat.max (level A) (level B).
Proof.
 cbn. omega with *.
Qed.

Lemma aux' A B : level (A -> B)%form = Nat.max (level A) (level B).
Proof.
  cbn. omega with *.
Qed.

Lemma aux2 q A : level (Quant q A)%form = Nat.pred (level A).
Proof.
 cbn. reflexivity.
Qed.

Lemma aux2' q A : Names.eq (fvars (Quant q A)%form) (fvars A).
Proof.
 reflexivity.
Qed.

Lemma aux3 A B : Names.eq (fvars (A <-> B)%form)
                          (Names.union (fvars A) (fvars B)).
Proof.
  cbn.
  unfold Names.eq.
  namedec.
Qed.

Lemma aux4 A B a : Names.In a (fvars (A /\ B)%form) -> Names.In a (Names.union (fvars A) (fvars B)).
Proof.
  cbn. easy.
Qed.

Lemma WfAx A : IsAx A -> Wf ZFSign A.
Proof.
 intros [ IN | [ (B & -> & HB & HB') | (C & -> & HC & HC') ] ].
 - apply Wf_iff.
   unfold axioms_list in IN.
   simpl in IN. intuition; subst; reflexivity.
 - repeat split; unfold separation_schema; cbn.
   + rewrite nForall_check. cbn.
     rewrite !check_lift_form_above, HB.
     easy.
   + red. rewrite nForall_level. rewrite !aux2, aux.
     cbn -[Nat.max].
     simpl (Nat.max 1 _).
     rewrite Nat.max_assoc. simpl (Nat.max 2 3).
     assert (H := level_lift_form_above B 1).
     omega with *.
   + apply nForall_fclosed. red. unfold Names.Empty. intro a. intro.
     rewrite !aux2', aux3 in H.
     apply Names.union_spec in H.
     destruct H.
     * rewrite <- Names.mem_spec in H. compute in H. easy.
     * apply aux4 in H. apply Names.union_spec in H. destruct H.
       -- cbn in H. easy.
       -- unfold FClosed in HB'. unfold Names.Empty in HB'. destruct HB' with (a := a). rewrite fvars_lift_form_above in H. assumption.
 - repeat split; unfold replacement_schema; cbn.
   + rewrite nForall_check. cbn.
     rewrite !check_lift_form_above, HC.
     easy.
   + red. rewrite nForall_level. repeat rewrite !aux2, !aux'.
     cbn -[Nat.max].
     simpl (Nat.max 1 _).
     assert (H := level_lift_form_above C 1).
     assert (H' := level_lift_form_above C 2).
     admit.
     (* omega with *. *)
   + apply nForall_fclosed. red. unfold Names.Empty. intro a. intro.
     rewrite !aux2' in H. cbn -[Names.union] in H.
     rewrite !fvars_lift_form_above in H.
     unfold FClosed in HC'. unfold Names.Empty in HC'. destruct HC' with (a := a).
     namedec.
Admitted.     

End ZFAx.

Local Open Scope string.
Local Open Scope formula_scope.

Definition ZFTheory :=
 {| sign := ZFSign;
    IsAxiom := ZFAx.IsAx;
    WfAxiom := ZFAx.WfAx |}.


Import ZFAx.