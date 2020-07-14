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

Open Scope formula_scope.

(* It is easy to notice that ∃ a ∀ x (x ∈ a <-> ~(x ∈ x)) is (almost) an instance of the
   comprehension axiom schema : it suffices to let A = ~ (a ∈ a). *)
Lemma Russell (a : variable) : Pr Intuiti ([ ∃∀ (#0 ∈ #1 <-> ~(#0 ∈ #0)) ] ⊢ False).
Proof.
  apply R'_Ex_e with (x := a); auto.
  + cbn - [Names.union]. intro. inversion H.
  + cbn. fold (#0 ∈ FVar a <-> ~ #0 ∈ #0)%form.
    set (comp := ∀ _ <-> _).
    set (Γ := [comp]).
    set (A := FVar a).
    apply R_Not_e with (A := A ∈ A).
    - apply R_Imp_e with (A := ~ A ∈ A).
      * apply R_And_e2 with (A := (A ∈ A -> ~ A ∈ A)).
        assert (Pr Intuiti (Γ ⊢ comp)). { apply R_Ax. compute; intuition. }
        apply R_All_e with (t := FVar a) in H; auto.
      * apply R_Not_i.
        set (Γ' := (_ :: Γ)).
        apply R_Not_e with (A := A ∈ A).
        ++ apply R_Ax. compute; intuition.
        ++ apply R_Imp_e with (A := A ∈ A).
            -- apply R_And_e1 with (B := (~ A ∈ A -> A ∈ A)).
               assert (Pr Intuiti (Γ' ⊢ comp)). { apply R_Ax. compute; intuition. }
               apply R_All_e with (t := FVar a) in H; auto.
            -- apply R_Ax. compute; intuition.
    - apply R_Not_i.
      set (Γ' := (_ :: Γ)).
      apply R_Not_e with (A := A ∈ A).
      * apply R_Ax. compute; intuition.
      * apply R_Imp_e with (A := A ∈ A).
        ++ apply R_And_e1 with (B := (~ A ∈ A -> A ∈ A)).
           assert (Pr Intuiti (Γ' ⊢ comp)). { apply R_Ax. compute; intuition. }
           apply R_All_e with (t := FVar a) in H; auto.
        ++ apply R_Ax. compute; intuition.
Qed.

(* Russell's paradox therefore shows that the naive set theory is inconsistent.
   We are to try to fix it, using ZF(C) theory, which has not been proved inconstitent so far
   (neither has it been proved consistent though...). *)

(** The ZF axioms *)

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
     apply andb_true_iff.
     split.
     * rewrite check_lift_form_above. assumption.
     * (* TODO *) apply orb_true_iff. left. rewrite check_lift_form_above. assumption.
   + red. rewrite nForall_level. rewrite !aux2, aux.
     cbn -[Nat.max].
     simpl (Nat.max 1 _).
     rewrite Nat.max_assoc. simpl (Nat.max 2 3). omega with *.
   + apply nForall_fclosed. red. unfold Names.Empty. intro a. intro.
     rewrite !aux2', aux3 in H.
     apply Names.union_spec in H.
     destruct H.
     * rewrite <- Names.mem_spec in H. compute in H. easy.
     * apply aux4 in H. apply Names.union_spec in H. destruct H.
       -- cbn in H. easy.
       -- unfold FClosed in HB''. unfold Names.Empty in HB''. destruct HB'' with (a := a). assumption.
 - repeat split; unfold replacement_schema; cbn.
   + rewrite nForall_check. cbn.
     apply andb_true_iff.
     split.
     * apply andb_true_iff.
       split; [ assumption | ].
       apply orb_true_iff.
       left.
       cbn.
       (* TODO bis *)
     rewrite !check_bsubst, HB; auto.
   + red. rewrite nForall_level. cbn.
     assert (level (bsubst 0 Zero B) <= level B).
     { apply level_bsubst'. auto. }
     assert (level (bsubst 0 (Succ(BVar 0)) B) <= level B).
     { apply level_bsubst'. auto. }
     omega with *.
   + apply nForall_fclosed. red. cbn.
     assert (FClosed (bsubst 0 Zero B)).
     { red. rewrite bsubst_fvars.
       intro x. rewrite Names.union_spec. cbn. red in HB'. intuition. }
     assert (FClosed (bsubst 0 (Succ(BVar 0)) B)).
     { red. rewrite bsubst_fvars.
       intro x. rewrite Names.union_spec. cbn - [Names.union].
       rewrite Names.union_spec.
       generalize (HB' x) (@Names.empty_spec x). intuition. }
     unfold FClosed in *. intuition.
Qed.

End ZFAx.

Local Open Scope string.
Local Open Scope formula_scope.

Definition ZFTheory :=
 {| sign := ZFSign;
    IsAxiom := ZFAx.IsAx;
    WfAxiom := ZFAx.WfAx |}.


Import ZFAx.
