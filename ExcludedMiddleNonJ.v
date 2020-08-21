
(** * Ad-Hoc proof that Excluded-Middle principle isn't provable in LJ *)

(** The NatDed development, Pierre Letouzey, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs Mix ProofExamples.
Import ListNotations.
Open Scope eqb_scope.

(** Instead of the classical interpretation of formulas by
    boolean truth values, we use here ternary truth values.
    This is actually a particular case of Kripke model dedicated
    to refuting [A‌\/~A] in intuitionistic logic. *)

Module Val3.

Inductive val3 := Zero | Half | One.
Definition t := val3.

Definition eqb x y :=
  match x, y with
  | Zero, Zero | Half, Half | One, One => true
  | _, _ => false
  end.

Lemma eqb_spec x y : reflect (x=y) (eqb x y).
Proof.
 destruct x, y; cbn; now constructor.
Qed.

Global Instance eqb_value : Eqb val3 := eqb.
Global Instance eqbspec_value : EqbSpec val3 := eqb_spec.

Definition leb x y :=
  match x, y with
  | Zero, _ | Half, Half | Half, One | One, One => true
  | _, _ => false
  end.

Definition le x y := leb x y = true.

Infix "<=?" := leb.
Infix "<=" := le.

Global Instance : PreOrder le.
Proof.
 split.
 - now intros [ ].
 - now intros [ ] [ ] [ ].
Qed.

Global Instance : Antisymmetric val3 eq le.
Proof.
 now intros [ ] [ ].
Qed.

Definition max x y := if x <=? y then y else x.

Definition min x y := if x <=? y then x else y.

Definition imp x y := if x <=? y then One else y.

Definition op o :=
  match o with
  | And => min
  | Or => max
  | Imp => imp
  end.

Lemma le_imp x y : y <= imp x y.
Proof.
 now destruct x, y.
Qed.

Lemma imp_one x y : imp x y = One <-> x <= y.
Proof.
 now destruct x, y.
Qed.

Lemma min_le_l x y : min x y <= x.
Proof.
 now destruct x, y.
Qed.

Lemma min_le_r x y : min x y <= y.
Proof.
 now destruct x, y.
Qed.

End Val3.
Import Val3.

Definition predicate_choice := predicate_symbol -> val3.

Fixpoint interp (pc:predicate_choice)(A:formula) :=
 match A with
 | True => One
 | False => Zero
 | Pred p l => pc p
 | Not A => Val3.imp (interp pc A) Zero
 | Op o A B => Val3.op o (interp pc A) (interp pc B)
 | Quant _ A => interp pc A
 end.

Fixpoint interp_ctx (pc:predicate_choice)(G:context) :=
 match G with
 | [] => One
 | A::G => Val3.min (interp pc A) (interp_ctx pc G)
 end.

Definition interp_seq (pc:predicate_choice)'(G ⊢ A) :=
 Val3.imp (interp_ctx pc G) (interp pc A).

Lemma interp_ctx_in pc G A : In A G -> interp_ctx pc G <= interp pc A.
Proof.
 induction G.
 - inversion 1.
 - cbn. intros [<-| ].
   + apply min_le_l.
   + etransitivity. apply min_le_r. now apply IHG.
Qed.

Lemma interp_bsubst pc A n t : interp pc (bsubst n t A) = interp pc A.
Proof.
 revert n t. induction A; cbn; intros; auto; f_equal; auto.
Qed.

Lemma correct seq pc : Pr J seq -> interp_seq pc seq = One.
Proof.
 induction 1; cbn in *;
  rewrite ?interp_bsubst in *;
  try now (destruct interp_ctx, interp, interp).
 - rewrite imp_one. now apply interp_ctx_in.
 - now destruct interp_ctx.
Qed.

(** One instance of Excluded-Middle which isn't provable in LJ :
    with a fresh predicate X of arity 0.
    Note : one can always extend a theory with extra symbols without
    extra axioms, this is a conservative extension, see
    Theories.ext_sign_only. *)

Definition X := Pred "X" [].

Lemma EM_non_J : ~Pr J ([] ⊢ X \/ ~ X).
Proof.
 intros H.
 now apply correct with (pc := fun _ => Half) in H.
Qed.

(** This also works for ~~X->X *)

Lemma NotNot_non_J : ~Pr J ([] ⊢ ~~X -> X).
Proof.
 intros H.
 now apply correct with (pc := fun _ => Half) in H.
Qed.

(** And for Peirce's Law where Y is False *)

Lemma Peirce_non_J : ~Pr J ([] ⊢ ((X->False)->X)->X).
Proof.
 intros H.
 now apply correct with (pc := fun _ => Half) in H.
Qed.

(** For other classical formulas, such as (X->Y)\/(Y->X),
    the method above is inconclusive : one would need more general
    Kripke models, not just Val3. Another approach might also be to
    use relative strength to show that these law are no more
    provable in LJ than one of the previous (?). *)

Import Meta.

Lemma ImpOr_K A B : Pr K ([] ⊢ (A->B)\/(B->A)).
Proof.
 eapply R_Or_e.
 - apply (Excluded_Middle A).
 - apply R_Or_i2.
   apply R_Imp_i. apply Pr_pop, R'_Ax.
 - apply R_Or_i1.
   apply R_Imp_i.
   apply R_Fa_e. apply R_Not_e with A. apply R'_Ax.
   apply Pr_pop, R'_Ax.
Qed.

Definition Y := Pred "Y" [].
Lemma ImpOr_interp pc : interp pc ((X->Y)\/(Y->X)) = One.
Proof.
 cbn. now destruct pc, pc.
Qed.
