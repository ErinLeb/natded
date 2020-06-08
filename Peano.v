
(** * The Theory of Peano Arithmetic and its Coq model *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Meta Theories PreModels Models.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

(** The Peano axioms *)

Definition PeanoSign := Finite.to_infinite peano_sign.

Definition Zero := Fun "O" [].
Definition Succ x := Fun "S" [x].

Notation "x = y" := (Pred "=" [x;y]) : formula_scope.
Notation "x + y" := (Fun "+" [x;y]) : formula_scope.
Notation "x * y" := (Fun "*" [x;y]) : formula_scope.

Module PeanoAx.
Local Open Scope formula_scope.

Definition ax1 := ∀ (#0 = #0).
Definition ax2 := ∀∀ (#1 = #0 -> #0 = #1).
Definition ax3 := ∀∀∀ (#2 = #1 /\ #1 = #0 -> #2 = #0).

Definition ax4 := ∀∀ (#1 = #0 -> Succ (#1) = Succ (#0)).
Definition ax5 := ∀∀∀ (#2 = #1 -> #2 + #0 = #1 + #0).
Definition ax6 := ∀∀∀ (#1 = #0 -> #2 + #1 = #2 + #0).
Definition ax7 := ∀∀∀ (#2 = #1 -> #2 * #0 = #1 * #0).
Definition ax8 := ∀∀∀ (#1 = #0 -> #2 * #1 = #2 * #0).

Definition ax9 := ∀ (Zero + #0 = #0).
Definition ax10 := ∀∀ (Succ(#1) + #0 = Succ(#1 + #0)).
Definition ax11 := ∀ (Zero * #0 = Zero).
Definition ax12 := ∀∀ (Succ(#1) * #0 = (#1 * #0) + #0).

Definition ax13 := ∀∀ (Succ(#1) = Succ(#0) -> #1 = #0).
Definition ax14 := ∀ ~(Succ(#0) = Zero).

Definition axioms_list :=
  [ ax1; ax2; ax3; ax4; ax5; ax6; ax7; ax8;
    ax9; ax10; ax11; ax12; ax13; ax14 ].

(** Beware, [bsubst] is ok below for turning [#0] into [Succ #0], but
    only since it contains now a [lift] of substituted terms inside
    quantifiers.
    And the unconventional [∀] before [A[0]] is to get the right
    bounded vars (Hack !). *)

Definition induction_schema A_x :=
  let A_0 := bsubst 0 Zero A_x in
  let A_Sx := bsubst 0 (Succ(#0)) A_x in
  nForall
    (Nat.pred (level A_x))
    (((∀ A_0) /\ (∀ (A_x -> A_Sx))) -> ∀ A_x).

Local Close Scope formula_scope.

Definition IsAx A :=
  List.In A axioms_list \/
  exists B, A = induction_schema B /\
            check PeanoSign B = true /\
            FClosed B.

Lemma WfAx A : IsAx A -> Wf PeanoSign A.
Proof.
 intros [ IN | (B & -> & HB & HB')].
 - apply Wf_iff.
   unfold axioms_list in IN.
   simpl in IN. intuition; subst; reflexivity.
 - repeat split; unfold induction_schema; cbn.
   + rewrite nForall_check. cbn.
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

End PeanoAx.

Local Open Scope string.
Local Open Scope formula_scope.

Definition PeanoTheory :=
 {| sign := PeanoSign;
    IsAxiom := PeanoAx.IsAx;
    WfAxiom := PeanoAx.WfAx |}.

(** Some basic proofs in Peano arithmetics. *)

Lemma ZeroRight : IsTheorem Intuiti PeanoTheory (∀ (#0 = #0 + Zero)).
Proof.
  unfold IsTheorem.
  split.
  + unfold Wf. split; [ auto | split; auto ].
  + exists ((induction_schema (#0 = #0 + Zero))::axioms_list).

Lemma Comm : IsTheorem Intuiti PeanoTheory (∀∀ (#0 + #1 = #1 + #0)).
Proof.
  Admitted.

(** A Coq model of this Peano theory, based on the [nat] type *)

Definition PeanoFuns : modfuns nat :=
  fun f =>
  if f =? "O" then Some (existT _ 0 0)
  else if f =? "S" then Some (existT _ 1 S)
  else if f =? "+" then Some (existT _ 2 Nat.add)
  else if f =? "*" then Some (existT _ 2 Nat.mul)
  else None.

Definition PeanoPreds : modpreds nat :=
  fun p =>
  if p =? "=" then Some (existT _ 2 (@Logic.eq nat))
  else None.

Lemma PeanoFuns_ok s :
 funsymbs PeanoSign s = get_arity (PeanoFuns s).
Proof.
 unfold PeanoSign, peano_sign, PeanoFuns. simpl.
 unfold eqb, eqb_inst_string.
 repeat (case string_eqb; auto).
Qed.

Lemma PeanoPreds_ok s :
 predsymbs PeanoSign s = get_arity (PeanoPreds s).
Proof.
 unfold PeanoSign, peano_sign, PeanoPreds. simpl.
 unfold eqb, eqb_inst_string.
 case string_eqb; auto.
Qed.

Definition PeanoPreModel : PreModel nat PeanoTheory :=
 {| someone := 0;
    funs := PeanoFuns;
    preds := PeanoPreds;
    funsOk := PeanoFuns_ok;
    predsOk := PeanoPreds_ok |}.

Lemma PeanoAxOk A :
  IsAxiom PeanoTheory A ->
  forall genv, interp_form PeanoPreModel genv [] A.
Proof.
 unfold PeanoTheory. simpl.
 unfold PeanoAx.IsAx.
 intros [IN|(B & -> & CK & CL)].
 - compute in IN. intuition; subst; cbn; intros; subst; omega.
 - intros genv.
   unfold PeanoAx.induction_schema.
   apply interp_nforall.
   intros stk Len. rewrite app_nil_r. cbn.
   intros (Base,Step).
   (* The Peano induction emulated by a Coq induction :-) *)
   induction m.
   + specialize (Base 0).
     apply -> interp_form_bsubst_gen in Base; simpl; eauto.
   + apply Step in IHm.
     apply -> interp_form_bsubst_gen in IHm; simpl; eauto.
     now intros [|k].
Qed.

Definition PeanoModel : Model nat PeanoTheory :=
 {| pre := PeanoPreModel;
    AxOk := PeanoAxOk |}.
