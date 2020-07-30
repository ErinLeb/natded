
(** * Ordering of the String datatype *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Bool Orders Ascii AsciiOrder String.
Local Open Scope string_scope.

Inductive string_lt : string -> string -> Prop :=
 | LtEmpty a s : string_lt "" (String a s)
 | LtHead a a' s s' : ascii_lt a a' -> string_lt (String a s) (String a' s')
 | LtTail a s s' : string_lt s s' -> string_lt (String a s) (String a s').
Hint Constructors string_lt.
Local Infix "<" := string_lt.

Definition string_le s s' := s<s' \/ s=s'.
Local Infix "<=" := string_le.

Lemma string_lt_strorder : StrictOrder string_lt.
Proof.
 split.
 - intros s. red. induction s; inversion_clear 1; auto.
   now apply ascii_lt_strorder in H0.
 - red. intros x y z H; revert z. induction H; inversion_clear 1; auto.
   constructor. eapply ascii_lt_strorder; eauto.
Qed.

Lemma string_le_lteq s s' : s<=s' <-> s<s' \/ s=s'.
Proof.
 reflexivity.
Qed.

Fixpoint string_compare s s' :=
  match s, s' with
  | "", "" => Eq
  | "", _ => Lt
  | _, "" => Gt
  | String a s, String a' s' =>
    match ascii_compare a a' with
    | Eq => string_compare s s'
    | Lt => Lt
    | Gt => Gt
    end
  end.

Lemma string_compare_spec s s' :
 CompareSpec (s=s') (s<s') (s'<s) (string_compare s s').
Proof.
 revert s'.
 induction s as [|a s IH]; destruct s' as [|a' s']; simpl; auto.
 case ascii_compare_spec; intros H; subst; simpl; auto.
 case IH; intros H; subst; auto.
Qed.

Definition string_eqb s s' :=
 match string_compare s s' with
 | Eq => true
 | _ => false
 end.

Definition string_ltb s s' :=
 match string_compare s s' with
 | Lt => true
 | _ => false
 end.

Definition string_leb s s' :=
 match string_compare s s' with
 | Gt => false
 | _ => true
 end.

Lemma string_eqb_spec s s' : reflect (s = s') (string_eqb s s').
Proof.
 unfold string_eqb.
 assert (H := string_compare_spec s s').
 destruct string_compare; constructor; inversion H; auto.
 intros <-. assert (~(s < s)) by apply string_lt_strorder. auto.
 intros <-. assert (~(s < s)) by apply string_lt_strorder. auto.
Qed.

Lemma string_ltb_spec s s' : BoolSpec (s < s') (s' <= s) (string_ltb s s').
Proof.
 unfold string_ltb, string_le.
 assert (H := string_compare_spec s s').
 destruct string_compare; constructor; inversion H; auto.
Qed.

Lemma string_leb_spec s s' : BoolSpec (s <= s') (s' < s) (string_leb s s').
Proof.
 unfold string_leb, string_le.
 assert (H := string_compare_spec s s').
 destruct string_compare; constructor; inversion H; auto.
Qed.


Module StringOT <: UsualOrderedType.
 Definition t := string.
 Definition eq := @Logic.eq string.
 Definition eq_equiv := @eq_equivalence string.
 Definition lt := string_lt.
 Lemma lt_compat : Proper (eq==>eq==>iff) lt.
 Proof. now intros ? ? -> ? ? ->. Qed.
 Definition lt_strorder := string_lt_strorder.
 Definition compare := string_compare.
 Definition compare_spec := string_compare_spec.
 Definition eq_dec := string_dec.
End StringOT.
