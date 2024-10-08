
(** * Ordering the Ascii datatype *)

(** The NatDed development, Pierre Letouzey, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Bool Ascii BinNat Orders OrdersEx.
Local Open Scope char_scope.

Lemma ascii_N_inj (c c' : ascii) :
 N_of_ascii c = N_of_ascii c' -> c = c'.
Proof.
 intros.
 rewrite <- (ascii_N_embedding c), <- (ascii_N_embedding c').
 now f_equal.
Qed.

Lemma ascii_N_iff (c c' : ascii) :
 N_of_ascii c = N_of_ascii c' <-> c = c'.
Proof.
 split. apply ascii_N_inj. intros; now subst.
Qed.

Definition ascii_lt c c' := (N_of_ascii c < N_of_ascii c')%N.
Definition ascii_le c c' := (N_of_ascii c <= N_of_ascii c')%N.
Definition ascii_compare c c' := (N_of_ascii c ?= N_of_ascii c')%N.
Definition ascii_eqb c c' := (N_of_ascii c =? N_of_ascii c')%N.
Definition ascii_ltb c c' := (N_of_ascii c <? N_of_ascii c')%N.
Definition ascii_leb c c' := (N_of_ascii c <=? N_of_ascii c')%N.

Local Infix "<" := ascii_lt.
Local Infix "<=" := ascii_le.

Lemma ascii_lt_strorder : StrictOrder ascii_lt.
Proof.
  split.
  - intros ?. apply N.lt_strorder.
  - intros ? ? ?. apply N.lt_strorder.
Qed.

Lemma ascii_le_lteq c c' : c<=c' <-> c<c' \/ c=c'.
Proof.
 rewrite <- ascii_N_iff.
 apply N.le_lteq.
Qed.

Lemma ascii_compare_spec (c c' : ascii) :
  CompareSpec (c=c') (c<c') (c'<c) (ascii_compare c c').
Proof.
  unfold ascii_compare, ascii_lt.
  case N.compare_spec; simpl; auto using ascii_N_inj.
Qed.

Lemma ascii_eqb_spec c c' : reflect (c = c') (ascii_eqb c c').
Proof.
  unfold ascii_eqb.
  case N.eqb_spec; intros; simpl; constructor;
   now rewrite <- ascii_N_iff.
Qed.

Lemma ascii_ltb_spec c c' : BoolSpec (c < c') (c' <= c) (ascii_ltb c c').
Proof.
  unfold ascii_ltb. case N.ltb_spec; simpl; auto.
Qed.

Lemma ascii_leb_spec c c' : BoolSpec (c <= c') (c' < c) (ascii_leb c c').
Proof.
  unfold ascii_leb. case N.leb_spec; simpl; auto.
Qed.

Module AsciiOT <: UsualOrderedType.
 Definition t := ascii.
 Definition eq := @Logic.eq ascii.
 Definition eq_equiv := @eq_equivalence ascii.
 Definition lt := ascii_lt.
 Lemma lt_compat : Proper (eq==>eq==>iff) lt.
 Proof. now intros ? ? -> ? ? ->. Qed.
 Definition lt_strorder := ascii_lt_strorder.
 Definition compare := ascii_compare.
 Definition compare_spec := ascii_compare_spec.
 Definition eq_dec := ascii_dec.
End AsciiOT.
