Require Import Bool Ascii String AsciiOrder StringOrder List.
Import ListNotations.
Open Scope lazy_bool_scope.

Lemma lazy_andb_iff (b b' : bool) :
 b &&& b' = true <-> b = true /\ b' = true.
Proof.
 now destruct b, b'.
Qed.

(** A bit of overloading of notations (via Coq Classes) *)

Delimit Scope eqb_scope with eqb.
Local Open Scope eqb_scope.

Class Eqb (A : Type) := eqb : A -> A -> bool.
Infix "=?" := eqb : eqb_scope.
Arguments eqb {A} _ a a' /.

Instance eqb_inst_nat : Eqb nat := Nat.eqb.
Instance eqb_inst_ascii : Eqb ascii := AsciiOrder.ascii_eqb.
Instance eqb_inst_string : Eqb string := StringOrder.string_eqb.

Arguments eqb_inst_nat /.
Arguments eqb_inst_ascii /.
Arguments eqb_inst_string /.

Fixpoint list_assoc {A B}`{Eqb A} x (l:list (A*B)) :=
 match l with
 | [] => None
 | (y,z)::l => if x =? y then Some z else list_assoc x l
 end.

Fixpoint list_mem {A}`{Eqb A} x (l:list A) :=
  match l with
  | [] => false
  | y::l => (x =? y) ||| list_mem x l
  end.

Definition list_forallb2 {A B} (f: A -> B -> bool) :=
 fix forallb2 l1 l2 :=
 match l1, l2 with
 | [], [] => true
 | x1::l1, x2::l2 => f x1 x2 &&& forallb2 l1 l2
 | _, _ => false
 end.

Fixpoint list_index {A} `{Eqb A} (x:A) l : option nat :=
  match l with
  | [] => None
  | y::l => if x =? y then Some 0
            else option_map S (list_index x l)
  end.

Fixpoint list_max l :=
  match l with
  | [] => 0
  | n::l => max n (list_max l)
  end.



Ltac cons := constructor; congruence.

Lemma forallb2_eqb_spec {A}(eqb : A -> A -> bool) :
 (forall x x', reflect (x=x') (eqb x x')) ->
 forall l l', reflect (l=l') (list_forallb2 eqb l l').
Proof.
 intros EQB.
 induction l; destruct l'; simpl; try cons.
 case EQB; [intros <- | cons].
 case IHl; cons.
Defined.
