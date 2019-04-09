
Require Export Arith Bool String MSetRBT StringOrder List Utils.
Require DecimalString.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

(** Signatures *)

(** Just in case, a signature that could be infinite *)

Definition function_symbol := string.
Definition predicate_symbol := string.
Definition arity := nat.

Bind Scope string_scope with function_symbol.
Bind Scope string_scope with predicate_symbol.

Record signature :=
  make_infinite_sign
  { funsymbs : function_symbol -> option arity;
    predsymbs : predicate_symbol -> option arity }.

(** A finite version *)

Module Finite.

Record signature :=
  make_finite_sign
  { funsymbs : list (function_symbol * arity);
    predsymbs : list (predicate_symbol * arity) }.

Definition to_infinite sign :=
  make_infinite_sign
    (fun s => list_assoc s sign.(funsymbs))
    (fun s => list_assoc s sign.(predsymbs)).

End Finite.


(** In pratice, the symbols could be special characters as "+", or
    names. In fact, pretty much anything that doesn't contain
    the parenthesis characters or the comma. *)

Definition peano_sign :=
  {| Finite.funsymbs := [("O",0);("S",1);("+",2);("*",2)];
     Finite.predsymbs := [("=",2)] |}.

Definition zf_sign :=
  {| Finite.funsymbs := [];
     Finite.predsymbs := [("=",2);("∈",2)] |}.


(** Variables *)

(** Variables are coded as string, and will follow the usual
    syntactic conventions for identifiers : a letter first, then
    letters or digits or "_". *)

Definition variable := string.

Bind Scope string_scope with variable.

Module Vars := MSetRBT.Make (StringOT).

(* Prevent incomplete reductions *)
Arguments Vars.singleton !_.
Arguments Vars.add !_ !_.
Arguments Vars.remove !_ !_.
Arguments Vars.union !_ !_.
Arguments Vars.inter !_ !_.
Arguments Vars.diff !_ !_.

Definition vars_of_list : list variable -> Vars.t :=
 fold_right Vars.add Vars.empty.

Fixpoint vars_unions (l: list Vars.t) :=
 match l with
 | [] => Vars.empty
 | vs::l => Vars.union vs (vars_unions l)
 end.

Definition vars_unionmap {A} (f: A -> Vars.t) :=
 fix flatmap (l:list A) :=
 match l with
 | [] => Vars.empty
 | a::l => Vars.union (f a) (flatmap l)
 end.

Definition vars_map (f:string->string) (vs : Vars.t) :=
  Vars.fold (fun v => Vars.add (f v)) vs Vars.empty.

Definition vars_flatmap (f:string->Vars.t) (vs : Vars.t) :=
  Vars.fold (fun v => Vars.union (f v)) vs Vars.empty.

(** [fresh_var vars] : gives a new variable not in the set [vars]. *)

Fixpoint fresh_var_loop (vars:Vars.t) (id:string) n : variable :=
  match n with
  | O => id
  | S n => if negb (Vars.mem id vars) then id
           else fresh_var_loop vars (id++"x") n
  end.

Definition fresh_var vars := fresh_var_loop vars "x" (Vars.cardinal vars).

(* Compute fresh_var (Vars.add "x" (Vars.add "y" (Vars.singleton "xx"))). *)


(** Misc types : operators, quantificators *)

Inductive op := And | Or | Impl.

Inductive quant := All | Ex.

Instance op_eqb : Eqb op :=
 fun o1 o2 =>
  match o1, o2 with
  | And, And | Or, Or | Impl, Impl => true
  | _, _ => false
  end.

Instance quant_eqb : Eqb quant :=
 fun q1 q2 =>
  match q1, q2 with
  | All, All | Ex, Ex => true
  | _, _ => false
  end.

Definition pr_op o :=
  match o with
  | And => "/\"
  | Or => "\/"
  | Impl => "->"
  end.

Definition pr_quant q :=
  match q with
  | All => "∀"
  | Ex => "∃"
  end.

Instance : EqbSpec op.
Proof.
 intros [ ] [ ]; now constructor.
Qed.

Instance : EqbSpec quant.
Proof.
 intros [ ] [ ]; now constructor.
Qed.

(** Which logic are we using : classical or intuitionistic ? *)

Inductive logic := Classic | Intuiti.

Instance logic_eqb : Eqb logic :=
  fun l1 l2 =>
    match l1, l2 with
    | Classic, Classic | Intuiti, Intuiti => true
    | _, _ => false
    end.

Instance : EqbSpec logic.
Proof.
 intros [ ] [ ]; now constructor.
Qed.
