
(** Natded again, with a Locally Nameless encoding *)

Require Import Defs.
Require DecimalString.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

(** We use here a Locally nameless representation of terms.
    See for instance http://www.chargueraud.org/research/2009/ln/main.pdf
*)

(** A term is given by the following recursive definition: *)

Inductive term :=
  | FVar : variable -> term (** Free variable (global name) *)
  | BVar : nat -> term (** Bounded variable (de Bruijn indices) *)
  | Fun : function_symbol -> list term -> term.

Definition Cst (f:function_symbol) := Fun f [].

Definition peano_term_example :=
  Fun "+" [Fun "S" [Cst "O"]; FVar "x"].

(** In the case of Peano, numbers are coded as iterated successors of zero *)

Fixpoint nat2term n :=
  match n with
  | O => Cst "O"
  | S n => Fun "S" [nat2term n]
  end.

Fixpoint term2nat t :=
  match t with
  | Fun f [] => if f =? "O" then Some O else None
  | Fun f [t] => if f =? "S" then option_map S (term2nat t) else None
  | _ => None
  end.

(** Term printing

    NB: + and * are printed in infix position, S(S(...O())) is printed as
    the corresponding number.
*)

Definition print_tuple {A} (pr: A -> string) (l : list A) :=
 "(" ++ String.concat "," (List.map pr l) ++ ")".

Definition is_binop s := list_mem s ["+";"*"].

Fixpoint print_term t :=
  match term2nat t with
  | Some n => DecimalString.NilZero.string_of_uint (Nat.to_uint n)
  | None =>
     match t with
     | FVar v => v
     | BVar n => "#" ++ DecimalString.NilZero.string_of_uint (Nat.to_uint n)
     | Fun f args =>
       if is_binop f then
         match args with
         | [t1;t2] =>
           "(" ++ print_term t1 ++ ")" ++ f ++ "(" ++ print_term t2 ++ ")"
         | _ => f ++ print_tuple print_term args
         end
       else f ++ print_tuple print_term args
     end
  end.

Compute print_term peano_term_example.

(** Term parsing *)

(** Actually, parsing is not so easy and not so important.
    Let's put the details elsewhere, and take for granted that
    parsing is doable :-).
*)

(* TODO: formula parsing *)


(** Some generic functions, meant to be overloaded
    with instances for terms, formulas, context, sequent, ... *)

(** Check for known function/predicate symbols + correct arity *)
Class Check (A : Type) := check : gen_signature -> A -> bool.
Arguments check {_} {_} _ !_.

(** Replace a bound variable with a term *)
Class BSubst (A : Type) := bsubst : nat -> term -> A -> A.
Arguments bsubst {_} {_} _ _ !_.

(** Level : succ of max bounded variable *)
Class Level (A : Type) := level : A -> nat.
Arguments level {_} {_} !_.

(** Compute the set of free variables *)
Class FVars (A : Type) := fvars : A -> Vars.t.
Arguments fvars {_} {_} !_.

(** General replacement of free variables *)
Class VMap (A : Type) := vmap : (variable -> term) -> A -> A.
Arguments vmap {_} {_} _ !_.

(** Some generic definitions based on the previous ones *)

Definition closed {A}`{Level A} (a:A) := level a = 0.

Hint Unfold closed.

(** Substitution of a free variable in a term :
    in [t], free var [v] is replaced by [u]. *)

Definition varsubst v u x := if v =? x then u else FVar x.

Definition fsubst {A}`{VMap A} (v:variable)(u:term) :=
 vmap (varsubst v u).

(** Some structural extensions of these generic functions *)

Instance check_list {A}`{Check A} : Check (list A) :=
 fun (sign : gen_signature) => List.forallb (check sign).

Instance bsubst_list {A}`{BSubst A} : BSubst (list A) :=
 fun n t => List.map (bsubst n t).

Instance level_list {A}`{Level A} : Level (list A) :=
 fun l => list_max (List.map level l).

Instance fvars_list {A}`{FVars A} : FVars (list A) :=
 vars_unionmap fvars.

Instance vmap_list {A}`{VMap A} : VMap (list A) :=
 fun h => List.map (vmap h).

Instance check_pair {A B}`{Check A}`{Check B} : Check (A*B) :=
 fun (sign : gen_signature) '(a,b) => check sign a &&& check sign b.

Instance bsubst_pair {A B}`{BSubst A}`{BSubst B} : BSubst (A*B) :=
 fun n t '(a,b) => (bsubst n t a, bsubst n t b).

Instance level_pair {A B}`{Level A}`{Level B} : Level (A*B) :=
 fun '(a,b) => Nat.max (level a) (level b).

Instance fvars_pair {A B}`{FVars A}`{FVars B} : FVars (A*B) :=
 fun '(a,b) => Vars.union (fvars a) (fvars b).

Instance vmap_pair {A B}`{VMap A}`{VMap B} : VMap (A*B) :=
 fun h '(a,b) => (vmap h a, vmap h b).


(** With respect to a particular signature, a term is valid
    iff it only refer to known function symbols and use them
    with the correct arity. *)

Instance check_term : Check term :=
 fun (sign : gen_signature) =>
 fix check_term t :=
 match t with
  | FVar _ | BVar _ => true
  | Fun f args =>
     match sign.(gen_fun_symbs) f with
     | None => false
     | Some ar =>
       (List.length args =? ar) &&& (List.forallb check_term args)
     end
 end.

Compute check (generalize_signature peano_sign) peano_term_example.

Instance term_fvars : FVars term :=
 fix term_fvars t :=
 match t with
 | BVar _ => Vars.empty
 | FVar v => Vars.singleton v
 | Fun _ args => vars_unionmap term_fvars args
 end.

Instance term_level : Level term :=
 fix term_level t :=
 match t with
 | BVar n => S n
 | FVar v => 0
 | Fun _ args => list_max (map term_level args)
 end.

Instance term_bsubst : BSubst term :=
 fun n u =>
 fix bsubst t :=
  match t with
  | FVar v => t
  | BVar k => if k =? n then u else t
  | Fun f args => Fun f (List.map bsubst args)
  end.

Instance term_vmap : VMap term :=
 fun (h:variable->term) =>
 fix vmap t :=
  match t with
  | BVar _ => t
  | FVar x => h x
  | Fun f args => Fun f (List.map vmap args)
  end.

Instance term_eqb : Eqb term :=
 fix term_eqb t1 t2 :=
  match t1, t2 with
  | BVar n1, BVar n2 => n1 =? n2
  | FVar v1, FVar v2 => v1 =? v2
  | Fun f1 args1, Fun f2 args2 =>
    (f1 =? f2) &&& (list_forallb2 term_eqb args1 args2)
  | _, _ => false
  end.

(** Formulas *)

Inductive formula :=
  | True
  | False
  | Pred : predicate_symbol -> list term -> formula
  | Not : formula -> formula
  | Op : op -> formula -> formula -> formula
  | Quant : quant -> formula -> formula.

(** Note the lack of variable name after [Quant], we're using
    de Bruijn indices there. *)

(** One extra pseudo-constructor :
    [a<->b] is a shortcut for [a->b /\ b->a] *)

Definition Iff a b := Op And (Op Impl a b) (Op Impl b a).

(** Formula printing *)

(** Notes:
    - We use {  } for putting formulas into parenthesis, instead of ( ).
*)

Definition is_infix_pred s := list_mem s ["=";"∈"].

(* TODO affichage court du <-> *)

Fixpoint print_formula f :=
  match f with
  | True => "True"
  | False => "False"
  | Pred p args =>
    if is_infix_pred p then
      match args with
      | [t1;t2] =>
        "(" ++ print_term t1 ++ ")" ++ p ++ "(" ++ print_term t2 ++ ")"
      |  _ => p ++ print_tuple print_term args
      end
    else p ++ print_tuple print_term args
  | Not f => "~{" ++ print_formula f ++ "}"
  | Op o f f' =>
    "{" ++ print_formula f ++ "}" ++ pr_op o ++ "{" ++ print_formula f' ++ "}"
  | Quant q f => pr_quant q ++ "{" ++ print_formula f ++ "}"
  end.

Compute print_formula (Quant Ex True).

Compute print_formula (Iff True False).

(* TODO: Formula parsing *)

(* Instead : Coq notations *)

Delimit Scope formula_scope with form.
Bind Scope formula_scope with formula.

Notation "~ f" := (Not f) : formula_scope.
Infix "/\" := (Op And) : formula_scope.
Infix "\/" := (Op Or) : formula_scope.
Infix "->" := (Op Impl) : formula_scope.
Infix "<->" := Iff : formula_scope.

Notation "# n" := (BVar n) (at level 20) : formula_scope.

Notation "∀ A" := (Quant All A)
 (at level 200, right associativity) : formula_scope.
Notation "∃ A" := (Quant Ex A)
 (at level 200, right associativity) : formula_scope.

Definition test_form := (∃ (True <-> Pred "p" [#0;#0]))%form.

(** Utilities about formula *)

Instance check_formula : Check formula :=
 fun (sign : gen_signature) =>
 fix check_formula f :=
  match f with
  | True | False => true
  | Not f => check_formula f
  | Op _ f f' => check_formula f &&& check_formula f'
  | Quant _ f => check_formula f
  | Pred p args =>
     match sign.(gen_pred_symbs) p with
     | None => false
     | Some ar =>
       (List.length args =? ar) &&& (List.forallb (check sign) args)
     end
  end.

Instance form_level : Level formula :=
  fix form_level f :=
  match f with
  | True | False => 0
  | Not f => form_level f
  | Op _ f f' => Nat.max (form_level f) (form_level f')
  | Quant _ f => Nat.pred (form_level f)
  | Pred _ args => list_max (map level args)
  end.

Instance form_bsubst : BSubst formula :=
 fix form_bsubst n t f :=
 match f with
  | True | False => f
  | Pred p args => Pred p (List.map (bsubst n t) args)
  | Not f => Not (form_bsubst n t f)
  | Op o f f' => Op o (form_bsubst n t f) (form_bsubst n t f')
  | Quant q f' => Quant q (form_bsubst (S n) t f')
 end.

Instance form_fvars : FVars formula :=
 fix form_fvars f :=
  match f with
  | True | False => Vars.empty
  | Not f => form_fvars f
  | Op _ f f' => Vars.union (form_fvars f) (form_fvars f')
  | Quant _ f => form_fvars f
  | Pred _ args => vars_unionmap fvars args
  end.

Instance form_vmap : VMap formula :=
 fun (h:variable->term) =>
 fix form_vmap f :=
   match f with
   | True | False => f
   | Pred p args => Pred p (List.map (vmap h) args)
   | Not f => Not (form_vmap f)
   | Op o f f' => Op o (form_vmap f) (form_vmap f')
   | Quant q f' => Quant q (form_vmap f')
   end.

Instance form_eqb : Eqb formula :=
 fix form_eqb f1 f2 :=
  match f1, f2 with
  | True, True | False, False => true
  | Pred p1 args1, Pred p2 args2 =>
    (p1 =? p2) &&& (args1 =? args2)
  | Not f1, Not f2 => form_eqb f1 f2
  | Op o1 f1 f1', Op o2 f2 f2' =>
    (o1 =? o2) &&&
    form_eqb f1 f2 &&&
    form_eqb f1' f2'
  | Quant q1 f1', Quant q2 f2' =>
    (q1 =? q2) &&& form_eqb f1' f2'
  | _,_ => false
  end.

Compute eqb
        (∀ (Pred "A" [ #0 ] -> Pred "A" [ #0 ]))%form
        (∀ (Pred "A" [FVar "z"] -> Pred "A" [FVar "z"]))%form.


(** Contexts *)

Definition context := list formula.

Definition print_ctx Γ :=
  String.concat "," (List.map print_formula Γ).

(** check, bsubst, level, fvars, vmap, eqb : given by instances
    on lists. *)

(** Sequent *)

Inductive sequent :=
| Seq : context -> formula -> sequent.

Infix "⊢" := Seq (at level 100).

Definition print_seq '(Γ ⊢ A) :=
  print_ctx Γ ++ " ⊢ " ++ print_formula A.

Instance check_seq : Check sequent :=
 fun sign '(Γ ⊢ A) => check sign Γ &&& check sign A.

Instance bsubst_seq : BSubst sequent :=
 fun n u '(Γ ⊢ A) => (bsubst n u Γ ⊢ bsubst n u A).

Instance level_seq : Level sequent :=
 fun '(Γ ⊢ A) => Nat.max (level Γ) (level A).

Instance seq_fvars : FVars sequent :=
 fun '(Γ ⊢ A) => Vars.union (fvars Γ) (fvars A).

Instance seq_vmap : VMap sequent :=
 fun h '(Γ ⊢ A) => (vmap h Γ ⊢ vmap h A).

Instance seq_eqb : Eqb sequent :=
 fun '(Γ1 ⊢ A1) '(Γ2 ⊢ A2) => (Γ1 =? Γ2) &&& (A1 =? A2).

(** Derivation *)

Inductive rule_kind :=
  | Ax
  | Tr_i
  | Fa_e
  | Not_i | Not_e
  | And_i | And_e1 | And_e2
  | Or_i1 | Or_i2 | Or_e
  | Imp_i | Imp_e
  | All_i (v:variable)| All_e (wit:term)
  | Ex_i (wit:term) | Ex_e (v:variable)
  | Absu.

Inductive derivation :=
  | Rule : rule_kind -> sequent -> list derivation -> derivation.

(** The final sequent of a derivation *)

Definition claim '(Rule _ s _) := s.

(** Utility functions on derivations:
    - bounded-vars level (used by the [closed] predicate),
    - check w.r.t. signature *)

Instance level_rule_kind : Level rule_kind :=
 fun r =>
 match r with
 | All_e wit | Ex_i wit => level wit
 | _ => 0
 end.

Instance level_derivation : Level derivation :=
 fix level_derivation d :=
  let '(Rule r s ds) := d in
  list_max (level r :: level s :: List.map level_derivation ds).

Instance check_rule_kind : Check rule_kind :=
 fun sign r =>
 match r with
 | All_e wit | Ex_i wit => check sign wit
 | _ => true
 end.

Instance check_derivation : Check derivation :=
 fun sign =>
 fix check_derivation d :=
  let '(Rule r s ds) := d in
  check sign r &&&
  check sign s &&&
  List.forallb check_derivation ds.


(** Validity of a derivation : is it using correct rules
    of classical logic (resp. intuitionistic logic) ? *)

Definition valid_deriv_step logic '(Rule r s ld) :=
  match r, s, List.map claim ld with
  | Ax,     (Γ ⊢ A), [] => list_mem A Γ
  | Tr_i,   (_ ⊢ True), [] => true
  | Fa_e,   (Γ ⊢ _), [s] => s =? (Γ ⊢ False)
  | Not_i,  (Γ ⊢ Not A), [s] => s =? (A::Γ ⊢ False)
  | Not_e,  (Γ ⊢ False), [Γ1 ⊢ A; Γ2 ⊢ Not A'] =>
    (A =? A') &&& (Γ =? Γ1) &&& (Γ =? Γ2)
  | And_i,  (Γ ⊢ A/\B), [s1; s2] =>
    (s1 =? (Γ ⊢ A)) &&& (s2 =? (Γ ⊢ B))
  | And_e1, s, [Γ ⊢ A/\_] => s =? (Γ ⊢ A)
  | And_e2, s, [Γ ⊢ _/\B] => s =? (Γ ⊢ B)
  | Or_i1,  (Γ ⊢ A\/_), [s] => s =? (Γ ⊢ A)
  | Or_i2,  (Γ ⊢ _\/B), [s] => s =? (Γ ⊢ B)
  | Or_e,   (Γ ⊢ C), [Γ' ⊢ A\/B; s2; s3] =>
     (Γ=?Γ') &&& (s2 =? (A::Γ ⊢ C)) &&& (s3 =? (B::Γ ⊢ C))
  | Imp_i,  (Γ ⊢ A->B), [s] => s =? (A::Γ ⊢ B)
  | Imp_e,  s, [Γ ⊢ A->B;s2] =>
     (s =? (Γ ⊢ B)) &&& (s2 =? (Γ ⊢ A))
  | All_i x,  (Γ⊢∀A), [Γ' ⊢ A'] =>
     (Γ =? Γ') &&& (A' =? bsubst 0 (FVar x) A)
     &&& negb (Vars.mem x (fvars (Γ⊢A)))
  | All_e t, (Γ ⊢ B), [Γ'⊢ ∀A] =>
    (Γ =? Γ') &&& (B =? bsubst 0 t A)
  | Ex_i t,  (Γ ⊢ ∃A), [Γ'⊢B] =>
    (Γ =? Γ') &&& (B =? bsubst 0 t A)
  | Ex_e x,  s, [Γ⊢∃A; A'::Γ'⊢B] =>
     (s =? (Γ ⊢ B)) &&& (Γ' =? Γ)
     &&& (A' =? bsubst 0 (FVar x) A)
     &&& negb (Vars.mem x (fvars (A::Γ⊢B)))
  | Absu, s, [Not A::Γ ⊢ False] =>
    (logic =? Classic) &&& (s =? (Γ ⊢ A))
  | _,_,_ => false
  end.

Fixpoint valid_deriv logic d :=
  valid_deriv_step logic d &&&
   (let '(Rule _ _ ld) := d in
    List.forallb (valid_deriv logic) ld).

(** Some examples of derivations *)

Definition deriv_example :=
  let A := Pred "A" [] in
  Rule Imp_i ([]⊢A->A) [Rule Ax ([A]⊢A) []].

Compute valid_deriv Intuiti deriv_example.

Definition example_gen (A:formula) :=
  Rule Imp_i ([]⊢A->A) [Rule Ax ([A]⊢A) []].

Compute valid_deriv Intuiti (example_gen (Pred "A" [])).

Definition example2 (A B : term->formula):=
  (Rule Imp_i ([]⊢(∀A(#0)/\B(#0))->(∀A(#0))/\(∀B(#0)))
    (let C := (∀(A(#0)/\B(#0))) in
     [Rule And_i ([C] ⊢ (∀A(#0))/\(∀B(#0)))
       [Rule (All_i "x") ([C]⊢∀A(#0))
         [Rule And_e1 ([C]⊢A(FVar "x"))
           [Rule (All_e (FVar "x")) ([C]⊢ A(FVar "x")/\B(FVar "x"))
             [Rule Ax ([C]⊢C) []]]]
        ;
        Rule (All_i "x") ([C]⊢∀B(#0))
         [Rule And_e2 ([C]⊢B(FVar "x"))
           [Rule (All_e (FVar "x")) ([C]⊢A(FVar "x")/\B(FVar "x"))
             [Rule Ax ([C]⊢C) []]]]]]))%form.

Compute valid_deriv Intuiti
         (example2 (fun x => Pred "A" [x])
                   (fun x => Pred "B" [x])).

Definition em (A:formula) :=
  Rule Absu ([]⊢A\/~A)
    [Rule Not_e ([~(A\/~A)]⊢False)
       [Rule Or_i2 ([~(A\/~A)]⊢A\/~A)
         [Rule Not_i ([~(A\/~A)]⊢~A)
           [Rule Not_e ([A;~(A\/~A)]⊢False)
             [Rule Or_i1 ([A;~(A\/~A)]⊢A\/~A)
               [Rule Ax ([A;~(A\/~A)]⊢A) []]
              ;
              Rule Ax ([A;~(A\/~A)]⊢~(A\/~A)) []]]]
        ;
        Rule Ax ([~(A\/~A)]⊢~(A\/~A)) []]]%form.

Compute valid_deriv Classic (em (Pred "A" [])).
Compute valid_deriv Intuiti (em (Pred "A" [])).

(** Example of free alpha-renaming during a proof,
    (not provable without alpha-renaming) *)

Definition captcha :=
  let A := fun x => Pred "A" [x] in
  Rule (All_i "z") ([A(FVar "x")]⊢∀(A(#0)->A(#0)))%form
   [Rule Imp_i ([A(FVar "x")]⊢A(FVar "z")->A(FVar "z"))
     [Rule Ax ([A(FVar "z");A(FVar "x")]⊢A(FVar "z")) []]].

Compute valid_deriv Intuiti captcha.

Definition captcha_bug :=
  let A := fun x => Pred "A" [x] in
  Rule (All_i "x") ([A(FVar "x")]⊢∀(A(#0)->A(#0)))%form
   [Rule Imp_i ([A(FVar "x")]⊢A(FVar "x")->A(FVar "x"))
    [Rule Ax ([A(FVar "x");A(FVar "x")]⊢A(FVar "x")) []]].

Compute valid_deriv Intuiti captcha_bug.

(** Correctness of earlier boolean equality tests *)

Instance : EqbSpec term.
Proof.
 red.
 fix IH 1. destruct x as [v|n|f l], y as [v'|n'|f' l']; cbn; try cons.
 - case eqbspec; cons.
 - case eqbspec; cons.
 - case eqbspec; [ intros <- | cons ].
   change (list_forallb2 eqb l l') with (l =? l').
   change (EqbSpec term) in IH.
   case eqbspec; cons.
Qed.

Instance : EqbSpec formula.
Proof.
 red.
 induction x; destruct y; cbn; try cons.
 - case eqbspec; [ intros <- | cons ].
   case eqbspec; cons.
 - case IHx; cons.
 - case eqbspec; [ intros <- | cons ].
   case IHx1; [ intros <- | cons].
   case IHx2; cons.
 - case eqbspec; [ intros <- | cons ].
   case IHx; cons.
Qed.

Instance : EqbSpec context.
Proof.
 apply eqbspec_list.
Qed.

Instance : EqbSpec sequent.
Proof.
 intros [] []. cbn. repeat (case eqbspec; try cons).
Qed.

(** Better induction principle on terms *)

Lemma term_ind' (P: term -> Prop) :
  (forall v, P (FVar v)) ->
  (forall n, P (BVar n)) ->
  (forall f args, (forall a, In a args -> P a) -> P (Fun f args)) ->
  forall t, P t.
Proof.
 intros Hv Hn Hl.
 fix IH 1. destruct t.
 - apply Hv.
 - apply Hn.
 - apply Hl.
   revert l.
   fix IH' 1. destruct l.
   + intros a [ ].
   + intros a [<-|Ha]. apply IH. apply (IH' l a Ha).
Qed.

(** Induction principle on derivations with correct
    handling of sub-derivation lists. *)

Lemma derivation_ind' (P: derivation -> Prop) :
  (forall r s ds, Forall P ds -> P (Rule r s ds)) ->
  forall d, P d.
Proof.
 intros Step.
 fix IH 1. destruct d as (r,s,ds).
 apply Step.
 revert ds.
 fix IH' 1. destruct ds; simpl; constructor.
 apply IH.
 apply IH'.
Qed.

(** A derivation "claims" a sequent ... if it ends with this sequent.
    This is just nicer than putting [claim ... = ...] everywhere. *)

Definition Claim d s := claim d = s.
Arguments Claim _ _ /.
Hint Extern 1 (Claim _ _) => cbn.

(** An inductive counterpart to valid_deriv, easier to use in proofs *)

Inductive Valid (l:logic) : derivation -> Prop :=
 | V_Ax Γ A : In A Γ -> Valid l (Rule Ax (Γ ⊢ A) [])
 | V_Tr_i Γ : Valid l (Rule Tr_i (Γ ⊢ True) [])
 | V_Fa_e d Γ A :
     Valid l d -> Claim d (Γ ⊢ False) ->
     Valid l (Rule Fa_e (Γ ⊢ A) [d])
 | V_Not_i d Γ A :
     Valid l d -> Claim d (A::Γ ⊢ False) ->
     Valid l (Rule Not_i (Γ ⊢ ~A) [d])
 | V_Not_e d1 d2 Γ A :
     Valid l d1 -> Valid l d2 ->
     Claim d1 (Γ ⊢ A) -> Claim d2 (Γ ⊢ ~A) ->
     Valid l (Rule Not_e (Γ ⊢ False) [d1;d2])
 | V_And_i d1 d2 Γ A B :
     Valid l d1 -> Valid l d2 ->
     Claim d1 (Γ ⊢ A) -> Claim d2 (Γ ⊢ B) ->
     Valid l (Rule And_i (Γ ⊢ A/\B) [d1;d2])
 | V_And_e1 d Γ A B :
     Valid l d -> Claim d (Γ ⊢ A/\B) ->
     Valid l (Rule And_e1 (Γ ⊢ A) [d])
 | V_And_e2 d Γ A B :
     Valid l d -> Claim d (Γ ⊢ A/\B) ->
     Valid l (Rule And_e2 (Γ ⊢ B) [d])
 | V_Or_i1 d Γ A B :
     Valid l d -> Claim d (Γ ⊢ A) ->
     Valid l (Rule Or_i1 (Γ ⊢ A\/B) [d])
 | V_Or_i2 d Γ A B :
     Valid l d -> Claim d (Γ ⊢ B) ->
     Valid l (Rule Or_i2 (Γ ⊢ A\/B) [d])
 | V_Or_e d1 d2 d3 Γ A B C :
     Valid l d1 -> Valid l d2 -> Valid l d3 ->
     Claim d1 (Γ ⊢ A\/B) -> Claim d2 (A::Γ ⊢ C) -> Claim d3 (B::Γ ⊢ C) ->
     Valid l (Rule Or_e (Γ ⊢ C) [d1;d2;d3])
 | V_Imp_i d Γ A B :
     Valid l d -> Claim d (A::Γ ⊢ B) ->
     Valid l (Rule Imp_i (Γ ⊢ A->B) [d])
 | V_Imp_e d1 d2 Γ A B :
     Valid l d1 -> Valid l d2 ->
     Claim d1 (Γ ⊢ A->B) -> Claim d2 (Γ ⊢ A) ->
     Valid l (Rule Imp_e (Γ ⊢ B) [d1;d2])
 | V_All_i x d Γ A :
     ~Vars.In x (fvars (Γ ⊢ A)) ->
     Valid l d -> Claim d (Γ ⊢ bsubst 0 (FVar x) A) ->
     Valid l (Rule (All_i x) (Γ ⊢ ∀A) [d])
 | V_All_e t d Γ A :
     Valid l d -> Claim d (Γ ⊢ ∀A) ->
     Valid l (Rule (All_e t) (Γ ⊢ bsubst 0 t A) [d])
 | V_Ex_i t d Γ A :
     Valid l d -> Claim d (Γ ⊢ bsubst 0 t A) ->
     Valid l (Rule (Ex_i t) (Γ ⊢ ∃A) [d])
 | V_Ex_e x d1 d2 Γ A B :
     ~Vars.In x (fvars (A::Γ⊢B)) ->
     Valid l d1 -> Valid l d2 ->
     Claim d1 (Γ ⊢ ∃A) -> Claim d2 ((bsubst 0 (FVar x) A)::Γ ⊢ B) ->
     Valid l (Rule (Ex_e x) (Γ ⊢ B) [d1;d2])
 | V_Absu d Γ A :
     l=Classic ->
     Valid l d -> Claim d (Not A :: Γ ⊢ False) ->
     Valid l (Rule Absu (Γ ⊢ A) [d]).

Hint Constructors Valid.

(** Let's prove now that [valid_deriv] is equivalent to [Valid] *)

Ltac break :=
 match goal with
 | H : match _ with true => _ | false => _ end = true |- _ =>
   rewrite !lazy_andb_iff in H
 | H : match claim ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | H : match map _ ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | H : match ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | _ => idtac
 end.

Ltac mytac :=
 cbn in *;
 break;
 rewrite ?andb_true_r, ?andb_true_iff, ?lazy_andb_iff in *;
 repeat match goal with H : _ /\ _ |- _ => destruct H end;
 repeat match goal with IH : Forall _ _  |- _ => inversion_clear IH end;
 rewrite ?@eqb_eq in * by auto with typeclass_instances.

Ltac rewr :=
 unfold Claim in *;
 match goal with
 | H: _ = _ |- _ => rewrite H in *; clear H; rewr
 | _ => rewrite ?eqb_refl
 end.

Lemma Valid_equiv l d : valid_deriv l d = true <-> Valid l d.
Proof.
 split.
 - induction d as [r s ds IH] using derivation_ind'.
   cbn - [valid_deriv_step]. rewrite lazy_andb_iff. intros (H,H').
   assert (IH' : Forall (fun d => Valid l d) ds).
   { rewrite Forall_forall, forallb_forall in *. auto. }
   clear IH H'.
   mytac; subst; eauto.
   + now apply V_Ax, list_mem_in.
   + apply V_All_i; auto.
     rewrite <- Vars.mem_spec. cbn. intros EQ. now rewrite EQ in *.
   + apply V_Ex_e with f; auto.
     rewrite <- Vars.mem_spec. cbn. intros EQ. now rewrite EQ in *.
 - induction 1; simpl; rewr; auto.
   + apply list_mem_in in H. now rewrite H.
   + rewrite <- Vars.mem_spec in H. destruct Vars.mem; auto.
   + rewrite <- Vars.mem_spec in H. destruct Vars.mem; auto.
Qed.

(** A notion of provability, directly on a sequent *)

Definition Provable logic (s : sequent) :=
  exists d, Valid logic d /\ Claim d s.

Lemma thm_example :
  let A := Pred "A" [] in
  Provable Intuiti ([]⊢A->A).
Proof.
 exists deriv_example. now rewrite <- Valid_equiv.
Qed.


(** A provability notion directly on sequents, without derivations.
    Pros: lighter
    Cons: no easy way to say later that the whole proof is closed *)

Inductive Pr (l:logic) : sequent -> Prop :=
 | R_Ax Γ A : In A Γ -> Pr l (Γ ⊢ A)
 | R_Tr_i Γ : Pr l (Γ ⊢ True)
 | R_Fa_e Γ A : Pr l (Γ ⊢ False) ->
                  Pr l (Γ ⊢ A)
 | R_Not_i Γ A : Pr l (A::Γ ⊢ False) ->
                   Pr l (Γ ⊢ ~A)
 | R_Not_e Γ A : Pr l (Γ ⊢ A) -> Pr l (Γ ⊢ ~A) ->
                   Pr l (Γ ⊢ False)
 | R_And_i Γ A B : Pr l (Γ ⊢ A) -> Pr l (Γ ⊢ B) ->
                   Pr l (Γ ⊢ A/\B)
 | R_And_e1 Γ A B : Pr l (Γ ⊢ A/\B) ->
                    Pr l (Γ ⊢ A)
 | R_And_e2 Γ A B : Pr l (Γ ⊢ A/\B) ->
                    Pr l (Γ ⊢ B)
 | R_Or_i1 Γ A B : Pr l (Γ ⊢ A) ->
                   Pr l (Γ ⊢ A\/B)
 | R_Or_i2 Γ A B : Pr l (Γ ⊢ B) ->
                   Pr l (Γ ⊢ A\/B)
 | R_Or_e Γ A B C :
     Pr l (Γ ⊢ A\/B) -> Pr l (A::Γ ⊢ C) -> Pr l (B::Γ ⊢ C) ->
     Pr l (Γ ⊢ C)
 | R_Imp_i Γ A B : Pr l (A::Γ ⊢ B) ->
                     Pr l (Γ ⊢ A->B)
 | R_Imp_e Γ A B : Pr l (Γ ⊢ A->B) -> Pr l (Γ ⊢ A) ->
                   Pr l (Γ ⊢ B)
 | R_All_i x Γ A : ~Vars.In x (fvars (Γ ⊢ A)) ->
                   Pr l (Γ ⊢ bsubst 0 (FVar x) A) ->
                   Pr l (Γ ⊢ ∀A)
 | R_All_e t Γ A : Pr l (Γ ⊢ ∀A) ->
                     Pr l (Γ ⊢ bsubst 0 t A)
 | R_Ex_i t Γ A : Pr l (Γ ⊢ bsubst 0 t A) ->
                    Pr l (Γ ⊢ ∃A)
 | R_Ex_e x Γ A B : ~Vars.In x (fvars (A::Γ⊢B)) ->
      Pr l (Γ ⊢ ∃A) -> Pr l ((bsubst 0 (FVar x) A)::Γ ⊢ B) ->
      Pr l (Γ ⊢ B)
 | R_Absu Γ A : l=Classic -> Pr l (Not A :: Γ ⊢ False) ->
                  Pr l (Γ ⊢ A).
Hint Constructors Pr.

Lemma Valid_Pr lg d :
  Valid lg d -> Pr lg (claim d).
Proof.
 induction 1; cbn in *; rewr; eauto 2.
Qed.

Lemma Provable_alt lg s :
  Pr lg s <-> Provable lg s.
Proof.
 split.
 - induction 1;
   repeat match goal with H:Provable _ _ |- _ =>
          let d := fresh "d" in destruct H as (d & ? & ?) end;
   eexists (Rule _ _ _); split; try reflexivity; eauto 2.
 - intros (d & Hd & <-). now apply Valid_Pr.
Qed.

Lemma Pr_intuit_classic s : Pr Intuiti s -> Pr Classic s.
Proof.
 induction 1; eauto 2.
Qed.

Lemma Pr_intuit_any lg s : Pr Intuiti s -> Pr lg s.
Proof.
 destruct lg. apply Pr_intuit_classic. trivial.
Qed.

Lemma Pr_any_classic lg s : Pr lg s -> Pr Classic s.
Proof.
 destruct lg. trivial. apply Pr_intuit_classic.
Qed.

Lemma intuit_classic d : Valid Intuiti d -> Valid Classic d.
Proof.
 induction 1; eauto.
Qed.

Lemma any_classic d lg : Valid lg d -> Valid Classic d.
Proof.
 destruct lg. trivial. apply intuit_classic.
Qed.
