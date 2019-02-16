
(** * Natded : a toy implementation of Natural Deduction *)

(** Pierre Letouzey, © 2019-today *)

(** A signature : a list of function symbols (with their arity)
    and a list of predicate symbols (with their arity).
    Functions of arity zero are also called constants.

    Note : in theory a signature could be infinite and hence not
    representable by some lists, but we'll never do this in practice.
*)

Require Import Defs.
Require DecimalString.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.


(** First possible encoding of terms and formulas :
    variables are always represented by a name (i.e. a string) *)

(** A term is given by the following recursive definition: *)

Inductive term :=
  | Var : variable -> term
  | Fun : function_symbol -> list term -> term.

Definition Cst (f:function_symbol) := Fun f [].

Definition peano_term_example :=
  Fun "+" [Fun "S" [Cst "O"]; Var "x"].

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
     | Var v => v
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

(** With respect to a particular signature, a term is valid
    iff it only refer to known function symbols and use them
    with the correct arity. *)

Fixpoint check_term (sign : gen_signature) t :=
 match t with
  | Var _ => true
  | Fun f args =>
     match sign.(gen_fun_symbs) f with
     | None => false
     | Some ar =>
       (List.length args =? ar) &&& (List.forallb (check_term sign) args)
     end
 end.

Compute check_term (generalize_signature peano_sign) peano_term_example.

(** The set of variables occurring in a term *)

Fixpoint term_vars t :=
 match t with
  | Var v => Vars.singleton v
  | Fun _ args => vars_unionmap term_vars args
 end.

(** Simultaneous substitution of many variables in a term. *)

Definition subst := list (variable * term).

Fixpoint term_substs (sub:subst) t :=
  match t with
  | Var v => list_assoc_dft v sub t
  | Fun f args => Fun f (List.map (term_substs sub) args)
  end.

(** Substitution of a variable in a term :
    in [t], [v] is replaced by [u] *)

Definition term_subst v u t := term_substs [(v,u)] t.

(** Formulas *)

Inductive formula :=
  | True
  | False
  | Pred : predicate_symbol -> list term -> formula
  | Not : formula -> formula
  | Op : op -> formula -> formula -> formula
  | Quant : quant -> variable -> formula -> formula.

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
  | Quant q v f => pr_quant q ++ v ++ ",{" ++ print_formula f ++ "}"
  end.

Compute print_formula (Quant Ex "x" True).

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

Notation "# n" := (nat2term n) (at level 20) : formula_scope.

Notation "∀ x , A" := (Quant All x A)
 (at level 200, right associativity) : formula_scope.
Notation "∃ x , A" := (Quant Ex x A)
 (at level 200, right associativity) : formula_scope.

Definition test_form := (∃ "x", True <-> Pred "p" [Var "x";#3])%form.


(** Utilities about formula *)

Fixpoint check_formula (sign : gen_signature) f :=
  match f with
  | True | False => true
  | Not f => check_formula sign f
  | Op _ f f' => check_formula sign f &&& check_formula sign f'
  | Quant _ v f => check_formula sign f
  | Pred p args =>
     match sign.(gen_pred_symbs) p with
     | None => false
     | Some ar =>
       (List.length args =? ar) &&& (List.forallb (check_term sign) args)
     end
  end.

Fixpoint allvars f :=
  match f with
  | True | False => Vars.empty
  | Not f => allvars f
  | Op _ f f' => Vars.union (allvars f) (allvars f')
  | Quant _ v f => Vars.add v (allvars f)
  | Pred _ args => vars_unionmap term_vars args
  end.

Fixpoint freevars f :=
  match f with
  | True | False => Vars.empty
  | Not f => freevars f
  | Op _ f f' => Vars.union (freevars f) (freevars f')
  | Quant _ v f => Vars.remove v (freevars f)
  | Pred _ args => vars_unionmap term_vars args
  end.

Definition subinvars (sub : subst) :=
  List.fold_right (fun p vs => Vars.add (fst p) vs) Vars.empty sub.

Definition suboutvars (sub : subst) :=
  vars_unionmap (fun '(_,t) => term_vars t) sub.

Definition subvars (sub : subst) :=
  Vars.union (subinvars sub) (suboutvars sub).

Fixpoint formula_substs sub f :=
 match f with
  | True | False => f
  | Pred p args => Pred p (List.map (term_substs sub) args)
  | Not f => Not (formula_substs sub f)
  | Op o f f' => Op o (formula_substs sub f) (formula_substs sub f')
  | Quant q v f' =>
    let sub := List.filter (fun '(x,_) => x =? v) sub in
    let out_vars := suboutvars sub in
    if negb (Vars.mem v out_vars) then
      Quant q v (formula_substs sub f')
    else
      (* variable capture : we change v into a fresh variable first *)
      let z := fresh_var (vars_unions [allvars f; out_vars; subinvars sub])
      in
      Quant q z (formula_substs ((v,Var z)::sub) f')
 end.

Definition formula_subst v t f := formula_substs [(v,t)] f.

Instance term_eqb : Eqb term :=
 fix term_eqb t1 t2 :=
  match t1, t2 with
  | Var v1, Var v2 => v1 =? v2
  | Fun f1 args1, Fun f2 args2 =>
    (f1 =? f2) &&& (list_forallb2 term_eqb args1 args2)
  | _, _ => false
  end.

Fixpoint alpha_equiv_gen sub1 f1 sub2 f2 :=
  match f1, f2 with
  | True, True | False, False => true
  | Pred p1 args1, Pred p2 args2 =>
     (p1 =? p2) &&&
      (List.map (term_substs sub1) args1 =?
       List.map (term_substs sub2) args2)
  | Not f1, Not f2 => alpha_equiv_gen sub1 f1 sub2 f2
  | Op o1 f1 f1', Op o2 f2 f2' =>
    (o1 =? o2) &&&
    alpha_equiv_gen sub1 f1 sub2 f2 &&&
    alpha_equiv_gen sub1 f1' sub2 f2'
  | Quant q1 v1 f1', Quant q2 v2 f2' =>
    (q1 =? q2) &&&
    (let z := fresh_var
                (vars_unions
                   [allvars f1; subvars sub1; allvars f2; subvars sub2]) in
     alpha_equiv_gen ((v1,Var z)::sub1) f1' ((v2,Var z)::sub2) f2')
  | _,_ => false
  end.

Definition alpha_equiv f1 f2 := alpha_equiv_gen [] f1 [] f2.

Definition AlphaEq f f' := alpha_equiv f f' = true.

Instance eqb_inst_form : Eqb formula := alpha_equiv.
Arguments eqb_inst_form !_ !_.

Compute alpha_equiv
        (∀ "x", Pred "A" [Var "x"] -> Pred "A" [Var "x"])
        (∀ "z", Pred "A" [Var "z"] -> Pred "A" [Var "z"]).


(** Contexts *)

Definition context := list formula.

Definition print_ctx Γ :=
  String.concat "," (List.map print_formula Γ).

Definition check_ctx sign Γ :=
  List.forallb (check_formula sign) Γ.

Definition allvars_ctx Γ := vars_unionmap allvars Γ.

Definition freevars_ctx Γ := vars_unionmap freevars Γ.

Definition ctx_subst v t Γ := List.map (formula_subst v t) Γ.

(** Sequent *)

Inductive sequent :=
| Seq : context -> formula -> sequent.

Infix "⊢" := Seq (at level 100).

Definition print_seq '(Γ ⊢ A) :=
  print_ctx Γ ++ " ⊢ " ++ print_formula A.

Definition check_seq sign '(Γ ⊢ A) :=
  check_ctx sign Γ &&& check_formula sign A.

Definition allvars_seq '(Γ ⊢ A) :=
  Vars.union (allvars_ctx Γ) (allvars A).

Definition freevars_seq '(Γ ⊢ A) :=
  Vars.union (freevars_ctx Γ) (freevars A).

Definition seq_subst v t '(Γ ⊢ A) :=
  (ctx_subst v t Γ, formula_subst v t A).

Instance seq_eqb : Eqb sequent :=
 fun '(Γ1 ⊢ A1) '(Γ2 ⊢ A2) => (Γ1 =? Γ2) &&& (A1 =? A2).

(** Derivation *)

Inductive rule_name :=
  | Ax
  | Tr_i
  | Fa_e
  | Not_i | Not_e
  | And_i | And_e1 | And_e2
  | Or_i1 | Or_i2 | Or_e
  | Imp_i | Imp_e
  | All_i (x:variable) | All_e (wit:term)
  | Ex_i (wit:term) | Ex_e (x:variable)
  | Absu.

Inductive derivation :=
  | Rule : rule_name -> sequent -> list derivation -> derivation.

Definition dseq '(Rule _ s _) := s.

Inductive logic := Classic | Intuiti.

Definition valid_deriv_step logic '(Rule r s ld) :=
  match r, s, List.map dseq ld with
  | Ax,     (Γ ⊢ A), [] => List.existsb (alpha_equiv A) Γ
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
  | All_i x,  s, [Γ ⊢ A] =>
     (s =? (Γ ⊢ ∀x,A)) &&& negb (Vars.mem x (freevars_ctx Γ))
  | All_e t, (Γ ⊢ B), [Γ'⊢ ∀x,A] =>
    (Γ =? Γ') &&& (B =? formula_subst x t A)
  | Ex_i t,  (Γ ⊢ ∃x,A), [Γ'⊢B] =>
    (Γ =? Γ') &&& (B =? formula_subst x t A)
  | Ex_e x,  s, [s1; A::Γ ⊢ B] =>
     (s =? (Γ ⊢ B)) &&& (s1 =? (Γ ⊢ ∃x, A)) &&&
     negb (Vars.mem x (freevars_seq s))
  | Absu, s, [Not A::Γ ⊢ False] =>
    match logic with
    | Classic => (s =? (Γ ⊢ A))
    | Intuiti => false
    end
  | _,_,_ => false
  end.

Fixpoint valid_deriv logic d :=
  valid_deriv_step logic d &&&
   (let '(Rule _ _ ld) := d in
    List.forallb (valid_deriv logic) ld).

Definition example :=
  let A := Pred "A" [] in
  Rule Imp_i ([]⊢A->A) [Rule Ax ([A]⊢A) []].

Compute valid_deriv Intuiti example.

Definition example2 :=
  let A := fun x => Pred "A" [Var x] in
  let B := fun x => Pred "B" [Var x] in
  Rule Imp_i ([]⊢(∀"x",A("x")/\B("x"))->(∀"x",A("x"))/\(∀"x",B("x")))
    (let C := (∀"x",A("x")/\B("x"))%form in
     [Rule And_i ([C] ⊢ (∀"x",A("x"))/\(∀"x",B("x")))
       [Rule (All_i "x") ([C]⊢∀"x",A("x"))
         [Rule And_e1 ([C]⊢A("x"))
           [Rule (All_e (Var "x")) ([C]⊢ A("x")/\B("x"))
             [Rule Ax ([C]⊢C) []]]]
        ;
        Rule (All_i "x") ([C]⊢∀"x",B("x"))
         [Rule And_e2 ([C]⊢B("x"))
           [Rule (All_e (Var "x")) ([C]⊢A("x")/\B("x"))
             [Rule Ax ([C]⊢C) []]]]]]).

Compute valid_deriv Intuiti example2.

Definition em :=
  let A := Pred "A" [] in
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

Compute valid_deriv Classic em.
Compute valid_deriv Intuiti em.

(** Example of free alpha-renaming during a proof,
    (not provable without alpha-renaming) *)

Definition captcha :=
  let A := fun x => Pred "A" [Var x] in
  Rule (All_i "z") ([A("x")]⊢∀"x",A("x")->A("x"))
   [Rule Imp_i ([A("x")]⊢A("z")->A("z"))
     [Rule Ax ([A("z");A("x")]⊢A("z")) []]].

Compute valid_deriv Intuiti captcha.

Definition captcha_bug :=
  let A := fun x => Pred "A" [Var x] in
  Rule (All_i "x") ([A("x")]⊢∀"x",A("x")->A("x"))
   [Rule Imp_i ([A("x")]⊢A("x")->A("x"))
    [Rule Ax ([A("x");A("x")]⊢A("x")) []]].

Compute valid_deriv Intuiti captcha_bug.

Instance : EqbSpec term.
Proof.
 red.
 fix IH 1. destruct x as [v|f l], y as [v'|f' l']; cbn; try cons.
 - case eqbspec; cons.
 - case eqbspec; [ intros <- | cons ].
   change (list_forallb2 eqb l l') with (l =? l').
   case (@eqbspec_list _ _ IH l l'); cons.
Qed.

Lemma term_ind' (P: term -> Prop) :
  (forall v, P (Var v)) ->
  (forall f args, (forall a, In a args -> P a) -> P (Fun f args)) ->
  forall t, P t.
Proof.
 intros Hv Hl.
 fix IH 1. destruct t.
 - apply Hv.
 - apply Hl.
   revert l.
   fix IH' 1. destruct l; simpl.
   + intros a [ ].
   + intros a [<-|H]. apply IH. apply (IH' l a H).
Qed.
