
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


(** Simultaneous substitution of many variables by terms.
    The bindings of this substitution will be handled in parallel,
    not sequentially. In particular, the variables introduced
    by a binding aren't modified by other bindings.
    If the substitution contains several bindings of the same
    variable, the leftmost binding wins (cf. [list_assoc]). *)

Definition substitution := list (variable * term).

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

Definition print_tuple {A} (pr: A -> string) (l : list A) :=
 "(" ++ String.concat "," (List.map pr l) ++ ")".

Definition is_binop s := list_mem s ["+";"*"].

Module Term.

(** Term printing

    NB: + and * are printed in infix position, S(S(...O())) is printed as
    the corresponding number.
*)

Fixpoint print t :=
  match term2nat t with
  | Some n => DecimalString.NilZero.string_of_uint (Nat.to_uint n)
  | None =>
     match t with
     | Var v => v
     | Fun f args =>
       if is_binop f then
         match args with
         | [t1;t2] =>
           "(" ++ print t1 ++ ")" ++ f ++ "(" ++ print t2 ++ ")"
         | _ => f ++ print_tuple print args
         end
       else f ++ print_tuple print args
     end
  end.

Compute Term.print peano_term_example.

(** Term parsing *)

(** Actually, parsing is not so easy and not so important.
    Let's put the details elsewhere, and take for granted that
    parsing is doable :-).
*)

(* TODO: formula parsing *)

(** With respect to a particular signature, a term is valid
    iff it only refer to known function symbols and use them
    with the correct arity. *)

Fixpoint check (sign : gen_signature) t :=
 match t with
  | Var _ => true
  | Fun f args =>
     match sign.(gen_fun_symbs) f with
     | None => false
     | Some ar =>
       (List.length args =? ar) &&& (List.forallb (check sign) args)
     end
 end.

Compute Term.check (generalize_signature peano_sign) peano_term_example.

(** The set of variables occurring in a term *)

Fixpoint vars t :=
 match t with
  | Var v => Vars.singleton v
  | Fun _ args => vars_unionmap vars args
 end.

(** Simultaneous substitution (see type [substs] above) *)

Fixpoint substs (sub:substitution) t :=
  match t with
  | Var v => list_assoc_dft v sub t
  | Fun f args => Fun f (List.map (substs sub) args)
  end.

(** Substitution of a variable in a term :
    in [t], [v] is replaced by [u] *)

Definition subst v u t := substs [(v,u)] t.

(** Boolean equality over terms *)

Instance eqb : Eqb term :=
 fix term_eqb t1 t2 :=
  match t1, t2 with
  | Var v1, Var v2 => v1 =? v2
  | Fun f1 args1, Fun f2 args2 =>
    (f1 =? f2) &&& (list_forallb2 term_eqb args1 args2)
  | _, _ => false
  end.

End Term.

Module Subst.

Definition t := substitution.

Definition invars (sub : substitution) :=
  List.fold_right (fun p vs => Vars.add (fst p) vs) Vars.empty sub.

Definition outvars (sub : substitution) :=
  vars_unionmap (fun '(_,t) => Term.vars t) sub.

Definition vars (sub : substitution) :=
  Vars.union (invars sub) (outvars sub).

End Subst.

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

(** Formula printing *)

(** Notes:
    - We use {  } for putting formulas into parenthesis, instead of ( ).
*)

Definition is_infix_pred s := list_mem s ["=";"∈"].

Module Form.

(* TODO affichage court du <-> *)

Fixpoint print f :=
  match f with
  | True => "True"
  | False => "False"
  | Pred p args =>
    if is_infix_pred p then
      match args with
      | [t1;t2] =>
        "(" ++ Term.print t1 ++ ")" ++ p ++ "(" ++ Term.print t2 ++ ")"
      |  _ => p ++ print_tuple Term.print args
      end
    else p ++ print_tuple Term.print args
  | Not f => "~{" ++ print f ++ "}"
  | Op o f f' =>
    "{" ++ print f ++ "}" ++ pr_op o ++ "{" ++ print f' ++ "}"
  | Quant q v f => pr_quant q ++ v ++ ",{" ++ print f ++ "}"
  end.

Compute Form.print (Quant Ex "x" True).

Compute Form.print (Iff True False).

(** Utilities about formula *)

Fixpoint check (sign : gen_signature) f :=
  match f with
  | True | False => true
  | Not f => check sign f
  | Op _ f f' => check sign f &&& check sign f'
  | Quant _ v f => check sign f
  | Pred p args =>
     match sign.(gen_pred_symbs) p with
     | None => false
     | Some ar =>
       (List.length args =? ar) &&& (List.forallb (Term.check sign) args)
     end
  end.

Fixpoint allvars f :=
  match f with
  | True | False => Vars.empty
  | Not f => allvars f
  | Op _ f f' => Vars.union (allvars f) (allvars f')
  | Quant _ v f => Vars.add v (allvars f)
  | Pred _ args => vars_unionmap Term.vars args
  end.

Fixpoint freevars f :=
  match f with
  | True | False => Vars.empty
  | Not f => freevars f
  | Op _ f f' => Vars.union (freevars f) (freevars f')
  | Quant _ v f => Vars.remove v (freevars f)
  | Pred _ args => vars_unionmap Term.vars args
  end.

(** Simultaneous substitution of many variables in a term.
    Capture of bounded variables is correctly handled. *)

Fixpoint substs (sub : substitution) f :=
 match f with
  | True | False => f
  | Pred p args => Pred p (List.map (Term.substs sub) args)
  | Not f => Not (substs sub f)
  | Op o f f' => Op o (substs sub f) (substs sub f')
  | Quant q v f' =>
    let sub := list_unassoc v sub in
    let out_vars := Subst.outvars sub in
    if negb (Vars.mem v out_vars) then
      Quant q v (substs sub f')
    else
      (* variable capture : we change v into a fresh variable first *)
      let z := fresh_var (vars_unions [allvars f; out_vars; Subst.invars sub])
      in
      Quant q z (substs ((v,Var z)::sub) f')
 end.

(** Substitution of a variable in a term :
    in [t], [v] is replaced by [u] *)

Definition subst v t f := substs [(v,t)] f.

(** Alpha equivalence *)

Fixpoint αeq_gen sub1 f1 sub2 f2 :=
  match f1, f2 with
  | True, True | False, False => true
  | Pred p1 args1, Pred p2 args2 =>
     (p1 =? p2) &&&
      (List.map (Term.substs sub1) args1 =?
       List.map (Term.substs sub2) args2)
  | Not f1, Not f2 => αeq_gen sub1 f1 sub2 f2
  | Op o1 f1 f1', Op o2 f2 f2' =>
    (o1 =? o2) &&&
    αeq_gen sub1 f1 sub2 f2 &&&
    αeq_gen sub1 f1' sub2 f2'
  | Quant q1 v1 f1', Quant q2 v2 f2' =>
    (q1 =? q2) &&&
    (let z := fresh_var
                (vars_unions
                   [allvars f1; Subst.vars sub1; allvars f2; Subst.vars sub2])
     in
     αeq_gen ((v1,Var z)::sub1) f1' ((v2,Var z)::sub2) f2')
  | _,_ => false
  end.

Definition αeq f1 f2 := αeq_gen [] f1 [] f2.

(** A propositional version *)

Definition AlphaEq f f' := αeq f f' = true.

(** This alpha equivalence can be see as a boolean equality,
    with syntax [=?]. But it will not be a [EqbSpec]. *)

Instance eqb_inst_form : Eqb formula := αeq.
Arguments eqb_inst_form !_ !_.

Compute αeq
        (∀ "x", Pred "A" [Var "x"] -> Pred "A" [Var "x"])
        (∀ "z", Pred "A" [Var "z"] -> Pred "A" [Var "z"]).

(** Alternative definition of substitution,
    closer to the initial document,
    but needs induction over height, due to nested recursive calls *)

Fixpoint height f :=
  match f with
  | True | False | Pred _ _ => 0
  | Not f => S (height f)
  | Op _ f1 f2 => S (Nat.max (height f1) (height f2))
  | Quant _ _ f => S (height f)
  end.

Module Alt.

Fixpoint hsubst h x t f :=
 match h with
 | 0 => True
 | S h =>
   match f with
   | True | False => f
   | Pred p args => Pred p (List.map (Term.subst x t) args)
   | Not f => Not (hsubst h x t f)
   | Op o f f' => Op o (hsubst h x t f) (hsubst h x t f')
   | Quant q v f' =>
     if x =? v then f
     else
       let out_vars := Term.vars t in
       if negb (Vars.mem v out_vars) then
         Quant q v (hsubst h x t f')
       else
         (* variable capture : we change v into a fresh variable first *)
         let z := fresh_var (vars_unions [allvars f; out_vars; Vars.singleton x])
         in
         Quant q z (hsubst h x t (hsubst h v (Var z) f'))
   end
 end.

Definition subst x t f := hsubst (S (height f)) x t f.

(** Same for alpha_equivalence *)

Fixpoint hαeq h f1 f2 :=
  match h with
  | 0 => false
  | S h =>
    match f1, f2 with
    | True, True | False, False => true
    | Pred p1 args1, Pred p2 args2 =>
      (p1 =? p2) &&& (args1 =? args2)
    | Not f1, Not f2 => hαeq h f1 f2
    | Op o1 f1 f1', Op o2 f2 f2' =>
      (o1 =? o2) &&& hαeq h f1 f2 &&& hαeq h f1' f2'
    | Quant q1 v1 f1', Quant q2 v2 f2' =>
      (q1 =? q2) &&&
      (let z := fresh_var (Vars.union (allvars f1) (allvars f2)) in
       hαeq h (subst v1 (Var z) f1') (subst v2 (Var z) f2'))
    | _,_ => false
    end
  end.

Definition αeq f1 f2 :=
 hαeq (S (Nat.max (height f1) (height f2))) f1 f2.

Definition AlphaEq f1 f2 := αeq f1 f2 = true.

End Alt.

(** Finally, a partial substitution, which does *not* handle
    correctly variable capture (and just return [f] in this case).
    This simpler definition is actually enough to define alpha
    equivalence (and reason on it). *)

Fixpoint partialsubst x t f :=
  match f with
  | True | False => f
  | Pred p args => Pred p (List.map (Term.subst x t) args)
  | Not f => Not (partialsubst x t f)
  | Op o f f' => Op o (partialsubst x t f) (partialsubst x t f')
  | Quant q v f' =>
    Quant q v
     (if (x=?v) || Vars.mem v (Term.vars t) then f'
      else partialsubst x t f')
  end.

End Form.


(** Contexts *)

Definition context := list formula.

Module Ctx.

Definition print Γ :=
  String.concat "," (List.map Form.print Γ).

Definition check sign Γ :=
  List.forallb (Form.check sign) Γ.

Definition allvars Γ := vars_unionmap Form.allvars Γ.

Definition freevars Γ := vars_unionmap Form.freevars Γ.

Definition subst v t Γ := List.map (Form.subst v t) Γ.

End Ctx.

(** Sequent *)

Inductive sequent :=
| Seq : context -> formula -> sequent.

Infix "⊢" := Seq (at level 100).

Module Seq.

Definition print '(Γ ⊢ A) :=
  Ctx.print Γ ++ " ⊢ " ++ Form.print A.

Definition check sign '(Γ ⊢ A) :=
  Ctx.check sign Γ &&& Form.check sign A.

Definition allvars '(Γ ⊢ A) :=
  Vars.union (Ctx.allvars Γ) (Form.allvars A).

Definition freevars '(Γ ⊢ A) :=
  Vars.union (Ctx.freevars Γ) (Form.freevars A).

Definition subst v t '(Γ ⊢ A) :=
  (Ctx.subst v t Γ, Form.subst v t A).

Instance eqb : Eqb sequent :=
 fun '(Γ1 ⊢ A1) '(Γ2 ⊢ A2) => (Γ1 =? Γ2) &&& (A1 =? A2).

End Seq.

(** Derivation *)

Inductive rule_kind :=
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
  | Rule : rule_kind -> sequent -> list derivation -> derivation.

Definition claim '(Rule _ s _) := s.

Definition valid_deriv_step logic '(Rule r s ld) :=
  match r, s, List.map claim ld with
  | Ax,     (Γ ⊢ A), [] => List.existsb (Form.αeq A) Γ
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
     (s =? (Γ ⊢ ∀x,A)) &&& negb (Vars.mem x (Ctx.freevars Γ))
  | All_e t, (Γ ⊢ B), [Γ'⊢ ∀x,A] =>
    (Γ =? Γ') &&& (B =? Form.subst x t A)
  | Ex_i t,  (Γ ⊢ ∃x,A), [Γ'⊢B] =>
    (Γ =? Γ') &&& (B =? Form.subst x t A)
  | Ex_e x,  s, [s1; A::Γ ⊢ B] =>
     (s =? (Γ ⊢ B)) &&& (s1 =? (Γ ⊢ ∃x, A)) &&&
     negb (Vars.mem x (Seq.freevars s))
  | Absu, s, [Not A::Γ ⊢ False] =>
    (logic =? Classic) &&& (s =? (Γ ⊢ A))
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

(** Two early proofs : correctness of boolean equality on terms ... *)

Instance : EqbSpec term.
Proof.
 red.
 fix IH 1. destruct x as [v|f l], y as [v'|f' l']; cbn; try cons.
 - case eqbspec; cons.
 - case eqbspec; [ intros <- | cons ].
   change (list_forallb2 eqb l l') with (l =? l').
   case (@eqbspec_list _ _ IH l l'); cons.
Qed.

(** ... and an alternative induction principle over terms
    (correctly handling list of sub-terms). *)

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
