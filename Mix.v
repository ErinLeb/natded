
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

(** With respect to a particular signature, a term is valid
    iff it only refer to known function symbols and use them
    with the correct arity. *)

Fixpoint check_term (sign : gen_signature) t :=
 match t with
  | FVar _ | BVar _ => true
  | Fun f args =>
     match sign.(gen_fun_symbs) f with
     | None => false
     | Some ar =>
       (List.length args =? ar) &&& (List.forallb (check_term sign) args)
     end
 end.

Compute check_term (generalize_signature peano_sign) peano_term_example.

(** Generic overloaded function for computing free variables *)

Class FVars (A : Type) := fvars : A -> Vars.t.
Arguments fvars {_} {_} !_.

(** The set of free variables occurring in a term *)

Instance term_fvars : FVars term :=
 fix term_fvars t :=
 match t with
 | BVar _ => Vars.empty
 | FVar v => Vars.singleton v
 | Fun _ args => vars_unionmap term_fvars args
 end.

Fixpoint term_level t :=
 match t with
 | BVar n => S n
 | FVar v => 0
 | Fun _ args => list_max (map term_level args)
 end.

Definition term_closed t := term_level t =? 0.

(** Substitution of a bounded variable in a term :
    in [t], bounded var [n] is replaced by [u].
    NB: [u] is meant to be closed, and [v] of level [S n] *)

Fixpoint term_bsubst n u t :=
  match t with
  | FVar v => t
  | BVar k => if k =? n then u else t
  | Fun f args => Fun f (List.map (term_bsubst n u) args)
  end.

(** General action on the free variables of a term *)

Definition term_vmap (h:variable->term) :=
  fix vmap t :=
    match t with
    | BVar _ => t
    | FVar x => h x
    | Fun f args => Fun f (List.map vmap args)
    end.

(** Substitution of a free variable in a term :
    in [t], free var [v] is replaced by [u]. *)

Definition fsubst v u x := if v =? x then u else FVar x.

Definition term_fsubst v u := term_vmap (fsubst v u).

(** Boolean equalities *)

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

Fixpoint check_formula (sign : gen_signature) f :=
  match f with
  | True | False => true
  | Not f => check_formula sign f
  | Op _ f f' => check_formula sign f &&& check_formula sign f'
  | Quant _ f => check_formula sign f
  | Pred p args =>
     match sign.(gen_pred_symbs) p with
     | None => false
     | Some ar =>
       (List.length args =? ar) &&& (List.forallb (check_term sign) args)
     end
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

Fixpoint level f :=
  match f with
  | True | False => 0
  | Not f => level f
  | Op _ f f' => max (level f) (level f')
  | Quant _ f => pred (level f)
  | Pred _ args => list_max (map term_level args)
  end.

Definition closed f := level f =? 0.

(** Substitution of bounded var [n] by closed term [t] in [f] *)

Fixpoint form_bsubst n t f :=
 match f with
  | True | False => f
  | Pred p args => Pred p (List.map (term_bsubst n t) args)
  | Not f => Not (form_bsubst n t f)
  | Op o f f' => Op o (form_bsubst n t f) (form_bsubst n t f')
  | Quant q f' =>
    Quant q (form_bsubst (S n) t f')
 end.

(** General action on free variables *)

Definition form_vmap (h:variable->term) :=
  fix vmap f :=
    match f with
    | True | False => f
    | Pred p args => Pred p (List.map (term_vmap h) args)
    | Not f => Not (vmap f)
    | Op o f f' => Op o (vmap f) (vmap f')
    | Quant q f' => Quant q (vmap f')
    end.

(** Substitution of a free variable [v] by term [u] *)

Definition form_fsubst v u : formula -> formula :=
  form_vmap (fsubst v u).

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

Compute form_eqb
        (∀ (Pred "A" [ #0 ] -> Pred "A" [ #0 ]))%form
        (∀ (Pred "A" [FVar "z"] -> Pred "A" [FVar "z"]))%form.


(** Contexts *)

Definition context := list formula.

Definition print_ctx Γ :=
  String.concat "," (List.map print_formula Γ).

Definition check_ctx sign Γ :=
  List.forallb (check_formula sign) Γ.

Instance ctx_fvars : FVars context := vars_unionmap fvars.
Arguments ctx_fvars !_.

Definition ctx_vmap h := List.map (form_vmap h).
Definition ctx_fsubst v u := List.map (form_fsubst v u).

(** NB: eqb given by generic eqb_inst_list *)

(** Sequent *)

Inductive sequent :=
| Seq : context -> formula -> sequent.

Infix "⊢" := Seq (at level 100).

Definition print_seq '(Γ ⊢ A) :=
  print_ctx Γ ++ " ⊢ " ++ print_formula A.

Definition check_seq sign '(Γ ⊢ A) :=
  check_ctx sign Γ &&& check_formula sign A.

Instance : FVars sequent :=
 fun '(Γ ⊢ A) => Vars.union (fvars Γ) (fvars A).

Definition seq_vmap h '(Γ ⊢ A) :=
  (ctx_vmap h Γ ⊢ form_vmap h A).

Definition seq_fsubst v u '(Γ ⊢ A) :=
  (ctx_fsubst v u Γ ⊢ form_fsubst v u A).

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
  | All_i (v:variable)| All_e (wit:term)
  | Ex_i (wit:term) | Ex_e (v:variable)
  | Absu.

Inductive derivation :=
  | Rule : rule_name -> sequent -> list derivation -> derivation.

Definition dseq '(Rule _ s _) := s.

Inductive logic := Classic | Intuiti.

Definition valid_deriv_step logic '(Rule r s ld) :=
  match r, s, List.map dseq ld with
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
     (Γ =? Γ') &&& (A' =? form_bsubst 0 (FVar x) A)
     &&& negb (Vars.mem x (fvars (Γ⊢A)))
  | All_e t, (Γ ⊢ B), [Γ'⊢ ∀A] =>
    (Γ =? Γ') &&& (B =? form_bsubst 0 t A)
  | Ex_i t,  (Γ ⊢ ∃A), [Γ'⊢B] =>
    (Γ =? Γ') &&& (B =? form_bsubst 0 t A)
  | Ex_e x,  s, [Γ⊢∃A; A'::Γ'⊢B] =>
     (s =? (Γ ⊢ B)) &&& (Γ' =? Γ)
     &&& (A' =? form_bsubst 0 (FVar x) A)
     &&& negb (Vars.mem x (fvars (A::Γ⊢B)))
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

Definition Provable logic (s : sequent) :=
  exists d, valid_deriv logic d = true /\ dseq d = s.

Definition deriv_example :=
  let A := Pred "A" [] in
  Rule Imp_i ([]⊢A->A) [Rule Ax ([A]⊢A) []].

Compute valid_deriv Intuiti deriv_example.

Lemma thm_example :
  let A := Pred "A" [] in
  Provable Intuiti ([]⊢A->A).
Proof.
 now exists deriv_example.
Qed.

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


Inductive Pr : logic -> sequent -> Prop :=
 | R_Ax Γ l A : In A Γ -> Pr l (Γ ⊢ A)
 | R_Tr_i l Γ : Pr l (Γ ⊢ True)
 | R_Fa_e l Γ A : Pr l (Γ ⊢ False) ->
                  Pr l (Γ ⊢ A)
 | R_Not_i l Γ A : Pr l (A::Γ ⊢ False) ->
                   Pr l (Γ ⊢ ~A)
 | R_Not_e l Γ A : Pr l (Γ ⊢ A) -> Pr l (Γ ⊢ ~A) ->
                   Pr l (Γ ⊢ False)
 | R_And_i l Γ A B : Pr l (Γ ⊢ A) -> Pr l (Γ ⊢ B) ->
                   Pr l (Γ ⊢ A/\B)
 | R_And_e1 l Γ A B : Pr l (Γ ⊢ A/\B) ->
                    Pr l (Γ ⊢ A)
 | R_And_e2 l Γ A B : Pr l (Γ ⊢ A/\B) ->
                    Pr l (Γ ⊢ B)
 | R_Or_i1 l Γ A B : Pr l (Γ ⊢ A) ->
                   Pr l (Γ ⊢ A\/B)
 | R_Or_i2 l Γ A B : Pr l (Γ ⊢ B) ->
                   Pr l (Γ ⊢ A\/B)
 | R_Or_e l Γ A B C :
     Pr l (Γ ⊢ A\/B) -> Pr l (A::Γ ⊢ C) -> Pr l (B::Γ ⊢ C) ->
     Pr l (Γ ⊢ C)
 | R_Imp_i l Γ A B : Pr l (A::Γ ⊢ B) ->
                     Pr l (Γ ⊢ A->B)
 | R_Imp_e l Γ A B : Pr l (Γ ⊢ A->B) -> Pr l (Γ ⊢ A) ->
                   Pr l (Γ ⊢ B)
 | R_All_i x l Γ A : ~Vars.In x (fvars (Γ ⊢ A)) ->
                   Pr l (Γ ⊢ form_bsubst 0 (FVar x) A) ->
                   Pr l (Γ ⊢ ∀A)
 | R_All_e t l Γ A : Pr l (Γ ⊢ ∀A) ->
                     Pr l (Γ ⊢ form_bsubst 0 t A)
 | R_Ex_i t l Γ A : Pr l (Γ ⊢ form_bsubst 0 t A) ->
                    Pr l (Γ ⊢ ∃A)
 | R_Ex_e x l Γ A B : ~Vars.In x (fvars (A::Γ⊢B)) ->
      Pr l (Γ ⊢ ∃A) -> Pr l ((form_bsubst 0 (FVar x) A)::Γ ⊢ B) ->
      Pr l (Γ ⊢ B)
 | R_Absu l Γ A : Pr l (Not A :: Γ ⊢ False) ->
                  Pr Classic (Γ ⊢ A).
Hint Constructors Pr.

Ltac mysubst :=
 match goal with
 | EQ: (_ =? _) = true |- _ =>
   apply eqb_eq in EQ; rewrite EQ in *; clear EQ; mysubst
 | _ => idtac
 end.

Ltac break :=
 match goal with
 | H : match _ with true => _ | false => _ end = true |- _ =>
   rewrite !lazy_andb_iff in H
 | H : match dseq ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | H : match map _ ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | H : match ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | _ => idtac
 end.

Ltac mytac :=
 cbn -[valid_deriv] in *;
 rewrite ?andb_true_r in *;
 rewrite ?andb_true_iff in *;
 rewrite ?lazy_andb_iff in *;
 repeat match goal with
        | H : _ /\ _ |- _ => destruct H
        end;
 repeat match goal with
        | IH : Forall _ _  |- _ => inversion_clear IH end;
 mysubst; simpl in *.

Lemma valid_deriv_Pr lg d :
  valid_deriv lg d = true -> Pr lg (dseq d).
Proof.
 revert d lg.
 fix IH 1.
 destruct d. cbn - [valid_deriv_step]. intros lg.
 rewrite lazy_andb_iff. intros (H,H').
 assert (IH' : Forall (fun d => Pr lg (dseq d)) l).
 { clear r s H.
   revert l H'.
   fix IH' 1.
   destruct l.
   - simpl. constructor.
   - simpl. rewrite andb_true_iff. intros (H,H').
     constructor.
     + now apply IH.
     + now apply IH'. }
 clear IH H'. simpl in *. Opaque Vars.union. break; mytac.
 - apply list_mem_in in H. now apply R_Ax.
 - now apply R_Fa_e.
 - now apply R_Not_i.
 - now apply R_Not_e with f0.
 - now apply R_And_i.
 - now apply R_And_e1 with f2.
 - now apply R_And_e2 with f1.
 - now apply R_Or_i1.
 - now apply R_Or_i2.
 - now apply R_Or_e with f0_1 f0_2.
 - now apply R_Imp_i.
 - now apply R_Imp_e with f1.
 - apply R_All_i with v; trivial.
   rewrite <- Vars.mem_spec. cbn. intros EQ. now rewrite EQ in *.
 - now apply R_All_e.
 - now apply (R_Ex_i wit).
 - apply R_Ex_e with v f; trivial.
   rewrite <- Vars.mem_spec. cbn. intros EQ. now rewrite EQ in *.
 - now apply R_Absu with Classic.
 Transparent Vars.union.
Qed.

Lemma Provable_Pr logic s :
  Provable logic s -> Pr logic s.
Proof.
 intros (d & Hd & <-). now apply valid_deriv_Pr.
Qed.

Lemma Pr_intuit_classic s : Pr Intuiti s -> Pr Classic s.
Proof.
 induction 1; auto.
 - now apply R_Not_e with A.
 - now apply R_And_e1 with B.
 - now apply R_And_e2 with A.
 - now apply R_Or_e with A B.
 - now apply R_Imp_e with A.
 - now apply R_All_i with x.
 - now apply R_Ex_i with t.
 - now apply R_Ex_e with x A.
 - now apply R_Absu with Classic.
Qed.

Lemma Pr_intuit_any lg s : Pr Intuiti s -> Pr lg s.
Proof.
 destruct lg. apply Pr_intuit_classic. trivial.
Qed.

Lemma Pr_any_classic lg s : Pr lg s -> Pr Classic s.
Proof.
 destruct lg. trivial. apply Pr_intuit_classic.
Qed.

Lemma intuit_classic_step d :
  valid_deriv_step Intuiti d = true ->
  valid_deriv_step Classic d = true.
Proof.
 intros.
 destruct d; simpl in *.
 break.
Qed.

Lemma intuit_classic d :
  valid_deriv Intuiti d = true ->
  valid_deriv Classic d = true.
Proof.
 revert d.
 fix IH 1.
 destruct d. cbn - [valid_deriv_step].
 rewrite !lazy_andb_iff. intros (H,H').
 split. now apply intuit_classic_step.
 clear r s H.
 revert l H'.
 fix IH' 1.
 destruct l.
 - trivial.
 - simpl. rewrite !andb_true_iff. intros (H,H').
   split. now apply IH. now apply IH'.
Qed.

Lemma any_classic d lg :
  valid_deriv lg d = true ->
  valid_deriv Classic d = true.
Proof.
 destruct lg. trivial. apply intuit_classic.
Qed.

Lemma Pr_Provable lg s :
  Pr lg s -> Provable lg s.
Proof.
 induction 1.
 - exists (Rule Ax (Γ ⊢ A) []). simpl. split; auto.
   apply list_mem_in in H. now rewrite H.
 - now exists (Rule Tr_i (Γ ⊢ True) []).
 - destruct IHPr as (d & Hd & Eq).
   exists (Rule Fa_e (Γ ⊢ A) [d]). simpl.
   apply eqb_eq in Eq. now rewrite Eq, Hd.
 - destruct IHPr as (d & Hd & Eq).
   exists (Rule Not_i (Γ ⊢ ~ A) [d]). simpl.
   apply eqb_eq in Eq. now rewrite Eq, Hd.
 - destruct IHPr1 as (d1 & Hd1 & Eq1).
   destruct IHPr2 as (d2 & Hd2 & Eq2).
   exists (Rule Not_e (Γ ⊢ False) [d1;d2]). simpl.
   now rewrite Eq1, Eq2, Hd1, Hd2, !eqb_refl.
 - destruct IHPr1 as (d1 & Hd1 & Eq1).
   destruct IHPr2 as (d2 & Hd2 & Eq2).
   exists (Rule And_i (Γ ⊢ A /\ B) [d1;d2]). simpl.
   now rewrite Eq1, Eq2, Hd1, Hd2, !eqb_refl.
 - destruct IHPr as (d & Hd & Eq).
   exists (Rule And_e1 (Γ ⊢ A) [d]). simpl.
   now rewrite Eq, Hd, !eqb_refl.
 - destruct IHPr as (d & Hd & Eq).
   exists (Rule And_e2 (Γ ⊢ B) [d]). simpl.
   now rewrite Eq, Hd, !eqb_refl.
 - destruct IHPr as (d & Hd & Eq).
   exists (Rule Or_i1 (Γ ⊢ A \/ B) [d]). simpl.
   now rewrite Eq, Hd, !eqb_refl.
 - destruct IHPr as (d & Hd & Eq).
   exists (Rule Or_i2 (Γ ⊢ A \/ B) [d]). simpl.
   now rewrite Eq, Hd, !eqb_refl.
 - destruct IHPr1 as (d1 & Hd1 & Eq1).
   destruct IHPr2 as (d2 & Hd2 & Eq2).
   destruct IHPr3 as (d3 & Hd3 & Eq3).
   exists (Rule Or_e (Γ ⊢ C) [d1;d2;d3]). simpl.
   now rewrite Eq1, Eq2, Eq3, Hd1, Hd2, Hd3, !eqb_refl.
 - destruct IHPr as (d & Hd & Eq).
   exists (Rule Imp_i (Γ ⊢ A -> B) [d]). simpl.
   now rewrite Eq, Hd, !eqb_refl.
 - destruct IHPr1 as (d1 & Hd1 & Eq1).
   destruct IHPr2 as (d2 & Hd2 & Eq2).
   exists (Rule Imp_e (Γ ⊢ B) [d1;d2]). simpl.
   now rewrite Eq1, Eq2, Hd1, Hd2, ?eqb_refl.
 - destruct IHPr as (d & Hd & Eq).
   exists (Rule (All_i x) (Γ ⊢ ∀A) [d]). simpl.
   rewrite Eq, Hd, ?eqb_refl.
   rewrite <- Vars.mem_spec in H.
   destruct Vars.mem; auto.
 - destruct IHPr as (d & Hd & Eq).
   exists (Rule (All_e t) (Γ ⊢ form_bsubst 0 t A) [d]). simpl.
   now rewrite Eq, Hd, ?eqb_refl.
 - destruct IHPr as (d & Hd & Eq).
   exists (Rule (Ex_i t) (Γ ⊢ ∃A) [d]). simpl.
   now rewrite Eq, Hd, ?eqb_refl.
 - destruct IHPr1 as (d1 & Hd1 & Eq1).
   destruct IHPr2 as (d2 & Hd2 & Eq2).
   exists (Rule (Ex_e x) (Γ ⊢ B) [d1;d2]). simpl.
   rewrite Eq1, Eq2, Hd1, Hd2, ?eqb_refl.
   rewrite <- Vars.mem_spec in H.
   destruct Vars.mem; auto.
 - destruct IHPr as (d & Hd & Eq).
   exists (Rule Absu (Γ ⊢ A) [d]). simpl.
   apply any_classic in Hd.
   now rewrite Eq, Hd, ?eqb_refl.
Qed.

Lemma Provable_alt lg s : Provable lg s <-> Pr lg s.
Proof.
 split. apply Provable_Pr. apply Pr_Provable.
Qed.

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
   fix IH' 1. destruct l; simpl.
   + intros a [ ].
   + intros a [<-|H]. apply IH. apply (IH' l a H).
Qed.
