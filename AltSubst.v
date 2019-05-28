
(** * An simultaneous definition of substitution for named formulas *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Nam Alpha Equiv.
Import ListNotations.
Import Nam.Form.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Module Subst.

Definition t := substitution.

Definition invars (sub : substitution) :=
  List.fold_right (fun p vs => Names.add (fst p) vs) Names.empty sub.

Definition outvars (sub : substitution) :=
  Names.unionmap (fun '(_,t) => Term.vars t) sub.

Definition vars (sub : substitution) :=
  Names.union (invars sub) (outvars sub).

End Subst.

Module Alt.

(** Term substitution *)

Fixpoint term_substs (sub:substitution) t :=
  match t with
  | Var v => list_assoc_dft v sub t
  | Fun f args => Fun f (List.map (term_substs sub) args)
  end.

Definition term_subst x u t := term_substs [(x,u)] t.

(** Simultaneous substitution of many variables in a term.
    Capture of bounded variables is correctly handled. *)

Fixpoint substs (sub : substitution) f :=
 match f with
  | True | False => f
  | Pred p args => Pred p (List.map (term_substs sub) args)
  | Not f => Not (substs sub f)
  | Op o f f' => Op o (substs sub f) (substs sub f')
  | Quant q v f' =>
    let sub := list_unassoc v sub in
    let out_vars := Subst.outvars sub in
    if negb (Names.mem v out_vars) then
      Quant q v (substs sub f')
    else
      (* variable capture : we change v into a fresh variable first *)
      let z := fresh (Names.unions [allvars f; out_vars; Subst.invars sub])
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
      (List.map (term_substs sub1) args1 =?
       List.map (term_substs sub2) args2)
  | Not f1, Not f2 => αeq_gen sub1 f1 sub2 f2
  | Op o1 f1 f1', Op o2 f2 f2' =>
    (o1 =? o2) &&&
    αeq_gen sub1 f1 sub2 f2 &&&
    αeq_gen sub1 f1' sub2 f2'
  | Quant q1 v1 f1', Quant q2 v2 f2' =>
    (q1 =? q2) &&&
    (let z := fresh
                (Names.unions
                   [allvars f1; Subst.vars sub1; allvars f2; Subst.vars sub2])
     in
     αeq_gen ((v1,Var z)::sub1) f1' ((v2,Var z)::sub2) f2')
  | _,_ => false
  end.

Definition αeq f1 f2 := αeq_gen [] f1 [] f2.

Definition AlphaEq f1 f2 := αeq f1 f2 = true.

End Alt.
