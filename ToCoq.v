Require Import Defs Mix.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.


Fixpoint arity_fun A n B :=
  match n with
  | O => B
  | S n => A -> (arity_fun A n B)
  end.

Definition model_funs A := string -> option { n:nat & arity_fun A n A }.
Definition model_preds A := string -> option { n:nat & arity_fun A n Prop }.

Definition optbind {A B} (o:option A)(f:A->option B) : option B :=
 match o with
 | None => None
 | Some x => f x
 end.

Infix ">>=" := optbind (at level 60).

Definition build_args {A B} :=
  fix build n (l : list (option A)) : arity_fun A n B -> option B :=
    match n, l with
    | 0, [] => fun f => Some f
    | S n, Some a :: l => fun f => build n l (f a)
    | _, _ => fun _ => None
    end.

Definition eval_term {A} (funs: model_funs A) genv lenv :=
  fix eval t :=
    match t with
    | FVar x => list_assoc x genv
    | BVar n => nth_error lenv n
    | Fun f args => funs f >>= (fun '(existT _ n f) =>
                                  build_args n (List.map eval args) f)
    end.

Definition eval_op o :=
 match o with
 | And => and
 | Or => or
 | Imp => (fun p q : Prop => p -> q)
 end.

Definition eval_form {A} (funs: model_funs A)(preds:model_preds A) genv :=
  fix eval lenv f :=
    match f with
    | True => Logic.True
    | False => Logic.False
    | Not f => ~(eval lenv f)
    | Op o f1 f2 => eval_op o (eval lenv f1) (eval lenv f2)
    | Pred p args =>
      let optp := preds p >>= fun '(existT _ n f) =>
                  build_args n (List.map (eval_term funs genv lenv) args) f
      in match optp with
         | Some p => p
         | None => Logic.False
         end
    | Quant All f => forall (a:A), eval (a::lenv) f
    | Quant Ex f => exists (a:A), eval (a::lenv) f
    end.

Definition eval_ctx {A} (funs:model_funs A) preds genv lenv l :=
  List.Forall (eval_form funs preds genv lenv) l.

Definition eval_seq {A} (funs: model_funs A) preds genv lenv '(Γ⊢C) :=
  eval_ctx funs preds genv lenv Γ /\
  eval_form funs preds genv lenv C.


Lemma correctness (sign:signature) {A} (funs:model_funs A) preds d :
 valid_deriv Intuiti d = true ->
(* check_deriv d = true ->
 closed_deriv d = true ->
 adequate funs preds signature -> *)
 forall genv,
   eval_seq funs preds genv [] (dseq d).
Admitted.

Lemma correctness2 (sign:signature) {A} (funs:model_funs A) preds d :
 valid_deriv Classic d = true ->
(* check_deriv d = true ->
 closed_deriv d = true ->
 adequate funs preds signature -> *)
 forall genv,
   (forall P:Prop, P\/~P) -> eval_seq funs preds genv [] (dseq d).
Admitted.
