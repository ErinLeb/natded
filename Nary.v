
(** * N-ary functions *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Export List NaryFunctions.
Import ListNotations.

(** For function of arity [n], we re-use [NaryFunctions.nfun A n B]
    and its notation [A^^n-->B]. *)

(** Then, a compact alternative to [option { n:nat & A^^n-->B }] *)

Inductive optnfun A B :=
| NFun n (f:A^^n-->B)
| Nop.

Arguments Nop {A B}.
Arguments NFun {A B} n f.

Definition get_arity {A B} (f : optnfun A B) :=
 match f with
 | Nop => None
 | NFun n _ => Some n
 end.

Fixpoint mk_nprod {A} n (l:list A)(dft:A) : A^n :=
 match n, l return A^n with
 | 0, _  => tt
 | S n, [] => (dft, mk_nprod n l dft)
 | S n, x::l => (x, mk_nprod n l dft)
 end.

Definition build_args {A B} :=
  fix build {n} (l : list A)(dft:B) : A^^n-->B -> B :=
    match n, l with
    | 0, [] => fun f => f
    | S n, a :: l => fun f => build l dft (f a)
    | _, _ => fun _ => dft
    end.

Definition optnapply {A B}(f:optnfun A B)(l:list A)(dft:B) :=
 match f with
 | NFun _ f => build_args l dft f
 | Nop => dft
 end.

Arguments nfun_to_nfun {A B C} f {n}.
Arguments ncurry {A B n}.
Arguments nuncurry {A B n}.
Arguments nprod_to_list {A n}.

Lemma build_args_ntn {A B B' n} (l : list A)(f:B->B')(any:B)(any':B') :
 length l = n ->
 forall (a : A^^n-->B),
 build_args l any' (nfun_to_nfun f a) = f (build_args l any a).
Proof.
 intros <-. induction l; simpl; auto.
Qed.

Lemma to_nprod {A} n (l:list A) :
  length l = n -> exists v : A^n, nprod_to_list v = l.
Proof.
 intros <-.
 exists (nprod_of_list _ l). induction l; cbn; f_equal; auto.
Qed.

Lemma nprod_to_list_length {A} n (v:A^n) :
 length (nprod_to_list v) = n.
Proof.
 induction n; cbn; auto. destruct v; cbn; auto.
Qed.

Lemma build_args_nprod {A B} n (v:A^n) (f:A^^n-->B) (dft:B) :
  build_args (nprod_to_list v) dft f = nuncurry f v.
Proof.
 induction n; cbn in *; auto.
 destruct v as (a,v). apply IHn.
Qed.

Lemma nuncurry_ncurry {A B n} (f : A^n->B) (v:A^n) :
  nuncurry (ncurry f) v = f v.
Proof.
 induction n; cbn in *; auto.
 - now destruct v.
 - destruct v as (a,v). now rewrite IHn.
Qed.
