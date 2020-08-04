
(** * N-ary functions *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Export List NaryFunctions.
Import ListNotations.

(** For function of arity [n], we re-use [NaryFunctions.nfun A n B]
    and its notation [A^^n-->B]. *)

Arguments ncurry {A B n}.
Arguments nuncurry {A B n}.
Arguments nprod_to_list {A n}.
Arguments nfun_to_nfun {A B C} f {n}.

Lemma nuncurry_ncurry {A B n} (f : A^n->B) (v:A^n) :
  nuncurry (ncurry f) v = f v.
Proof.
 induction n; cbn in *; auto.
 - now destruct v.
 - destruct v as (a,v). now rewrite IHn.
Qed.

Lemma nprod_to_list_length {A} n (v:A^n) :
 length (nprod_to_list v) = n.
Proof.
 induction n; cbn; auto. destruct v; cbn; auto.
Qed.

(** A variant of [nprod_of_list] with a precise size as target *)

Fixpoint optnprod {A} n (l:list A) : option (A^n) :=
 match n, l return option (A^n) with
 | 0, []  => Some tt
 | S n, x::l => option_map (pair x) (optnprod n l)
 | _, _ => None
 end.

Lemma optnprod_some {A} n (l:list A) :
  optnprod n l <> None <-> length l = n.
Proof.
 revert l. induction n; destruct l; cbn; try easy.
 specialize (IHn l).
 destruct (optnprod n l); cbn in *; intuition; try easy.
 f_equal. now apply H.
Qed.

Lemma optnprod_to_list {A} n (l:list A) (v:A^n) :
 optnprod n l = Some v <-> nprod_to_list v = l.
Proof.
 revert l. induction n; destruct l; cbn in *.
 - now destruct v.
 - now intuition.
 - now intuition.
 - destruct v as (b,v). specialize (IHn v l).
   destruct (optnprod n l); cbn.
   + split; intros [= <- <-]; f_equal. now apply IHn.
     intuition. congruence.
   + split. easy. intros [= <- <-]. now intuition.
Qed.

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

Definition optnapply {A B}(f:optnfun A B)(l:list A) :=
 match f with
 | NFun n f => option_map (nuncurry f) (optnprod n l)
 | Nop => None
 end.

Definition napply_dft {A B}(f:optnfun A B)(l:list A)(dft:B) :=
 match optnapply f l with
 | Some b => b
 | None => dft
 end.
