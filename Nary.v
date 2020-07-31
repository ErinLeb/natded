
(** * N-ary functions *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Vector.
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

Lemma build_args_ntn {A B B' n} (l : list A)(f:B->B')(any:B)(any':B') :
 length l = n ->
 forall (a : A^^n-->B),
 build_args l any' (nfun_to_nfun f a) = f (build_args l any a).
Proof.
 intros <-. induction l; simpl; auto.
Qed.

(** See also nprod *)

(** N-ary curry / uncurry conversions :
    isomorphism between [arity_fun] and functions expecting a [Vector.t]
    as first argument. *)

Section Curry.
Context {A B : Type}.
Import Vector.VectorNotations.
Local Open Scope vector_scope.

Fixpoint uncurry {n} : (A^^n-->B) -> Vector.t A n -> B :=
  match n with
  | 0 => fun b _ => b
  | S n => fun f v => uncurry (f (Vector.hd v)) (Vector.tl v)
  end.

Fixpoint curry {n} : (Vector.t A n -> B) -> (A^^n-->B) :=
 match n with
 | 0 => fun f => f (Vector.nil _)
 | S n => fun f a => curry (fun v => f (a::v))
 end.

Lemma uncurry_curry n (phi : Vector.t A n -> B) v :
  uncurry (curry phi) v = phi v.
Proof.
 induction v; cbn; auto. now rewrite IHv.
Qed.

Lemma to_vect n (l:list A) :
  length l = n -> exists v : Vector.t A n, Vector.to_list v = l.
Proof.
 revert n; induction l as [|a l IH]; simpl.
 - intros n <-. now exists [].
 - destruct n as [|n]; intros [= E].
   destruct (IH n E) as (v & Hv). exists (a::v). cbn; f_equal; auto.
Qed.

End Curry.
