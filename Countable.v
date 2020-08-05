
(** * Explicit enumeration of countable types *)

(** The NatDed development, Pierre Letouzey, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Ascii NArith Defs Mix NameProofs Meta.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Set Implicit Arguments.

Definition Onto {A B} (f:A->B) :=
 forall b, exists a, f a = b.

Definition Countable A := exists f:nat->A, Onto f.

Lemma countable_by_inverse A (f:nat->A)(g:A->nat) :
 (forall a, f (g a) = a) -> Countable A.
Proof.
 intros E.
 exists f.
 intros a. now exists (g a).
Qed.

Lemma countable_nat : Countable nat.
Proof.
 exists (fun x => x). intros x; now exists x.
Qed.

Lemma countable_unit : Countable unit.
Proof.
 exists (fun _ => tt). intros [ ]. now exists 0.
Qed.


(** Our set of variables is countable *)

Definition base := 256.

Fixpoint string_enum_loop n m :=
 match m, n with
 | 0, _ | _, 0 => EmptyString
 | S m, _ =>
   String (Ascii.ascii_of_nat ((n-1) mod base))
          (string_enum_loop ((n-1)/base) m)
 end.

Definition string_enum n := string_enum_loop n n.

Fixpoint string_index s :=
 match s with
 | EmptyString => 0
 | String c s =>
   S (Ascii.nat_of_ascii c) + base * (string_index s)
 end.

Lemma string_enum_indep m m' n :
  n<=m -> n<=m' -> string_enum_loop n m = string_enum_loop n m'.
Proof.
 revert n m'.
 induction m as [|m IH]; destruct m' as [|m']; auto.
 - now inversion 1.
 - now inversion 2.
 - destruct n as [|n]; intros Hn Hn'; trivial.
   cbn - [base]. rewrite Nat.sub_0_r. f_equal. apply IH.
   transitivity n; [|omega].
   apply Nat.div_le_upper_bound; unfold base; auto with *.
   transitivity n; [|omega].
   apply Nat.div_le_upper_bound; unfold base; auto with *.
Qed.

Lemma N_of_digits_bound l :
 (Ascii.N_of_digits l < 2^(N.of_nat (length l)))%N.
Proof.
 induction l.
 - now compute.
 - cbn - [N.mul N.pow N.of_nat].
   rewrite Nat2N.inj_succ, N.pow_succ_r'.
   destruct a; omega with *.
Qed.

Lemma N_of_ascii_bound c : (N_of_ascii c < 2^8)%N.
Proof.
 unfold N_of_ascii. destruct c. apply N_of_digits_bound.
Qed.

Lemma nat_of_ascii_bound c : nat_of_ascii c < base.
Proof.
 unfold base.
 unfold nat_of_ascii.
 change 256 with (N.to_nat (2^8)).
 generalize (N_of_ascii_bound c).
 unfold N.lt. rewrite N2Nat.inj_compare.
 case Nat.compare_spec; easy.
Qed.

Lemma string_enum_index s : string_enum (string_index s) = s.
Proof.
 induction s as [|c s IH].
 - trivial.
 - cbn - [base]. rewrite !Nat.sub_0_r. f_equal.
   + rewrite Nat.mul_comm, Nat.mod_add by (unfold base; auto with *).
     rewrite Nat.mod_small by apply nat_of_ascii_bound.
     apply ascii_nat_embedding.
   + rewrite Nat.mul_comm, Nat.div_add by (unfold base; auto with *).
     rewrite Nat.div_small by apply nat_of_ascii_bound; simpl.
     rewrite <- IH at 3.
     apply string_enum_indep; auto.
     unfold base. omega with *.
Qed.

Lemma countable_variables : Countable variable.
Proof.
 apply (countable_by_inverse _ _ string_enum_index).
Qed.

(** nat * nat is countable *)

Definition code_pair '(x,y) := y + ((x+y)*(S (x+y)))/2.

Fixpoint inv_tri n :=
 match n with
 | 0 => 0
 | S n =>
   let k := inv_tri n in
   if (k+1)*(k+2) <=? 2*S n then S k else k
 end.

Definition decode_pair n :=
  let k := inv_tri n in
  let y := n - (k*(k+1))/2 in
  (k-y, y).

Lemma inv_tri_ok n :
  let k := inv_tri n in
  k*(k+1) <= 2*n < (k+1)*(k+2).
Proof.
 induction n as [|n IH].
 - simpl; auto with *.
 - simpl in *.
   case Nat.leb_spec; revert IH; set (k := inv_tri n);
   rewrite (Nat.add_succ_r n), !Nat.add_0_r;
   rewrite <- ?(Nat.add_1_r k), <- ?Nat.add_assoc; simpl;
   rewrite !Nat.mul_add_distr_r, !Nat.mul_add_distr_l; simpl;
   omega with *.
Qed.

Lemma tri_incr_iff k l : k<l <-> k * S k < l * S l.
Proof.
 assert (forall k l, k<l -> k * S k < l * S l).
 { intros. apply Nat.mul_lt_mono; auto with *. }
 split; auto.
 destruct (Nat.compare_spec k l); auto.
 - subst. omega with *.
 - apply H in H0. omega with *.
Qed.

Lemma tri_inj k l : k = l <-> k * S k = l * S l.
Proof.
 split; [now intros ->|].
 destruct (Nat.compare_spec k l); auto.
 apply tri_incr_iff in H; omega.
 apply tri_incr_iff in H; omega.
Qed.

Lemma inv_tri_carac_aux n k l:
  k*(k+1) <= 2*n < (k+1)*(k+2) ->
  l*(l+1) <= 2*n < (l+1)*(l+2) -> k = l.
Proof.
 rewrite !Nat.add_succ_r, !Nat.add_0_r.
 intros Hk Hl.
 assert (k < S l).
 { apply tri_incr_iff. omega. }
 assert (l < S k).
 { apply tri_incr_iff. omega. }
 omega.
Qed.

Lemma inv_tri_carac n k :
  k*(k+1) <= 2*n < (k+1)*(k+2) -> k = inv_tri n.
Proof.
 intros Hk.
 eapply inv_tri_carac_aux; eauto.
 apply inv_tri_ok.
Qed.

Lemma tri_pair x : (x * S x) mod 2 = 0.
Proof.
 induction x.
 - reflexivity.
 - change (S (S x)) with (2+x).
   rewrite Nat.mul_add_distr_l.
   rewrite Nat.add_comm.
   rewrite Nat.mod_add; auto with *.
   now rewrite Nat.mul_comm.
Qed.
Hint Resolve tri_pair.

Lemma decode_code_pair x y :
  decode_pair (code_pair (x,y)) = (x,y).
Proof.
 unfold code_pair, decode_pair.
 set (z := x + y).
 set (n := y + z * (S z) / 2).
 set (k := inv_tri n).
 assert (k = z).
 { unfold k. symmetry. apply inv_tri_carac.
   unfold n. rewrite (Nat.mul_add_distr_l 2).
   assert (2*(z*S z/2) = z * S z).
   { symmetry. apply Nat.div_exact; auto with *. }
   rewrite H.
   rewrite Nat.add_1_r.
   split; try omega.
   rewrite Nat.mul_add_distr_l.
   rewrite (Nat.mul_comm z (S z)). omega with *. }
 rewrite H.
 clear k H.
 rewrite Nat.add_1_r.
 f_equal; omega with *.
Qed.

Lemma countable_nat2 : Countable (nat*nat).
Proof.
 apply (countable_by_inverse decode_pair code_pair).
 intros (x,y). apply decode_code_pair.
Qed.

Lemma countable_product A B :
 Countable A -> Countable B -> Countable (A*B).
Proof.
 intros (f,Hf) (g,Hg).
 exists (fun n => let (x,y) := decode_pair n in (f x, g y)).
 intros (a,b).
 destruct (Hf a) as (p,Hp), (Hg b) as (q,Hq).
 exists (code_pair (p, q)).
 rewrite decode_code_pair. congruence.
Qed.

Fixpoint tuple n A :=
 match n with
 | 0 => (unit:Type)
 | S n => (A * tuple n A)%type
 end.

Fixpoint map_tuple n {A B} (f:A->B) : tuple n A -> tuple n B :=
 match n with
 | 0 => fun t => t
 | S n => fun '(a,t) => (f a, map_tuple n f t)
 end.

Fixpoint code_tuple n : tuple n nat -> nat :=
 match n with
 | 0 => fun _ => 0
 | S n => fun '(a,t) => code_pair (a, code_tuple n t)
 end.

Fixpoint decode_tuple n m : tuple n nat :=
 match n with
 | 0 => tt
 | S n =>
   let (a,t) := decode_pair m in
   (a, decode_tuple n t)
 end.

Lemma decode_code_tuple n (t : tuple n nat) :
  decode_tuple n (code_tuple n t) = t.
Proof.
 revert t.
 induction n.
 - simpl. now destruct t.
 - cbn -[code_pair decode_pair].
   intros (a,b). now rewrite decode_code_pair, IHn.
Qed.

Lemma countable_tuple n A :
 Countable A -> Countable (tuple n A).
Proof.
 intros. induction n; simpl.
 - apply countable_unit.
 - now apply countable_product.
Qed.

Fixpoint tuple2list {n} {A} : tuple n A -> list A :=
 match n with
 | 0 => fun _ => []
 | S n => fun '(a,t) => a::tuple2list t
 end.

Fixpoint list2tuple {A} (l:list A) : tuple (length l) A :=
 match l with
 | [] => tt
 | a::l => (a, list2tuple l)
 end.

Lemma tuple_list_ok A (l:list A) :
  tuple2list (list2tuple l) = l.
Proof.
 induction l as [|a l IH]; simpl; f_equal; auto.
Qed.

Definition code_listnat (l:list nat) :=
 code_pair (length l, code_tuple _ (list2tuple l)).

Definition decode_listnat m :=
 let (n,p) := decode_pair m in
 tuple2list (decode_tuple n p).

Lemma decode_code_listnat (l:list nat) :
  decode_listnat (code_listnat l) = l.
Proof.
 unfold code_listnat, decode_listnat.
 now rewrite decode_code_pair, decode_code_tuple, tuple_list_ok.
Qed.

Lemma countable_listnat : Countable (list nat).
Proof.
 apply (countable_by_inverse _ _ decode_code_listnat).
Qed.

Lemma countable_list A : Countable A -> Countable (list A).
Proof.
 intros (f,Hf).
 exists (fun m => map f (decode_listnat m)).
 intros l.
 assert (exists l', map f l' = l).
 { induction l as [|a l (l',IH)].
   - now exists [].
   - destruct (Hf a) as (n,Hn).
     exists (n::l'). simpl. now f_equal. }
 destruct H as (l', Hl').
 exists (code_listnat l').
 now rewrite decode_code_listnat.
Qed.

(** Note: we could also have proved that [string] is countable
    by saying that [string] is isomorphic to [list ascii]. *)

(** By the way, Cantor's diagonal proof shows that [nat->nat]
    isn't countable *)

Lemma uncountable_funnatnat : ~Countable (nat -> nat).
Proof.
 intros (f,Hf).
 unfold Onto in Hf.
 destruct (Hf (fun n => S (f n n))) as (a,Ha).
 set (fa := fun n : nat => S (f n n)) in *.
 assert (f a a = fa a) by now rewrite Ha.
 unfold fa in H. omega.
Qed.

(** Same for [nat->A] as soon as [A] has at least two elements *)

Lemma uncountable_funnatbool : ~Countable (nat -> bool).
Proof.
 intros (f,Hf).
 unfold Onto in Hf.
 destruct (Hf (fun n => negb (f n n))) as (a,Ha).
 set (fa := fun n : nat => negb (f n n)) in *.
 assert (f a a = fa a) by now rewrite Ha.
 unfold fa in H. destruct (f a a); easy.
Qed.

Lemma countable_measured_partition A
 (measure : A -> nat)(f : nat -> nat -> A) :
 (forall m a, measure a < m -> exists n, f m n = a) ->
 Countable A.
Proof.
 intros Hf.
 exists (fun n => let (m,x) := decode_pair n in f m x).
 intros a.
 destruct (Hf (S (measure a)) a) as (n,Hn); auto.
 exists (code_pair (S (measure a), n)).
 now rewrite decode_code_pair.
Qed.

Fixpoint code_hterm t :=
  match t with
  | FVar v => code_pair (0, string_index v)
  | BVar n => code_pair (1, n)
  | Fun f l => code_pair (2,
                 code_pair (string_index f,
                            code_listnat (map code_hterm l)))
  end.

Definition code_term t :=
 code_pair (S (term_height t), code_hterm t).

Fixpoint decode_hterm h n :=
  match h with
  | 0 => BVar 0 (* arbitrary *)
  | S h =>
    let (kind,m) := decode_pair n in
    match kind with
    | 0 => FVar (string_enum m)
    | 1 => BVar m
    | _ => let (p,q) := decode_pair m in
           let f := string_enum p in
           let l := map (decode_hterm h) (decode_listnat q) in
           Fun f l
    end
  end.

Definition decode_term n :=
 let (h,m) := decode_pair n in
 decode_hterm h m.

Lemma decode_code_hterm h t :
 term_height t < h -> decode_hterm h (code_hterm t) = t.
Proof.
 revert t.
 induction h as [|h IH].
 - simpl. inversion 1.
 - destruct t as [v|n|f l].
   + intros _; cbn -[decode_pair code_pair].
     now rewrite decode_code_pair, string_enum_index.
   + intros _; cbn -[decode_pair code_pair].
     now rewrite decode_code_pair.
   + cbn -[decode_pair code_pair].
     intros H. apply Nat.succ_lt_mono in H.
     rewrite !decode_code_pair. f_equal.
     apply string_enum_index.
     rewrite decode_code_listnat.
     rewrite map_map.
     apply map_id_iff.
     intros t Ht. apply IH.
     apply (list_max_lt _ _ H).
     now apply in_map.
Qed.

Lemma decode_code_term t : decode_term (code_term t) = t.
Proof.
 unfold decode_term, code_term.
 rewrite decode_code_pair.
 apply decode_code_hterm; auto.
Qed.

Lemma countable_term : Countable term.
Proof.
 apply (countable_by_inverse _ _ decode_code_term).
Qed.

Definition code_op o :=
  match o with
  | And => 4
  | Or => 5
  | Impl => 6
  end.

Definition decode_op n :=
  match n with
  | 4 => And
  | 5 => Or
  | _ => Impl
  end.

Definition code_quant q :=
  match q with
  | All => 7
  | Ex => 8
  end.

Definition decode_quant n :=
  match n with
  | 7 => All
  | _ => Ex
  end.

Fixpoint code_hform t :=
  match t with
  | True => code_pair (0, 0)
  | False => code_pair (1, 0)
  | Pred p l =>
    code_pair (2,
               code_pair (string_index p,
                          code_listnat (map code_term l)))
  | Not f => code_pair (3, code_hform f)
  | Op o f1 f2 =>
    code_pair (code_op o,
               code_pair (code_hform f1, code_hform f2))
  | Quant q f =>
    code_pair (code_quant q, code_hform f)
  end.

Fixpoint decode_hform h n :=
  match h with
  | 0 => True (* arbitrary *)
  | S h =>
    let (kind,m) := decode_pair n in
    match kind with
    | 0 => True
    | 1 => False
    | 2 =>
      let (p,q) := decode_pair m in
      let s := string_enum p in
      let l := map decode_term (decode_listnat q) in
      Pred s l
    | 3 => Not (decode_hform h m)
    | 4 | 5 | 6 =>
      let (p,q) := decode_pair m in
      Op (decode_op kind) (decode_hform h p) (decode_hform h q)
    | _ =>
      Quant (decode_quant kind) (decode_hform h m)
    end
  end.

Definition code_form f :=
  code_pair (S (height f), code_hform f).

Definition decode_form n :=
  let (h,m) := decode_pair n in
  decode_hform h m.

Lemma decode_code_hform h f :
  height f < h -> decode_hform h (code_hform f) = f.
Proof.
 revert f.
 induction h as [|h IH].
 - inversion 1.
 - destruct f; cbn - [decode_pair code_pair];
   rewrite !decode_code_pair; auto.
   + intros _.
     rewrite decode_code_listnat.
     rewrite string_enum_index.
     rewrite map_map.
     f_equal. apply map_id_iff. intros. apply decode_code_term.
   + intros H. apply Nat.succ_lt_mono in H.
     f_equal; auto.
   + intros H. apply Nat.succ_lt_mono, max_lt in H. destruct H.
     destruct o; simpl; f_equal; auto.
   + intros H. apply Nat.succ_lt_mono in H.
     destruct q; simpl; f_equal; auto.
Qed.

Lemma decode_code_form f : decode_form (code_form f) = f.
Proof.
 unfold decode_form, code_form.
 rewrite decode_code_pair.
 apply decode_code_hform; auto.
Qed.

Lemma countable_form : Countable formula.
Proof.
 apply (countable_by_inverse _ _ decode_code_form).
Qed.
