
(** * Proofs about name sets *)

(** The NatDed development, Pierre Letouzey, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Ascii MSetFacts MSetProperties StringUtils Defs.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

Module NamesP := Properties(Names).
Module NamesF := NamesP.FM.
Ltac namedec := NamesP.Dec.fsetdec.
Ltac nameiff := NamesF.set_iff.

Hint Extern 10 => namedec : set.

Lemma InA_In {A} x (l:list A) : InA eq x l <-> In x l.
Proof.
 split.
 rewrite InA_alt. now intros (y & <- & H).
 apply In_InA; auto with *.
Qed.

Import Names.
Import Logic. (* for [eq] *)
Local Open Scope nat. (* needed for Coq 8.11 *)

Lemma mem_false x vs :
 ~In x vs -> mem x vs = false.
Proof.
 rewrite <- mem_spec. now case mem.
Qed.

Lemma names_of_list_in l x : In x (of_list l) <-> List.In x l.
Proof.
 induction l as [|y l IH]; simpl. namedec.
 nameiff. intuition.
Qed.

Lemma unions_in (l: list t) v :
 In v (unions l) <-> exists vs, In v vs /\ List.In vs l.
Proof.
 induction l; simpl.
 - split. namedec. intros (vs & _ & [ ]).
 - nameiff. rewrite IHl. split.
   + intros [H | (vs & H1 & H2)].
     * exists a; intuition.
     * exists vs; intuition.
   + intros (vs & H1 & [->|H2]).
     * now left.
     * right; now exists vs.
Qed.

Lemma unionmap_alt {A} (f: A -> t) (l: list A) :
 Equal (unionmap f l) (unions (List.map f l)).
Proof.
 induction l; simpl.
 - namedec.
 - rewrite IHl. namedec.
Qed.

Lemma unionmap_in {A} (f: A -> t) (l: list A) v :
 In v (unionmap f l) <-> exists a, In v (f a) /\ List.In a l.
Proof.
 rewrite unionmap_alt.
 rewrite unions_in.
 split.
 - intros (vs & H1 & H2).
   rewrite in_map_iff in H2. destruct H2 as (a & <- & H3).
   now exists a.
 - intros (a & H1 & H2). exists (f a); split; auto using in_map.
Qed.

Lemma unionmap_in' {A} (f: A -> t) (l: list A) a v :
 In v (f a) -> List.In a l -> In v (unionmap f l).
Proof.
 intros. apply unionmap_in. now exists a.
Qed.

Hint Resolve unionmap_in' : set.

Lemma unionmap_notin {A} (f: A -> t) (l: list A) v a :
 ~In v (unionmap f l) -> List.In a l -> ~In v (f a).
Proof.
 intros NI IN. contradict NI. eapply unionmap_in'; eauto.
Qed.

Lemma unionmap_map_in {A B} (f: B -> t) (g : A -> B) (l: list A) v :
 In v (unionmap f (List.map g l)) <-> exists a, In v (f (g a)) /\ List.In a l.
Proof.
 rewrite unionmap_in.
 split.
 - intros (b & Hv & Hb). apply in_map_iff in Hb.
   destruct Hb as (a & <- & Ha). now exists a.
 - intros (a & Hv & Ha). exists (g a). split; auto.
   apply in_map_iff. now exists a.
Qed.

Lemma subset_unionmap_map {A} (f: A -> t) (g : A -> A) (l: list A) s :
 (forall x, List.In x l -> Subset (f (g x)) (union s (f x))) ->
 Subset (unionmap f (List.map g l)) (union s (unionmap f l)).
Proof.
 intros H v.
 rewrite union_spec, unionmap_map_in, unionmap_in.
 intros (a & Hv & Ha). apply H in Hv; auto.
 rewrite union_spec in Hv. destruct Hv as [Hv|Hv]; auto.
 right. now exists a.
Qed.

Lemma subset_unionmap_map' {A} (f: A -> t) (g : A -> A) (l: list A) c :
 (forall x, List.In x l -> Subset (f (g x)) (add c (f x))) ->
 Subset (unionmap f (List.map g l)) (add c (unionmap f l)).
Proof.
 intros H. rewrite NamesP.add_union_singleton.
 apply subset_unionmap_map. intros x Hx.
 rewrite <- NamesP.add_union_singleton; auto.
Qed.

Lemma map_in_aux (f : name -> name) l y acc :
 In y
  (List.fold_left (fun vs a => add (f a) vs) l acc) <->
 (In y acc \/ exists x, f x = y /\ List.In x l).
Proof.
 revert acc.
 induction l as [|a l IH]; intros acc.
 - simpl. firstorder.
 - simpl. rewrite IH; clear IH. nameiff.
   firstorder congruence.
Qed.

Lemma map_in (f : name -> name) vs y :
  In y (map f vs) <-> (exists x, f x = y /\ In x vs).
Proof.
 unfold map.
 rewrite fold_spec.
 rewrite map_in_aux.
 nameiff.
 setoid_rewrite NamesF.elements_iff.
 setoid_rewrite InA_In. intuition.
Qed.

Lemma map_card_aux (f : name -> name) l acc :
 (forall x y, List.In x l ->
              List.In y l -> f x = f y -> x = y) ->
 (forall x, List.In x l -> ~In (f x) acc) ->
 NoDupA eq l ->
 cardinal (List.fold_left (fun vs a => add (f a) vs) l acc) =
 cardinal acc + List.length l.
Proof.
 revert acc.
 induction l as [|a l IH]; simpl; auto.
 intros acc Hf Hf' ND.
 inversion_clear ND.
 rewrite InA_In in H.
 rewrite IH; clear IH; auto.
 rewrite NamesP.add_cardinal_2. omega.
 apply Hf'; auto.
 intros x Hx. nameiff. intros [Eq|IN].
 apply Hf in Eq; auto. congruence.
 apply Hf' in IN; auto.
Qed.

Lemma map_cardinal (f : name -> name) vs :
 (forall x y, In x vs -> In y vs -> f x = f y -> x = y) ->
 cardinal (map f vs) = cardinal vs.
Proof.
 intros Hf.
 unfold map. rewrite fold_spec.
 rewrite map_card_aux.
 - simpl. now rewrite cardinal_spec.
 - intros x y Hx Hy. apply Hf.
   now rewrite NamesF.elements_iff, InA_In.
   now rewrite NamesF.elements_iff, InA_In.
 - intros x. nameiff. intuition.
 - apply elements_spec2w.
Qed.

Lemma unionmap_app {A} f (l l':list A) :
 Equal (unionmap f (l++l')) (union (unionmap f l) (unionmap f l')).
Proof.
 induction l; simpl; namedec.
Qed.

Lemma unionmap_rev {A} f (l:list A) :
 Equal (unionmap f (rev l)) (unionmap f l).
Proof.
 induction l; simpl. namedec. rewrite unionmap_app.
 simpl. namedec.
Qed.

Lemma flatmap_alt (f:name->t) vs :
 Equal (flatmap f vs) (unionmap f (elements vs)).
Proof.
 unfold flatmap.
 rewrite NamesP.fold_spec_right, <- unionmap_rev.
 change name with elt.
 induction (rev (elements vs)); simpl; auto; namedec.
Qed.

Lemma flatmap_in (f:name->t) vs v :
  In v (flatmap f vs) <->
  exists w, In v (f w) /\ In w vs.
Proof.
 rewrite flatmap_alt, unionmap_in.
 setoid_rewrite <- (elements_spec1 vs).
 now setoid_rewrite InA_In.
Qed.

Instance flatmap_subset :
 Proper (eq ==> Subset ==> Subset) flatmap.
Proof.
 intros f f' <- s s' E v.
 rewrite !flatmap_in.
 intros (w & Hw & Hw'). exists w; auto.
Qed.

Instance map_proper :
 Proper (eq ==> Equal ==> Equal) map.
Proof.
 unfold map.
 intros f f' <- s s' E.
 apply NamesP.fold_equal; auto.
 - split; eauto with set.
 - now intros x x' <- y y' <-.
 - intros x y z. namedec.
Qed.

Instance flatmap_proper :
 Proper (eq ==> Equal ==> Equal) flatmap.
Proof.
 unfold flatmap.
 intros f f' <- s s' E.
 apply NamesP.fold_equal; auto.
 - split; eauto with set.
 - now intros x x' <- y y' <-.
 - intros x y z. namedec.
Qed.

Lemma flatmap_union (f:name->t) vs vs' :
 Equal (flatmap f (union vs vs'))
       (union (flatmap f vs) (flatmap f vs')).
Proof.
 intros x. nameiff. rewrite !flatmap_in.
 setoid_rewrite union_spec. firstorder.
Qed.

Lemma string_app_empty_r s : s ++ "" = s.
Proof.
 induction s. auto. simpl. now f_equal.
Qed.

Fixpoint prefixes s :=
  match s with
  | "" => singleton ""
  | String a s => add "" (map (String a) (prefixes s))
  end.

Lemma prefixes_in s u : In u (prefixes s) <-> Prefix u s.
Proof.
 revert u.
 induction s as [|a s IH]; simpl; intros u.
 - nameiff. split. now intros <-. now inversion 1.
 - nameiff. rewrite map_in.
   setoid_rewrite IH.
   split.
   + intros [<- | (x & <- & H)]; auto.
   + inversion_clear 1. now left. right. now eexists.
Qed.

Definition strict_prefixes s :=
 remove "" (remove s (prefixes s)).

Lemma prefixes_cardinal s :
 cardinal (prefixes s) = S (String.length s).
Proof.
 induction s as [|a s IH]; simpl.
 - apply NamesP.singleton_cardinal.
 - rewrite NamesP.add_cardinal_2.
   + f_equal. rewrite <- IH.
     apply map_cardinal.
     now intros x y _ _ [= ].
   + rewrite map_in. intros (x & [= ] & _).
Qed.

Lemma strict_prefixes_cardinal s :
  cardinal (strict_prefixes s) = pred (String.length s).
Proof.
 destruct (string_dec s "").
 - subst. simpl. unfold strict_prefixes. simpl.
   apply NamesP.cardinal_Empty. namedec.
 - unfold strict_prefixes.
   assert (E := prefixes_cardinal s).
   rewrite <- (NamesP.remove_cardinal_1 (x:=s)) in E.
   injection E as E.
   rewrite <- (NamesP.remove_cardinal_1 (x:="")) in E.
   now rewrite <- E.
   + nameiff; split; auto. apply prefixes_in. auto.
   + apply prefixes_in. apply Prefix_refl.
Qed.

Lemma subset_equal u v:
  Subset u v -> cardinal u = cardinal v ->
  Equal u v.
Proof.
 intros SU CA.
 apply NamesP.subset_antisym; auto.
 intros x IN.
 destruct (NamesP.In_dec x u) as [H|H]; auto.
 generalize (NamesP.subset_cardinal_lt SU IN H). omega.
Qed.

Lemma string_app_length s s' :
 String.length (s++s') = String.length s + String.length s'.
Proof.
 induction s; simpl; auto.
Qed.

Lemma prefixes_app s s' :
  Equal (prefixes (s++s'))
        (union (prefixes s) (map (append s) (prefixes s'))).
Proof.
 intro x.
 nameiff.
 rewrite map_in.
 repeat setoid_rewrite prefixes_in.
 apply Prefix_app_r.
Qed.

Lemma prefixes_more s a :
  Equal (prefixes (s++String a ""))
        (add (s++String a "") (prefixes s)).
Proof.
 rewrite prefixes_app.
 rewrite NamesP.add_union_singleton.
 rewrite NamesP.union_sym.
 intro x.
 nameiff.
 rewrite map_in.
 setoid_rewrite prefixes_in.
 split; [intros [(y & <- & H)|H] | intros [<-|H]]; auto.
 - inversion_clear H.
   + right. rewrite string_app_empty_r. apply Prefix_refl.
   + inversion_clear H0; auto.
 - left. exists (String a ""); auto.
Qed.

Lemma strict_prefixes_more s a :
  Equal (strict_prefixes (s++String a ""))
        (remove "" (add s (strict_prefixes s))).
Proof.
 unfold strict_prefixes.
 rewrite prefixes_more.
 intros x.
 nameiff. rewrite prefixes_in. intuition; subst.
 - destruct (string_dec s x); auto.
 - right. apply Prefix_refl.
 - assert (String.length (x++String a "") = String.length x).
   { now f_equal. }
   rewrite string_app_length in *. simpl in *. omega.
 - apply Prefix_length in H.
   rewrite string_app_length in *. simpl in *. omega.
Qed.

Lemma fresh_loop_ok names id n :
 cardinal names < n + String.length id ->
 Subset (strict_prefixes id) names ->
 ~In (fresh_loop names id n) names.
Proof.
 revert names id.
 induction n.
 - simpl. intros vars id LT SU.
   assert (E : cardinal (strict_prefixes id) = cardinal vars).
   { apply NamesP.subset_cardinal in SU.
     rewrite strict_prefixes_cardinal in *.
     omega. }
   apply subset_equal in E; auto. clear SU.
   rewrite <- E.
   unfold strict_prefixes. nameiff. intuition.
 - simpl. intros vars id LT SU.
   destruct (mem id vars) eqn:ME; simpl.
   + rewrite mem_spec in ME.
     apply IHn.
     * rewrite string_app_length. simpl. omega.
     * rewrite strict_prefixes_more; auto.
       { intros x. red in SU. nameiff. intuition. }
   + rewrite <- mem_spec. now destruct mem.
Qed.

Lemma fresh_ok names :
  ~In (fresh names) names.
Proof.
 unfold fresh. apply fresh_loop_ok.
 simpl. omega.
 change "x" with (""++String "x" "").
 rewrite strict_prefixes_more.
 unfold strict_prefixes. simpl. namedec.
Qed.

Ltac setfresh vars z Hz :=
 match goal with |- context [fresh ?v] => set (vars := v) end;
 assert (Hz := fresh_ok vars);
 set (z:=fresh vars) in *;
 clearbody z.

Lemma exist_fresh names : exists z, ~In z names.
Proof.
 exists (fresh names). apply fresh_ok.
Qed.

Instance : Proper (Equal ==> eq ==> eq ==> eq) fresh_loop.
Proof.
 intros vs vs' EQ id id' <- n n' <-.
 revert vs vs' EQ id.
 induction n; cbn; intros vs vs' EQ id; auto.
 rewrite <- EQ. destruct mem; cbn; auto.
Qed.

Instance : Proper (Equal ==> eq) fresh.
Proof.
 intros vs vs' EQ.
 unfold fresh. now rewrite <-EQ.
Qed.
