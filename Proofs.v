
Require Import Ascii Omega MSetFacts MSetProperties
 Setoid Utils StringUtils Defs.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

Module VarsP := Properties(Vars).
Module VarsF := VarsP.FM.
Ltac varsdec := VarsP.Dec.fsetdec.

Hint Extern 10 => varsdec : set.

Lemma vars_mem_false x vs : ~Vars.In x vs -> Vars.mem x vs = false.
Proof.
 rewrite <- Vars.mem_spec. now case Vars.mem.
Qed.

Lemma vars_of_list_in l x : Vars.In x (vars_of_list l) <-> In x l.
Proof.
 induction l as [|y l IH]; simpl. varsdec.
 VarsF.set_iff. intuition.
Qed.

Lemma InA_In {A} x (l:list A) : InA eq x l <-> In x l.
Proof.
 split.
 rewrite InA_alt. now intros (y & <- & H).
 apply In_InA; auto with *.
Qed.

Lemma vars_unions_in (l: list Vars.t) v :
 Vars.In v (vars_unions l) <-> exists vs, Vars.In v vs /\ In vs l.
Proof.
 induction l; simpl.
 - split. varsdec. intros (vs & _ & [ ]).
 - VarsF.set_iff. rewrite IHl. split.
   + intros [H | (vs & H1 & H2)].
     * exists a; intuition.
     * exists vs; intuition.
   + intros (vs & H1 & [->|H2]).
     * now left.
     * right; now exists vs.
Qed.

Lemma vars_unionmap_alt {A} (f: A -> Vars.t) (l: list A) :
 Vars.Equal (vars_unionmap f l) (vars_unions (List.map f l)).
Proof.
 induction l; simpl.
 - varsdec.
 - rewrite IHl. varsdec.
Qed.

Lemma vars_unionmap_in {A} (f: A -> Vars.t) (l: list A) v :
 Vars.In v (vars_unionmap f l) <-> exists a, Vars.In v (f a) /\ In a l.
Proof.
 rewrite vars_unionmap_alt.
 rewrite vars_unions_in.
 split.
 - intros (vs & H1 & H2).
   rewrite in_map_iff in H2. destruct H2 as (a & <- & H3).
   now exists a.
 - intros (a & H1 & H2). exists (f a); split; auto using in_map.
Qed.

Lemma vars_unionmap_in' {A} (f: A -> Vars.t) (l: list A) a v :
 Vars.In v (f a) -> In a l -> Vars.In v (vars_unionmap f l).
Proof.
 intros. apply vars_unionmap_in. now exists a.
Qed.

Hint Resolve vars_unionmap_in' : set.

Lemma vars_map_in_aux (f : string -> string) l y acc :
 Vars.In y
  (List.fold_left (fun vs a => Vars.add (f a) vs) l acc) <->
 (Vars.In y acc \/ exists x, f x = y /\ List.In x l).
Proof.
 revert acc.
 induction l as [|a l IH]; intros acc.
 - simpl. firstorder.
 - simpl. rewrite IH; clear IH. VarsF.set_iff.
   firstorder congruence.
Qed.

Lemma vars_map_in (f : string -> string) vs y :
  Vars.In y (vars_map f vs) <-> (exists x, f x = y /\ Vars.In x vs).
Proof.
 unfold vars_map.
 rewrite Vars.fold_spec.
 rewrite vars_map_in_aux.
 VarsF.set_iff.
 setoid_rewrite VarsF.elements_iff.
 setoid_rewrite InA_In. intuition.
Qed.

Lemma vars_map_card_aux (f : string -> string) l acc :
 (forall x y, List.In x l ->
              List.In y l -> f x = f y -> x = y) ->
 (forall x, List.In x l -> ~Vars.In (f x) acc) ->
 NoDupA Logic.eq l ->
 Vars.cardinal (List.fold_left (fun vs a => Vars.add (f a) vs) l acc) =
 Vars.cardinal acc + List.length l.
Proof.
 revert acc.
 induction l as [|a l IH]; simpl; auto.
 intros acc Hf Hf' ND.
 inversion_clear ND.
 rewrite InA_In in H.
 rewrite IH; clear IH; auto.
 rewrite VarsP.add_cardinal_2. omega.
 apply Hf'; auto.
 intros x Hx. VarsF.set_iff. intros [Eq|IN].
 apply Hf in Eq; auto. congruence.
 apply Hf' in IN; auto.
Qed.

Lemma vars_map_cardinal (f : string -> string) vs :
 (forall x y, Vars.In x vs -> Vars.In y vs -> f x = f y -> x = y) ->
 Vars.cardinal (vars_map f vs) = Vars.cardinal vs.
Proof.
 intros Hf.
 unfold vars_map. rewrite Vars.fold_spec.
 rewrite vars_map_card_aux.
 - simpl. now rewrite Vars.cardinal_spec.
 - intros x y Hx Hy. apply Hf.
   now rewrite VarsF.elements_iff, InA_In.
   now rewrite VarsF.elements_iff, InA_In.
 - intros x. VarsF.set_iff. intuition.
 - apply Vars.elements_spec2w.
Qed.

Lemma vars_unionmap_app {A} f (l l':list A) :
 Vars.Equal (vars_unionmap f (l++l'))
  (Vars.union (vars_unionmap f l) (vars_unionmap f l')).
Proof.
 induction l; simpl; varsdec.
Qed.

Lemma vars_unionmap_rev {A} f (l:list A) :
 Vars.Equal (vars_unionmap f (rev l)) (vars_unionmap f l).
Proof.
 induction l; simpl. varsdec. rewrite vars_unionmap_app.
 simpl. varsdec.
Qed.

Lemma vars_flatmap_alt (f:string->Vars.t) vs :
 Vars.Equal (vars_flatmap f vs)
            (vars_unionmap f (Vars.elements vs)).
Proof.
 unfold vars_flatmap.
 rewrite VarsP.fold_spec_right, <- vars_unionmap_rev.
 change string with Vars.elt.
 induction (rev (Vars.elements vs)); simpl; auto; varsdec.
Qed.

Lemma vars_flatmap_in (f:string->Vars.t) vs v :
  Vars.In v (vars_flatmap f vs) <->
  exists w, Vars.In v (f w) /\ Vars.In w vs.
Proof.
 rewrite vars_flatmap_alt, vars_unionmap_in.
 setoid_rewrite <- (Vars.elements_spec1 vs).
 now setoid_rewrite InA_In.
Qed.

Instance vars_flatmap_subset :
 Proper (eq ==> Vars.Subset ==> Vars.Subset) vars_flatmap.
Proof.
 intros f f' <- s s' E v.
 rewrite !vars_flatmap_in.
 intros (w & Hw & Hw'). exists w; auto.
Qed.

Instance vars_map_proper :
 Proper (eq ==> Vars.Equal ==> Vars.Equal) vars_map.
Proof.
 unfold vars_map.
 intros f f' <- s s' E.
 apply VarsP.fold_equal; auto.
 - split; eauto with set.
 - now intros x x' <- y y' <-.
 - intros x y z. varsdec.
Qed.

Instance vars_flatmap_proper :
 Proper (eq ==> Vars.Equal ==> Vars.Equal) vars_flatmap.
Proof.
 unfold vars_flatmap.
 intros f f' <- s s' E.
 apply VarsP.fold_equal; auto.
 - split; eauto with set.
 - now intros x x' <- y y' <-.
 - intros x y z. varsdec.
Qed.

Lemma vars_flatmap_union (f:string->Vars.t) vs vs' :
 Vars.Equal (vars_flatmap f (Vars.union vs vs'))
            (Vars.union (vars_flatmap f vs) (vars_flatmap f vs')).
Proof.
 intros x. VarsF.set_iff. rewrite !vars_flatmap_in.
 setoid_rewrite Vars.union_spec. firstorder.
Qed.

Lemma string_app_empty_r s : s ++ "" = s.
Proof.
 induction s. auto. simpl. now f_equal.
Qed.

Fixpoint prefixes s :=
  match s with
  | "" => Vars.singleton ""
  | String a s => Vars.add "" (vars_map (String a) (prefixes s))
  end.

Lemma prefixes_in s u : Vars.In u (prefixes s) <-> Prefix u s.
Proof.
 revert u.
 induction s as [|a s IH]; simpl; intros u.
 - VarsF.set_iff. split. now intros <-. now inversion 1.
 - VarsF.set_iff. rewrite vars_map_in.
   setoid_rewrite IH.
   split.
   + intros [<- | (x & <- & H)]; auto.
   + inversion_clear 1. now left. right. now eexists.
Qed.

Definition strict_prefixes s :=
 Vars.remove "" (Vars.remove s (prefixes s)).

Lemma prefixes_cardinal s :
 Vars.cardinal (prefixes s) = S (String.length s).
Proof.
 induction s as [|a s IH]; simpl.
 - apply VarsP.singleton_cardinal.
 - rewrite VarsP.add_cardinal_2.
   + f_equal. rewrite <- IH.
     apply vars_map_cardinal.
     now intros x y _ _ [= ].
   + rewrite vars_map_in. intros (x & [= ] & _).
Qed.

Lemma strict_prefixes_cardinal s :
  Vars.cardinal (strict_prefixes s) = pred (String.length s).
Proof.
 destruct (string_dec s "").
 - subst. simpl. unfold strict_prefixes. simpl.
   apply VarsP.cardinal_Empty. varsdec.
 - unfold strict_prefixes.
   assert (E := prefixes_cardinal s).
   rewrite <- (VarsP.remove_cardinal_1 (x:=s)) in E.
   injection E as E.
   rewrite <- (VarsP.remove_cardinal_1 (x:="")) in E.
   now rewrite <- E.
   + VarsF.set_iff; split; auto. apply prefixes_in. auto.
   + apply prefixes_in. apply Prefix_refl.
Qed.

Lemma subset_equal u v:
  Vars.Subset u v -> Vars.cardinal u = Vars.cardinal v ->
  Vars.Equal u v.
Proof.
 intros SU CA.
 apply VarsP.subset_antisym; auto.
 intros x IN.
 destruct (VarsP.In_dec x u) as [H|H]; auto.
 generalize (VarsP.subset_cardinal_lt SU IN H). omega.
Qed.

Lemma string_app_length s s' :
 String.length (s++s') = String.length s + String.length s'.
Proof.
 induction s; simpl; auto.
Qed.

Lemma prefixes_app s s' :
  Vars.Equal (prefixes (s++s'))
             (Vars.union (prefixes s)
                         (vars_map (append s) (prefixes s'))).
Proof.
 intro x.
 VarsF.set_iff.
 rewrite vars_map_in.
 repeat setoid_rewrite prefixes_in.
 apply Prefix_app_r.
Qed.

Lemma prefixes_more s a :
  Vars.Equal (prefixes (s++String a ""))
             (Vars.add (s++String a "") (prefixes s)).
Proof.
 rewrite prefixes_app.
 rewrite VarsP.add_union_singleton.
 rewrite VarsP.union_sym.
 intro x.
 VarsF.set_iff.
 rewrite vars_map_in.
 setoid_rewrite prefixes_in.
 split; [intros [(y & <- & H)|H] | intros [<-|H]]; auto.
 - inversion_clear H.
   + right. rewrite string_app_empty_r. apply Prefix_refl.
   + inversion_clear H0; auto.
 - left. exists (String a ""); auto.
Qed.

Lemma strict_prefixes_more s a :
  Vars.Equal (strict_prefixes (s++String a ""))
             (Vars.remove "" (Vars.add s (strict_prefixes s))).
Proof.
 unfold strict_prefixes.
 rewrite prefixes_more.
 intros x.
 VarsF.set_iff. rewrite prefixes_in. intuition; subst.
 - destruct (string_dec s x); auto.
 - right. apply Prefix_refl.
 - assert (String.length (x++String a "") = String.length x).
   { now f_equal. }
   rewrite string_app_length in *. simpl in *. omega.
 - apply Prefix_length in H.
   rewrite string_app_length in *. simpl in *. omega.
Qed.

Lemma fresh_var_loop_ok vars id n :
 (Vars.cardinal vars < n + String.length id)%nat ->
 Vars.Subset (strict_prefixes id) vars ->
 ~Vars.In (fresh_var_loop vars id n) vars.
Proof.
 revert vars id.
 induction n.
 - simpl. intros vars id LT SU.
   assert (E : Vars.cardinal (strict_prefixes id) = Vars.cardinal vars).
   { apply VarsP.subset_cardinal in SU.
     rewrite strict_prefixes_cardinal in *.
     omega. }
   apply subset_equal in E; auto. clear SU.
   rewrite <- E.
   unfold strict_prefixes. VarsF.set_iff. intuition.
 - simpl. intros vars id LT SU.
   destruct (Vars.mem id vars) eqn:ME; simpl.
   + rewrite Vars.mem_spec in ME.
     apply IHn.
     * rewrite string_app_length. simpl. omega.
     * rewrite strict_prefixes_more; auto.
       { intros x. red in SU. VarsF.set_iff. intuition. }
   + rewrite <- Vars.mem_spec. now destruct Vars.mem.
Qed.

Lemma fresh_var_ok vars :
  ~Vars.In (fresh_var vars) vars.
Proof.
 unfold fresh_var. apply fresh_var_loop_ok.
 simpl. omega.
 change "x" with (""++String "x" "").
 rewrite strict_prefixes_more.
 unfold strict_prefixes. simpl. varsdec.
Qed.

Instance : Proper (Vars.Equal ==> eq ==> eq ==> eq) fresh_var_loop.
Proof.
 intros vs vs' EQ id id' <- n n' <-.
 revert vs vs' EQ id.
 induction n; cbn; intros vs vs' EQ id; auto.
 rewrite <- EQ. destruct Vars.mem; cbn; auto.
Qed.

Instance : Proper (Vars.Equal ==> eq) fresh_var.
Proof.
 intros vs vs' EQ.
 unfold fresh_var. now rewrite <-EQ.
Qed.
