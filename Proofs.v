
Require Import Ascii Omega MSetFacts MSetProperties
 Setoid Utils StringUtils Defs.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

Module VarsP := Properties(Vars).
Module VarsF := VarsP.FM.
Ltac varsdec := VarsP.Dec.fsetdec.

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
 setoid_rewrite InA_alt.
 firstorder congruence.
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
 assert (~In a l). { rewrite InA_alt in *. firstorder. }
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
   rewrite VarsF.elements_iff, InA_alt. firstorder.
   rewrite VarsF.elements_iff, InA_alt. firstorder.
 - intros x. VarsF.set_iff. intuition.
 - apply Vars.elements_spec2w.
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
       { intros x. red in SU. VarsF.set_iff. intuition. now subst. }
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
