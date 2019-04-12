Require Import Defs Mix Proofs Meta Omega Setoid Morphisms Theories PreModels.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Record Model (M:Type)(th : theory) :=
 { pre :> PreModel M th;
   AxOk : forall A, IsAxiom th A ->
                    forall genv, interp_form pre genv [] A }.

Lemma validity logic th :
 CoqRequirements logic ->
 forall T, IsTheorem logic th T ->
 forall M (mo : Model M th) genv, interp_form mo genv [] T.
Proof.
 intros CR T Thm M mo genv.
 rewrite thm_alt in Thm.
 destruct Thm as (WF & d & axs & (CK & BC & V) & F & C).
 assert (CO:=@correctness th M mo logic d CR V BC genv).
 rewrite C in CO. apply CO. intros A HA. apply AxOk.
 rewrite Forall_forall in F; auto.
Qed.

Lemma consistency_by_model logic th :
 CoqRequirements logic ->
 { M & Model M th } -> Consistent logic th.
Proof.
 intros CR (M,mo) Thm.
 apply (validity _ _ CR _ Thm M mo (fun _ => mo.(someone))).
Qed.

Lemma Thm_Not_e th A :
 IsTheorem Classic th A -> IsTheorem Classic th (~A) ->
 IsTheorem Classic th False.
Proof.
 intros (_ & axs & F & PR) (_ & axs' & F' & PR').
 split. apply False_wf.
 exists (axs++axs'); split.
 rewrite Forall_forall in *; intros x; rewrite in_app_iff;
  intros [ | ]; auto.
 apply R_Not_e with A.
 - clear PR'; eapply Pr_weakening; eauto. constructor.
   intros a. rewrite in_app_iff; auto.
 - eapply Pr_weakening; eauto. constructor.
   intros a. rewrite in_app_iff; auto.
Qed.

Definition Wf_term (sign:signature) (t:term) :=
  check sign t = true /\ BClosed t /\ FClosed t.

Definition closed_term sign :=
 { t : term | Wf_term sign t }.

Fixpoint map_arity {A B B'}(f:B->B') n
 : arity_fun A n B -> arity_fun A n B' :=
 match n with
 | 0 => f
 | S n => fun ab a => map_arity f n (ab a)
 end.

Lemma build_map_arity {A B B'} n (l : list A)(f:B->B')(any:B)(any':B') :
 length l = n ->
 forall (a : arity_fun A n B),
 build_args n l any' (map_arity f n a) =
 f (build_args n l any a).
Proof.
 intros <-. induction l; simpl; auto.
Qed.


Section SyntacticPreModel.
Variable logic : Defs.logic.
Variable th : theory.
Variable oneconst : string.
Hypothesis Honeconst : th.(funsymbs) oneconst = Some 0.

Let M := closed_term th.

Lemma cons_ok (t : term) (l : list term) n :
 Wf_term th t ->
 length l = n /\ Forall (Wf_term th) l ->
 length (t::l) = S n /\ Forall (Wf_term th) (t::l).
Proof.
 intros WF (L,F).
 split; simpl; auto.
Qed.

Definition sized_wf_listterm n :=
  {l : list term | length l = n /\ Forall (Wf_term th) l}.

Fixpoint mk_args n : arity_fun M n (sized_wf_listterm n) :=
 match n with
 | 0 => exist _ [] (conj eq_refl (Forall_nil _))
 | S n => fun t =>
          map_arity (fun '(exist _ l Hl) =>
                       let '(exist _ t Ht) := t in
                       exist _ (t::l) (cons_ok t l n Ht Hl))
                    n (mk_args n)
 end.

Lemma Fun_wf f l :
  Wf_term th (Fun f l) <->
   th.(funsymbs) f = Some (length l) /\ Forall (Wf_term th) l.
Proof.
 split.
 - intros (CK & BC & FC); cbn in *.
   destruct (funsymbs th f); [|easy].
   rewrite lazy_andb_iff, eqb_eq in CK.
   destruct CK as (->,CK). split; auto.
   rewrite forallb_forall in CK.
   apply Forall_forall. intros t Ht.
   repeat split; auto.
   + unfold BClosed in *. cbn in BC.
     rewrite list_max_map_0 in BC; auto.
   + unfold FClosed in *. cbn in FC.
     intros v. specialize (FC v). contradict FC.
     rewrite vars_unionmap_in. now exists t.
 - intros (E,F).
   rewrite Forall_forall in F.
   repeat split; cbn.
   + rewrite E, eqb_refl. apply forallb_forall.
     intros u Hu. now apply F.
   + red; cbn. apply list_max_map_0. intros u Hu. now apply F.
   + red; cbn. intro v. rewrite vars_unionmap_in.
     intros (a & IN & IN'). apply F in IN'. now apply IN' in IN.
Qed.

Lemma Pred_wf p l :
  Wf th (Pred p l) <->
   th.(predsymbs) p = Some (length l) /\ Forall (Wf_term th) l.
Proof.
 split.
 - intros (CK & BC & FC); cbn in *.
   destruct (predsymbs th p); [|easy].
   rewrite lazy_andb_iff, eqb_eq in CK.
   destruct CK as (->,CK). split; auto.
   rewrite forallb_forall in CK.
   apply Forall_forall. intros t Ht.
   repeat split; auto.
   + unfold BClosed in *. cbn in BC.
     rewrite list_max_map_0 in BC; auto.
   + unfold FClosed in *. cbn in FC.
     intros v. specialize (FC v). contradict FC.
     rewrite vars_unionmap_in. now exists t.
 - intros (E,F).
   rewrite Forall_forall in F.
   repeat split; cbn.
   + rewrite E, eqb_refl. apply forallb_forall.
     intros u Hu. now apply F.
   + red; cbn. apply list_max_map_0. intros u Hu. now apply F.
   + red; cbn. intro v. rewrite vars_unionmap_in.
     intros (a & IN & IN'). apply F in IN'. now apply IN' in IN.
Qed.


Lemma Cst_wf c :
  th.(funsymbs) c = Some 0 -> Wf_term th (Cst c).
Proof.
 intros. now apply Fun_wf.
Qed.

Definition one_listterm n : sized_wf_listterm n.
Proof.
 induction n as [|n (l & L & F)].
 - now exists [].
 - exists (Cst oneconst :: l).
   split; simpl; auto using Cst_wf.
Qed.

Lemma build_mk n (l : list M) (any:sized_wf_listterm n) :
 length l = n ->
 proj1_sig (build_args n l any (mk_args n)) =
 map (@proj1_sig _ _) l.
Proof.
 intros <-.
 induction l as [|(t,Ht) l IH]; simpl; auto.
 set (l0 := one_listterm (length l)).
 rewrite build_map_arity  with (any0:=l0); auto.
 specialize (IH l0).
 destruct (build_args _); simpl in *. f_equal; auto.
Qed.

(*
Definition rich_funs f :
  { o : option { n:nat & arity_fun M n M } |
    th.(funsymbs) f = get_arity o }.
Proof.
 destruct (th.(funsymbs) f) as [n|] eqn:E.
 - assert (r : arity_fun M n M).
   { generalize (mk_args n).
     apply map_arity. intros (l & Hl & WF).
     exists (Fun f l). apply Fun_wf; subst; auto. }
   now exists (Some (existT _ n r)).
 - now exists None.
Defined.
*)

Definition fun_core f n :
  (th.(funsymbs) f = Some n) -> arity_fun M n M.
Proof.
 intros E.
 generalize (mk_args n).
 apply map_arity. intros (l & Hl).
 exists (Fun f l). apply Fun_wf; destruct Hl; subst; auto.
Defined.

Definition rich_funs f :
  { o : option { n:nat & arity_fun M n M } |
    th.(funsymbs) f = get_arity o /\
    match o with
    | None => Logic.True
    | Some (existT _ n a) =>
      forall (l: list M)(any : M), length l = n ->
        proj1_sig (build_args n l any a) =
        Fun f (map (@proj1_sig _ _) l)
    end }.
Proof.
 destruct (th.(funsymbs) f) as [n|] eqn:E.
 - set (r := fun_core f n E).
   exists (Some (existT _ n r)); split; auto.
   intros l any Hl.
   unfold r, fun_core.
   rewrite build_map_arity with (any0 := one_listterm n); auto.
   rewrite <- (build_mk n l (one_listterm n) Hl).
   destruct build_args. now cbn.
 - now exists None.
Defined.

Definition mk_funs : modfuns M :=
  fun f => proj1_sig (rich_funs f).

Lemma mk_funs_ok f : th.(funsymbs) f = get_arity (mk_funs f).
Proof.
 unfold mk_funs. now destruct (rich_funs f).
Qed.

Definition mk_preds : modpreds M.
Proof.
 intro p.
 destruct (th.(predsymbs) p) as [n|].
 - apply Some. exists n.
   generalize (mk_args n).
   apply map_arity.
   exact (fun sl => IsTheorem logic th (Pred p (proj1_sig sl))).
 - apply None.
Defined.

Lemma mk_preds_ok p : th.(predsymbs) p = get_arity (mk_preds p).
Proof.
 unfold mk_preds.
 now destruct (th.(predsymbs) p) as [n|].
Qed.

Definition SyntacticPreModel : PreModel M th :=
 {| someone := exist _ (Cst oneconst) (Cst_wf _ Honeconst);
    funs := mk_funs;
    preds := mk_preds;
    funsOk := mk_funs_ok;
    predsOk := mk_preds_ok |}.

End SyntacticPreModel.

Section SyntacticModel.
Variable th : theory.
Hypothesis consistent : Consistent Classic th.
Hypothesis complete : Complete Classic th.
Hypothesis witsat : WitnessSaturated Classic th.
Variable oneconst : string.
Hypothesis Honeconst : th.(funsymbs) oneconst = Some 0.

Let M := closed_term th.
Let mo : PreModel M th :=
 SyntacticPreModel Classic th oneconst Honeconst.

Let term_closure (genv:variable -> M) (t:term) :=
  vmap (fun v:variable => proj1_sig (genv v)) t.

Let closure (genv:variable -> M) (f:formula) :=
  vmap (fun v:variable => proj1_sig (genv v)) f.

Lemma interp_pred p l :
 check th (Pred p l) = true ->
 BClosed (Pred p l) ->
 forall genv,
   interp_form mo genv [] (Pred p l) <->
   IsTheorem Classic th
     (Pred p (map (fun t => proj1_sig (interp_term mo genv [] t)) l)).
Proof.
 unfold BClosed. cbn.
 destruct (predsymbs th p) as [n|] eqn:E; [|easy].
 rewrite lazy_andb_iff, eqb_eq. intros (L,CK) BC genv.
 unfold mk_preds; rewrite E. clear E.
 set (l0 := one_listterm th oneconst Honeconst n).
 rewrite build_map_arity with (any := l0) by now rewrite map_length.
 rewrite build_mk with (oneconst := oneconst) by (auto; now rewrite map_length).
 rewrite map_map; reflexivity.
Qed.

Lemma interp_term_carac t :
  check th t = true -> BClosed t ->
  forall genv,
    proj1_sig (interp_term mo genv [] t) = term_closure genv t.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 - unfold BClosed. cbn. easy.
 - destruct (funsymbs th f) as [n|] eqn:E; [|easy].
   rewrite lazy_andb_iff, eqb_eq.
   intros (L,CK) BC genv.
   unfold mk_funs.
   destruct rich_funs as ([(n',a)| ] & Ho & Ho'); cbn in *.
   2: congruence.
   assert (Hn : n' = n) by congruence.
   subst n'.
   rewrite Ho' by now rewrite map_length.
   clear Ho Ho'.
   rewrite map_map.
   f_equal. apply map_ext_iff.
   intros t Ht. apply IH; auto.
   + rewrite forallb_forall in CK; auto.
   + red in BC. cbn in BC. rewrite list_max_map_0 in BC; auto.
Qed.

Lemma complete' A : Wf th A ->
 IsTheorem Classic th (~A) <-> ~IsTheorem Classic th A.
Proof.
 split.
 - intros Thm' Thm. apply consistent.
   apply Thm_Not_e with A; auto.
 - destruct (complete A); trivial. now intros [ ].
Qed.

Lemma thm_and A B :
  IsTheorem Classic th A /\ IsTheorem Classic th B <->
  IsTheorem Classic th (A /\ B).
Proof.
 split.
 - intros ((WfA & axsA & FA & PRA), (WfB & axsB & FB & PRB)).
   split. now apply Op_wf.
   exists (axsA ++ axsB); split.
   + rewrite Forall_forall in *; intros x; rewrite in_app_iff;
     intros [ | ]; auto.
   + apply R_And_i.
     * clear PRB; eapply Pr_weakening; eauto. constructor.
       intros a. rewrite in_app_iff; auto.
     * eapply Pr_weakening; eauto. constructor.
       intros a. rewrite in_app_iff; auto.
 - intros (WF & axs & F & PR); rewrite Op_wf in WF. split.
   + split. easy.
     exists axs; split; auto.
     apply R_And_e1 with B; auto.
   + split. easy.
     exists axs; split; auto.
     apply R_And_e2 with A; auto.
Qed.

Lemma thm_or A B : Wf th (A\/B) ->
  IsTheorem Classic th A \/ IsTheorem Classic th B <->
  IsTheorem Classic th (A \/ B).
Proof.
 intros WF.
 split.
 - intros [(_ & axs & F & PR)|(_ & axs & F & PR)].
   + split; auto. exists axs; split; auto.
   + split; auto. exists axs; split; auto.
 - intros (_ & axs & F & PR); rewrite Op_wf in WF.
   destruct (complete A); try easy. now left.
   destruct (complete B); try easy. now right.
   destruct consistent.
(* ... *)
Admitted.



Lemma term_closure_check t (genv:variable->M) :
  check th (term_closure genv t) = check th t.
Proof.
 revert t.
 fix IH 1. destruct t as [ | | f l]; cbn; auto.
 - destruct (genv v) as (t,Ht); cbn; auto. apply Ht.
 - rewrite map_length.
   destruct (funsymbs th f); [|easy].
   case eqb; [|easy].
   revert l. fix IH' 1. destruct l as [|t l]; cbn; auto.
   f_equal. apply IH. apply IH'.
Qed.

Lemma term_closure_level t (genv:variable->M) :
  level (term_closure genv t) = level t.
Proof.
 revert t.
 fix IH 1. destruct t as [ | | f l]; cbn; auto.
 - destruct (genv v) as (t,Ht); cbn; auto. apply Ht.
 - revert l. fix IH' 1. destruct l as [|t l]; cbn; auto.
   f_equal. apply IH. apply IH'.
Qed.

Lemma empty_union s s' : Vars.Empty (Vars.union s s') <->
 Vars.Empty s /\ Vars.Empty s'.
Proof.
 split. split; varsdec. varsdec.
Qed.

Lemma term_closure_fclosed t (genv:variable->M) :
  FClosed (term_closure genv t).
Proof.
 revert t.
 fix IH 1. destruct t as [ | | f l]; cbn; auto.
 - destruct (genv v) as (t,Ht); cbn; auto. apply Ht.
 - unfold FClosed in *. cbn.
   revert l. fix IH' 1. destruct l as [|t l]; cbn; auto.
   unfold term_closure in *.
   apply empty_union; auto.
Qed.

Lemma closure_check f genv :
 check th (closure genv f) = check th f.
Proof.
 induction f; cbn; auto.
 - rewrite map_length.
   destruct predsymbs; [|easy].
   case eqb; [|easy].
   revert l.
   induction l as [|t l]; cbn; auto. f_equal; auto.
   change (check th (term_closure genv t) = check th t). (* TODO *)
   apply term_closure_check.
 - unfold closure in *. now rewrite IHf1, IHf2.
Qed.

Lemma closure_level f (genv:variable->M) :
  level (closure genv f) = level f.
Proof.
 induction f; cbn; auto.
 revert l. induction l as [|t l IH]; cbn; auto.
 f_equal; auto.
 apply (term_closure_level t genv). (* TODO *)
Qed.

Lemma closure_fclosed f (genv:variable->M) :
  FClosed (closure genv f).
Proof.
 induction f; cbn; auto.
 - unfold FClosed in *. cbn.
   revert l. induction l as [|t l IH]; cbn; auto.
   apply empty_union; split; auto.
   apply (term_closure_fclosed t genv).
 - unfold FClosed in *. cbn.
   apply empty_union; split; auto.
Qed.

Lemma term_closure_wf t genv :
  check th t = true -> BClosed t ->
  Wf_term th (term_closure genv t).
Proof.
 repeat split.
 - now rewrite term_closure_check.
 - red. now rewrite term_closure_level.
 - apply term_closure_fclosed.
Qed.

Lemma closure_wf f genv :
  check th f = true -> BClosed f ->
  Wf th (closure genv f).
Proof.
 repeat split.
 - now rewrite closure_check.
 - red. now rewrite closure_level.
 - apply closure_fclosed.
Qed.

Lemma light_interp_carac f : check th f = true -> BClosed f ->
 forall genv,
   interp_form mo genv [] f <->
     IsTheorem Classic th (closure genv f).
Proof.
 induction f; intros CK BC genv.
 - cbn.
   unfold IsTheorem. intuition.
   now exists [].
 - cbn.
   unfold IsTheorem. intuition.
   + apply consistent; split; auto.
 - rewrite interp_pred; auto. simpl.
   unfold vmap, vmap_list.
   assert (forall t, In t l ->
            proj1_sig (interp_term mo genv [] t) =
            term_vmap (fun v : variable => proj1_sig (genv v)) t).
   { intros t Ht. apply interp_term_carac.
     cbn in CK.
     destruct predsymbs; [|easy]. destruct eqb; [|easy].
     rewrite forallb_forall in CK; auto.
     red in BC. cbn in BC. rewrite list_max_map_0 in BC; auto. }
   apply map_ext_iff in H. rewrite H. reflexivity.
 - simpl. rewrite IHf; auto.
   symmetry. apply complete'.
   apply closure_wf; auto.
 - cbn in CK. rewrite lazy_andb_iff in CK. destruct CK as (CK1,CK2).
   red in BC. cbn in BC. apply max_0 in BC. destruct BC as (BC1,BC2).
   destruct o; simpl; rewrite IHf1, IHf2; auto.
   + admit.
   + admit.
   + admit.
 - simpl.
Admitted.

(* Overkill ?

Lemma interp_carac f : check th f = true -> BClosed f ->
 forall genv,
   (interp_form mo genv [] f <->
     IsTheorem Classic th (closure genv f)) /\
   (interp_form mo genv [] (~f) <->
     IsTheorem Classic th (~(closure genv f))).
Proof.
 induction f; intros CK BC genv.
 - cbn.
   unfold IsTheorem. intuition.
   + now exists [].
   + destruct H3 as (axs & F & PR).
     apply consistent. split. apply False_wf.
     exists axs. split; auto.
     apply R_Not_e with True; auto.
 - cbn.
   unfold IsTheorem. intuition.
   + apply consistent; split; auto.
   + exists []. split; auto.
     apply R_Not_i. apply R_Ax; simpl; auto.
 - change (interp_form mo genv [] (~ Pred p l))
   with (~interp_form mo genv [] (Pred p l)).
   rewrite interp_pred; auto. simpl.
   unfold vmap, vmap_list.
   assert (forall t, In t l ->
            proj1_sig (interp_term mo genv [] t) =
            term_vmap (fun v : variable => proj1_sig (genv v)) t).
   { intros t Ht. apply interp_term_carac.
     cbn in CK.
     destruct predsymbs; [|easy]. destruct eqb; [|easy].
     rewrite forallb_forall in CK; auto.
     red in BC. cbn in BC. rewrite list_max_map_0 in BC; auto. }
   apply map_ext_iff in H. rewrite H.
   split. reflexivity. clear H.
   symmetry. apply complete'.
   change (Wf th (Pred p (map (term_closure genv) l))).
   apply Pred_wf'; auto.
 - destruct (IHf CK BC genv) as (IH,IH').
   split. apply IH'. simpl. rewrite IH.

   cbn in CK.
   destruct (predsymbs th p) as [n|] eqn:E; [|easy].
   rewrite lazy_andb_iff in CK. destruct CK as (CK,CKl).
   unfold mk_preds; rewrite E.
*)

Lemma axioms_ok A :
  IsAxiom th A ->
  forall genv, interp_form mo genv [] A .
Admitted.

End SyntacticModel.