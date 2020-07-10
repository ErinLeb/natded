
(** * Models of theories *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Eqdep_dec Defs Mix NameProofs Meta Theories PreModels.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Record Model (M:Type)(th : theory) :=
 { pre :> PreModel M th;
   AxOk : forall A, IsAxiom th A ->
                    forall genv, interp_form pre genv [] A }.

Lemma validity_theorem logic th :
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
 apply (validity_theorem _ _ CR _ Thm M mo (fun _ => mo.(someone))).
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

Definition wf_term (sign:signature) (t:term) :=
 check sign t && (level t =? 0) && Names.is_empty (fvars t).

Lemma Wf_term_alt sign t : Wf_term sign t <-> wf_term sign t = true.
Proof.
 unfold Wf_term, wf_term.
 split.
 - intros (-> & -> & H). cbn. now rewrite Names.is_empty_spec.
 - rewrite !andb_true_iff, !eqb_eq. unfold BClosed.
   intros ((->,->),H); repeat split; auto.
   now rewrite Names.is_empty_spec in H.
Qed.

Lemma Fun_wf sign f l :
  Wf_term sign (Fun f l) <->
   sign.(funsymbs) f = Some (length l) /\ Forall (Wf_term sign) l.
Proof.
 split.
 - intros (CK & BC & FC); cbn in *.
   destruct (funsymbs _ f); [|easy].
   rewrite lazy_andb_iff, eqb_eq in CK.
   destruct CK as (->,CK). split; auto.
   rewrite forallb_forall in CK.
   apply Forall_forall. intros t Ht.
   repeat split; auto.
   + unfold BClosed in *. cbn in BC.
     rewrite list_max_map_0 in BC; auto.
   + unfold FClosed in *. cbn in FC.
     intros v. eapply unionmap_notin; eauto.
 - intros (E,F).
   rewrite Forall_forall in F.
   repeat split; cbn.
   + rewrite E, eqb_refl. apply forallb_forall.
     intros u Hu. now apply F.
   + red; cbn. apply list_max_map_0. intros u Hu. now apply F.
   + red; cbn. intro v. rewrite unionmap_in.
     intros (a & IN & IN'). apply F in IN'. now apply IN' in IN.
Qed.

Lemma Pred_wf sign p l :
  Wf sign (Pred p l) <->
   sign.(predsymbs) p = Some (length l) /\ Forall (Wf_term sign) l.
Proof.
 split.
 - intros (CK & BC & FC); cbn in *.
   destruct (predsymbs _ p); [|easy].
   rewrite lazy_andb_iff, eqb_eq in CK.
   destruct CK as (->,CK). split; auto.
   rewrite forallb_forall in CK.
   apply Forall_forall. intros t Ht.
   repeat split; auto.
   + unfold BClosed in *. cbn in BC.
     rewrite list_max_map_0 in BC; auto.
   + unfold FClosed in *. cbn in FC.
     intros v. eapply unionmap_notin; eauto.
 - intros (E,F).
   rewrite Forall_forall in F.
   repeat split; cbn.
   + rewrite E, eqb_refl. apply forallb_forall.
     intros u Hu. now apply F.
   + red; cbn. apply list_max_map_0. intros u Hu. now apply F.
   + red; cbn. intro v. rewrite unionmap_in.
     intros (a & IN & IN'). apply F in IN'. now apply IN' in IN.
Qed.

Lemma Cst_wf sign c :
  sign.(funsymbs) c = Some 0 -> Wf_term sign (Cst c).
Proof.
 intros. now apply Fun_wf.
Qed.

Lemma Cst_wf' sign c :
  sign.(funsymbs) c = Some 0 -> wf_term sign (Cst c) = true.
Proof.
 intros. now apply Wf_term_alt, Fun_wf.
Qed.


Definition closed_term sign :=
 { t : term | wf_term sign t = true }.

Lemma proof_irr sign (s s' : closed_term sign) :
 s = s' <-> proj1_sig s = proj1_sig s'.
Proof.
 destruct s, s'. cbn. split.
 - now injection 1.
 - intros <-. f_equal.
   destruct (wf_term sign x); [|easy].
   rewrite UIP_refl_bool. apply UIP_refl_bool.
Qed.

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
 wf_term th t = true ->
 length l = n /\ Forall (Wf_term th) l ->
 length (t::l) = S n /\ Forall (Wf_term th) (t::l).
Proof.
 intros WF (L,F).
 apply Wf_term_alt in WF.
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

Definition fun_core f n :
  (th.(funsymbs) f = Some n) -> arity_fun M n M.
Proof.
 intros E.
 generalize (mk_args n).
 apply map_arity. intros (l & Hl).
 exists (Fun f l). apply Wf_term_alt, Fun_wf; destruct Hl; subst; auto.
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
 {| someone := exist _ (Cst oneconst) (Cst_wf' _ _ Honeconst);
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

Lemma term_closure_check t (genv:variable->M) :
  check th (term_closure genv t) = check th t.
Proof.
 revert t.
 fix IH 1. destruct t as [ | | f l]; cbn; auto.
 - destruct (genv v) as (t,Ht); cbn; auto.
   apply Wf_term_alt in Ht. apply Ht.
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
 - destruct (genv v) as (t,Ht); cbn; auto.
   apply Wf_term_alt in Ht. apply Ht.
 - revert l. fix IH' 1. destruct l as [|t l]; cbn; auto.
   f_equal. apply IH. apply IH'.
Qed.

Lemma empty_union s s' : Names.Empty (Names.union s s') <->
 Names.Empty s /\ Names.Empty s'.
Proof.
 split. split; namedec. namedec.
Qed.

Lemma term_closure_fclosed t (genv:variable->M) :
  FClosed (term_closure genv t).
Proof.
 revert t.
 fix IH 1. destruct t as [ | | f l]; cbn; auto.
 - destruct (genv v) as (t,Ht); cbn; auto.
   apply Wf_term_alt in Ht. apply Ht.
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

Lemma term_closure_wf' t genv :
  check th t = true -> BClosed t ->
  wf_term th (term_closure genv t) = true.
Proof.
 intros CK BC. apply Wf_term_alt. now apply term_closure_wf.
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

Lemma closure_bsubst n t f genv :
 FClosed t ->
 closure genv (bsubst n t f) = bsubst n t (closure genv f).
Proof.
 unfold closure.
 intros FC.
 rewrite form_vmap_bsubst.
 f_equal.
 rewrite term_vmap_id; auto.
 intros v. red in FC. intuition.
 intros v. destruct (genv v) as (u,Hu); simpl.
 apply Wf_term_alt in Hu. apply Hu.
Qed.

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

Lemma interp_term_carac' (t:term) genv
  (CK : check th t = true) (BC : BClosed t) :
  interp_term mo genv [] t =
  exist _ (term_closure genv t) (term_closure_wf' t genv CK BC).
Proof.
 apply proof_irr. cbn. now apply interp_term_carac.
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
   destruct (complete A) as [HA|HA]; [easy|now left|].
   destruct HA as (WfA & axsA & FA & PRA).
   destruct (complete B) as [HB|HB]; [easy|now right|].
   destruct HB as (WfB & axsB & FB & PRB).
   destruct consistent.
   split. apply False_wf.
   exists (axs++axsA++axsB). split.
   rewrite Forall_forall in *; intros x; rewrite !in_app_iff;
     intros [|[ | ]]; auto.
   apply R_Or_e with A B.
   + clear PRA PRB; eapply Pr_weakening; eauto. constructor.
     intros a. rewrite in_app_iff; auto.
   + apply R_Not_e with A.
     * apply R'_Ax.
     * clear PR PRB; eapply Pr_weakening; eauto. constructor.
       intros a. simpl. rewrite !in_app_iff; auto.
   + apply R_Not_e with B.
     * apply R'_Ax.
     * clear PR PRA; eapply Pr_weakening; eauto. constructor.
       intros a. simpl. rewrite !in_app_iff; auto.
Qed.


Lemma thm_impl A B : Wf th (A->B) ->
  (IsTheorem Classic th A -> IsTheorem Classic th B) <->
  IsTheorem Classic th (A -> B).
Proof.
 intros WF.
 split.
 - intros IM.
   destruct (complete A) as [HA|HA]; [rewrite Op_wf in WF; easy | | ].
   + specialize (IM HA).
     destruct IM as (WfB & axsB & FB & PRB).
     split; auto.
     exists axsB; split; auto.
     apply R_Imp_i.
     eapply Pr_weakening; eauto. constructor. intros a; simpl; auto.
   + destruct HA as (WfA & axsA & FA & PRA).
     split; auto.
     exists axsA; split; auto.
     apply R_Imp_i.
     apply R_Fa_e.
     apply R_Not_e with A. apply R'_Ax.
     eapply Pr_weakening; eauto. constructor. intros a; simpl; auto.
 - intros (_ & axsAB & FAB & PRAB) (_ & axsA & FA & PRA).
   split. now rewrite Op_wf in WF.
   exists (axsAB++axsA). split.
   rewrite Forall_forall in *; intros x; rewrite !in_app_iff;
     intros [|]; auto.
   apply R_Imp_e with A.
   + clear PRA; eapply Pr_weakening; eauto. constructor.
       intros a. simpl. rewrite !in_app_iff; auto.
   + clear PRAB; eapply Pr_weakening; eauto. constructor.
       intros a. simpl. rewrite !in_app_iff; auto.
Qed.

Lemma pr_notex_allnot logic c A :
 Pr logic (c ⊢ ~∃A) <-> Pr logic (c ⊢ ∀~A).
Proof.
 destruct (exist_fresh (fvars (c ⊢ A))) as (x,Hx).
 split.
 - intros NE.
   apply R_All_i with x; cbn - [Names.union] in *. namedec.
   apply R_Not_i.
   apply R_Not_e with (∃A)%form.
   + apply R_Ex_i with (FVar x); auto using R'_Ax.
   + eapply Pr_weakening; eauto. constructor; red; simpl; auto.
 - intros AN.
   apply R_Not_i.
   apply R'_Ex_e with x. cbn in *. namedec.
   eapply R_Not_e; [apply R'_Ax|].
   eapply Pr_weakening. eapply R_All_e with (t:=FVar x); eauto.
   constructor. red; simpl; auto.
Qed.

Lemma pr_notexnot c A :
 Pr Classic (c ⊢ ~∃~A) <-> Pr Classic (c ⊢ ∀A).
Proof.
 destruct (exist_fresh (fvars (c ⊢ A))) as (x,Hx).
 split.
 - intros NEN.
   apply R_All_i with x; cbn - [Names.union] in *. namedec.
   apply R_Absu; auto.
   apply R_Not_e with (∃~A)%form.
   apply R_Ex_i with (FVar x); auto using R'_Ax.
   eapply Pr_weakening; eauto. constructor; red; simpl; auto.
 - intros ALL.
   apply R_Not_i.
   apply R'_Ex_e with x. cbn in *. namedec.
   cbn.
   eapply R_Not_e; [|eapply R'_Ax].
   eapply Pr_weakening. eapply R_All_e with (t:=FVar x); eauto.
   constructor. red; simpl; auto.
Qed.

Lemma thm_notexnot A : Wf th (∀A) ->
  IsTheorem Classic th (~∃~A) <-> IsTheorem Classic th (∀A).
Proof.
 intros WF.
 split; intros (_ & axs & F & P).
 - split; auto. exists axs; split; auto. now apply pr_notexnot.
 - split; auto. exists axs; split; auto. now apply pr_notexnot.
Qed.

Lemma Wf_bsubst f t :
 Wf th (∀f) -> Wf_term th t -> Wf th (bsubst 0 t f).
Proof.
 intros (CKf & BCf & FCf) (CKt & BCt & FCt).
 repeat split.
 - apply check_bsubst; auto.
 - apply Nat.le_0_r.
   apply level_bsubst; red in BCf; red in BCt; cbn in *; omega.
 - unfold FClosed in *. rewrite bsubst_fvars. namedec.
Qed.

Lemma thm_all_e logic A t : Wf_term th t ->
 IsTheorem logic th (∀A) -> IsTheorem logic th (bsubst 0 t A).
Proof.
 intros WFt (WFA & axs & F & P).
 split. apply Wf_bsubst; auto.
 exists axs. split; auto.
Qed.

Lemma thm_ex_i logic A t : Wf th (∃A) ->
 IsTheorem logic th (bsubst 0 t A) ->
 IsTheorem logic th (∃A).
Proof.
 intros WFA (_ & axs & F & P).
 split; auto.
 exists axs. split; auto.
 apply R_Ex_i with t; auto.
Qed.


Fixpoint height f :=
  match f with
  | True | False | Pred _ _ => 0
  | Not f => S (height f)
  | Op _ f1 f2 => S (Nat.max (height f1) (height f2))
  | Quant _ f => S (height f)
  end.

Lemma height_bsubst n t f :
 height (bsubst n t f) = height f.
Proof.
 revert n t.
 induction f; cbn; f_equal; auto.
Qed.

Lemma height_ind (P : formula -> Prop) :
 (forall h, (forall f, height f < h -> P f) ->
            (forall f, height f < S h -> P f)) ->
 forall f, P f.
Proof.
 intros IH f.
 set (h := S (height f)).
 assert (LT : height f < h) by (cbn; auto with * ).
 clearbody h. revert f LT.
 induction h as [|h IHh]; [inversion 1|eauto].
Qed.

Lemma interp_carac f : check th f = true -> BClosed f ->
 forall genv,
   interp_form mo genv [] f <->
     IsTheorem Classic th (closure genv f).
Proof.
 induction f as [h IH f Hf] using height_ind. destruct f; intros CK BC genv.
 - clear IH Hf. cbn.
   unfold IsTheorem. intuition.
   now exists [].
 - clear IH Hf. cbn.
   unfold IsTheorem. intuition.
   apply consistent; split; auto.
 - clear IH Hf.
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
   apply map_ext_iff in H. rewrite H. reflexivity.
 - simpl. rewrite IH; auto with arith.
   symmetry. apply complete'.
   apply closure_wf; auto.
 - cbn in *. rewrite lazy_andb_iff in CK. destruct CK as (CK1,CK2).
   red in BC. cbn in BC. apply max_0 in BC. destruct BC as (BC1,BC2).
   destruct o; simpl; rewrite !IH; auto; try omega with *.
   + apply thm_and.
   + apply thm_or. apply Op_wf. split; apply (closure_wf _ genv); auto.
   + apply thm_impl. apply Op_wf. split; apply (closure_wf _ genv); auto.
 - simpl.
   destruct q; split.
   + intros H.
     destruct (complete (closure genv (∃~f))); [apply closure_wf; auto| | ].
     * destruct (witsat (closure genv (~f)) H0) as (c & Hc & Thm).
       rewrite <- closure_bsubst in Thm by auto.
       change (closure _ _) with (~closure genv (bsubst 0 (Cst c) f))%form in Thm.
       assert (check th (bsubst 0 (Cst c) f) = true).
       { apply check_bsubst; cbn; auto. now rewrite Hc, eqb_refl. }
       assert (BClosed (bsubst 0 (Cst c) f)).
       { apply Nat.le_0_r, level_bsubst; auto.
         cbn. red in BC; cbn in BC. omega. }
       rewrite complete' in Thm by (apply closure_wf; auto).
       rewrite <- IH in Thm; auto.
       { rewrite <- interp_form_bsubst0 in Thm; auto.
         destruct Thm. apply H.
         cbn. red in BC; cbn in BC. omega. }
       { rewrite height_bsubst. cbn. cbn in Hf. omega. }
     * apply thm_notexnot; auto.
       apply (closure_wf (∀ f) genv); auto.
   + intros Thm (t,Ht).
     rewrite interp_form_bsubst0 with (u:=t).
     2:{ red in BC. cbn in BC. omega. }
     2:{ apply Wf_term_alt in Ht. apply Ht. }
     2:{ destruct (proj2 (Wf_term_alt _ _) Ht) as (CKt & BCt & FCt).
         rewrite (interp_term_carac' t genv CKt BCt).
         apply proof_irr. cbn. apply term_vmap_id. intros v.
         red in FCt. intuition. }
     apply Wf_term_alt in Ht.
     rewrite IH.
     { rewrite closure_bsubst by apply Ht.
       apply thm_all_e; auto. }
     { rewrite height_bsubst. cbn in Hf. omega. }
     { rewrite check_bsubst; auto. apply Ht. }
     { apply Nat.le_0_r. apply level_bsubst. red in BC.
       cbn in BC. omega. apply Nat.le_0_r, Ht. }
   + intros ((t,Ht),Int).
     rewrite interp_form_bsubst0 with (u:=t) in Int.
     2:{ red in BC. cbn in BC. omega. }
     2:{ clear Int.
         apply Wf_term_alt in Ht. apply Ht. }
     2:{ clear Int.
         destruct (proj2 (Wf_term_alt _ _) Ht) as (CKt & BCt & FCt).
         rewrite (interp_term_carac' t genv CKt BCt).
         apply proof_irr. cbn. apply term_vmap_id. intros v.
         red in FCt. intuition. }
     apply Wf_term_alt in Ht.
     rewrite IH in Int.
     { rewrite closure_bsubst in Int by apply Ht.
       apply thm_ex_i with t; auto.
       apply (closure_wf (∃f) genv); auto. }
     { rewrite height_bsubst. cbn in Hf. omega. }
     { rewrite check_bsubst; auto. apply Ht. }
     { apply Nat.le_0_r. apply level_bsubst. red in BC.
       cbn in BC. omega. apply Nat.le_0_r, Ht. }
   + intros Thm.
     destruct (witsat (closure genv f) Thm) as (c & Hc & Thm').
     rewrite <- closure_bsubst in Thm' by auto.
     rewrite <- IH in Thm'.
     2:{ rewrite height_bsubst. cbn in Hf. omega. }
     2:{ rewrite check_bsubst; auto. cbn. now rewrite Hc, eqb_refl. }
     2:{ apply Nat.le_0_r. apply level_bsubst. red in BC.
         cbn in BC. omega. auto. }
     exists (exist _ (Cst c) (Cst_wf' th c Hc)).
     rewrite interp_form_bsubst0; eauto.
     { red in BC. cbn in BC. omega. }
     { apply proof_irr. rewrite interp_term_carac; auto.
       cbn. now rewrite Hc, eqb_refl. }
Qed.

Lemma interp_carac_closed f genv : Wf th f ->
 interp_form mo genv [] f <-> IsTheorem Classic th f.
Proof.
 intros WF.
 replace f with (closure genv f) at 2.
 apply interp_carac; apply WF.
 apply form_vmap_id. intros v. destruct WF as (_ & _ & FC).
 red in FC. intuition.
Qed.

Lemma axioms_ok A :
  IsAxiom th A ->
  forall genv, interp_form mo genv [] A.
Proof.
 intros HA genv. apply interp_carac_closed.
 apply WfAxiom; auto.
 apply ax_thm; auto.
Qed.

Definition SyntacticModel : Model M th :=
 {| pre := mo;
    AxOk := axioms_ok |}.

End SyntacticModel.

Lemma premodel_restrict sign sign' M :
 SignExtend sign sign' ->
 PreModel M sign' -> PreModel M sign.
Proof.
 intros SE mo.
 set (fs := fun f => match sign.(funsymbs) f with
                     | None => None
                     | _ => mo.(funs) f
                     end).
 set (ps := fun f => match sign.(predsymbs) f with
                     | None => None
                     | _ => mo.(preds) f
                     end).
 apply Build_PreModel with fs ps.
 - exact mo.(someone).
 - intros f. unfold fs.
   generalize (mo.(funsOk) f).
   destruct SE as (SE,_). unfold optfun_finer,opt_finer in SE.
   destruct (SE f) as [-> | ->]; auto.
   destruct (funsymbs sign' f); auto.
 - intros p. unfold ps.
   generalize (mo.(predsOk) p).
   destruct SE as (_,SE). unfold optfun_finer,opt_finer in SE.
   destruct (SE p) as [-> | ->]; auto.
   destruct (predsymbs sign' p); auto.
Defined.

Lemma interp_term_restrict sign sign' M
 (mo:PreModel M sign')(SE:SignExtend sign sign') :
 forall genv lenv t, check sign t = true ->
  interp_term (premodel_restrict sign sign' M SE mo) genv lenv t =
  interp_term mo genv lenv t.
Proof.
 induction t as [ | | f args IH ] using term_ind'; cbn; auto.
 destruct (funsymbs sign f); [|easy].
 case eqbspec; [|easy]. intros _ F.
 destruct (funs mo f) as [(n,ar)|]; auto.
 f_equal. apply map_ext_iff. intros t Ht.
 apply IH; auto. rewrite forallb_forall in F; auto.
Qed.

Lemma interp_form_restrict sign sign' M
 (mo:PreModel M sign')(SE:SignExtend sign sign') :
 forall genv lenv f, check sign f = true ->
  interp_form (premodel_restrict sign sign' M SE mo) genv lenv f <->
  interp_form mo genv lenv f.
Proof.
 intros genv lenv f; revert genv lenv.
 induction f; cbn; intros genv lenv Hf; f_equal;
 try (rewrite lazy_andb_iff in Hf; destruct Hf); try reflexivity.
 - destruct (predsymbs sign p); [|easy].
   rewrite lazy_andb_iff in Hf. destruct Hf as (_,Hf).
   destruct (preds mo p) as [(n,ar)|]; [|reflexivity].
   f_equiv. apply map_ext_iff. intros t Ht.
   apply interp_term_restrict. rewrite forallb_forall in Hf; auto.
 - now rewrite IHf.
 - destruct o; simpl; rewrite IHf1, IHf2; intuition.
 - destruct q; simpl; split.
   + intros H m. apply IHf; auto.
   + intros H m. apply IHf; auto.
   + intros (m,H). exists m. apply IHf; auto.
   + intros (m,H). exists m. apply IHf; auto.
Qed.

Lemma model_restrict logic th th' M :
 CoqRequirements logic ->
 Extend logic th th' -> Model M th' -> Model M th.
Proof.
 intros CR (SE,EX) mo.
 apply Build_Model with (premodel_restrict th th' M SE mo).
 intros A HA genv.
 rewrite interp_form_restrict by (apply WfAxiom; auto).
 assert (Thm : IsTheorem logic th' A).
 { apply EX, ax_thm; auto. }
 apply (validity_theorem logic th' CR A Thm M mo).
Defined.

Lemma consistent_has_model (th:theory) (nc : NewCsts th) :
 (forall A, A\/~A) ->
 Consistent Classic th ->
 { M & Model M th }.
Proof.
 intros EM C.
 set (th' := supercomplete Classic th nc).
 exists (closed_term th').
 apply (model_restrict Classic th th'). red; intros; apply EM.
 apply supercomplete_extend.
 apply SyntacticModel with (oneconst := nc 0).
 - apply supercomplete_consistent; auto.
 - apply supercomplete_complete; auto. red; intros; apply EM.
 - apply supercomplete_saturated; auto.
 - unfold th'. cbn.
   replace (test th nc (nc 0)) with true; auto.
   symmetry. apply test_ok. now exists 0.
Qed.

(** Stdlib [proj1] is opaque ! *)

Definition proj1' {A B:Prop} (c:A/\B) : A :=
 let '(conj a _) := c in a.

Lemma completeness_theorem (th:theory) (nc : NewCsts th) :
 (forall A, A\/~A) ->
 forall T,
   Wf th T ->
   (forall M (mo : Model M th) genv, interp_form mo genv [] T)
   -> IsTheorem Classic th T.
Proof.
 intros EM T WF HT.
 destruct (EM (IsTheorem Classic th T)) as [Thm|NT]; auto.
 exfalso.
 assert (WF' : forall A, A = (~T)%form \/ IsAxiom th A -> Wf th A).
 { intros A [->|HA]; auto using WfAxiom. }
 set (th' := {| sign := th;
                IsAxiom := fun f => f = (~T)%form \/ IsAxiom th f;
                WfAxiom := WF' |}).
 assert (nc' : NewCsts th').
 { apply (Build_NewCsts th')
   with (csts:=csts _ nc) (test:=test _ nc).
   - apply csts_inj.
   - intros. cbn. apply csts_ok.
   - apply test_ok. }
 assert (C : Consistent Classic th').
 { intros (_ & axs & F & P).
   set (axs' := filter (fun f => negb (f =? (~T)%form)) axs).
   apply NT; split; auto.
   exists axs'. split.
   - rewrite Forall_forall in *. intros A.
     unfold axs'. rewrite filter_In, negb_true_iff, eqb_neq.
     intros (HA,NE). destruct (F A HA); intuition.
   - apply R_Absu; auto.
     eapply Pr_weakening; eauto. constructor.
     intros A; simpl. unfold axs'.
     rewrite filter_In, negb_true_iff, eqb_neq.
     case (eqbspec A (~T)%form); intuition. }
 destruct (consistent_has_model th' nc' EM) as (M,mo); auto.
 assert (EX : Extend Classic th th').
 { apply extend_alt. split.
   - cbn. apply signext_refl.
   - intros B HB. apply ax_thm. cbn. now right. }
 set (mo' := model_restrict Classic th th' M EM EX mo).
 set (genv := fun (_:variable) => mo.(someone)).
 assert (interp_form mo genv [] (~T)).
 { apply AxOk. cbn. now left. }
 cbn in H. apply H. clear H.
 set (SE := let (p,_) := EX in p).
 assert (U := interp_form_restrict th th' M mo SE genv [] T).
 change (sign th') with (sign th) in U at 2.
 rewrite <- U by (apply WF).
 assert (E : pre _ _ mo' = premodel_restrict th th' M SE mo).
 { unfold mo'; cbn. unfold model_restrict. cbn. now destruct EX. }
 rewrite <- E.
 apply HT.
Qed.
