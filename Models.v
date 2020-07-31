
(** * Models of theories *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Eqdep_dec Defs Mix NameProofs Meta.
Require Import Wellformed Theories NaryFunctions Nary PreModels.
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
 destruct Thm as (WF & d & axs & ((CK & BC) & V) & F & C).
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


Definition wcterm sign :=
 { t : term | wc sign t = true }.

Lemma proof_irr sign (s s' : wcterm sign) :
 s = s' <-> proj1_sig s = proj1_sig s'.
Proof.
 destruct s, s'. cbn. split.
 - now injection 1.
 - intros <-. f_equal.
   destruct (wc sign x); [|easy].
   rewrite UIP_refl_bool. apply UIP_refl_bool.
Qed.

Section SyntacticPreModel.
Variable logic : Defs.logic.
Variable th : theory.
Variable oneconst : string.
Hypothesis Honeconst : th.(funsymbs) oneconst = Some 0.

Let M := wcterm th.

Lemma cons_ok (t : term) (l : list term) n :
 wc th t = true ->
 length l = n /\ Forall (WC th) l ->
 length (t::l) = S n /\ Forall (WC th) (t::l).
Proof.
 intros WF (L,F).
 apply term_wc_iff in WF.
 split; simpl; auto.
Qed.

Definition sized_wc_listterm n :=
  {l : list term | length l = n /\ Forall (WC th) l}.

Fixpoint mk_args n : M^^n --> sized_wc_listterm n :=
 match n with
 | 0 => exist _ [] (conj eq_refl (Forall_nil _))
 | S n => fun t =>
          nfun_to_nfun (fun '(exist _ l Hl) =>
                       let '(exist _ t Ht) := t in
                       exist _ (t::l) (cons_ok t l n Ht Hl))
                    (mk_args n)
 end.

Definition one_listterm n : sized_wc_listterm n.
Proof.
 induction n as [|n (l & L & F)].
 - now exists [].
 - exists (Cst oneconst :: l).
   split; simpl; auto using Cst_WC.
Qed.

Lemma build_mk n (l : list M) (any:sized_wc_listterm n) :
 length l = n ->
 proj1_sig (build_args l any (mk_args n)) =
 map (@proj1_sig _ _) l.
Proof.
 intros <-.
 induction l as [|(t,Ht) l IH]; simpl; auto.
 set (l0 := one_listterm (length l)).
 rewrite build_args_ntn  with (any0:=l0); auto.
 specialize (IH l0).
 destruct (build_args _); simpl in *. f_equal; auto.
Qed.

Definition fun_core f n :
  (th.(funsymbs) f = Some n) -> M^^n-->M.
Proof.
 intros E.
 generalize (mk_args n).
 apply nfun_to_nfun. intros (l & Hl).
 exists (Fun f l). apply term_wc_iff, Fun_WC; destruct Hl; subst; auto.
Defined.

Definition rich_funs f :
  { o : optnfun M M |
    th.(funsymbs) f = get_arity o /\
    match o with
    | Nop => Logic.True
    | NFun n a =>
      forall (l: list M)(any : M), length l = n ->
        proj1_sig (build_args l any a) =
        Fun f (map (@proj1_sig _ _) l)
    end }.
Proof.
 destruct (th.(funsymbs) f) as [n|] eqn:E.
 - set (r := fun_core f n E).
   exists (NFun _ r); split; auto.
   intros l any Hl.
   unfold r, fun_core.
   rewrite build_args_ntn with (any0 := one_listterm n); auto.
   rewrite <- (build_mk n l (one_listterm n) Hl).
   destruct build_args. now cbn.
 - now exists Nop.
Defined.

Definition mk_funs : string -> optnfun M M :=
  fun f => proj1_sig (rich_funs f).

Lemma mk_funs_ok f : th.(funsymbs) f = get_arity (mk_funs f).
Proof.
 unfold mk_funs. now destruct (rich_funs f).
Qed.

Definition mk_preds : string -> optnfun M Prop.
Proof.
 intro p.
 destruct (th.(predsymbs) p) as [n|].
 - apply (NFun n).
   generalize (mk_args n).
   apply nfun_to_nfun.
   exact (fun sl => IsTheorem logic th (Pred p (proj1_sig sl))).
 - apply Nop.
Defined.

Lemma mk_preds_ok p : th.(predsymbs) p = get_arity (mk_preds p).
Proof.
 unfold mk_preds.
 now destruct (th.(predsymbs) p) as [n|].
Qed.

Definition SyntacticPreModel : PreModel M th :=
 {| someone := exist _ (Cst oneconst) (Cst_wc _ _ Honeconst);
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

Let M := wcterm th.
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
   apply term_wc_iff in Ht. apply Ht.
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
   apply term_wc_iff in Ht. apply Ht.
 - revert l. fix IH' 1. destruct l as [|t l]; cbn; auto.
   f_equal. apply IH. apply IH'.
Qed.

Lemma term_closure_fclosed t (genv:variable->M) :
  FClosed (term_closure genv t).
Proof.
 induction t using term_ind'; cbn; auto.
 - destruct (genv v) as (t,Ht); cbn; auto.
   apply term_wc_iff in Ht. apply Ht.
 - change (FClosed (Fun f (map (term_closure genv) args))).
   rewrite <- term_fclosed_spec. cbn.
   apply forallb_forall. intros a Ha. rewrite term_fclosed_spec.
   rewrite in_map_iff in Ha. destruct Ha as (x & <- & IN); auto.
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
 - change (FClosed (Pred p (map (term_closure genv) l))).
   rewrite <- form_fclosed_spec. cbn.
   apply forallb_forall. intros a Ha. rewrite term_fclosed_spec.
   rewrite in_map_iff in Ha.
   destruct Ha as (x & <- & IN); auto using term_closure_fclosed.
 - rewrite <- form_fclosed_spec in *. cbn. now rewrite lazy_andb_iff.
Qed.

Lemma term_closure_wc t genv :
  WF th t -> WC th (term_closure genv t).
Proof.
 intros (?,?). repeat split.
 - now rewrite term_closure_check.
 - red. now rewrite term_closure_level.
 - apply term_closure_fclosed.
Qed.

Lemma term_closure_wc' t genv :
  WF th t -> wc th (term_closure genv t) = true.
Proof.
 intro. apply term_wc_iff. now apply term_closure_wc.
Qed.

Lemma closure_wc f genv :
  WF th f -> WC th (closure genv f).
Proof.
 intros (?,?). repeat split.
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
 apply term_wc_iff in Hu. apply Hu.
Qed.

Lemma interp_pred p l :
 WF th (Pred p l) ->
 forall genv,
   interp_form mo genv [] (Pred p l) <->
   IsTheorem Classic th
     (Pred p (map (fun t => proj1_sig (interp_term mo genv [] t)) l)).
Proof.
 unfold WF, BClosed. cbn.
 destruct (predsymbs th p) as [n|] eqn:E; [|easy].
 rewrite lazy_andb_iff, eqb_eq. intros ((L,CK),BC) genv.
 unfold mk_preds; rewrite E. cbn. clear E.
 set (l0 := one_listterm th oneconst Honeconst n).
 rewrite build_args_ntn with (any := l0) by now rewrite map_length.
 rewrite build_mk with (oneconst := oneconst) by (auto; now rewrite map_length).
 rewrite map_map; reflexivity.
Qed.

Lemma interp_term_carac t :
  WF th t ->
  forall genv,
    proj1_sig (interp_term mo genv [] t) = term_closure genv t.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 - now unfold WF,BClosed.
 - unfold WF. cbn. destruct (funsymbs th f) as [n|] eqn:E; [|easy].
   rewrite lazy_andb_iff, eqb_eq.
   intros ((L,CK),BC) genv.
   unfold mk_funs.
   destruct rich_funs as ([n' a| ] & Ho & Ho'); cbn in *.
   2: congruence.
   assert (Hn : n' = n) by congruence.
   subst n'.
   rewrite Ho' by now rewrite map_length.
   clear Ho Ho'.
   rewrite map_map.
   f_equal. apply map_ext_iff.
   intros t Ht. apply IH; auto. split.
   + rewrite forallb_forall in CK; auto.
   + red in BC. cbn in BC. rewrite list_max_map_0 in BC; auto.
Qed.

Lemma interp_term_carac' (t:term) genv (W : WF th t) :
  interp_term mo genv [] t =
  exist _ (term_closure genv t) (term_closure_wc' t genv W).
Proof.
 apply proof_irr. cbn. now apply interp_term_carac.
Qed.

Lemma complete' A : WC th A ->
 IsTheorem Classic th (~A) <-> ~IsTheorem Classic th A.
Proof.
 split.
 - intros Thm' Thm. apply consistent.
   apply Thm_Not_e with A; auto.
 - destruct (complete A); trivial. now intros [ ].
Qed.

Lemma Thm_Or A B : WC th (A\/B) ->
  IsTheorem Classic th A \/ IsTheorem Classic th B <->
  IsTheorem Classic th (A \/ B).
Proof.
 intros WF.
 split.
 - now apply Thm_or_i.
 - intros (_ & axs & F & Por); rewrite Op_WC in WF.
   destruct (complete A) as [HA|HA]; [easy|now left|].
   destruct HA as (_ & axsA & FA & PnA).
   destruct (complete B) as [HB|HB]; [easy|now right|].
   destruct HB as (_ & axsB & FB & PnB).
   destruct consistent.
   split. apply False_WC.
   exists (axs++axsA++axsB). split; [now rewrite !Forall_app|].
   apply R_Or_e with A B.
   + now apply Pr_app_l.
   + eapply R_Not_e; [apply R'_Ax|].
     now apply Pr_pop, Pr_app_r, Pr_app_l.
   + eapply R_Not_e; [apply R'_Ax|].
     now apply Pr_pop, Pr_app_r, Pr_app_r.
Qed.

Lemma Thm_Imp A B : WC th (A->B) ->
  (IsTheorem Classic th A -> IsTheorem Classic th B) <->
  IsTheorem Classic th (A -> B).
Proof.
 intros W. split; try apply Thm_Imp_e.
 intros IM.
 destruct (complete A) as [HA|HA]; [rewrite Op_WC in W; easy | | ].
 - destruct (IM HA) as (_ & axs & F & P). split; auto.
   exists axs; split; auto.
   apply R_Imp_i. now apply Pr_pop.
 - destruct HA as (_ & axs & F & P). split; auto.
   exists axs; split; auto.
   apply R_Imp_i.
   apply R_Fa_e.
   eapply R_Not_e; [apply R'_Ax|]. now apply Pr_pop.
Qed.

Lemma pr_notex_allnot logic c A :
 Pr logic (c ⊢ ~∃A) <-> Pr logic (c ⊢ ∀~A).
Proof.
 destruct (exist_fresh (fvars (c ⊢ A))) as (x,Hx).
 split.
 - intros NE.
   apply R_All_i with x; cbn - [Names.union] in *. namedec.
   apply R_Not_i.
   apply R_Not_e with (∃A)%form; [|now apply Pr_pop].
   apply R_Ex_i with (FVar x); auto using R'_Ax.
 - intros AN.
   apply R_Not_i.
   apply R'_Ex_e with x. cbn in *. namedec.
   eapply R_Not_e; [apply R'_Ax|].
   apply Pr_pop. now apply R_All_e with (t:=FVar x) in AN.
Qed.

Lemma pr_notexnot c A :
 Pr Classic (c ⊢ ~∃~A) <-> Pr Classic (c ⊢ ∀A).
Proof.
 destruct (exist_fresh (fvars (c ⊢ A))) as (x,Hx).
 split.
 - intros NEN.
   apply R_All_i with x; cbn - [Names.union] in *. namedec.
   apply R_Absu; auto.
   apply R_Not_e with (∃~A)%form; [|now apply Pr_pop].
   apply R_Ex_i with (FVar x); auto using R'_Ax.
 - intros ALL.
   apply R_Not_i.
   apply R'_Ex_e with x; cbn in *. namedec.
   eapply R_Not_e; [|eapply R'_Ax].
   apply Pr_pop. eapply R_All_e with (t:=FVar x); eauto.
Qed.

Lemma thm_notexnot A : WC th (∀A) ->
  IsTheorem Classic th (~∃~A) <-> IsTheorem Classic th (∀A).
Proof.
 intros WF.
 split; intros (_ & axs & F & P); split; auto; exists axs; split; auto.
 - now apply pr_notexnot.
 - now apply pr_notexnot.
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

Lemma interp_carac f : WF th f ->
 forall genv,
   interp_form mo genv [] f <->
     IsTheorem Classic th (closure genv f).
Proof.
 induction f as [h IH f Hf] using height_ind. destruct f; intros W genv.
 - clear IH Hf. cbn.
   unfold IsTheorem. intuition.
   now exists [].
 - clear IH Hf. cbn.
   unfold IsTheorem. intuition.
   apply consistent; split; auto.
 - clear IH Hf.
   rewrite interp_pred; auto. simpl.
   unfold vmap, vmap_list.
   f_equiv. f_equiv. apply map_ext_iff. intros t Ht.
   apply interp_term_carac. revert t Ht. apply Forall_forall.
   now apply Pred_WF in W.
 - simpl. rewrite IH; auto with arith.
   symmetry. apply complete'.
   apply closure_wc; auto.
 - apply Op_WF in W. cbn in Hf. apply Nat.succ_lt_mono in Hf.
   apply max_lt in Hf.
   destruct o; simpl; rewrite !IH by easy.
   + apply Thm_And.
   + apply Thm_Or. apply Op_WC. split; now apply closure_wc.
   + apply Thm_Imp. apply Op_WC. split; now apply closure_wc.
 - simpl.
   cbn in Hf. apply Nat.succ_lt_mono in Hf.
   assert (L : level f <= 1).
   { unfold WF,BClosed in W. cbn in W. omega. }
   assert (Hf' : forall t, height (bsubst 0 t f) < h).
   { intro. now rewrite height_bsubst. }
   destruct q; split.
   + intros H.
     destruct (complete (closure genv (∃~f))); [apply closure_wc; auto| | ].
     * destruct (witsat (closure genv (~f)) H0) as (c & Hc & Thm).
       rewrite <- closure_bsubst in Thm by auto.
       change (closure _ _) with (~closure genv (bsubst 0 (Cst c) f))%form
        in Thm.
       assert (WF th (bsubst 0 (Cst c) f)).
       { split.
         - apply check_bsubst; cbn; auto. now rewrite Hc, eqb_refl.
           apply W.
         - apply Nat.le_0_r, level_bsubst; auto. }
       rewrite complete' in Thm by (apply closure_wc; auto).
       rewrite <- IH in Thm; auto.
       rewrite <- interp_form_bsubst0 in Thm; auto. destruct Thm. apply H.
     * apply thm_notexnot; auto. apply (closure_wc (∀ f) genv); auto.
   + intros Thm (t,Ht).
     rewrite interp_form_bsubst0 with (u:=t); auto.
     2:{ apply term_wc_iff in Ht. apply Ht. }
     2:{ destruct (proj2 (term_wc_iff _ _) Ht) as (W',F').
         rewrite (interp_term_carac' t genv W').
         apply proof_irr. cbn. apply term_vmap_id. intros v.
         red in F'. intuition. }
     apply term_wc_iff in Ht.
     rewrite IH; auto.
     * rewrite closure_bsubst by apply Ht. apply Thm_All_e; auto.
     * apply bsubst_WF; auto. apply Ht.
   + intros ((t,Ht),Int).
     rewrite interp_form_bsubst0 with (u:=t) in Int; auto.
     2:{ clear Int. apply term_wc_iff in Ht. apply Ht. }
     2:{ clear Int.
         destruct (proj2 (term_wc_iff _ _) Ht) as (W',F').
         rewrite (interp_term_carac' t genv W').
         apply proof_irr. cbn. apply term_vmap_id. intros v.
         red in F'. intuition. }
     apply term_wc_iff in Ht.
     rewrite IH in Int; auto.
     * rewrite closure_bsubst in Int by apply Ht.
       apply Thm_Ex_i with t; auto.
       apply (closure_wc (∃f) genv); auto.
     * apply bsubst_WF; auto. apply Ht.
   + intros Thm.
     destruct (witsat (closure genv f) Thm) as (c & Hc & Thm').
     rewrite <- closure_bsubst in Thm' by auto.
     rewrite <- IH in Thm'.
     2:{ now rewrite height_bsubst. }
     2:{ apply bsubst_WF; auto. now apply Cst_WC. }
     exists (exist _ (Cst c) (Cst_wc th c Hc)).
     rewrite interp_form_bsubst0; eauto.
     apply proof_irr. rewrite interp_term_carac; auto. now apply Cst_WC.
Qed.

Lemma interp_carac_closed f genv : WC th f ->
 interp_form mo genv [] f <-> IsTheorem Classic th f.
Proof.
 intros W.
 replace f with (closure genv f) at 2.
 apply interp_carac. apply W.
 apply form_vmap_id. intros v. destruct W as (_,F).
 red in F. intuition.
Qed.

Lemma axioms_ok A :
  IsAxiom th A ->
  forall genv, interp_form mo genv [] A.
Proof.
 intros HA genv. apply interp_carac_closed.
 apply WCAxiom; auto.
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
                     | None => Nop
                     | _ => mo.(funs) f
                     end).
 set (ps := fun f => match sign.(predsymbs) f with
                     | None => Nop
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
 f_equiv. apply map_ext_iff. intros t Ht.
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
 rewrite interp_form_restrict by (apply WCAxiom; auto).
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
 exists (wcterm th').
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
   WC th T ->
   (forall M (mo : Model M th) genv, interp_form mo genv [] T)
   -> IsTheorem Classic th T.
Proof.
 intros EM T WF HT.
 destruct (EM (IsTheorem Classic th T)) as [Thm|NT]; auto.
 exfalso.
 assert (WC' : forall A, A = (~T)%form \/ IsAxiom th A -> WC th A).
 { intros A [->|HA]; auto using WCAxiom. }
 set (th' := {| sign := th;
                IsAxiom := fun f => f = (~T)%form \/ IsAxiom th f;
                WCAxiom := WC' |}).
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
