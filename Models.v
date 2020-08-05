
(** * Models of theories *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Eqdep_dec Defs Mix NameProofs Toolbox Meta ProofExamples.
Require Import Wellformed Theories NaryFunctions Nary PreModels.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

(** We'll frequently consider interpretations of formulas over all
    possible global environments, so here's a convenient shortcut *)

Definition interp {sign M} (mo : PreModel M sign) A :=
  forall G, finterp mo G [] A.

(** A Model is a PreModel that satisfies all the axioms of the theory. *)

Record Model (M:Type)(th : theory) :=
 { pre :> PreModel M th;
   AxOk : forall A, IsAxiom th A -> interp pre A }.

Lemma validity_theorem logic th :
 CoqRequirements logic ->
 forall T, IsTheorem logic th T ->
 forall M (mo : Model M th), interp mo T.
Proof.
 intros CR T Thm M mo G.
 rewrite thm_alt in Thm.
 destruct Thm as (WF & d & axs & ((CK & BC) & V) & F & C).
 assert (CO:=@correctness th M mo logic d CR V BC G).
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

Record cterm sign :=
  { this :> term;
    closed : wc sign this = true }.

Arguments this {sign}.

Lemma proof_irr sign (s s' : cterm sign) :
 s = s' <-> s.(this) = s'.(this).
Proof.
 destruct s as (t,w), s' as (t',w'). cbn. split.
 - now injection 1.
 - intros <-. f_equal.
   destruct (wc sign t); [|easy].
   rewrite UIP_refl_bool. apply UIP_refl_bool.
Qed.

Section SyntacticPreModel.
Variable th : theory.
Variable oneconst : string.
Hypothesis Honeconst : th.(funsymbs) oneconst = Some 0.

Let M := cterm th.

Definition oneM :=
  {| this := Cst oneconst;
     closed := Cst_wc _ _ Honeconst |}.

Lemma cons_ok n (t : cterm th) (v : term^n) :
 Forall (WC th) (nprod_to_list v) ->
 Forall (WC th) (nprod_to_list (n:=S n) (t.(this),v)).
Proof.
 intros W. cbn. constructor; auto. apply term_wc_iff, closed.
Qed.

(** [these] : convert to list + repeat the [this] projection to terms *)
Definition these {n} (v:M^n) := map this (nprod_to_list v).

Lemma closed_fun f n (v:M^n) :
 funsymbs th f = Some n ->
 wc th (Fun f (these v)) = true.
Proof.
 intros E.
 rewrite <- term_wc_iff, Fun_WC.
 unfold these. rewrite map_length, nprod_to_list_length.
 split; trivial.
 clear E.
 revert v.
 induction n; destruct v; cbn; constructor; auto.
 apply term_wc_iff, closed.
Qed.

(** Note : the decidability on [option nat] below is mainly to avoid
    some mess in dependent equality. It's morally always [left E]. *)
Definition syntactic_fun f n (v:M^n) : M :=
  match option_nat_dec (funsymbs th f) (Some n) with
  | left E => {| this := Fun f (these v); closed := closed_fun f n v E |}
  | right _ => oneM
  end.

Definition syntactic_pred p n (v:M^n) : Prop :=
  IsTheorem K th (Pred p (these v)).

Definition mkfuns f : optnfun M M :=
 match funsymbs th f with
 | Some n => NFun n (ncurry (syntactic_fun f n))
 | None => Nop
 end.

Definition mkpreds p : optnfun M Prop :=
 match predsymbs th p with
 | Some n => NFun n (ncurry (syntactic_pred p n))
 | None => Nop
 end.

Lemma mkfuns_ok f : funsymbs th f = get_arity (mkfuns f).
Proof.
 unfold mkfuns. now destruct (funsymbs th f).
Qed.

Lemma syntactic_fun_some f n (v:M^n) : funsymbs th f = Some n ->
 this (syntactic_fun f n v) = Fun f (these v).
Proof.
 unfold syntactic_fun. intros E.
 destruct option_nat_dec as [|[ ]]; auto.
Qed.

Lemma mkpreds_ok p : predsymbs th p = get_arity (mkpreds p).
Proof.
 unfold mkpreds. now destruct predsymbs.
Qed.

Definition SyntacticPreModel : PreModel M th :=
 {| someone := oneM;
    funs := mkfuns;
    preds := mkpreds;
    funsOk := mkfuns_ok;
    predsOk := mkpreds_ok |}.

End SyntacticPreModel.

Section SyntacticModel.
Variable th : theory.
Hypothesis consistent : Consistent K th.
Hypothesis complete : Complete K th.
Hypothesis witsat : WitnessSaturated K th.
Variable oneconst : string.
Hypothesis Honeconst : th.(funsymbs) oneconst = Some 0.

Let M := cterm th.

Let mo : PreModel M th := SyntacticPreModel th oneconst Honeconst.

Implicit Types G : variable -> M.
Implicit Types t : term.
Implicit Types A : formula.

Definition closure {T}`{VMap T} G : T -> T := vmap G.

Lemma tclosure_check G t :
  check th (closure G t) = check th t.
Proof.
 induction t using term_ind'; cbn; auto.
 - destruct G as (t,Ht); cbn; auto. apply term_wc_iff in Ht. apply Ht.
 - rewrite map_length.
   destruct (funsymbs th f); [|easy].
   case eqb; [|easy].
   rewrite forallb_map. now apply forallb_ext.
Qed.

Lemma tclosure_level G t :
  level (closure G t) = level t.
Proof.
 induction t using term_ind'; cbn; auto.
 - destruct G as (t,Ht); cbn; auto. apply term_wc_iff in Ht. apply Ht.
 - rewrite map_map. now apply list_max_map_ext.
Qed.

Lemma tclosure_fclosed G t : FClosed (closure G t).
Proof.
 induction t using term_ind'; cbn; auto.
 - destruct G as (t,Ht); cbn; auto. apply term_wc_iff in Ht. apply Ht.
 - rewrite <- term_fclosed_spec. cbn.
   rewrite forallb_map.
   apply forallb_forall. now setoid_rewrite term_fclosed_spec.
Qed.

Lemma fclosure_check G A :
 check th (closure G A) = check th A.
Proof.
 induction A; cbn; auto.
 - rewrite map_length.
   destruct predsymbs; [|easy].
   case eqb; [|easy].
   rewrite forallb_map. apply forallb_ext. intros x _.
   apply tclosure_check.
 - now rewrite IHA1, IHA2.
Qed.

Lemma fclosure_level G A :
  level (closure G A) = level A.
Proof.
 induction A; cbn; auto.
 revert l. induction l as [|t l IH]; cbn; auto.
 f_equal; auto. apply tclosure_level.
Qed.

Lemma fclosure_fclosed G A :
  FClosed (closure G A).
Proof.
 induction A; cbn; auto.
 - change (FClosed (Pred p (map (closure G) l))).
   rewrite <- form_fclosed_spec. cbn.
   rewrite forallb_map.
   apply forallb_forall. intros x _. rewrite term_fclosed_spec.
   apply tclosure_fclosed.
 - rewrite <- form_fclosed_spec in *. cbn. now rewrite lazy_andb_iff.
Qed.

Lemma tclosure_wc G t:
  WF th t -> WC th (closure G t).
Proof.
 intros (?,?). repeat split.
 - now rewrite tclosure_check.
 - red. now rewrite tclosure_level.
 - apply tclosure_fclosed.
Qed.

Lemma tclosure_wc' G t :
  WF th t -> wc th (closure G t) = true.
Proof.
 intro. apply term_wc_iff. now apply tclosure_wc.
Qed.

Lemma fclosure_wc G A :
  WF th A -> WC th (closure G A).
Proof.
 intros (?,?). repeat split.
 - now rewrite fclosure_check.
 - red. now rewrite fclosure_level.
 - apply fclosure_fclosed.
Qed.

Lemma fclosure_bsubst G n t A :
 FClosed t ->
 closure G (bsubst n t A) = bsubst n t (closure G A).
Proof.
 unfold closure.
 intros FC.
 rewrite form_vmap_bsubst.
 f_equal.
 rewrite term_vmap_id; auto.
 intros v. red in FC. intuition.
 intros v. destruct G as (u,Hu); simpl.
 apply term_wc_iff in Hu. apply Hu.
Qed.

Lemma interp_pred p l :
 WF th (Pred p l) ->
 forall G,
   finterp mo G [] (Pred p l) <->
   IsTheorem K th
     (Pred p (map (fun t => this (tinterp mo G [] t)) l)).
Proof.
 rewrite Pred_WF. intros (E,F) G.
 cbn. unfold mkpreds. rewrite E.
 set (n := length l) in *.
 unfold napply_dft, optnapply.
 destruct optnprod as [a|] eqn:E'.
 2:{ exfalso. revert E'. apply optnprod_some. now rewrite map_length. }
 cbn. rewrite nuncurry_ncurry. unfold syntactic_pred. f_equiv.
 f_equal. unfold these.
 apply optnprod_to_list in E'. fold M. now rewrite E', map_map.
Qed.

Lemma tinterp_carac t :
 WF th t ->
 forall G, this (tinterp mo G [] t) = closure G t.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 - now rewrite wf_iff.
 - rewrite Fun_WF. intros (E,F) G.
   set (n := length l) in *.
   unfold napply_dft, optnapply.
   unfold mkfuns. rewrite E.
   destruct optnprod as [a|] eqn:E'.
   2:{ exfalso. revert E'. apply optnprod_some. now rewrite map_length. }
   cbn.
   rewrite nuncurry_ncurry.
   rewrite syntactic_fun_some; auto.
   f_equal. unfold these.
   apply optnprod_to_list in E'. fold M. rewrite E', map_map.
   apply map_ext_iff. intros x Hx. apply IH; auto.
   revert x Hx. now apply Forall_forall.
Qed.

Lemma tinterp_carac' (t:term) G (W : WF th t) :
  tinterp mo G [] t =
  {| this := closure G t; closed := tclosure_wc' G t W |}.
Proof.
 apply proof_irr. cbn. now apply tinterp_carac.
Qed.

(** For a consistent and complete theory, [IsTheorem] has some nice
    extra properties : *)

Lemma Thm_Not A : WC th A ->
 IsTheorem K th (~A) <-> ~IsTheorem K th A.
Proof.
 split.
 - intros Thm' Thm. apply consistent.
   apply Thm_Not_e with A; auto.
 - destruct (complete A); trivial. now intros [ ].
Qed.

Lemma Thm_Or A B : WC th (A\/B) ->
  IsTheorem K th A \/ IsTheorem K th B <->
  IsTheorem K th (A \/ B).
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
  (IsTheorem K th A -> IsTheorem K th B) <->
  IsTheorem K th (A -> B).
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

Lemma interp_carac A : WF th A ->
 forall G, finterp mo G [] A <-> IsTheorem K th (closure G A).
Proof.
 induction A as [h IH A HA] using height_ind. destruct A; intros W G.
 - clear IH HA. cbn.
   unfold IsTheorem. intuition.
   now exists [].
 - clear IH HA. cbn.
   unfold IsTheorem. intuition.
   apply consistent; split; auto.
 - clear IH HA.
   rewrite interp_pred; auto. f_equiv. cbn. f_equiv.
   apply map_ext_iff. intros t Ht.
   apply tinterp_carac. revert t Ht. apply Forall_forall.
   now apply Pred_WF in W.
 - simpl. rewrite IH; auto with arith.
   symmetry. apply Thm_Not.
   apply fclosure_wc; auto.
 - assert (W' := fclosure_wc G _ W).
   apply Op_WF in W.
   cbn in HA. apply Nat.succ_lt_mono in HA. apply max_lt in HA.
   destruct o; simpl; rewrite !IH by easy.
   + apply Thm_And.
   + now apply Thm_Or.
   + now apply Thm_Imp.
 - simpl.
   cbn in HA. apply Nat.succ_lt_mono in HA.
   assert (L : level A <= 1).
   { unfold WF,BClosed in W. cbn in W. omega. }
   assert (HA' : forall t, height (bsubst 0 t A) < h).
   { intro. now rewrite height_bsubst. }
   destruct q; split.
   + intros H.
     destruct (complete (closure G (∃~A)%form));
      [apply fclosure_wc; auto| | ].
     * destruct (witsat (closure G (~A)%form) H0) as (c & Hc & Thm).
       rewrite <- fclosure_bsubst in Thm by auto.
       change (closure _ _) with (~closure G (bsubst 0 (Cst c) A))%form
        in Thm.
       assert (WF th (bsubst 0 (Cst c) A)).
       { split.
         - apply check_bsubst; cbn; auto. now rewrite Hc, eqb_refl.
           apply W.
         - apply Nat.le_0_r, level_bsubst; auto. }
       rewrite Thm_Not in Thm by (apply fclosure_wc; auto).
       rewrite <- IH in Thm; auto.
       rewrite <- finterp_bsubst0 in Thm; auto. destruct Thm. apply H.
     * cbn. apply Thm_NotExNot; auto. apply (fclosure_wc _ (∀A)); auto.
   + intros Thm (t,Ht).
     rewrite finterp_bsubst0 with (u:=t); auto.
     2:{ apply term_wc_iff in Ht. apply Ht. }
     2:{ destruct (proj2 (term_wc_iff _ _) Ht) as (W',F').
         rewrite (tinterp_carac' t G W').
         apply proof_irr. cbn. apply term_vmap_id. intros v.
         red in F'. intuition. }
     apply term_wc_iff in Ht.
     rewrite IH; auto.
     * rewrite fclosure_bsubst by apply Ht. apply Thm_All_e; auto.
     * apply bsubst_WF; auto. apply Ht.
   + intros ((t,Ht),Int).
     rewrite finterp_bsubst0 with (u:=t) in Int; auto.
     2:{ clear Int. apply term_wc_iff in Ht. apply Ht. }
     2:{ clear Int.
         destruct (proj2 (term_wc_iff _ _) Ht) as (W',F').
         rewrite (tinterp_carac' t G W').
         apply proof_irr. cbn. apply term_vmap_id. intros v.
         red in F'. intuition. }
     apply term_wc_iff in Ht.
     rewrite IH in Int; auto.
     * rewrite fclosure_bsubst in Int by apply Ht.
       apply Thm_Ex_i with t; auto.
       apply (fclosure_wc _ (∃A)); auto.
     * apply bsubst_WF; auto. apply Ht.
   + intros Thm.
     destruct (witsat (closure G A) Thm) as (c & Hc & Thm').
     rewrite <- fclosure_bsubst in Thm' by auto.
     rewrite <- IH in Thm'.
     2:{ now rewrite height_bsubst. }
     2:{ apply bsubst_WF; auto. now apply Cst_WC. }
     exists {| this := Cst c; closed := Cst_wc th c Hc |}.
     rewrite finterp_bsubst0; eauto.
     apply proof_irr. rewrite tinterp_carac; auto. now apply Cst_WC.
Qed.

Lemma interp_carac_closed G A : WC th A ->
 finterp mo G [] A <-> IsTheorem K th A.
Proof.
 intros W.
 replace A with (closure G A) at 2.
 apply interp_carac. apply W.
 apply form_vmap_id. intros v. destruct W as (_,F).
 red in F. intuition.
Qed.

Lemma axioms_ok A : IsAxiom th A -> interp mo A.
Proof.
 intros HA G. apply interp_carac_closed.
 apply WCAxiom; auto.
 apply ax_thm; auto.
Qed.

Definition SyntacticModel : Model M th :=
 {| pre := mo;
    AxOk := axioms_ok |}.

End SyntacticModel.

Definition nopify {X Y} (o:option nat) (f:optnfun X Y) :=
  match o with None => Nop | _ => f end.

Lemma premodel_restrict sign sign' M :
 SignExtend sign sign' ->
 PreModel M sign' -> PreModel M sign.
Proof.
 intros SE mo'.
 set (fs := fun f => nopify (funsymbs sign f) (funs mo' f)).
 set (ps := fun f => nopify (predsymbs sign f) (preds mo' f)).
 apply Build_PreModel with fs ps.
 - exact mo'.(someone).
 - intros f. unfold fs.
   generalize (funsOk mo' f).
   destruct SE as (SE,_). destruct (SE f) as [-> | ->]; auto.
   destruct (funsymbs sign' f); auto.
 - intros p. unfold ps.
   generalize (predsOk mo' p).
   destruct SE as (_,SE). destruct (SE p) as [-> | ->]; auto.
   destruct (predsymbs sign' p); auto.
Defined.

Lemma premodel_restrict_antiextend sign sign' M
 (E:SignExtend sign sign')(mo' : PreModel M sign') :
 PreModelExtend (premodel_restrict sign sign' M E mo') mo'.
Proof.
 repeat split; intros; unfold premodel_restrict; cbn.
 destruct funsymbs; red; auto.
 destruct predsymbs; red; auto.
Qed.

Lemma model_restrict logic th th' M :
 CoqRequirements logic ->
 Extend logic th th' -> Model M th' -> Model M th.
Proof.
 intros CR (SE,EX) mo'.
 apply Build_Model with (premodel_restrict th th' M SE mo').
 intros A HA G.
 rewrite finterp_premodelext with (mo':=mo').
 - assert (Thm : IsTheorem logic th' A). { apply EX, ax_thm; auto. }
   eapply validity_theorem; eauto.
 - auto using premodel_restrict_antiextend.
 - now apply WCAxiom.
Defined.

Lemma consistent_has_model (th:theory) (nc : NewCsts th) :
 (forall A, A\/~A) ->
 Consistent K th ->
 { M & Model M th }.
Proof.
 intros EM C.
 set (th' := supercomplete K th nc).
 exists (cterm th').
 apply (model_restrict K th th'). red; intros; apply EM.
 apply supercomplete_extend.
 apply SyntacticModel with (oneconst := nc 0).
 - apply supercomplete_consistent; auto.
 - apply supercomplete_complete; auto. red; intros; apply EM.
 - apply supercomplete_saturated; auto.
 - unfold th'. cbn.
   replace (test th nc (nc 0)) with true; auto.
   symmetry. apply test_ok. now exists 0.
Qed.

Lemma completeness_theorem (th:theory) (nc : NewCsts th) :
 (forall A, A\/~A) ->
 forall T,
   WC th T ->
   (forall M (mo : Model M th) G, finterp mo G [] T)
   -> IsTheorem K th T.
Proof.
 intros EM T WF HT.
 destruct (EM (IsTheorem K th T)) as [Thm|NT]; auto.
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
 assert (C : Consistent K th').
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
 destruct (consistent_has_model th' nc' EM) as (M,mo'); auto.
 assert (EX : Extend K th th').
 { apply extend_alt. split.
   - cbn. apply signext_refl.
   - intros B HB. apply ax_thm. cbn. now right. }
 set (mo := model_restrict K th th' M EM EX mo').
 set (G := fun (_:variable) => mo'.(someone)).
 assert (finterp mo' G [] (~T)). { apply AxOk. cbn. now left. }
 cbn in H. apply H. clear H.
 rewrite <- finterp_premodelext with (mo:=mo); [apply HT| |apply WF].
 destruct EX. apply premodel_restrict_antiextend.
Qed.

(*
Print Assumptions completeness_theorem.
*)
