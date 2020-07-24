
(** * Pre-models of theories *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs Mix NameProofs Meta Restrict.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Set Implicit Arguments.

(** A pre-model (also called a Σ-structure) is a non-empty domain M
    alongside some interpretations for function symbols and predicate
    symbols. For a full model of a theorie, we'll need the axioms
    of the theories, and the facts that their interpretations are
    valid. *)

Fixpoint arity_fun A n B :=
  match n with
  | O => B
  | S n => A -> (arity_fun A n B)
  end.

Definition get_arity {A B} (o : option { n:nat & arity_fun A n B}) :=
  match o with
  | None => None
  | Some (existT _ n _) => Some n
  end.

Definition modfuns M := string -> option { n:nat & arity_fun M n M }.
Definition modpreds M := string -> option { n:nat & arity_fun M n Prop }.

Record PreModel (M:Type)(sign:signature) :=
  { someone : M; (* M is non-empty *)
    funs : modfuns M;
    preds : modpreds M;
    funsOk : forall s, sign.(funsymbs) s = get_arity (funs s);
    predsOk : forall s, sign.(predsymbs) s = get_arity (preds s)
  }.

(** Note: actually, we're not using [sign], [funsOk], [predsOK]
    anywhere in this file !! See [BogusPoint] below :
    if an interpretation hasn't the right arity, we'll proceed
    nonetheless, ending up with dummy formulas that won't allow
    later to prove that the axioms of our theory are valid in
    our model. We leave [funsOk] and [predsOk] here nonetheless,
    as a remainder againts obvious goofs. *)

Section PREMODEL.
 Variable sign : signature.
 Variable M:Type.
 Variable Mo : PreModel M sign.

Definition build_args {A B} :=
  fix build n (l : list A)(def:B) : arity_fun A n B -> B :=
    match n, l with
    | 0, [] => fun f => f
    | S n, a :: l => fun f => build n l def (f a)
    | _, _ => fun _ => def
    end.

(** In case of ill-formed term (w.r.t. signature [sign]), we'll
    use the arbitrary point [Mo.(someone)]. Same if we encounter
    a local variable larger than the local environment *)
Definition BogusPoint := Mo.(someone).

Definition interp_term genv lenv :=
  fix interp t :=
    match t with
    | FVar x => genv x
    | BVar n => nth n lenv BogusPoint
    | Fun f args =>
      match Mo.(funs) f with
      | Some (existT _ n f) =>
        build_args n (List.map interp args) BogusPoint f
      | None => BogusPoint
      end
    end.

Definition interp_op o :=
 match o with
 | And => and
 | Or => or
 | Imp => (fun p q : Prop => p -> q)
 end.

(** In case of ill-formed formula (w.r.t. signature [sign]), we'll
    evaluate to the arbitrary proposition [False]. *)
Definition BogusProp := Logic.False.

Definition interp_form genv :=
  fix interp lenv f :=
    match f with
    | True => Logic.True
    | False => Logic.False
    | Not f => ~(interp lenv f)
    | Op o f1 f2 => interp_op o (interp lenv f1) (interp lenv f2)
    | Pred p args =>
      match Mo.(preds) p with
      | Some (existT _ n f) =>
        build_args n (List.map (interp_term genv lenv) args) BogusProp f
      | None => BogusProp
      end
    | Quant All f => forall (m:M), interp (m::lenv) f
    | Quant Ex f => exists (m:M), interp (m::lenv) f
    end.

Definition interp_ctx genv lenv l :=
  forall f, In f l -> interp_form genv lenv f.

Definition interp_seq genv lenv '(Γ⊢C) :=
  interp_ctx genv lenv Γ ->
  interp_form genv lenv C.

Lemma interp_term_ext genv genv' lenv t :
 (forall v, Names.In v (fvars t) -> genv v = genv' v) ->
 interp_term genv lenv t = interp_term genv' lenv t.
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn;
  intros H; auto with set.
 case (Mo.(funs) f) as [(n,fn)|]; cbn; auto. f_equal.
 apply map_ext_in. eauto with set.
Qed.

Lemma interp_form_ext genv genv' lenv f :
 (forall v, Names.In v (fvars f) -> genv v = genv' v) ->
 interp_form genv lenv f <-> interp_form genv' lenv f.
Proof.
 revert lenv.
 induction f; cbn; auto; intros; f_equal; auto with set.
 - case (Mo.(preds) p) as [(n,fn)|]; cbn; [|reflexivity]; clear p.
   f_equiv. clear n fn. apply map_ext_in.
   eauto using interp_term_ext with set.
 - rewrite IHf; intuition.
 - destruct o; cbn; rewrite IHf1, IHf2; intuition.
 - destruct q.
   + split; intros Hm m;
     [rewrite <-IHf|rewrite IHf]; auto with set.
   + split; intros (m,Hm); exists m;
     [rewrite <-IHf|rewrite IHf]; auto with set.
Qed.

Lemma interp_ctx_ext genv genv' lenv c :
 (forall v, Names.In v (fvars c) -> genv v = genv' v) ->
 interp_ctx genv lenv c <-> interp_ctx genv' lenv c.
Proof.
 intros E.
 unfold interp_ctx.
 split; intros H f Hf.
 - rewrite <- (interp_form_ext genv); auto with set.
   intros v Hv. apply E. unfold fvars, fvars_list.
   eauto with set.
 - rewrite (interp_form_ext genv); auto with set.
   intros v Hv. apply E. unfold fvars, fvars_list.
   eauto with set.
Qed.

Lemma interp_term_more_lenv genv lenv lenv' t :
 level t <= List.length lenv ->
 interp_term genv (lenv++lenv') t = interp_term genv lenv t.
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn; intros H.
 - reflexivity.
 - rewrite app_nth1; trivial.
 - case (Mo.(funs) f) as [(k,fk)|]; cbn in *; auto. f_equal.
   apply map_ext_in.
   rewrite list_max_map_le in H. auto.
Qed.

Lemma interp_term_closed genv lenv t :
 BClosed t ->
 interp_term genv lenv t = interp_term genv [] t.
Proof.
 unfold BClosed. intros E.
 apply (interp_term_more_lenv genv [] lenv). simpl. auto with *.
Qed.

Lemma interp_form_more_lenv genv lenv lenv' f :
 level f <= List.length lenv ->
 interp_form genv (lenv++lenv') f <-> interp_form genv lenv f.
Proof.
 revert lenv.
 induction f; cbn; intros lenv LE; try tauto.
 - case (Mo.(preds) p) as [(k,fk)|]; cbn; [|reflexivity]; clear p.
   f_equiv.
   apply map_ext_in. intros a Ha.
   apply interp_term_more_lenv.
   transitivity (list_max (map level l)); auto.
   now apply list_max_map_in.
 - now rewrite (IHf lenv).
 - apply Nat.max_lub_iff in LE.
   destruct o; cbn; rewrite (IHf1 lenv), (IHf2 lenv); intuition.
 - destruct q.
   + split; intros Hm' m'.
     * rewrite <-(IHf (m'::lenv)); simpl; auto. omega.
     * rewrite (IHf (m'::lenv)); simpl; auto. omega.
   + split; intros (m',Hm'); exists m'.
     * rewrite (IHf (m'::lenv)) in Hm'; simpl; auto. omega.
     * rewrite (IHf (m'::lenv)); simpl; auto. omega.
Qed.

Lemma interp_form_closed genv lenv f :
 BClosed f ->
 interp_form genv lenv f <-> interp_form genv [] f.
Proof.
 unfold BClosed. intros E.
 apply (interp_form_more_lenv genv [] lenv). simpl. omega.
Qed.

Lemma interp_lift genv lenv m t :
 interp_term genv (m :: lenv) (lift t) = interp_term genv lenv t.
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn; auto.
 case (funs Mo f) as [(k,fk)|]; cbn; auto. f_equal.
 rewrite map_map. apply map_ext_iff; auto.
Qed.

Lemma interp_term_bsubst_gen genv lenv lenv' u m n t :
 interp_term genv lenv u = m ->
 nth_error lenv' n = Some m ->
 (forall k, k<>n -> nth_error lenv' k = nth_error lenv k) ->
 interp_term genv lenv (bsubst n u t) = interp_term genv lenv' t.
Proof.
 revert u.
 induction t as [ | |f l IH] using term_ind'; cbn; intros u Hm Hn Hk.
 - trivial.
 - case eqbspec; intros; subst; auto.
   + symmetry. now apply nth_error_some_nth.
   + cbn. apply nth_error_ext; auto. symmetry; auto.
 - case (Mo.(funs) f) as [(k,fk)|]; cbn; auto. f_equal.
   rewrite map_map. apply map_ext_in; auto.
Qed.

Lemma interp_term_bsubst genv lenv u m n t :
 level t <= S n ->
 List.length lenv = n ->
 BClosed u ->
 interp_term genv [] u = m ->
 interp_term genv (lenv++[m]) t =
  interp_term genv lenv (bsubst n u t).
Proof.
 intros LE Len BC Hu.
 symmetry. eapply interp_term_bsubst_gen; eauto.
 - rewrite nth_error_app2; rewrite Len; auto.
   rewrite Nat.sub_diag; simpl. f_equal. rewrite <- Hu. symmetry.
   apply interp_term_closed; auto.
 - intro k. rewrite Nat.lt_gt_cases. intros [LT|GT].
   + rewrite nth_error_app1; auto. omega.
   + rewrite !(proj2 (nth_error_None _ _)); simpl; auto. omega.
     rewrite app_length; simpl. omega.
Qed.

Lemma interp_form_bsubst_gen genv lenv lenv' u m n f :
 interp_term genv lenv u = m ->
 nth_error lenv' n = Some m ->
 (forall k, k<>n -> nth_error lenv' k = nth_error lenv k) ->
 interp_form genv lenv (bsubst n u f) <-> interp_form genv lenv' f.
Proof.
 revert n u lenv lenv'.
 induction f; cbn; auto; intros; f_equal; auto; try reflexivity.
 - case (Mo.(preds) p) as [(k,fk)|]; cbn; [|reflexivity]; clear p.
   f_equiv.
   rewrite map_map. apply map_ext_in. intros a _.
   eapply interp_term_bsubst_gen; eauto.
 - rewrite (IHf n u lenv lenv'); intuition.
 - destruct o; cbn;
    rewrite (IHf1 n u lenv lenv'), (IHf2 n u lenv lenv'); intuition.
 - destruct q.
   + split; intros Hm' m'; specialize (Hm' m').
     * rewrite IHf in Hm'; eauto.
       now rewrite interp_lift.
       intros [|k]; simpl; auto.
     * rewrite (IHf _ _ _ (m'::lenv')); auto. now rewrite interp_lift.
       intros [|k]; simpl; auto.
   + split; intros (m',Hm'); exists m'.
     * rewrite (IHf _ _ _ (m'::lenv')) in Hm'; auto.
       now rewrite interp_lift.
       intros [|k]; simpl; auto.
     * rewrite (IHf _ _ _ (m'::lenv')); auto. now rewrite interp_lift.
       intros [|k]; simpl; auto.
Qed.

Lemma interp_form_bsubst genv lenv u m n f :
 level f <= S n ->
 List.length lenv = n ->
 BClosed u ->
 interp_term genv [] u = m ->
 interp_form genv (lenv++[m]) f <-> interp_form genv lenv (bsubst n u f).
Proof.
 intros LE Len BC Hu.
 symmetry. eapply interp_form_bsubst_gen; eauto.
 - rewrite nth_error_app2; rewrite Len; auto.
   rewrite Nat.sub_diag; simpl. f_equal. rewrite <- Hu. symmetry.
   apply interp_term_closed; auto.
 - intro k. rewrite Nat.lt_gt_cases. intros [LT|GT].
   + rewrite nth_error_app1; auto. omega.
   + rewrite !(proj2 (nth_error_None _ _)); simpl; auto. omega.
     rewrite app_length; simpl. omega.
Qed.

Lemma interp_form_bsubst0 genv u m f :
 level f <= 1 ->
 BClosed u ->
 interp_term genv [] u = m ->
 interp_form genv [m] f <-> interp_form genv [] (bsubst 0 u f).
Proof.
 intros. apply (@interp_form_bsubst genv [] u m 0 f); auto.
Qed.

Ltac prove_ext := intros ? ?; cbn; case eqbspec; auto; namedec.

Lemma interp_form_bsubst_adhoc genv m x f :
 level f <= 1 ->
 ~Names.In x (fvars f) ->
 interp_form genv [m] f <->
 interp_form (fun v => if v =? x then m else genv v) []
  (bsubst 0 (FVar x) f).
Proof.
 intros.
 rewrite <- interp_form_bsubst0 with (m:=m); auto.
 - apply interp_form_ext. prove_ext.
 - cbn. now rewrite eqb_refl.
Qed.

Lemma interp_ctx_cons genv f c :
 interp_form genv [] f ->
 interp_ctx genv [] c ->
 interp_ctx genv [] (f::c).
Proof.
 intros Hf Hc f' [<-|Hf']; auto.
Qed.
Hint Resolve interp_ctx_cons.

Definition CoqRequirements lg :=
 match lg with
 | Classic => forall A:Prop, A\/~A
 | Intuiti => Logic.True
 end.

(** Note: we do not ask here for the derivation [d] to be
    well-formed w.r.t. the signature [sign] (cf. [Mix.check]) !!
    An ill-formed derivation will involve [BogusPoint] and/or
    [BogusProp] in its evaluation. Since the derivation [d] is
    valid, the ill-formed parts will cancel themselves during
    the proof, as in [Pred("=",[])->Pred("=",[])], and we'll
    end up with uninteresting (but true) evaluations. *)

Ltac instlevel :=
 repeat match goal with
 | H : level ?d = 0 -> _ |- _ =>
   let LV := fresh "LV" in
   assert (LV : level d = 0) by intuition;
   specialize (H LV)
 end.

Ltac tryinstgenv :=
 repeat match goal with
 | H : (forall (genv:variable->M), _), genv: variable->M |- _ =>
   specialize (H genv)
 end.

Ltac substClaim :=
 repeat match goal with
 | H : Claim _ _ |- _ => red in H; rewrite H in * end.

Lemma correctness (logic:Defs.logic)(d:derivation) :
 CoqRequirements logic ->
 Valid logic d ->
 BClosed d ->
 forall genv, interp_seq genv [] (claim d).
Proof.
 unfold BClosed.
 intros CR.
 induction 1; intros CL genv Hc; substClaim;
  cbn in CL; rewrite ?eqb_eq, ?max_0 in CL;
  instlevel; cbn in *; try (tryinstgenv; intuition eauto 3; fail).
 - intros m.
   rewrite interp_form_bsubst_adhoc with (x:=x) by auto with *.
   apply IHValid.
   rewrite <- (interp_ctx_ext genv); auto with *.
 - rewrite <- interp_form_bsubst0 with (u:=t); auto with *.
   destruct d as (?,s,?); cbn in *; subst s; cbn in *; omega with *.
 - exists (interp_term genv [] t).
   rewrite interp_form_bsubst0 with (u:=t); auto with *.
 - destruct (IHValid1 genv) as (m & Hm); auto.
   rewrite interp_form_bsubst_adhoc with (x:=x) in Hm; [ | | namedec].
   erewrite interp_form_ext.
   eapply IHValid2; eauto.
   apply interp_ctx_cons. apply Hm.
   now rewrite <- (interp_ctx_ext genv) by prove_ext.
   prove_ext.
   destruct d1 as (?,s,?); cbn in *; subst s; cbn in *; omega with *.
 - subst logic.
   destruct (CR (interp_form genv [] A)); auto.
   destruct (IHValid genv); auto.
Qed.

(** We hence cannot have a valid proof of False in an empty context. *)

Lemma coherence logic : CoqRequirements logic ->
 forall (d:derivation),
 Valid logic d ->
 ~Claim d ([]⊢False).
Proof.
 intros CR d VD E.
 destruct (exist_fresh (fvars d)) as (x,Hx).
 assert (VD' := forcelevel_deriv_valid logic x d Hx VD).
 assert (BC' := forcelevel_deriv_bclosed x d).
 set (d' := forcelevel_deriv x d) in *.
 assert (E' : Claim d' ([] ⊢ False)).
 { unfold d', Claim. now rewrite claim_forcelevel, E. }
 clearbody d'.
 red in E'.
 set (genv := fun (_:variable) => Mo.(someone)).
 assert (interp_seq genv [] (claim d')).
 { apply correctness with logic; auto. }
 rewrite E' in H. cbn in *. apply H. intros A. destruct 1.
Qed.

End PREMODEL.


(** An n-ary forall construction and its interpretation.
    This will be used in [Peano.v]. *)

Fixpoint nForall n A :=
  match n with
  | 0 => A
  | S n => (∀ (nForall n A))%form
  end.

Lemma nForall_check sign n A :
 check sign (nForall n A) = check sign A.
Proof.
 induction n; simpl; auto.
Qed.

Lemma nForall_fclosed n A :
 FClosed A <-> FClosed (nForall n A).
Proof.
 induction n; simpl; easy.
Qed.

Lemma nForall_level n A :
 level (nForall n A) = level A - n.
Proof.
 induction n; cbn; auto with arith.
 rewrite IHn. omega.
Qed.

Lemma interp_nforall {sign}{M}(Mo : PreModel M sign) genv lenv n f :
  interp_form Mo genv lenv (nForall n f) <->
  (forall stk, length stk = n -> interp_form Mo genv (stk++lenv) f).
Proof.
 revert lenv.
 induction n; simpl.
 - split.
   + now intros H [| ].
   + intros H. now apply (H []).
 - split.
   + intros H stk.
     rewrite <- (rev_involutive stk).
     destruct (rev stk) as [|m rstk]; simpl; try easy.
     rewrite app_length. simpl. rewrite Nat.add_1_r. intros [= E].
     rewrite <- app_assoc. simpl. apply IHn; auto.
   + intros H m. apply IHn. intros stk Len.
     change (m::lenv) with ([m]++lenv)%list. rewrite app_assoc.
     apply H. rewrite app_length. simpl. omega.
Qed.
