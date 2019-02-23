Require Import Defs Mix Proofs Meta Omega Setoid Morphisms.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

Set Implicit Arguments.

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

Record PreModel (M:Type)(sign:gen_signature) :=
  { someone : M; (* M is non-empty *)
    funs : modfuns M;
    preds : modpreds M;
    funsOk : forall s, sign.(gen_fun_symbs) s = get_arity (funs s);
    predsOk : forall s, sign.(gen_pred_symbs) s = get_arity (preds s)
  }.

(** A premodel is also called a Σ-structure. For a complete model
    of a theorie, we'll need the axioms of the theories, and
    the facts that their interpretations are valid. *)

(** Note: actually, we're not using [sign], [funsOk], [predsOK]
    anywhere in this file (yet?) !! *)

Section PREMODEL.
 Variable sign : gen_signature.
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
 (forall v, Vars.In v (fvars t) -> genv v = genv' v) ->
 interp_term genv lenv t = interp_term genv' lenv t.
Proof.
 revert t.
 fix IH 1. destruct t; cbn; auto.
 - intros. apply H. varsdec.
 - intros. case (Mo.(funs) f) as [(n,fn)|]; cbn; auto. clear f.
   f_equal. clear n fn. revert l H.
   fix IH' 1. destruct l; cbn; auto.
   intros E. f_equal; auto with set.
Qed.

Lemma interp_form_ext genv genv' lenv f :
 (forall v, Vars.In v (fvars f) -> genv v = genv' v) ->
 interp_form genv lenv f <-> interp_form genv' lenv f.
Proof.
 revert lenv.
 induction f; cbn; auto; intros; f_equal; auto with set.
 - case (Mo.(preds) p) as [(n,fn)|]; cbn; [|reflexivity]; clear p.
   f_equiv. clear n fn. revert l H. induction l; cbn; auto.
   intros E. f_equal; auto using interp_term_ext with set.
 - rewrite IHf; intuition.
 - destruct o; cbn; rewrite IHf1, IHf2; intuition.
 - destruct q.
   + split; intros Hm m;
     [rewrite <-IHf|rewrite IHf]; auto with set.
   + split; intros (m,Hm); exists m;
     [rewrite <-IHf|rewrite IHf]; auto with set.
Qed.

Lemma interp_ctx_ext genv genv' lenv c :
 (forall v, Vars.In v (fvars c) -> genv v = genv' v) ->
 interp_ctx genv lenv c <-> interp_ctx genv' lenv c.
Proof.
 intros E.
 unfold interp_ctx.
 split; intros H f Hf.
 rewrite <- (interp_form_ext genv); auto with set.
 intros v Hv. apply E. unfold fvars, fvars_list.
 rewrite vars_unionmap_in. exists f. now split.
 rewrite (interp_form_ext genv); auto with set.
 intros v Hv. apply E. unfold fvars, fvars_list.
 rewrite vars_unionmap_in. exists f. now split.
Qed.

Lemma interp_term_more_lenv genv lenv lenv' t :
 (level t <= List.length lenv)%nat ->
 interp_term genv (lenv++lenv') t = interp_term genv lenv t.
Proof.
 revert t.
 fix IH 1. destruct t; cbn in *; intros H.
 - reflexivity.
 - rewrite app_nth1; trivial.
 - case (Mo.(funs) f) as [(k,fk)|]; cbn in *; auto.
   f_equal.
   clear k fk f.
   revert l H.
   fix IH' 1. destruct l; cbn; auto.
   intros H. f_equal. apply IH. omega with *. apply IH'. omega with *.
Qed.

Lemma interp_term_closed genv lenv t :
 closed t ->
 interp_term genv lenv t = interp_term genv [] t.
Proof.
 unfold closed. intros E.
 apply (interp_term_more_lenv genv [] lenv). simpl. auto with *.
Qed.

Lemma interp_term_bsubst genv lenv u m n t :
 (level t <= S n)%nat ->
 List.length lenv = n ->
 closed u ->
 interp_term genv [] u = m ->
 interp_term genv (lenv++[m]) t =
  interp_term genv lenv (bsubst n u t).
Proof.
 revert t.
 fix IH 1. destruct t; cbn; auto; intros LE Hn CL Hu.
 - case eqbspec; intros.
   + rewrite app_nth2; try omega.
     replace (n0 - length lenv) with 0 by omega. cbn.
     now rewrite interp_term_closed.
   + apply app_nth1. omega.
 - case (Mo.(funs) f) as [(k,fk)|]; cbn; auto. f_equal. clear f k fk.
   revert l LE.
   fix IH' 1. destruct l; cbn; auto.
   intros LE. f_equal.
   apply IH; auto. omega with *.
   apply IH'; auto. omega with *.
Qed.

Lemma interp_form_bsubst genv lenv u m n f :
 (level f <= S n)%nat ->
 List.length lenv = n ->
 closed u ->
 interp_term genv [] u = m ->
 interp_form genv (lenv++[m]) f <-> interp_form genv lenv (bsubst n u f).
Proof.
 revert n lenv.
 induction f; cbn; auto; intros; f_equal; auto with set.
 - case (Mo.(preds) p) as [(k,fk)|]; cbn; [|reflexivity]; clear p.
   f_equiv.
   clear k fk.
   revert l H.
   induction l; cbn; auto.
   intros H. f_equal.
   apply interp_term_bsubst; auto. omega with *.
   apply IHl; auto. omega with *.
 - rewrite (IHf n); intuition.
 - destruct o; cbn; rewrite (IHf1 n), (IHf2 n); intuition; omega with *.
 - destruct q.
   + split; intros Hm' m'.
     * rewrite <-IHf; cbn; auto with set. omega with *.
     * change (m'::(lenv++[m]))%list with ((m'::lenv)++[m])%list.
       rewrite IHf; auto with set. omega with *. simpl; auto.
   + split; intros (m',Hm'); exists m'.
     * rewrite <-IHf; cbn; auto with set. omega with *.
     * change (m'::(lenv++[m]))%list with ((m'::lenv)++[m])%list.
       erewrite IHf; eauto with set. omega with *. simpl; auto.
Qed.

Lemma interp_form_bsubst0 genv u m f :
 (level f <= 1)%nat ->
 closed u ->
 interp_term genv [] u = m ->
 interp_form genv [m] f <-> interp_form genv [] (bsubst 0 u f).
Proof.
 intros. apply (@interp_form_bsubst genv [] u m 0 f); auto.
Qed.

Ltac prove_ext := intros ? ?; cbn; case eqbspec; auto; varsdec.

Lemma interp_form_bsubst_adhoc genv m x f :
 (level f <= 1)%nat ->
 ~Vars.In x (fvars f) ->
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

Lemma correctness (logic:Mix.logic)(d:derivation) :
 CoqRequirements logic ->
 Valid logic d ->
 closed d ->
 forall genv, interp_seq genv [] (claim d).
Proof.
 unfold closed.
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
   rewrite interp_form_bsubst_adhoc with (x:=x) in Hm; [ | | varsdec].
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
 closed d ->
 ~Claim d ([]⊢False).
Proof.
 intros CR d VD CL E.
 red in E.
 set (genv := fun (_:variable) => Mo.(someone)).
 assert (interp_seq genv [] (claim d)).
 { apply correctness with logic; auto. }
 rewrite E in H. cbn in *. apply H. intros A. destruct 1.
Qed.

End PREMODEL.
