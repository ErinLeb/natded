
(** * Pre-models of theories *)

(** The NatDed development, Pierre Letouzey, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs Mix NameProofs Toolbox Meta Restrict Theories.
Require Import NaryFunctions Nary.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Set Implicit Arguments.

Implicit Types t u : term.
Implicit Types A B : formula.

(** A pre-model (also called a Σ-structure) is a non-empty domain M
    alongside some interpretations for function symbols and predicate
    symbols. For a full model of a theory, we'll need later to ensure
    that all axioms of this theory have valid interpretations, see
    [Models.v].

    For encoding the interpretations of symbols, we use [Nary.optnfun],
    which is based on [NaryFunctions.nfun], the dependent type of
    functions of arity [n]. More precisely, an [optnfun] is either
    [Nop] for symbols not in the signature, or [NFun n f], where
    [f] is a function expecting [n] arguments. Note that [n] is
    internal (existential), and may be retrieved via [get_arity].

    This choice of representation allows the direct use of Coq
    usual functions in concrete models, e.g. [NFun 2 Nat.add] for
    Peano's "+". But [nfun] may be tricky to use in proofs,
    so we often switch to an equivalent forms based
    on dependent n-uplets [NaryFunctions.nprod], thanks to
    [NaryFunctions.nuncurry] and [NaryFunctions.ncurry]. These
    n-uplets are iterated pairs, but Coq Vectors could also have
    been considered. *)

Record PreModel (M:Type)(sign:signature) :=
  { someone : M; (* M is non-empty *)
    funs : string -> optnfun M M;
    preds : string -> optnfun M Prop;
    funsOk : forall s, sign.(funsymbs) s = get_arity (funs s);
    predsOk : forall s, sign.(predsymbs) s = get_arity (preds s)
  }.

(** Note: actually, we're not using [sign], [funsOk], [predsOK]
    anywhere in this part !! See [BogusPoint] below :
    if an interpretation hasn't the right arity, we'll proceed
    nonetheless, ending up with dummy formulas that won't allow
    later to prove that the axioms of our theory are valid in
    our model. We leave [funsOk] and [predsOk] here nonetheless,
    as a remainder againts obvious goofs. *)

Section PREMODEL.
Variable sign : signature.
Variable M:Type.
Variable Mo : PreModel M sign.

Implicit Types G : variable -> M. (* Global environment, for Free Var *)
Implicit Types L : list M. (* Local environment, for Bounded Var *)

(** In case of ill-formed term (w.r.t. signature [sign]), we'll
    use the arbitrary point [Mo.(someone)]. Same if we encounter
    a local variable larger than the local environment *)
Definition BogusPoint := Mo.(someone).

Definition tinterp G L :=
  fix tinterp t :=
    match t with
    | FVar x => G x
    | BVar n => nth n L BogusPoint
    | Fun f args => napply_dft (funs Mo f) (map tinterp args) BogusPoint
    end.

Definition ointerp op :=
 match op with
 | And => and
 | Or => or
 | Imp => (fun p q : Prop => p -> q)
 end.

(** In case of ill-formed formula (w.r.t. signature [sign]), we'll
    evaluate to the arbitrary proposition [False]. *)
Definition BogusProp := Logic.False.

Definition finterp G :=
  fix finterp L f :=
    match f with
    | True => Logic.True
    | False => Logic.False
    | Not f => ~(finterp L f)
    | Op o f1 f2 => ointerp o (finterp L f1) (finterp L f2)
    | Pred p args =>
      napply_dft (preds Mo p) (map (tinterp G L) args) BogusProp
    | Quant All f => forall (m:M), finterp (m::L) f
    | Quant Ex f => exists (m:M), finterp (m::L) f
    end.

Definition cinterp G L (c:context) := forall A, In A c -> finterp G L A.

Definition sinterp G L '(Γ⊢C) := cinterp G L Γ -> finterp G L C.

Global Instance ointerp_m :
 Proper (eq ==> iff ==> iff ==> iff) ointerp.
Proof.
 intros o o' <- p p' Hp q q' Hq. destruct o; cbn; now rewrite Hp, Hq.
Qed.

Lemma interp_quant q G G' L L' A A' :
 (forall m, finterp G (m::L) A <-> finterp G' (m::L') A') ->
 finterp G L (Quant q A) <-> finterp G' L' (Quant q A').
Proof.
 intros E. cbn. destruct q; now setoid_rewrite E.
Qed.

Lemma tinterp_ext G L G' L' t :
 (forall v, Names.In v (fvars t) -> G v = G' v) ->
 (forall k, k < level t -> nth_error L k = nth_error L' k) ->
 tinterp G L t = tinterp G' L' t.
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn;
  intros EG EL; auto with set.
 - apply nth_error_ext; auto.
 - f_equal. apply map_ext_in.
   intros a Ha. apply IH; eauto with set.
   intros k LT. apply EL. apply Nat.lt_le_trans with (level a); auto.
   now apply list_max_map_in.
Qed.

Lemma finterp_ext G L G' L' A :
 (forall v, Names.In v (fvars A) -> G v = G' v) ->
 (forall k, k < level A -> nth_error L k = nth_error L' k) ->
 finterp G L A <-> finterp G' L' A.
Proof.
 revert L L'.
 induction A; intros L L' EG EL; try apply (interp_quant q);
  cbn in *; f_equiv; auto with set.
 - apply map_ext_in.
   intros a Ha. apply tinterp_ext; eauto with set.
   intros k LT. apply EL. apply Nat.lt_le_trans with (level a); auto.
   now apply list_max_map_in.
 - setoid_rewrite Nat.max_lt_iff in EL. apply IHA1; eauto with set.
 - setoid_rewrite Nat.max_lt_iff in EL. apply IHA2; eauto with set.
 - intros m. apply IHA; eauto with set.
   destruct k; cbn; auto. intros H. apply EL. lia.
Qed.

Lemma cinterp_ext G L G' L' (c:context) :
 (forall v, Names.In v (fvars c) -> G v = G' v) ->
 (forall k, k < level c -> nth_error L k = nth_error L' k) ->
 cinterp G L c <-> cinterp G' L' c.
Proof.
 intros EG EL.
 split; intros H f Hf.
 - rewrite <- (finterp_ext G L); auto.
   + intros v Hv. apply EG. unfold fvars, fvars_list. eauto with set.
   + intros k Hk. apply EL. unfold level, level_list.
     apply Nat.lt_le_trans with (level f); auto.
     now apply list_max_map_in.
 - rewrite (finterp_ext G L); auto.
   + intros v Hv. apply EG. unfold fvars, fvars_list. eauto with set.
   + intros k Hk. apply EL. unfold level, level_list.
     apply Nat.lt_le_trans with (level f); auto.
     now apply list_max_map_in.
Qed.

Lemma tinterp_bclosed G L t :
 BClosed t ->
 tinterp G L t = tinterp G [] t.
Proof.
 intros BC. apply tinterp_ext; auto. intro k. rewrite BC. inversion 1.
Qed.

Lemma finterp_bclosed G L A :
 BClosed A ->
 finterp G L A <-> finterp G [] A.
Proof.
 intros BC. apply finterp_ext; auto. intro k. rewrite BC. inversion 1.
Qed.

Lemma tinterp_lift G L t n :
 tinterp G L (lift n t) = tinterp G (list_drop n L) t.
Proof.
 induction t using term_ind'; cbn; auto.
 - case Nat.leb_spec; cbn; intros.
   + now rewrite list_drop_nth_high.
   + now rewrite list_drop_nth_low.
 - f_equal. rewrite map_map. apply map_ext_in; auto.
Qed.

Lemma finterp_lift G L A n :
 finterp G L (lift n A) <-> finterp G (list_drop n L) A.
Proof.
 revert n L; induction A; intros; try apply interp_quant;
  cbn; f_equiv; try easy.
 - rewrite map_map. apply map_ext; auto using tinterp_lift.
 - intros m; apply IHA.
Qed.

Lemma tinterp_bsubst_gen G L L' u m n t :
 tinterp G L u = m ->
 nth_error L' n = Some m ->
 (forall k, k<>n -> nth_error L' k = nth_error L k) ->
 tinterp G L (bsubst n u t) = tinterp G L' t.
Proof.
 revert u.
 induction t as [ | |f l IH] using term_ind'; cbn; intros u Hm Hn Hk.
 - trivial.
 - case eqbspec; intros; subst; auto.
   + symmetry. now apply nth_error_some_nth.
   + cbn. apply nth_error_ext; auto. symmetry; auto.
 - f_equiv. rewrite map_map. apply map_ext_in; auto.
Qed.

Lemma tinterp_bsubst G L u m n t :
 level t <= S n ->
 length L = n ->
 BClosed u ->
 tinterp G [] u = m ->
 tinterp G (L++[m]) t = tinterp G L (bsubst n u t).
Proof.
 intros LE Len BC Hu.
 symmetry. eapply tinterp_bsubst_gen; eauto.
 - rewrite nth_error_app2; rewrite Len; auto.
   rewrite Nat.sub_diag; simpl. f_equal. rewrite <- Hu. symmetry.
   apply tinterp_bclosed; auto.
 - intro k. rewrite Nat.lt_gt_cases. intros [LT|GT].
   + rewrite nth_error_app1; auto. lia.
   + rewrite !(proj2 (nth_error_None _ _)); simpl; auto. lia.
     rewrite app_length; simpl. lia.
Qed.

Lemma finterp_bsubst_gen G L L' u m n A :
 tinterp G L u = m ->
 nth_error L' n = Some m ->
 (forall k, k<>n -> nth_error L' k = nth_error L k) ->
 finterp G L (bsubst n u A) <-> finterp G L' A.
Proof.
 revert n u L L'.
 induction A; intros; try apply interp_quant; cbn in *; f_equiv; auto; try easy.
 - rewrite map_map. apply map_ext. intros a.
   eapply tinterp_bsubst_gen; eauto.
 - intros m'; apply IHA; auto.
   now rewrite tinterp_lift.
   intros [|k]; simpl; auto.
Qed.

Lemma finterp_bsubst G L u m n A :
 level A <= S n ->
 length L = n ->
 BClosed u ->
 tinterp G [] u = m ->
 finterp G (L++[m]) A <-> finterp G L (bsubst n u A).
Proof.
 intros LE Len BC Hu.
 symmetry. eapply finterp_bsubst_gen; eauto.
 - rewrite nth_error_app2; rewrite Len; auto.
   rewrite Nat.sub_diag; simpl. f_equal. rewrite <- Hu. symmetry.
   apply tinterp_bclosed; auto.
 - intro k. rewrite Nat.lt_gt_cases. intros [LT|GT].
   + rewrite nth_error_app1; auto. lia.
   + rewrite !(proj2 (nth_error_None _ _)); simpl; auto. lia.
     rewrite app_length; simpl. lia.
Qed.

Lemma finterp_bsubst0 G u m A :
 level A <= 1 ->
 BClosed u ->
 tinterp G [] u = m ->
 finterp G [m] A <-> finterp G [] (bsubst 0 u A).
Proof.
 intros. apply (@finterp_bsubst G [] u m 0 A); auto.
Qed.

Ltac prove_ext := intros ? ?; cbn; case eqbspec; auto; namedec.

Lemma finterp_bsubst_adhoc G m x A :
 level A <= 1 ->
 ~Names.In x (fvars A) ->
 finterp G [m] A <->
 finterp (fun v => if v =? x then m else G v) [] (bsubst 0 (FVar x) A).
Proof.
 intros.
 rewrite <- finterp_bsubst0 with (m:=m); auto.
 - apply finterp_ext. prove_ext. auto.
 - cbn. now rewrite eqb_refl.
Qed.

Lemma cinterp_cons G L A (c:context) :
 finterp G L A -> cinterp G L c -> cinterp G L (A::c).
Proof.
 intros Hf Hc f' [<-|Hf']; auto.
Qed.
Hint Resolve cinterp_cons.

Definition CoqRequirements lg :=
 match lg with
 | K => forall A:Prop, A\/~A
 | J => Logic.True
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

Ltac tryinstG :=
 repeat match goal with
 | H : (forall (G:variable->M), _), G: variable->M |- _ =>
   specialize (H G)
 end.

Ltac substClaim :=
 repeat match goal with
 | H : Claim _ _ |- _ => red in H; rewrite H in * end.

Lemma correctness (logic:Defs.logic)(d:derivation) :
 CoqRequirements logic ->
 Valid logic d ->
 BClosed d ->
 forall G, sinterp G [] (claim d).
Proof.
 unfold BClosed.
 intros CR.
 induction 1; intros CL G Hc; substClaim;
  cbn in CL; rewrite ?eqb_eq, ?max_0 in CL;
  instlevel; cbn in *; try (tryinstG; intuition eauto 3; fail).
 - intros m.
   rewrite finterp_bsubst_adhoc with (x:=x) by (auto with *; lia).
   apply IHValid.
   rewrite <- (cinterp_ext G); eauto with *.
 - rewrite <- finterp_bsubst0 with (u:=t); auto with *; try easy.
   destruct d as (?,s,?); cbn in *; subst s; cbn in *; lia.
 - exists (tinterp G [] t).
   rewrite finterp_bsubst0 with (u:=t); auto; try easy. lia.
 - destruct (IHValid1 G) as (m & Hm); auto.
   rewrite finterp_bsubst_adhoc with (x:=x) in Hm; [ | | namedec].
   erewrite finterp_ext.
   eapply IHValid2; eauto.
   apply cinterp_cons. apply Hm.
   rewrite <- (cinterp_ext G); eauto. prove_ext. prove_ext. auto.
   destruct d1 as (?,s,?); cbn in *; subst s; cbn in *; lia.
 - subst logic.
   destruct (CR (finterp G [] A)); auto.
   destruct (IHValid G); auto.
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
 set (G := fun (_:variable) => Mo.(someone)).
 assert (sinterp G [] (claim d')).
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
 rewrite IHn. lia.
Qed.

Lemma interp_nforall {sign}{M}(Mo : PreModel M sign) G L n A :
  finterp Mo G L (nForall n A) <->
  (forall stk, length stk = n -> finterp Mo G (stk++L) A).
Proof.
 revert L.
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
     change (m::L) with ([m]++L)%list. rewrite app_assoc.
     apply H. rewrite app_length. simpl. lia.
Qed.

(** Premodel extension *)

Definition optnfun_finer {X Y} (f f' : optnfun X Y) :=
 f=Nop \/ f = f'.

Record PreModelExtend {sg sg' M} (mo:PreModel M sg) (mo':PreModel M sg') :=
  { extOne : someone mo = someone mo';
    extFun : forall f, optnfun_finer (funs mo f) (funs mo' f);
    extPred : forall p, optnfun_finer (preds mo p) (preds mo' p) }.

Lemma PreModelExtend_sign sg sg' M (mo:PreModel M sg)(mo':PreModel M sg'):
 PreModelExtend mo mo' -> SignExtend sg sg'.
Proof.
 intros (_,F,P). split.
 - intros f. red. rewrite (funsOk mo f), (funsOk mo' f).
   destruct (F f) as [-> | ->]; auto.
 - intros p. red. rewrite (predsOk mo p), (predsOk mo' p).
   destruct (P p) as [-> | ->]; auto.
Qed.

(** A premodel extension keeps interpreting identically terms and
    formulas written on the former signature *)

Lemma tinterp_premodelext sg sg' M (mo:PreModel M sg) (mo':PreModel M sg') :
 PreModelExtend mo mo' ->
 forall t, check sg t = true ->
  forall G L, tinterp mo G L t = tinterp mo' G L t.
Proof.
 intros (SO,SF,SP).
 induction t as [ | | f l IH] using term_ind'; cbn.
 - trivial.
 - intros. f_equal. apply SO.
 - generalize (funsOk mo f).
   destruct (funsymbs sg f) as [ar|] eqn:E; try easy.
   rewrite lazy_andb_iff, forallb_forall.
   destruct (SF f) as [-> | ->]; try easy. intros _ (_,Ht) G L.
   f_equal; auto using map_ext_in.
Qed.

Lemma finterp_premodelext sg sg' M (mo:PreModel M sg) (mo':PreModel M sg') :
 PreModelExtend mo mo' ->
 forall A, check sg A = true ->
 forall G L, finterp mo G L A <-> finterp mo' G L A.
Proof.
 intros ME.
 induction A; cbn.
 - intuition.
 - intuition.
 - generalize (predsOk mo p).
   destruct (predsymbs sg p) as [ar|] eqn:E; try easy.
   rewrite lazy_andb_iff, forallb_forall.
   destruct (extPred ME p) as [-> | ->]; try easy. intros _ (_,Ht) G L.
   f_equiv. apply map_ext_in. intros. apply tinterp_premodelext; auto.
 - intros CA G L. f_equiv; auto.
 - rewrite lazy_andb_iff. intros (CA1,CA2) G L. f_equiv; auto.
 - intros CA G L.
   destruct q; setoid_rewrite IHA; firstorder.
Qed.
