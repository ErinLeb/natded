
(** * First-order theories *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)


Require Import ChoiceFacts.
Require Vector.
Require Import Defs NameProofs Mix Meta Theories PreModels Models.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

Notation K := Classic.

Implicit Types th : theory.

(** [downvars n = [#n ; ... ; #1] ]. *)

Fixpoint downvars n :=
  match n with
  | O => nil
  | S n' => BVar n :: downvars n'
  end.

Lemma seq_S a n : seq a (S n) = seq a n ++ [n+a].
Proof.
 revert a; induction n; cbn; try easy.
 intros. f_equal. rewrite <- Nat.add_succ_r.
 now rewrite <- IHn.
Qed.

Lemma downvars_alt n : downvars n = rev (map BVar (seq 1 n)).
Proof.
 induction n.
 - cbn; auto.
 - rewrite seq_S. cbn. rewrite map_app, rev_app_distr. cbn.
   rewrite Nat.add_1_r. now f_equal.
Qed.

Lemma level_downvars n : n<>0 -> level (downvars n) = S n.
Proof.
 induction n; try easy.
 destruct n. easy.
 intros. set (m := S n) in *.
 assert (IH : level (downvars m) = S m) by now apply IHn.
 clearbody m. clear IHn.
 cbn -[Nat.max]. change (list_max _) with (level (downvars m)).
 rewrite IH. omega with *.
Qed.

Lemma level_downvars_le n : level (downvars n) <= S n.
Proof.
 destruct n. auto. rewrite level_downvars; auto.
Qed.

Lemma interp_downvars sign M (mo:PreModel M sign) genv n l m :
 length l = n ->
 map (interp_term mo genv (m :: l)) (downvars n) = rev l.
Proof.
 intros E.
 rewrite downvars_alt, map_rev. f_equal.
 rewrite <- seq_shift, !map_map.
 cbn.
 revert l E. induction n; destruct l; cbn; intros; try easy.
 f_equal. rewrite <- seq_shift, map_map. apply IHn. now injection E.
Qed.

(** N-ary curry / uncurry conversions :
    isomorphism between [arity_fun] and functions expecting a [Vector.t]
    as first argument. *)

Section Curry.
Context {A B : Type}.
Import Vector.VectorNotations.
Local Notation "A ^ n" := (Vector.t A n) : types_scope.
Local Open Scope types_scope.
Local Open Scope vector_scope.

Fixpoint uncurry {n} : arity_fun A n B -> A^n -> B :=
  match n with
  | 0 => fun b _ => b
  | S n => fun f v => uncurry (f (Vector.hd v)) (Vector.tl v)
  end.

Fixpoint curry {n} : (A^n -> B) -> arity_fun A n B :=
 match n with
 | 0 => fun f => f (Vector.nil _)
 | S n => fun f a => curry (fun v => f (a::v))
 end.

Lemma uncurry_curry n (phi : A^n -> B) v :
  uncurry (curry phi) v = phi v.
Proof.
 induction v; cbn; auto. now rewrite IHv.
Qed.

Lemma to_vect n (l:list A) :
  length l = n -> exists v : Vector.t A n, Vector.to_list v = l.
Proof.
 revert n; induction l as [|a l IH]; simpl.
 - intros n <-. now exists [].
 - destruct n as [|n]; intros [= E].
   destruct (IH n E) as (v & Hv). exists (a::v). cbn; f_equal; auto.
Qed.

End Curry.

(** Skolem extension : from a theorem [∀..∀∃A],
    adding a new symbol [f] giving existential witnesses
    and the new axiom [∀xi A(xi,f(xi))].
*)

Definition Skolem_sign sign f n :=
  modify_funsymbs sign
   (fun funs s => if s =? f then Some n else funs s).

Lemma Skolem_signext sign f n :
 sign.(funsymbs) f = None ->
 SignExtend sign (Skolem_sign sign f n).
Proof.
 intros Hc.
 split; unfold optfun_finer, opt_finer; cbn; auto.
 intros a. case eqbspec; intros; subst; auto.
Qed.

(** The Skolem axiom for formula A, new symbol f of arity n.
    The n+1 foralls is a hack, the last one is just there for
     de Bruijn indices to be correctly aligned. *)

Definition Skolem_axiom A f n :=
 nForall (S n) (bsubst 0 (Fun f (downvars n)) A).

Lemma Skolem_axiom_wf sign f n A :
  funsymbs sign f = Some n ->
  Wf sign (nForall n (∃ A)) ->
  Wf sign (Skolem_axiom A f n).
Proof.
 unfold Skolem_axiom.
 intros Hf (CA & LA & FA). repeat split.
 - rewrite nForall_check, check_bsubst in *; auto.
   cbn. rewrite Hf.
   clear. induction n; simpl; auto.
 - unfold BClosed in *. rewrite nForall_level in *.
   cbn in LA.
   apply Nat.sub_0_le. etransitivity; [apply level_bsubst_max|].
   apply Nat.max_lub; try omega with *.
   apply level_downvars_le.
 - rewrite <- nForall_fclosed in *.
   rewrite <- form_fclosed_spec in *.
   cbn in FA. rewrite fclosed_bsubst; auto.
   clear. induction n; simpl; auto.
Qed.

Definition SkolemAx Ax (A:formula) f n :=
  fun B => Ax B \/ B = Skolem_axiom A f n.

Lemma SkolemAxWf th A f n :
 th.(funsymbs) f = None ->
 IsTheorem K th (nForall n (∃A)) ->
 forall B, SkolemAx th.(IsAxiom) A f n B -> Wf (Skolem_sign th f n) B.
Proof.
 intros Hc (CL & _) B [HB| -> ].
 - eauto using signext_wf, Skolem_signext, WfAxiom.
 - apply Skolem_axiom_wf.
   + simpl. now rewrite eqb_refl.
   + eauto using signext_wf, Skolem_signext.
Qed.

Definition Skolem_ext th A f n
 (E:th.(funsymbs) f = None)
 (Thm:IsTheorem K th (nForall n (∃A))) :=
 {| sign := Skolem_sign th f n;
    IsAxiom := SkolemAx th.(IsAxiom) A f n;
    WfAxiom := SkolemAxWf th A f n E Thm |}.

Section SkolemTheorem.
Variable EM : forall A:Prop, A\/~A.
Variable Choice : forall A B, FunctionalChoice_on A B.

Variable th : theory.
Variable NC : NewCsts th.

Definition Skolem_premodel_ext sign M (mo:PreModel M sign)
 f n (phi : arity_fun M n M) : PreModel M (Skolem_sign sign f n).
Proof.
set (sign' := Skolem_sign _ _ _).
set (funs' := fun s => if s =? f then Some (existT _ n phi) else funs mo s).
eapply (Build_PreModel sign' (someone mo) funs' (preds mo)); intros s.
- unfold funs'. cbn. case eqbspec; intros; auto using funsOk.
- cbn. apply predsOk.
Defined.

Lemma interp_form_premodel_ext sign sign' M
 (mo:PreModel M sign) (mo':PreModel M sign') :
  (someone mo = someone mo') ->
  (forall f, funs mo f = None \/ funs mo f = funs mo' f) ->
  (forall p, preds mo p = preds mo' p) ->
  (forall A, check sign A = true ->
    forall genv lenv,
      interp_form mo genv lenv A <-> interp_form mo' genv lenv A).
Proof.
 intros SO FU PR.
 assert (Ht : forall (t:term), check sign t = true ->
               forall genv lenv, interp_term mo genv lenv t =
                                 interp_term mo' genv lenv t).
 { induction t as [ | | f l IH] using term_ind'; cbn; trivial.
   - unfold BogusPoint. now rewrite <- SO.
   - destruct (funsymbs sign f) as [ar|] eqn:E; try easy.
     rewrite lazy_andb_iff. intros (_ & F) genv lenv.
     destruct (FU f) as [Hf|Hf].
     + exfalso. now rewrite (funsOk mo f), Hf in E.
     + rewrite <- Hf. destruct (funs mo f) as [(p,q)|]; auto.
       unfold BogusPoint. rewrite <- SO. f_equal.
       apply map_ext_in. intros a Ha.
       apply IH; auto. rewrite forallb_forall in F; auto. }
 induction A; cbn.
 - intuition.
 - intuition.
 - destruct (predsymbs sign p) as [ar|] eqn:E; try easy.
   rewrite lazy_andb_iff. intros (_ & F) genv lenv.
   rewrite <- PR. destruct (preds mo p) as [(u,v)|]; try easy.
   f_equiv. apply map_ext_in. intros a Ha. apply Ht.
   rewrite forallb_forall in F; auto.
 - intros WA genv lenv. now rewrite IHA.
 - rewrite lazy_andb_iff.
   intros (WA1,WA2) genv lenv.
   specialize (IHA1 WA1 genv lenv).
   specialize (IHA2 WA2 genv lenv).
   destruct o; cbn; now rewrite IHA1, IHA2.
 - intros WA genv lenv.
   destruct q; setoid_rewrite IHA; firstorder.
Qed.

Lemma interp_form_skolem_premodel_ext sign M f n (F:arity_fun M n M)
 (mo:PreModel M sign) (mo':PreModel M (Skolem_sign sign f n))
 (E':mo'=Skolem_premodel_ext sign M mo f n F)
 (E:sign.(funsymbs) f = None) :
 forall A, check sign A = true ->
 forall genv lenv,
  interp_form mo genv lenv A <-> interp_form mo' genv lenv A.
Proof.
 apply interp_form_premodel_ext; rewrite E'; try easy.
 intros f0. unfold Skolem_premodel_ext. cbn.
 case eqbspec; auto.
 intros ->. left. rewrite (funsOk mo f) in E.
 now destruct (funs mo f) as [(p,q)|].
Qed.

Definition interp_phi {n th M} (mo:Model M th)(phi : Vector.t M n -> M) A :=
 forall genv v, interp_form mo genv (phi v :: rev (Vector.to_list v)) A.

Definition Skolem_model_AxOk A f n
 (E:th.(funsymbs) f = None)
 (Thm:IsTheorem K th (nForall n (∃A)))
 M (mo:Model M th)(phi : Vector.t M n -> M)(Hphi : interp_phi mo phi A) :
  forall A0 : formula,
  IsAxiom (Skolem_ext th A f n E Thm) A0 ->
  forall genv : variable -> M,
  interp_form (Skolem_premodel_ext th M mo f n (curry phi)) genv [] A0.
Proof.
set (th' := Skolem_ext _ _ _ _ _ _) in *.
set (Phi := curry phi).
set (mo' := Skolem_premodel_ext _ _ _ _ _ _).
intros A0 [ | -> ] genv.
- unfold th'. simpl.
  rewrite <- (interp_form_skolem_premodel_ext th M f n Phi mo); auto.
  + now apply AxOk.
  + now apply WfAxiom.
- unfold Skolem_axiom.
  rewrite interp_nforall. intros. rewrite app_nil_r.
  destruct stk as [|m l]; try easy.
  injection H as H.
  rewrite <- rev_length in H.
  destruct (to_vect _ _ H) as (v & Hv).
  rewrite interp_form_bsubst_gen with (lenv' := phi v :: l); auto.
  + unfold th'. simpl.
    rewrite <- (interp_form_skolem_premodel_ext th M f n Phi mo); auto.
    * rewrite <- (rev_involutive l), <- Hv. apply Hphi.
    * clear -Thm. destruct Thm as ((CA & _ & _),_).
      rewrite nForall_check in CA. apply CA.
  + simpl nth_error. f_equal.
    cbn. rewrite eqb_refl.
    rewrite interp_downvars, <- Hv by (now rewrite rev_length in H).
    symmetry. clear -v. unfold Phi.
    rewrite <- (uncurry_curry _ phi v). induction v; cbn; auto.
  + destruct k; try easy.
Qed.

Definition Skolem_model_ext A f n
 (E:th.(funsymbs) f = None)
 (Thm:IsTheorem K th (nForall n (∃A)))
 M (mo:Model M th)(phi : Vector.t M n -> M)(Hphi : interp_phi mo phi A) :
 Model M (Skolem_ext th A f n E Thm).
Proof.
set (th' := Skolem_ext _ _ _ _ _ _).
apply (Build_Model _ th' (Skolem_premodel_ext th M mo f n (curry phi))).
apply Skolem_model_AxOk; auto.
Defined.

Lemma Skolem_consext A f n
 (E:th.(funsymbs) f = None)
 (Thm:IsTheorem K th (nForall n (∃A))) :
 ConservativeExt K th (Skolem_ext th A f n E Thm).
Proof.
 apply consext_alt.
 split.
 - rewrite extend_alt. split.
   + now apply Skolem_signext.
   + intros B HB. split.
     * apply signext_wf with th.
       now apply Skolem_signext.
       now apply WfAxiom.
     * exists [B]. split. constructor; auto. simpl. red. now left.
       apply R'_Ax.
 - intros T HT CT.
   apply completeness_theorem; auto.
   + split; auto. apply HT.
   + intros M mo genv.
     set (th' := Skolem_ext _ _ _ _ _ _) in *.
     assert (interp_form mo genv [] (nForall n (∃ A))).
     { eapply validity_theorem; eauto. red; auto. }
     rewrite interp_nforall in H.
     assert (C : forall (v : Vector.t M n), exists m,
                  interp_form mo genv (m::rev (Vector.to_list v)) A).
     { intros v.
       specialize (H (rev (Vector.to_list v))).
       rewrite app_nil_r in H. apply H. rewrite rev_length.
       clear. revert v; induction v; simpl; auto. }
     apply Choice in C. destruct C as (phi, Hphi). clear H.
     assert (Hphi' : forall genv v,
                interp_form mo genv (phi v :: rev (Vector.to_list v)) A).
     { intros genv' v. rewrite interp_form_ext; eauto.
       intros. clear - H Thm. destruct Thm as ((_ & _ & FA),_).
       apply nForall_fclosed in FA. red in FA. cbn in FA.
       now destruct (FA v0). }
     set (mo' := Skolem_model_ext A f n E Thm M mo phi Hphi').
     assert (ok' : interp_form mo' genv [] T).
     { eapply validity_theorem; eauto. red; auto. }
     rewrite interp_form_skolem_premodel_ext; eauto.
     unfold mo' in ok'. unfold Skolem_model_ext in ok'. cbn in ok'.
     apply ok'.
Qed.
End SkolemTheorem.

(*
Check Skolem_consext.
Print Assumptions Skolem_consext.
*)
