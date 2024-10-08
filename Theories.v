
(** * First-order theories *)

(** The NatDed development, Pierre Letouzey, Samuel Ben Hamou, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Toolbox Meta ProofExamples Wellformed.
Require Import Restrict Countable.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

Record theory :=
  { sign :> signature;
    IsAxiom : formula -> Prop;
    WCAxiom : forall A, IsAxiom A -> WC sign A }.

Implicit Type th : theory.

Definition ValidDerivOn logic (sign:signature) d :=
  WF sign d /\ Valid logic d.

Section SomeLogic.
Variable logic : Defs.logic.

Definition IsTheoremStrict th (T:formula) :=
  WC th T /\
  exists d axs,
    ValidDerivOn logic th d /\
    Forall th.(IsAxiom) axs /\
    Claim d (axs ⊢ T).

Definition IsTheorem th T :=
  WC th T /\
  exists axs,
    Forall th.(IsAxiom) axs /\
    Pr logic (axs ⊢ T).

Hint Unfold IsTheorem IsTheoremStrict.

(** Some derivation rules lifted on [IsTheorem]. *)

Lemma Thm_Imp_e th A B :
  IsTheorem th (A -> B) -> IsTheorem th A -> IsTheorem th B.
Proof.
  intros (W & l & F & P) (W' & l' & F' & P'). split.
  - now rewrite Op_WC in W.
  - exists (l ++ l'); split.
    + now apply Forall_app.
    + apply R_Imp_e with A. now apply Pr_app_l. now apply Pr_app_r.
Qed.

Definition ModusPonens := Thm_Imp_e. (* old name *)

Lemma Thm_Not_e th A :
 IsTheorem th A -> IsTheorem th (~A) -> IsTheorem th False.
Proof.
 intros (_ & l & F & P) (_ & l' & F' & P'). split.
 - apply False_WC.
 - exists (l++l'); split.
   + now apply Forall_app.
   + apply R_Not_e with A. now apply Pr_app_l. now apply Pr_app_r.
Qed.

Lemma Thm_And th A B :
  IsTheorem th A /\ IsTheorem th B <-> IsTheorem th (A /\ B).
Proof.
 split.
 - intros ((W & l & F & P), (W' & l' & F' & P')).
   split; [now apply Op_WC|].
   exists (l++l'); split.
   + now apply Forall_app.
   + apply R_And_i. now apply Pr_app_l. now apply Pr_app_r.
 - intros (W & l & F & P); rewrite Op_WC in W. split.
   + split; [easy|]. exists l; split; auto. now apply R_And_e1 with B.
   + split; [easy|]. exists l; split; auto. now apply R_And_e2 with A.
Qed.

Lemma Thm_or_i th A B : WC th (A\/B) ->
  IsTheorem th A \/ IsTheorem th B -> IsTheorem th (A \/ B).
Proof.
 intros W [(_ & l & F & P)|(_ & l & F & P)]; split; auto; exists l; auto.
Qed.

Lemma Thm_All_e th A t : WC th t ->
 IsTheorem th (∀A) -> IsTheorem th (bsubst 0 t A).
Proof.
 intros Wt (W & l & F & P).
 split. apply bsubst_WC; auto. exists l. auto.
Qed.

Lemma Thm_Ex_i th A t : WC th (∃A) ->
 IsTheorem th (bsubst 0 t A) -> IsTheorem th (∃A).
Proof.
 intros W (_ & l & F & P).
 split; auto. exists l. split; auto. apply R_Ex_i with t; auto.
Qed.

Lemma Thm_NotExNot th A : logic=K -> WC th (∀A) ->
  IsTheorem th (~∃~A)%form <-> IsTheorem th (∀A)%form.
Proof.
 intros WF.
 split; intros (_ & axs & F & P); split; auto; exists axs; split; auto;
  subst; now apply NotExNot.
Qed.


(** We can "fix" a proof made with things not in the signature,
    or a signature badly used, or with remaining bounded vars. *)

Lemma thm_alt th T :
  IsTheorem th T <-> IsTheoremStrict th T.
Proof.
 split.
 - intros (W & axs & F & P).
   split; auto. rewrite Provable_alt in P.
   destruct P as (d & V & C).
   exists (forceWF th d).
   exists axs; split; split; auto using forceWF_WF, forceWF_Valid.
   unfold Claim in *. rewrite <- C. apply forceWF_claim.
   rewrite C, seq_WF. split; try apply W.
   rewrite ctx_WF. rewrite Forall_forall in *. intros x Hx.
   apply WCAxiom; auto.
 - intros (W & d & axs & V & F & C).
   split; auto.
   exists axs; split; auto.
   rewrite Provable_alt.
   exists d; split; auto.
   apply V.
Qed.

Lemma ax_thm th A : IsAxiom th A -> IsTheorem th A.
Proof.
 intros Ax.
 repeat split.
 - now apply WCAxiom.
 - eapply WCAxiom; eauto.
 - eapply WCAxiom; eauto.
 - exists [A]; split.
   + constructor; auto.
   + apply R'_Ax.
Qed.

Definition Inconsistent th := IsTheorem th False.

Definition Consistent th := ~IsTheorem th False.

Definition opt_finer {A} (o o' : option A) :=
 o=None \/ o=o'.

Definition optfun_finer {A B} (f f' : A -> option B) :=
 forall a, opt_finer (f a) (f' a).

Definition SignExtend sign sign' :=
  optfun_finer (sign.(funsymbs)) (sign'.(funsymbs)) /\
  optfun_finer (sign.(predsymbs)) (sign'.(predsymbs)).

Lemma signext_refl sign : SignExtend sign sign.
Proof.
 red; unfold optfun_finer, opt_finer. intuition.
Qed.

Lemma signext_trans sign1 sign2 sign3 :
 SignExtend sign1 sign2 -> SignExtend sign2 sign3 ->
 SignExtend sign1 sign3.
Proof.
 intros (F12,P12) (F23,P23).
 split; unfold optfun_finer, opt_finer in *; intros a.
 - destruct (F12 a) as [? | ->]; auto.
 - destruct (P12 a) as [? | ->]; auto.
Qed.

Lemma signext_check_term sign sign' (t:term) :
 SignExtend sign sign' -> check sign t = true -> check sign' t = true.
Proof.
 intros (SE,_).
 induction t using term_ind'; cbn; auto.
 destruct (SE f) as [->|<-]; try easy.
 destruct funsymbs; auto.
 destruct (length args =? a); auto.
 rewrite !forallb_forall; auto.
Qed.

Lemma signext_check sign sign' (f:formula) :
 SignExtend sign sign' -> check sign f = true -> check sign' f = true.
Proof.
 intros SE.
 induction f; cbn; auto.
 destruct (proj2 SE p) as [->|<-]; try easy.
 destruct predsymbs; auto.
 destruct (length l =? a); auto.
 rewrite !forallb_forall; eauto using signext_check_term.
 rewrite !lazy_andb_iff; intuition.
Qed.

Lemma signext_wc sign sign' (f:formula) :
  SignExtend sign sign' -> WC sign f -> WC sign' f.
Proof.
 intros SE ((CK & BC) & FV). split; eauto using signext_check.
Qed.

Definition Extend th1 th2 :=
 SignExtend th1 th2 /\
 forall T, IsTheorem th1 T -> IsTheorem th2 T.

Lemma extend_refl th : Extend th th.
Proof.
 split; auto using signext_refl.
Qed.

Lemma extend_trans th1 th2 th3 :
 Extend th1 th2 -> Extend th2 th3 -> Extend th1 th3.
Proof.
 intros (SE12,TH12) (SE23,TH23).
 split; eauto using signext_trans.
Qed.

Lemma Pr_relay c c' f :
  Pr logic (c ⊢ f) ->
  (forall A, In A c -> Pr logic (c' ⊢ A)) ->
  Pr logic (c' ⊢ f).
Proof.
 revert c' f.
 induction c.
 - intros c' f PR _.
   eapply Pr_weakening; eauto. constructor. now red.
 - intros c' f PR H. simpl in H.
   apply R_Imp_e with a; auto.
Qed.

Lemma extend_alt th1 th2 :
 Extend th1 th2 <->
  SignExtend th1 th2 /\
  forall A, IsAxiom th1 A -> IsTheorem th2 A.
Proof.
 split.
 - intros (SE,TT); split; auto.
   intros A HA. apply ax_thm in HA. auto.
 - intros (SE,AT); split; auto.
   intros T (CL & axs & Haxs & PR).
   split.
   + eapply signext_wc; eauto.
   + assert (exists axs2, Forall (IsAxiom th2) axs2 /\
                          forall A, In A axs -> Pr logic (axs2 ⊢ A)).
     { clear SE CL PR.
       induction axs.
       - exists []; split; auto.
       - inversion_clear Haxs.
         destruct IHaxs as (axs2 & U & V); auto.
         destruct (AT a) as (_ & axa & Haxa & PR); auto.
         exists (axa ++ axs2); split.
         + now apply Forall_app.
         + simpl. intros A [->|HA]; auto using Pr_app_l, Pr_app_r. }
     destruct H as (axs2 & Haxs2 & PR').
     exists axs2; split; auto.
     apply Pr_relay with axs; auto.
Qed.

Definition IsEqualityTheory th :=
 th.(predsymbs) "=" = Some 2 /\
 IsTheorem th (∀Pred "=" [#0; #0])%form /\
 forall A z,
   check th A = true ->
   BClosed A ->
   Names.Equal (fvars A) (Names.singleton z) ->
   IsTheorem th (∀∀(Pred "=" [#1;#0] -> fsubst z (#1) A -> fsubst z (#0) A))%form.

(** TODO: more about equality theories *)

Definition ConservativeExt th1 th2 :=
 Extend th1 th2 /\
 forall T, IsTheorem th2 T /\ WC th1 T <-> IsTheorem th1 T.

Lemma consext_alt th1 th2 :
 ConservativeExt th1 th2 <->
 (Extend th1 th2 /\
  forall T, IsTheorem th2 T -> check th1 T = true -> IsTheorem th1 T).
Proof.
 split; intros (U,V); split; auto.
 - intros T HT CK. apply V; split; auto.
   eapply WC_new_sign; eauto. apply HT.
 - intros T. split.
   + intros (W,X). apply V; auto. apply X.
   + split. now apply U. apply H.
Qed.

Lemma consext_inconsistency th1 th2 :
 ConservativeExt th1 th2 -> Inconsistent th2 <-> Inconsistent th1.
Proof.
 unfold Inconsistent. intros (_,<-). intuition.
Qed.

Lemma consext_consistency th1 th2 :
 ConservativeExt th1 th2 -> Consistent th1 <-> Consistent th2.
Proof.
 unfold Consistent. intros (_,<-). intuition.
Qed.

Lemma consext_refl th : ConservativeExt th th.
Proof.
 rewrite consext_alt.
 split; auto using extend_refl.
Qed.

Lemma consext_trans th1 th2 th3 :
  ConservativeExt th1 th2 -> ConservativeExt th2 th3 ->
  ConservativeExt th1 th3.
Proof.
 rewrite !consext_alt.
 intros (E12,T12) (E23,T23).
 split; eauto using extend_trans.
 intros T HT C.
 apply T12; auto.
 apply T23; auto.
 eapply signext_check; eauto. apply E12.
Qed.

(** If we only extend the signature, not the axioms, then
    it's a conservative extension.
    To prove this, normally we restrict a proof to the small
    signature, but here with [Pr] it's implicit (see thm_alt) *)

Lemma ext_sign_only th1 th2 :
 SignExtend th1 th2 ->
 (forall A, IsAxiom th1 A <-> IsAxiom th2 A) ->
 ConservativeExt th1 th2.
Proof.
 intros SE EQ. rewrite consext_alt. split.
 - apply extend_alt. split; auto.
   intros A. rewrite EQ. apply ax_thm.
 - intros T (CL & axs & F & PR) CK. split.
   + eapply WC_new_sign; eauto.
   + exists axs. split; auto.
     rewrite Forall_forall in *. intros x Hx. rewrite EQ; auto.
Qed.

(** Tweaking the function symbols of a signature *)

Definition modify_funsymbs sign modif :=
 {| funsymbs := modif (sign.(funsymbs));
    predsymbs := sign.(predsymbs) |}.

(** Henkin extension : from an existential theorem [∃A],
    adding a new constant [c] as witness and the new axiom [A(c)].
*)

Definition Henkin_sign sign c :=
  modify_funsymbs sign
   (fun funs f => if f =? c then Some 0 else funs f).

Definition Henkin_axiom Ax (A:formula) c :=
  fun f => Ax f \/ f = bsubst 0 (Cst c) A.

Lemma Henkin_signext sign c :
 sign.(funsymbs) c = None ->
 SignExtend sign (Henkin_sign sign c).
Proof.
 intros Hc.
 split; unfold optfun_finer, opt_finer; cbn; auto.
 intros a. case eqbspec; intros; subst; auto.
Qed.

Lemma Henkin_ax_wc th A c :
 th.(funsymbs) c = None ->
 IsTheorem th (∃A) ->
 forall B, Henkin_axiom th.(IsAxiom) A c B ->
           WC (Henkin_sign th c) B.
Proof.
 intros Hc (CL & _) B [HB| -> ].
 - eauto using signext_wc, Henkin_signext, WCAxiom.
 - apply bsubst_cst_WC.
   + simpl. now rewrite eqb_refl.
   + eauto using signext_wc, Henkin_signext.
Qed.

Definition Henkin_ext th A c
 (E:th.(funsymbs) c = None)
 (Thm:IsTheorem th (∃A)) :=
 {| sign := Henkin_sign th c;
    IsAxiom := Henkin_axiom th.(IsAxiom) A c;
    WCAxiom := Henkin_ax_wc th A c E Thm
 |}.

Lemma Henkin_consext th A c
 (E:th.(funsymbs) c = None)
 (Thm:IsTheorem th (∃A)) :
 ConservativeExt th (Henkin_ext th A c E Thm).
Proof.
 rewrite consext_alt.
 split.
 - apply extend_alt. split.
   + now apply Henkin_signext.
   + intros A0 HA0.
     apply ax_thm; simpl; left; auto.
 - intros T (CL & axs & F & PR) CK; simpl in *.
   split.
   + eapply WC_new_sign; eauto.
   + set (newAx := bsubst 0 (Cst c) A).
     set (axs' := filter (fun f => negb (f =? newAx)) axs).
     simpl in *.
     destruct Thm as (CLA & axsA & FA & PRA).
     assert (F' : Forall (IsAxiom th) axs').
     { rewrite Forall_forall in *.
       intros x. unfold axs'. rewrite filter_In.
       rewrite negb_true_iff, eqb_neq.
       intros (IN,NE); auto. apply F in IN.
       unfold Henkin_axiom in IN; intuition. }
     exists (axs' ++ axsA); split.
     * now apply Forall_app.
     * assert (PR' : Pr logic (newAx::axs' ⊢ T)).
       { eapply Pr_weakening; eauto.
         constructor. unfold axs'.
         intros v. simpl. rewrite filter_In.
         rewrite negb_true_iff, eqb_neq.
         destruct (eqbspec v newAx); intuition. }
       apply Provable_alt in PR'.
       destruct PR' as (d & V & C).
       assert (Names.Empty (fvars (axs' ++ axsA))).
       { intros v. unfold fvars, fvars_list.
         rewrite unionmap_in.
         intros (a & Hv & Ha).
         rewrite in_app_iff in Ha.
         revert v Hv. apply (WCAxiom th).
         rewrite Forall_forall in F', FA; intuition. }
       apply NamesP.empty_is_empty_1 in H.
       set (vars := Names.union (fvars A) (fvars d)).
       destruct (exist_fresh vars) as (x,Hx).
       apply (restrict_valid logic th x) in V; auto with set.
       assert (C' := claim_restrict th x d).
       rewrite C in C'. cbn in C'.
       rewrite (restrict_id th x T) in C'; auto.
       assert (map (restrict th x) axs' = axs').
       { apply map_id_iff. intros a Ha.
         apply restrict_id.
         apply WCAxiom. rewrite Forall_forall in F'; auto. }
       rewrite H0 in C'; clear H0.
       assert (restrict th x newAx = bsubst 0 (FVar x) A).
       { unfold newAx.
         rewrite restrict_bsubst. f_equal.
         - cbn. now rewrite E.
         - apply restrict_id. apply CLA. }
       rewrite H0 in C'; clear H0.
       apply Valid_Pr in V. rewrite C' in V.
       apply (R_Ex_e logic x _ A).
       { cbn. rewrite H. destruct d.
         unfold vars in Hx. cbn in C. subst s.
         cbn in Hx. namedec. }
       { now apply Pr_app_r. }
       { now apply (Pr_app_l _ (bsubst 0 (FVar x) A :: axs') axsA). }
Qed.

(** A variant of Henkin where the constant is already
    in the signature (but not used in the axioms nor in the
    existential theorem we consider). Not a conservative
    extension stricto sensu, but at least this preserves
    consistency. *)

Definition delcst sign c :=
  modify_funsymbs sign
   (fun funs f => if f =? c then None else funs f).

Lemma delcst_signext sign c :
 SignExtend (delcst sign c) sign.
Proof.
 split; unfold optfun_finer, opt_finer; cbn; auto.
 intros a. case eqbspec; intros; subst; auto.
Qed.

Definition AxiomsWithout th c :=
 forall A, IsAxiom th A -> WC (delcst th c) A.

Definition delcst_th th c (AW : AxiomsWithout th c) :=
 {| sign := delcst th c;
    IsAxiom := IsAxiom th;
    WCAxiom := AW
 |}.

Lemma delcst_consext th c (AW : AxiomsWithout th c) :
 ConservativeExt (delcst_th th c AW) th.
Proof.
 apply ext_sign_only. now apply delcst_signext.
 intuition.
Qed.

Lemma Henkin_ax_wf' th A c :
 th.(funsymbs) c = Some 0 ->
 IsTheorem th (∃A) ->
 forall B, Henkin_axiom th.(IsAxiom) A c B -> WC th B.
Proof.
 intros E Thm B [HB| -> ].
 - now apply WCAxiom.
 - apply bsubst_cst_WC; auto. apply Thm.
Qed.

Definition Henkin_halfext th A c
 (E : th.(funsymbs) c = Some 0)
 (Thm : IsTheorem th (∃A))
 :=
 {| sign := th;
    IsAxiom := Henkin_axiom th.(IsAxiom) A c;
    WCAxiom := Henkin_ax_wf' th A c E Thm
 |}.

(** The extension from [th - c] to [Henkin_halfext] is
    conservative, but not the one from [th] to [Henkin_halfext].
    For instance, [A(c)] is a theorem of the extension, and is
    in the language of [th], but it has no reason to be a theorem
    of [th]. *)

Lemma Henkin_halfext_consext th A c
 (E : th.(funsymbs) c = Some 0)
 (Thm : IsTheorem th (∃A))
 (AW : AxiomsWithout th c)
 (CK : check (delcst th c) A = true) :
 ConservativeExt (delcst_th th c AW)
                 (Henkin_halfext th A c E Thm).
Proof.
 rewrite consext_alt.
 split.
 - apply extend_trans with th.
   + apply delcst_consext.
   + rewrite extend_alt.
     split; cbn; auto using signext_refl.
     intros B HB. apply ax_thm. cbn. now left.
 - intros T.
   assert (E' : funsymbs (delcst_th th c AW) c = None).
   { cbn. now rewrite eqb_refl. }
   assert (Thm' : IsTheorem (delcst_th th c AW) (∃A)).
   { apply delcst_consext; split; auto. cbn.
     eapply WC_new_sign; eauto. apply Thm. }
   assert (HC := Henkin_consext _ _ _ E' Thm').
   rewrite consext_alt in HC.
   intros HT CKT.
   apply HC; auto.
   split.
   + eapply signext_wc.
     * apply Henkin_signext. cbn. now rewrite eqb_refl.
     * eapply WC_new_sign. apply CKT. apply HT.
   + cbn. apply HT.
Qed.

(** At least we preserve consistency *)

Lemma Henkin_halfext_consistent th A c
 (E : th.(funsymbs) c = Some 0)
 (Thm : IsTheorem th (∃A))
 (AW : AxiomsWithout th c)
 (CK : check (delcst th c) A = true) :
 Consistent th <-> Consistent (Henkin_halfext th A c E Thm).
Proof.
 rewrite <- (consext_consistency (delcst_th th c AW) th)
  by apply delcst_consext.
 apply consext_consistency. now apply Henkin_halfext_consext.
Qed.


(** Henkin extensions over *all* existential formulas. *)


(** The ultimate goal : building a theory that is saturated
    of Henkin witnesses. *)

Definition WitnessSaturated th :=
 forall A, IsTheorem th (∃ A) ->
           exists c,
             th.(funsymbs) c = Some 0 /\
             IsTheorem th (bsubst 0 (Cst c) A).

(** Actually, we won't bother considering only existential
    *theorems* (since anyway we'll have additionnal theorems
    later).
    Instead, for all [∃A] formula, we obtain "conditional"
    statements [∃A -> A(c)] for some constant [c].
    This is done by an Henkin extension based on the
    (classical) tautology [∃y((∃xA(x))->A(y))]. *)

(** So the intermediate goal is to build a theory which is
    "super-saturated" of Henkin witnesses : *)

Definition WitnessSuperSaturated th :=
 forall A, WC th (∃ A) ->
           exists c,
             th.(funsymbs) c = Some 0 /\
             IsTheorem th ((∃ A) -> bsubst 0 (Cst c) A).

(** Super-saturated implies saturated *)

Lemma supersaturated_saturated th :
 WitnessSuperSaturated th -> WitnessSaturated th.
Proof.
 intros WSS A Thm.
 destruct (WSS A (proj1 Thm)) as (c & Hc & Thm').
 exists c; eauto using Thm_Imp_e.
Qed.

(** We'll need an infinite pool of fresh constant names
    (axiomatized as an injective function from nat to string).
    Moreover, we should be able to recognize these names
    (for building the new signature). *)

Record NewCsts (sign : signature) :=
  { csts :> nat -> string;
    csts_inj : forall n m, csts n = csts m -> n = m;
    csts_ok : forall n, sign.(funsymbs) (csts n) = None;
    test : string -> bool;
    test_ok : forall s, test s = true <-> exists n, csts n = s }.

(** An important technical note : we cannot just iterate on
    formulas of the initial theory, otherwise, we'll end up
    with some final existential formulas not handled (the one
    using the constants we've added in the process). So we add
    all these "fresh" constants at first, and then do Henkin
    "half-extensions" (see above). *)

Definition HenkinAll_sign sign (nc : NewCsts sign) :=
  modify_funsymbs sign
   (fun funs f => if test _ nc f then Some 0 else funs f).

Lemma HenkinAll_signext sign (nc : NewCsts sign) :
 SignExtend sign (HenkinAll_sign sign nc).
Proof.
 split; unfold optfun_finer, opt_finer; cbn; auto.
 intros a. destruct test eqn:E; intros; subst; auto.
 left. apply test_ok in E. destruct E as (n & <-). apply csts_ok.
Qed.

Lemma exex_thm th A :
 logic = K ->
 WC th (∃A) -> IsTheorem th (∃ ((∃ A) -> A)).
Proof.
 intros LG CL.
 split.
 - destruct CL as ((CK & BC) & FC). repeat split.
   + cbn in *. now rewrite CK.
   + red. cbn. rewrite BC. cbn. apply BC.
   + red; red in FC. cbn in *. namedec.
 - exists []; split; auto.
   subst logic. apply ExEx.
   assert (Nat.pred (level A) = 0) by apply CL. lia.
Qed.

Fixpoint term_funs t :=
  match t with
  | FVar _ | BVar _ => Names.empty
  | Fun f l => Names.add f (Names.unionmap term_funs l)
  end.

Fixpoint form_funs f :=
  match f with
  | True | False => Names.empty
  | Pred p l => Names.unionmap term_funs l
  | Not f => form_funs f
  | Op _ f1 f2 => Names.union (form_funs f1) (form_funs f2)
  | Quant _ f => form_funs f
  end.

Lemma term_funs_ok sign t c :
 ~Names.In c (term_funs t) ->
 check (delcst sign c) t = check sign t.
Proof.
 revert t.
 fix IH 1. destruct t as [ | | f l]; cbn; auto.
 intros NI.
 case eqbspec; [namedec|].
 intros _. destruct funsymbs; auto.
 case eqb; auto.
 revert l NI.
 fix IH' 1. destruct l as [ |t l]; cbn; auto.
 intros NI'.
 rewrite IH by namedec. f_equal. apply IH'. namedec.
Qed.

Lemma form_funs_ok sign f c :
 ~Names.In c (form_funs f) ->
 check (delcst sign c) f = check sign f.
Proof.
 induction f; cbn; auto.
 - intros NI. destruct predsymbs; auto.
   case eqb; auto.
   revert l NI.
   induction l as [|t l]; cbn; auto.
   intros NI'.
   rewrite term_funs_ok by namedec. f_equal. apply IHl. namedec.
 - intros NI.
   now rewrite IHf1, IHf2 by namedec.
Qed.

Lemma form_funs_wc sign f c :
 ~Names.In c (form_funs f) ->
 WC (delcst sign c) f <-> WC sign f.
Proof.
 intros NI.
 split; intros W; eapply WC_new_sign; try apply W.
 - rewrite <- (form_funs_ok sign f c); auto. apply W.
 - rewrite form_funs_ok; auto. apply W.
Qed.

Fixpoint fresh_cst_loop n used candidates :=
 match n with
 | 0 => candidates 0
 | S n =>
   let c := candidates 0 in
   if Names.mem c used then
     let candidates' := fun n => candidates (S n) in
     fresh_cst_loop n (Names.remove c used) candidates'
   else c
 end.

Definition fresh_cst used candidates :=
  fresh_cst_loop (Names.cardinal used) used candidates.

Lemma fresh_cst_loop_in_cands n used candidates :
 Names.cardinal used = n ->
 exists m, fresh_cst_loop n used candidates = candidates m.
Proof.
 revert used candidates.
 induction n; simpl; intros used cs E; auto.
 - now exists 0.
 - destruct Names.mem eqn:M.
   + rewrite Names.mem_spec in M.
     destruct (IHn (Names.remove (cs 0) used)
                   (fun n : nat => cs (S n))) as (m,Hm).
     rewrite <- (@NamesP.remove_cardinal_1 used (cs 0)) in E; auto.
     now exists (S m).
   + now exists 0.
Qed.

Lemma fresh_cst_in_cands used candidates :
 exists m, fresh_cst used candidates = candidates m.
Proof.
 now apply fresh_cst_loop_in_cands.
Qed.

Lemma fresh_cst_loop_ok n used candidates :
 Names.cardinal used = n ->
 (forall n m, candidates n = candidates m -> n = m) ->
 ~Names.In (fresh_cst_loop n used candidates) used.
Proof.
 revert used candidates.
 induction n as [|n IH]; intros used cs E INJ.
 - apply NamesP.cardinal_inv_1 in E. namedec.
 - simpl. destruct Names.mem eqn:M.
   + set (used' := Names.remove (cs 0) used).
     set (cs' := fun n : nat => cs (S n)).
     specialize (IH used' cs').
     unfold used' in IH at 3. rewrite Names.remove_spec in IH.
     assert (Names.cardinal used' = n).
     { unfold used'.
       rewrite Names.mem_spec in M.
       rewrite <- (@NamesP.remove_cardinal_1 used (cs 0)) in E; auto. }
     intros IN. apply IH; auto.
     * unfold cs'. intros m p E'. apply INJ in E'; auto.
     * split; auto.
       destruct (fresh_cst_loop_in_cands n used' cs') as (m,->); auto.
       unfold cs'. intros E'. now apply INJ in E'.
   + rewrite <-Names.mem_spec. now rewrite M.
Qed.

Lemma fresh_cst_ok used candidates :
 (forall n m, candidates n = candidates m -> n = m) ->
 ~Names.In (fresh_cst used candidates) used.
Proof.
 now apply fresh_cst_loop_ok.
Qed.

Fixpoint HenkinAxList th (nc : NewCsts th) n :=
 match n with
 | 0 => []
 | S n =>
   let axs := HenkinAxList th nc n in
   let A := decode_form n in
   if wc (HenkinAll_sign th nc) (∃A)
   then
     let used := Names.union (form_funs A)
                             (Names.unionmap form_funs axs) in
     let c := fresh_cst used nc in
     ((∃A)-> bsubst 0 (Cst c) A)%form :: axs
   else axs
 end.

Lemma equivtheories_thm th th' :
 sign th = sign th' ->
 (forall A, IsAxiom th A <-> IsAxiom th' A) ->
 forall T, IsTheorem th T -> IsTheorem th' T.
Proof.
 intros E AX T (WF & axs & F & V).
 split.
 - now rewrite <- E.
 - exists axs; split; auto.
   rewrite Forall_forall in *. intros B HB. rewrite <- AX; auto.
Qed.

Lemma equivtheories_consistency th th' :
 sign th = sign th' ->
 (forall A, IsAxiom th A <-> IsAxiom th' A) ->
 Consistent th <-> Consistent th'.
Proof.
 intros E AX.
 split; intros H Thm.
 - apply (equivtheories_thm th' th) in Thm; auto.
   intros A. now symmetry.
 - apply (equivtheories_thm th th') in Thm; auto.
Qed.

Lemma delcst_HenkinAll_signext th (nc : NewCsts th) n :
 SignExtend th (delcst (HenkinAll_sign th nc) (nc n)).
Proof.
 split; cbn; unfold optfun_finer, opt_finer; auto.
 intros a. case eqbspec.
 - intros ->. left. apply csts_ok.
 - intros _. destruct (test th nc a) eqn:E; auto.
   left. apply test_ok in E. destruct E as (m, <-).
   apply csts_ok.
Qed.

Lemma HenkinAxList_wc th (nc : NewCsts th) n :
 forall A, IsAxiom th A \/ In A (HenkinAxList th nc n) ->
           WC (HenkinAll_sign th nc) A.
Proof.
 induction n as [|n IH].
 - simpl.
   intros A [HA|Fa]; [|easy].
   eauto using signext_wc, HenkinAll_signext, WCAxiom.
 - intros A [HA|IN]; auto.
   simpl in IN.
   set (f := decode_form n) in *.
   destruct (wc_spec (HenkinAll_sign th nc) (∃ f)); auto.
   set (used := Names.union _ _) in *.
   destruct (fresh_cst_in_cands used nc) as (m,Hm).
   assert (NI := fresh_cst_ok used nc (csts_inj _ nc)).
   set (c := fresh_cst used nc) in *.
   destruct IN as [<-|IN]; auto.
   apply Op_WC; auto. split; auto.
   apply bsubst_cst_WC; auto.
   simpl.
   replace (test _ nc c) with true; auto.
   symmetry. rewrite Hm, test_ok. now exists m.
Qed.

Definition HenkinSeq th (nc : NewCsts th) n :=
 {| sign := HenkinAll_sign th nc;
    IsAxiom := fun A => IsAxiom th A \/ In A (HenkinAxList th nc n);
    WCAxiom := HenkinAxList_wc th nc n
 |}.

Lemma HenkinSeq_extend th nc n :
 Extend th (HenkinSeq th nc n).
Proof.
 apply extend_alt. split.
 apply HenkinAll_signext.
 intros.
 apply ax_thm. simpl. now left.
Qed.

Lemma HenkinSeq_consistent th nc n :
 logic = K ->
 Consistent th <-> Consistent (HenkinSeq th nc n).
Proof.
 intros LG.
 induction n; simpl.
 - apply consext_consistency.
   apply ext_sign_only; cbn.
   + apply HenkinAll_signext.
   + intuition.
 - rewrite IHn.
   unfold Consistent, IsTheorem. simpl.
   set (f := decode_form n) in *.
   destruct wc eqn:Ew; [|reflexivity].
   assert (W : WC (HenkinAll_sign th nc) (∃ f)) by now apply wc_iff.
   set (used := Names.union _ _) in *.
   destruct (fresh_cst_in_cands used nc) as (m,Hm).
   assert (NI := fresh_cst_ok used nc (csts_inj _ nc)).
   set (c := fresh_cst used nc) in *.
   assert (E : (HenkinSeq th nc n).(funsymbs) c = Some 0).
   { simpl. replace (test th nc c) with true; auto.
     symmetry. rewrite Hm, test_ok. now exists m. }
   assert (Thm : IsTheorem (HenkinSeq th nc n)
                           (∃ ((∃ f) -> f))%form).
   { apply exex_thm; auto. }
   rewrite (Henkin_halfext_consistent _ ((∃ f) -> f)%form c E Thm).
   rewrite (equivtheories_consistency
              (Henkin_halfext (HenkinSeq th nc n) ((∃ f) -> f) c E Thm)
              (HenkinSeq th nc (S n))).
   + unfold Consistent, IsTheorem. simpl.
     fold f. rewrite Ew. reflexivity.
   + simpl; auto.
   + intros A. cbn - [decode_form].
     fold f. rewrite Ew. fold used. fold c. clearbody f.
     clearbody c.
     unfold Henkin_axiom. simpl.
     split.
     * intros [[H|H]|H]; auto.
       right; left. rewrite H.
       cbn. f_equal. f_equal. symmetry.
       apply form_level_bsubst_id.
       assert (pred (level f) = 0) by apply W. lia.
     * intros [H|[H|H]]; auto.
       right. rewrite <- H.
       cbn. f_equal. f_equal. symmetry.
       apply form_level_bsubst_id.
       assert (pred (level f) = 0) by apply W. lia.
   + intros A [HA|HA].
     * cbn. apply signext_wc with th; auto using WCAxiom.
       rewrite Hm. apply delcst_HenkinAll_signext.
     * rewrite form_funs_wc. apply WCAxiom. simpl. now right.
       eapply unionmap_notin; eauto; namedec.
   + clearbody f. clear Ew. rewrite form_funs_ok. cbn.
     destruct W as ((CK,?),?). cbn in CK. now rewrite CK.
     cbn. namedec.
Qed.

Lemma HenkinSeq_ax_grows th (nc : NewCsts th) n m A :
 n <= m ->
 IsAxiom (HenkinSeq th nc n) A ->
 IsAxiom (HenkinSeq th nc m) A.
Proof.
 induction 1; auto.
 intros Hn. specialize (IHle Hn). clear Hn.
 simpl.
 destruct wc; [|auto].
 simpl.
 cbn in IHle. intuition.
Qed.

Definition HenkinAll_axioms th (nc : NewCsts th) :=
 fun f => exists n, IsAxiom (HenkinSeq th nc n) f.

Lemma HenkinAll_ax_wc th (nc : NewCsts th) :
 forall B, HenkinAll_axioms th nc B ->
           WC (HenkinAll_sign th nc) B.
Proof.
 intros B (n & Hn).
 now apply WCAxiom in Hn.
Qed.

Definition HenkinAll_ext th (nc : NewCsts th) :=
 {| sign := HenkinAll_sign th nc;
    IsAxiom := HenkinAll_axioms th nc;
    WCAxiom := HenkinAll_ax_wc th nc
 |}.

Lemma HenkinAll_extend th (nc : NewCsts th) :
 Extend th (HenkinAll_ext th nc).
Proof.
 apply extend_alt.
 split.
 - apply HenkinAll_signext.
 - intros A HA. apply ax_thm. exists 0. now left.
Qed.

Lemma HenkinAll_Forall_max th (nc : NewCsts th) axs :
 Forall (HenkinAll_axioms th nc) axs ->
 exists n, Forall (IsAxiom (HenkinSeq th nc n)) axs.
Proof.
 induction axs.
 - intros _. now exists 0.
 - inversion_clear 1. destruct IHaxs as (n & F); auto.
   destruct H0 as (n' & H').
   exists (Nat.max n' n).
   constructor.
   apply HenkinSeq_ax_grows with n'; auto with *.
   rewrite Forall_forall in *.
   intros f Hf.
   apply HenkinSeq_ax_grows with n; auto with *.
Qed.

(** TODO: conservative extention over th. Not that useful... *)

Lemma HenkinAll_consistent th (nc : NewCsts th) :
 logic = K ->
 Consistent th -> Consistent (HenkinAll_ext th nc).
Proof.
 intros LG C (_ & axs & F & V).
 apply HenkinAll_Forall_max in F.
 destruct F as (n & F).
 rewrite (HenkinSeq_consistent th nc n) in C; auto. apply C.
 split.
 - apply False_WC.
 - exists axs; auto.
Qed.

Lemma HenkinAll_ext_supersaturated th (nc : NewCsts th) :
 logic = K ->
 WitnessSuperSaturated (HenkinAll_ext th nc).
Proof.
 red. intros LG A CL.
 set (n := code_form A).
 assert (Ax : forall A, In A (HenkinAxList th nc (S n)) ->
                   IsAxiom (HenkinAll_ext th nc) A).
 { intros B HB. exists (S n). now right. }
 cbn - [decode_form code_form] in Ax.
 assert (HA : decode_form n = A) by apply decode_code_form.
 rewrite HA in Ax.
 cbn in CL. apply wc_iff in CL. rewrite CL in Ax.
 set (used := Names.union _ _) in *.
 destruct (fresh_cst_in_cands used nc) as (m,Hm).
 assert (NI := fresh_cst_ok used nc (csts_inj _ nc)).
 set (c := fresh_cst used nc) in *.
 exists c; split.
 - rewrite Hm. cbn.
   replace (test th nc (nc m)) with true; auto.
   symmetry. apply test_ok. now exists m.
 - apply ax_thm. apply Ax. now left.
Qed.


(** Completeness of a theory *)

Definition Complete th :=
 forall A, WC th A ->
           IsTheorem th A \/ IsTheorem th (~A).

Definition DecidedBy (Ax:formula->Prop) f :=
 exists c, Forall Ax c /\ (Pr logic (c ⊢ f) \/ Pr logic (c ⊢ ~f)).

Fixpoint ax_completion th n : formula -> Prop :=
  match n with
  | 0 => IsAxiom th
  | S n =>
    let prev := ax_completion th n in
    fun f =>
      prev f \/
      (f = decode_form n /\ WC th f /\ ~DecidedBy prev f)
  end.

Definition ax_infinite_completion th :=
 fun f => exists n, ax_completion th n f.

Lemma completion_wc th n :
  forall A, ax_completion th n A -> WC th A.
Proof.
 induction n; simpl.
 - apply WCAxiom.
 - intuition.
Qed.

Lemma infcompletion_wc th :
  forall A, ax_infinite_completion th A -> WC th A.
Proof.
 intros A (n,HA). eapply completion_wc; eauto.
Qed.

Definition th_completion th n :=
 {| sign := th;
    IsAxiom := ax_completion th n;
    WCAxiom := completion_wc th n
 |}.

Definition th_infcompletion th :=
 {| sign := th;
    IsAxiom := ax_infinite_completion th;
    WCAxiom := infcompletion_wc th
 |}.

Lemma ax_completion_carac th n A :
 ax_completion th n A <->
 IsAxiom th A \/
  (exists m, m < n /\
             A = decode_form m /\
             WC th A /\
             ~DecidedBy (ax_completion th m) A).
Proof.
 induction n; simpl.
 - split; auto.
   intros [H|(m & Hm & _)]; auto. inversion Hm.
 - split; [intros [H|H]|intros [H|(m & Hm & H)]].
   + apply IHn in H. destruct H as [H|(m & Hm & H)]; auto.
     right; exists m; auto with *.
   + right. exists n; auto with *.
   + left. apply IHn. now left.
   + inversion Hm; try subst; auto.
     left. apply IHn. right. exists m. split; auto with *.
Qed.

Lemma ax_completion_grows th n m : n <= m ->
 forall A, ax_completion th n A -> ax_completion th m A.
Proof.
 intros LE A.
 rewrite !ax_completion_carac. intros [H|(k & Hk & H)]; auto.
 right. exists k. intuition; lia.
Qed.

Lemma ax_completion_init th :
 forall A, IsAxiom th A -> ax_infinite_completion th A.
Proof.
 intros A HA. now exists 0.
Qed.

Lemma th_infcompletion_extend th : Extend th (th_infcompletion th).
Proof.
 apply extend_alt. split; simpl.
 - firstorder.
 - intros A HA. apply ax_thm. simpl. now apply ax_completion_init.
Qed.

Lemma adhoc_partition {A} c (U V:A -> Prop) l :
 Forall (fun x => U x \/ (x=c/\ V x)) l ->
 exists l', Forall U l' /\ (ListSubset l l' \/ (V c /\ ListSubset l (c::l'))).
Proof.
 induction l.
 - exists []. split; auto. now left.
 - inversion_clear 1.
   destruct IHl as (l' & Hl' & OR); auto.
   destruct H0 as [H0|(<-,H0)].
   + exists (a::l'); firstorder.
   + exists l'; firstorder.
Qed.

Lemma th_completion_consistent th n :
 Consistent th -> Consistent (th_completion th n).
Proof.
 intros C.
 induction n; simpl.
 - unfold Consistent, IsTheorem. simpl. auto.
 - unfold Consistent, IsTheorem. simpl.
   set (fn := decode_form n). clearbody fn.
   intros (_ & axs & F & PR).
   apply adhoc_partition in F.
   destruct F as (axs' & F & [LS|((CL,ND),LS)]).
   + eapply Pr_weakening in PR; eauto.
     apply IHn. split. split; cbn; auto.
     exists axs'; cbn; auto.
   + apply ND.
     exists axs'; split; auto. right.
     apply R_Not_i.
     eapply Pr_weakening in PR; eauto.
Qed.

Lemma Forall_max th axs :
 Forall (ax_infinite_completion th) axs ->
 exists n, Forall (ax_completion th n) axs.
Proof.
 induction axs.
 - intros _. now exists 0.
 - inversion_clear 1. destruct IHaxs as (n & F); auto.
   destruct H0 as (n' & H0).
   exists (Nat.max n n'). constructor.
   apply ax_completion_grows with n'; auto with *.
   rewrite Forall_forall in F |- *.
   intros x Hx. apply ax_completion_grows with n; auto with *.
Qed.

Lemma th_infcompletion_consistent th :
 Consistent th -> Consistent (th_infcompletion th).
Proof.
 intros C.
 unfold Consistent, IsTheorem. simpl.
 intros (_ & axs & F & PR).
 apply Forall_max in F. destruct F as (n,F).
 apply (th_completion_consistent th n) in C.
 apply C.
 split. split; cbn; auto.
 now exists axs.
Qed.

Definition MyExcludedMiddle :=
 forall Ax A, DecidedBy Ax A \/ ~DecidedBy Ax A.

Lemma th_completion_decides_fn th n :
 MyExcludedMiddle ->
 WC th (decode_form n) ->
 DecidedBy (ax_completion th (S n)) (decode_form n).
Proof.
 intros EM.
 set (fn := decode_form n).
 intros CL.
 unfold DecidedBy.
 simpl.
 destruct (EM (ax_completion th n) fn) as [(axs & F & OR)|N].
 - exists axs; split; auto.
   rewrite Forall_forall in *; intuition.
 - exists [fn]; split; auto.
   left. apply R_Ax; simpl; auto.
Qed.

Lemma completion_infcompletion_extend th n A :
 IsTheorem (th_completion th n) A -> IsTheorem (th_infcompletion th) A.
Proof.
 intros (CL & axs & F & PR).
 split; auto.
 exists axs; split; auto.
 simpl in *.
 rewrite Forall_forall in *.
 intros x Hx. exists n; auto.
Qed.

Lemma th_infcompletion_complete th :
 MyExcludedMiddle ->
 Complete (th_infcompletion th).
Proof.
 intros EM A CL.
 destruct (th_completion_decides_fn th (code_form A)) as (axs & F & OR);
  rewrite ?decode_code_form in *; auto.
 set (n := code_form A) in *. clearbody n.
 destruct OR as [LF|RG]; [left|right];
  apply completion_infcompletion_extend with (S n).
 - split; auto. exists axs; auto.
 - split; auto. exists axs; auto.
Qed.

Theorem completion th :
 MyExcludedMiddle ->
 Consistent th ->
 exists th', Extend th th' /\ Consistent th' /\ Complete th'.
Proof.
 intros EM C.
 exists (th_infcompletion th); split; [|split].
 - apply th_infcompletion_extend.
 - now apply th_infcompletion_consistent.
 - apply th_infcompletion_complete; auto.
Qed.

(** Combining both saturation and completion *)

Definition supercomplete th (nc : NewCsts th) :=
 th_infcompletion (HenkinAll_ext th nc).

Lemma supercomplete_extend th nc :
 Extend th (supercomplete th nc).
Proof.
 eapply extend_trans; [|eapply th_infcompletion_extend].
 apply HenkinAll_extend.
Qed.

Lemma supercomplete_consistent th nc :
 logic = K ->
 Consistent th -> Consistent (supercomplete th nc).
Proof.
 intros LG C.
 apply th_infcompletion_consistent.
 apply HenkinAll_consistent; auto.
Qed.

Lemma supercomplete_supersaturated th nc :
 logic = K ->
 WitnessSuperSaturated (supercomplete th nc).
Proof.
 intros LG.
 intros A WF. cbn in WF.
 destruct (HenkinAll_ext_supersaturated th nc LG A WF) as (c & Hc & Thm).
 exists c. split; auto.
 unfold supercomplete.
 now apply th_infcompletion_extend.
Qed.

Lemma supercomplete_saturated th nc :
 logic = K ->
 WitnessSaturated (supercomplete th nc).
Proof.
 intros LG.
 now apply supersaturated_saturated, supercomplete_supersaturated.
Qed.

Lemma supercomplete_complete th nc :
 MyExcludedMiddle ->
 Complete (supercomplete th nc).
Proof.
 apply th_infcompletion_complete.
Qed.

Lemma supercompletion :
 logic = K ->
 MyExcludedMiddle ->
 forall th (nc : NewCsts th),
  Consistent th ->
  { th' |
   Extend th th' /\ Consistent th' /\
   WitnessSaturated th' /\ Complete th' }.
Proof.
 intros LG EM th nc C.
 exists (supercomplete th nc). split;[|split;[|split]].
 - now apply supercomplete_extend.
 - now apply supercomplete_consistent.
 - now apply supercomplete_saturated.
 - now apply supercomplete_complete.
Qed.

End SomeLogic.
