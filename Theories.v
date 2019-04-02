
(** Notion of 1st order theories *)

Require Import Arith Omega Defs Proofs Mix Meta Countable.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope eqb_scope.

Definition ClosedFormulaOn (sign:gen_signature) (A:formula) :=
  check sign A = true /\ closed A /\ Vars.Empty (fvars A).

Record theory :=
  { sign :> gen_signature;
    IsAxiom : formula -> Prop;
    WfAxiom : forall A, IsAxiom A -> ClosedFormulaOn sign A }.

Implicit Type th : theory.

Section SomeLogic.
Variable logic : Defs.logic.

Definition IsTheorem th T :=
  ClosedFormulaOn th T /\
  exists axs, Forall th.(IsAxiom) axs /\ Pr logic (axs ⊢ T).

Lemma ax_thm th A : IsAxiom th A -> IsTheorem th A.
Proof.
 intros Ax.
 repeat split.
 - now apply WfAxiom.
 - eapply WfAxiom; eauto.
 - eapply WfAxiom; eauto.
 - exists [A]; split.
   + apply Forall_forall. simpl; intuition; now subst.
   + apply R_Ax; simpl; auto.
Qed.

Definition Inconsistent th := IsTheorem th False.

Definition Consistent th := ~IsTheorem th False.

Definition opt_finer {A} (o o' : option A) :=
 o=None \/ o=o'.

Definition optfun_finer {A B} (f f' : A -> option B) :=
 forall a, opt_finer (f a) (f' a).

Definition SignExtend sign sign' :=
  optfun_finer (sign.(gen_fun_symbs)) (sign'.(gen_fun_symbs)) /\
  optfun_finer (sign.(gen_pred_symbs)) (sign'.(gen_pred_symbs)).

Lemma signext_check_term sign sign' (t:term) :
 SignExtend sign sign' -> check sign t = true -> check sign' t = true.
Proof.
 intros (SE,_).
 induction t using term_ind'; cbn; auto.
 destruct (SE f) as [->|<-]; try easy.
 destruct gen_fun_symbs; auto.
 destruct (length args =? a); auto.
 rewrite !forallb_forall; auto.
Qed.

Lemma signext_check sign sign' (f:formula) :
 SignExtend sign sign' -> check sign f = true -> check sign' f = true.
Proof.
 intros SE.
 induction f; cbn; auto.
 destruct (proj2 SE p) as [->|<-]; try easy.
 destruct gen_pred_symbs; auto.
 destruct (length l =? a); auto.
 rewrite !forallb_forall; eauto using signext_check_term.
 rewrite !lazy_andb_iff; intuition.
Qed.

Definition Extend th1 th2 :=
 SignExtend th1 th2 /\
 forall T, IsTheorem th1 T -> IsTheorem th2 T.

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
   intros T ((CK & CL & EM) & axs & Haxs & PR).
   repeat split; auto.
   + eapply signext_check; eauto.
   + assert (exists axs2, Forall (IsAxiom th2) axs2 /\
                          forall A, In A axs -> Pr logic (axs2 ⊢ A)).
     { clear SE CK CL  EM PR.
       induction axs.
       - exists []; split; auto.
       - inversion_clear Haxs.
         destruct IHaxs as (axs2 & U & V); auto.
         destruct (AT a) as (_ & axa & Haxa & PR); auto.
         exists (axa ++ axs2); split.
         + rewrite Forall_forall in *. intros x. rewrite in_app_iff. intuition.
         + simpl. intros A [->|HA].
           * eapply Pr_weakening; eauto. constructor.
             intros x Hx. rewrite in_app_iff. intuition.
           * eapply Pr_weakening with (axs2 ⊢ A); eauto. constructor.
             intros x Hx. rewrite in_app_iff. intuition. }
     destruct H as (axs2 & Haxs2 & PR').
     exists axs2; split; auto.
     apply Pr_relay with axs; auto.
Qed.

Definition IsEqualityTheory th :=
 th.(gen_pred_symbs) "=" = Some 2 /\
 IsTheorem th (∀Pred "=" [#0; #0])%form /\
 forall A z,
   check (th.(sign)) A = true ->
   closed A ->
   Vars.Equal (fvars A) (Vars.singleton z) ->
   IsTheorem th (∀∀(Pred "=" [#1;#0] -> fsubst z (#1) A -> fsubst z (#0) A))%form.

(** TODO: more about equality theories *)

Definition ConservativeExt th1 th2 :=
 Extend th1 th2 /\
 forall T, IsTheorem th2 T -> check th1 T = true -> IsTheorem th1 T.

Lemma consext_inconsistency th1 th2 :
 ConservativeExt th1 th2 -> Inconsistent th2 -> Inconsistent th1.
Proof.
 unfold Inconsistent. intros (U,V).
 intros H2.
 apply V; auto.
Qed.

Lemma consext_consistency th1 th2 :
 ConservativeExt th1 th2 -> Consistent th1 -> Consistent th2.
Proof.
 unfold Consistent in *. intros U V W. apply V.
 eapply consext_inconsistency; eauto.
Qed.

Lemma ext_sign_only th1 th2 :
 SignExtend th1 th2 ->
 (forall A, IsAxiom th1 A <-> IsAxiom th2 A) ->
 ConservativeExt th1 th2.
Proof.
Admitted.

Definition Henkin_sign sign c :=
  {| gen_fun_symbs := fun f => if f =? c then Some 0 else
                                  sign.(gen_fun_symbs) f;
     gen_pred_symbs := sign.(gen_fun_symbs) |}.

Definition Henkin_axiom Ax (A:formula) c :=
  fun f => f = (bsubst 0 (Fun c []) A) \/ Ax f.

Lemma Henkin_ax_wf th A c :
 th.(gen_fun_symbs) c = None ->
 IsTheorem th (∃A) ->
 forall B, Henkin_axiom th.(IsAxiom) A c B ->
           ClosedFormulaOn (Henkin_sign th.(sign) c) B.
Proof.
Admitted.

Definition Henkin_ext th A c
 (E:th.(gen_fun_symbs) c = None)
 (Thm:IsTheorem th (∃A)) :=
 {| sign := Henkin_sign th.(sign) c;
    IsAxiom := Henkin_axiom th.(IsAxiom) A c;
    WfAxiom := Henkin_ax_wf th A c E Thm
 |}.

Lemma Henkin_consext th A c
 (E:th.(gen_fun_symbs) c = None)
 (Thm:IsTheorem th (∃A)) :
 ConservativeExt th (Henkin_ext th A c E Thm).
Proof.
Admitted.

Definition Complete th :=
 forall A, ClosedFormulaOn th A ->
           IsTheorem th A \/ IsTheorem th (~A)%form.

Definition DecidedBy (Ax:formula->Prop) f :=
 exists c, Forall Ax c /\ (Pr logic (c ⊢ f) \/ Pr logic (c ⊢ ~f)).

Fixpoint ax_completion th n : formula -> Prop :=
  match n with
  | 0 => IsAxiom th
  | S n =>
    let prev := ax_completion th n in
    fun f =>
      prev f \/
      (f = decode_form n /\ ClosedFormulaOn th f /\ ~DecidedBy prev f)
  end.

Definition ax_infinite_completion th :=
 fun f => exists n, ax_completion th n f.

Lemma completion_wf th n :
  forall A, ax_completion th n A -> ClosedFormulaOn th A.
Proof.
 induction n; simpl.
 - apply WfAxiom.
 - intuition.
Qed.

Lemma infcompletion_wf th :
  forall A, ax_infinite_completion th A -> ClosedFormulaOn th A.
Proof.
 intros A (n,HA). eapply completion_wf; eauto.
Qed.

Definition th_completion th n :=
 {| sign := th.(sign);
    IsAxiom := ax_completion th n;
    WfAxiom := completion_wf th n
 |}.

Definition th_infcompletion th :=
 {| sign := th.(sign);
    IsAxiom := ax_infinite_completion th;
    WfAxiom := infcompletion_wf th
 |}.

Lemma ax_completion_carac th n A :
 ax_completion th n A <->
 IsAxiom th A \/
  (exists m, m < n /\
             A = decode_form m /\
             ClosedFormulaOn th A /\
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
   + inversion Hm; subst; auto.
     left. apply IHn. right. exists m. split; auto with *.
Qed.

Lemma ax_completion_grows th n m : n <= m ->
 forall A, ax_completion th n A -> ax_completion th m A.
Proof.
 intros LE A.
 rewrite !ax_completion_carac. intros [H|(k & Hk & H)]; auto.
 right. exists k; auto with *.
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

Axiom MyExcludedMiddle : forall Ax A, DecidedBy Ax A \/ ~DecidedBy Ax A.

Lemma th_completion_decides_fn th n :
 ClosedFormulaOn th (decode_form n) ->
 DecidedBy (ax_completion th (S n)) (decode_form n).
Proof.
 set (fn := decode_form n).
 intros CL.
 unfold DecidedBy.
 simpl.
 destruct (MyExcludedMiddle (ax_completion th n) fn) as [(axs & F & OR)|N].
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
 Complete (th_infcompletion th).
Proof.
 intros A CL.
 destruct (th_completion_decides_fn th (code_form A)) as (axs & F & OR);
  rewrite ?decode_code_form in *; auto.
 set (n := code_form A) in *. clearbody n.
 destruct OR as [LF|RG]; [left|right];
  apply completion_infcompletion_extend with (S n).
 - split; auto. exists axs; auto.
 - split; auto. exists axs; auto.
Qed.

Theorem completion th :
 Consistent th ->
 exists th', Extend th th' /\ Consistent th' /\ Complete th'.
Proof.
 intros C.
 exists (th_infcompletion th); split; [|split].
 - apply th_infcompletion_extend.
 - now apply th_infcompletion_consistent.
 - apply th_infcompletion_complete.
Qed.


End SomeLogic.