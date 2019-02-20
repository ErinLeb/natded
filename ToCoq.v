Require Import Defs Mix Proofs Meta Omega.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

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

Section SIGN.
 Variable sign : gen_signature.
 Variable M:Type.
 Variable funs : modfuns M.
 Variable preds : modpreds M.

 Definition Adequate :=
  (exists m:M, Logic.True) /\
  (forall s, sign.(gen_fun_symbs) s = get_arity (funs s)) /\
  (forall s, sign.(gen_pred_symbs) s = get_arity (preds s)).


Definition optbind {A B} (o:option A)(f:A->option B) : option B :=
 match o with
 | None => None
 | Some x => f x
 end.

Infix ">>=" := optbind (at level 60).

Definition build_args {A B} :=
  fix build n (l : list (option A)) : arity_fun A n B -> option B :=
    match n, l with
    | 0, [] => fun f => Some f
    | S n, Some a :: l => fun f => build n l (f a)
    | _, _ => fun _ => None
    end.

Definition eval_term genv lenv :=
  fix eval t :=
    match t with
    | FVar x => Some (genv x)
    | BVar n => nth_error lenv n
    | Fun f args => funs f >>= (fun '(existT _ n f) =>
                                  build_args n (List.map eval args) f)
    end.

Definition eval_op o :=
 match o with
 | And => and
 | Or => or
 | Imp => (fun p q : Prop => p -> q)
 end.

Definition eval_form genv :=
  fix eval lenv f :=
    match f with
    | True => Logic.True
    | False => Logic.False
    | Not f => ~(eval lenv f)
    | Op o f1 f2 => eval_op o (eval lenv f1) (eval lenv f2)
    | Pred p args =>
      let optp := preds p >>= fun '(existT _ n f) =>
                  build_args n (List.map (eval_term genv lenv) args) f
      in match optp with
         | Some p => p
         | None => Logic.False
         end
    | Quant All f => forall (m:M), eval (m::lenv) f
    | Quant Ex f => exists (m:M), eval (m::lenv) f
    end.

Definition eval_ctx genv lenv l :=
  forall f, In f l -> eval_form genv lenv f.

Definition eval_seq genv lenv '(Γ⊢C) :=
  eval_ctx genv lenv Γ ->
  eval_form genv lenv C.

Lemma max_0 n m : Nat.max n m = 0 <-> n=0 /\ m=0.
Proof.
 omega with *.
Qed.

Lemma list_max_0 l : list_max l = 0 <-> forall n, In n l -> n = 0.
Proof.
 induction l; simpl; rewrite ?max_0 in *; intuition.
Qed.

Lemma build_args_uncheck {A B} n l (f:arity_fun A n B) :
  List.length l <> n \/ In None l <-> build_args n l f = None.
Proof.
 revert n l f.
 induction n; destruct l as [|o l]; cbn; intros f; auto.
 - intuition easy.
 - intuition easy.
 - intuition easy.
 - destruct o. rewrite <- IHn; intuition; easy. intuition.
Qed.

Lemma eval_term_notNone :
 Adequate ->
 forall genv (t:term),
 check sign t = true /\ closed t = true <->
  eval_term genv [] t <> None.
Proof.
 intros (_ & AD & _) genv.
 fix IH 1. destruct t; cbn; auto; try easy.
 - destruct n; cbn in *; intuition.
 - rewrite AD. destruct (funs f) as [(n,fn)|]; cbn; [|intuition].
   case eqbspec; intro LN.
   + clear f.
     assert (E : build_args n (map (eval_term genv []) l) fn <> None
             <-> ~In None (map (eval_term genv []) l)).
     { rewrite <- build_args_uncheck, map_length. intuition. }
     rewrite E; clear E.
     clear n fn LN. rewrite eqb_eq. revert l.
     fix IH' 1. destruct l; cbn; auto.
     intuition.
     rewrite andb_true_iff, max_0.
     specialize (IH' l). specialize (IH t).
     unfold closed in IH. rewrite eqb_eq in IH.
     intuition.
   + rewrite <- build_args_uncheck, map_length. intuition.
Qed.

Lemma eval_term_ext genv genv' lenv t :
 (forall v, Vars.In v (fvars t) -> genv v = genv' v) ->
 eval_term genv lenv t = eval_term genv' lenv t.
Proof.
 revert t.
 fix IH 1. destruct t; cbn; auto.
 - intros. f_equal. apply H. varsdec.
 - intros. case (funs f) as [(n,fn)|]; cbn; auto. clear f.
   f_equal. clear n fn. revert l H.
   fix IH' 1. destruct l; cbn; auto.
   intros E. f_equal; auto with set.
Qed.

Lemma eval_form_ext genv genv' lenv f :
 (forall v, Vars.In v (fvars f) -> genv v = genv' v) ->
 eval_form genv lenv f <-> eval_form genv' lenv f.
Proof.
 revert lenv.
 induction f; cbn; auto; intros; f_equal; auto with set.
 - case (preds p) as [(n,fn)|]; cbn; [|reflexivity]; clear p.
   assert (E : map (eval_term genv lenv) l =
               map (eval_term genv' lenv) l).
   { clear n fn.
     revert l H.
     induction l; cbn; auto.
     intros E. f_equal; auto with set. apply eval_term_ext.
     auto with set. }
   now rewrite E.
 - rewrite IHf; intuition.
 - destruct o; cbn; rewrite IHf1, IHf2; intuition.
 - destruct q.
   + split; intros Hm m;
     [rewrite <-IHf|rewrite IHf]; auto with set.
   + split; intros (m,Hm); exists m;
     [rewrite <-IHf|rewrite IHf]; auto with set.
Qed.

Lemma eval_ctx_ext genv genv' lenv c :
 (forall v, Vars.In v (fvars c) -> genv v = genv' v) ->
 eval_ctx genv lenv c <-> eval_ctx genv' lenv c.
Proof.
 intros E.
 unfold eval_ctx.
 split; intros H f Hf.
 rewrite <- (eval_form_ext genv); auto with set.
 intros v Hv. apply E. unfold fvars, fvars_list.
 rewrite vars_unionmap_in. exists f. now split.
 rewrite (eval_form_ext genv); auto with set.
 intros v Hv. apply E. unfold fvars, fvars_list.
 rewrite vars_unionmap_in. exists f. now split.
Qed.

Lemma eval_term_more_lenv genv lenv lenv' t :
 eval_term genv lenv t <> None ->
 eval_term genv (lenv++lenv') t = eval_term genv (lenv) t.
Proof.
 revert t.
 fix IH 1. destruct t; cbn in *; intros H.
 - reflexivity.
 - rewrite nth_error_app1; trivial.
   now apply nth_error_Some.
 - case (funs f) as [(k,fk)|]; cbn in *; auto.
   f_equal.
   assert (H' : ~In None (map (eval_term genv lenv) l)).
   { rewrite <- build_args_uncheck in H. intuition. }
   clear H k fk f.
   revert l H'.
   fix IH' 1. destruct l; cbn; auto.
   intros H. f_equal; auto.
Qed.

Lemma eval_term_bsubst genv lenv u m n t :
 (level t <= S n)%nat ->
 (List.length lenv = n) ->
 eval_term genv [] u = Some m ->
 eval_term genv (lenv++[m]) t = eval_term genv lenv (bsubst n u t).
Proof.
 revert t.
 fix IH 1. destruct t; cbn; auto; intros LE Hn Hu.
 - case eqbspec; intros.
   + rewrite nth_error_app2; try omega.
     replace (n0 - length lenv) with 0 by omega. simpl.
     rewrite <- Hu. symmetry.
     apply (eval_term_more_lenv genv [] lenv). now rewrite Hu.
   + apply nth_error_app1. omega.
 - case (funs f) as [(k,fk)|]; cbn; auto. f_equal. clear f k fk.
   revert l LE Hn.
   fix IH' 1. destruct l; cbn; auto.
   intros LE Hn. f_equal.
   apply IH; auto. omega with *.
   apply IH'; auto. omega with *.
Qed.

Lemma eval_form_bsubst genv lenv u m n f :
 (level f <= S n)%nat ->
 (List.length lenv = n) ->
 eval_term genv [] u = Some m ->
 eval_form genv (lenv++[m]) f <-> eval_form genv lenv (bsubst n u f).
Proof.
 revert n lenv.
 induction f; cbn; auto; intros; f_equal; auto with set.
 - case (preds p) as [(k,fk)|]; cbn; [|reflexivity]; clear p.
   assert (E : map (eval_term genv (lenv++[m])) l =
               map (eval_term genv lenv) (map (bsubst n u) l)).
   { clear k fk.
     revert l H H0.
     induction l; cbn; auto.
     intros LE E. f_equal.
     apply eval_term_bsubst; auto. omega with *.
     apply IHl; auto. omega with *. }
   now rewrite E.
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

Lemma eval_form_bsubst0 genv u m f :
 (level f <= 1)%nat ->
 eval_term genv [] u = Some m ->
 eval_form genv [m] f <-> eval_form genv [] (bsubst 0 u f).
Proof.
 intros LE.
 now apply (eval_form_bsubst genv [] u m 0 f).
Qed.

Lemma eval_form_bsubst_adhoc genv m x f :
 (level f <= 1)%nat ->
 ~Vars.In x (fvars f) ->
 eval_form genv [m] f <->
 eval_form (fun v => if v =? x then m else genv v) []
  (bsubst 0 (FVar x) f).
Proof.
 intros.
 rewrite <- eval_form_bsubst0 with (m:=m); auto.
 - apply eval_form_ext. intros v Hv.
   case eqbspec; auto. intros ->. varsdec.
 - cbn. now rewrite eqb_refl.
Qed.

Definition eval_logic lg :=
 match lg with
 | Classic => forall A:Prop, A\/~A
 | Intuiti => Logic.True
 end.

Lemma correctness :
 Adequate ->
 forall (d:derivation) logic genv,
 eval_logic logic ->
 check sign d = true ->
 closed d = true ->
 valid_deriv logic d = true ->
 eval_seq genv [] (dseq d).
Proof.
 intros AD.
 induction d as [r s ds IH] using derivation_ind'.
 cbn - [valid_deriv_step].
 intros logic genv.
 rewrite !lazy_andb_iff. rewrite eqb_eq, !max_0.
 intros LG ((Cr,Cs),Cds) (Lr&Ls&Lds) (V,Vds).
 assert (IH' : Forall (fun d => forall genv, eval_seq genv [] (dseq d)) ds).
 { rewrite Forall_forall, forallb_forall in *.
   rewrite list_max_0 in Lds.
   intros d Hd genv'. eapply IH; eauto.
   unfold closed. rewrite eqb_eq. apply Lds. now apply in_map. }
 clear IH Cds Vds. mytac; cbn in *; intros Hc.
 - now apply Hc, list_mem_in.
 - destruct (H1 genv); auto.
 - intro Hf. apply (H1 genv).
   intros ? [<-|E]; auto.
 - apply (H6 genv); auto.
 - intuition.
 - apply (H genv); auto.
 - apply (H genv); auto.
 - intuition.
 - intuition.
 - destruct (H4 genv); auto.
   + apply (H6 genv). intros ? [<-|E]; auto.
   + apply (H5 genv). intros ? [<-|E]; auto.
 - intros Hf1. apply (H2 genv). intros ? [<-|E]; auto.
 - apply (H1 genv); auto.
 - intros m.
   rewrite <- not_false_iff_true, negb_false_iff in H0.
   rewrite Vars.mem_spec in H0.
   rewrite eval_form_bsubst_adhoc with (x:=v).
   apply H4.
   rewrite <- (eval_ctx_ext genv); auto.
   intros y Hy. case eqbspec; auto. intros <-. varsdec.
   omega with *.
   varsdec.
 - assert (Hwit := eval_term_notNone AD genv wit).
   destruct (eval_term genv [] wit) as [m|] eqn:E.
   + rewrite <- eval_form_bsubst0 with (m:=m); auto.
     rewrite !max_0 in Lds. intuition.
   + unfold closed in Hwit. rewrite eqb_eq in Hwit. intuition.
 - assert (Hwit := eval_term_notNone AD genv wit).
   destruct (eval_term genv [] wit) as [m|] eqn:E.
   + exists m.
     rewrite eval_form_bsubst0 with (u:=wit); auto.
     rewrite !max_0 in Ls. intuition.
   + unfold closed in Hwit. rewrite eqb_eq in Hwit. intuition.
 - destruct (H3 genv) as (m & Hm); auto.
   rewrite <- not_false_iff_true, negb_false_iff in H0.
   rewrite Vars.mem_spec in H0.
   rewrite eval_form_bsubst_adhoc with (x:=v) in Hm.
   erewrite eval_form_ext.
   eapply H5.
   intros A [<-|HA]. eapply Hm.
   rewrite <- (eval_form_ext genv); auto.
   intros y Hy. case eqbspec; auto. intros ->.
   assert (Vars.In v (fvars c)).
   { unfold fvars, fvars_list. rewrite vars_unionmap_in.
     exists A; now split. }
   varsdec.
   intros y Hy. cbn. case eqbspec; auto. intros ->. varsdec.
   rewrite !max_0 in Lds. intuition.
   varsdec.
 - destruct (LG (eval_form genv [] f0)); auto.
   destruct (H genv). intros A [<-|HA]; auto.
Qed.

Lemma coherence :
 Adequate ->
 forall (d:derivation) logic,
 eval_logic logic ->
 check sign d = true ->
 closed d = true ->
 valid_deriv logic d = true ->
 dseq d <> ([]⊢False)%form.
Proof.
 intros AD d logic LG CH CL VD E.
 case AD. intros (m,_) _.
 set (genv := fun (_:variable) => m).
 assert (eval_seq genv [] (dseq d)).
 { apply correctness with logic; auto. }
 rewrite E in H. cbn in *. apply H. intros A. destruct 1.
Qed.

End SIGN.
