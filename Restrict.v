
(** * Restrict a proof or derivation to a signature and/or a level *)

(** The NatDed development, Pierre Letouzey, 2019-2020.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Defs NameProofs Mix Wellformed.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

Implicit Type t u : term.
Implicit Type f : formula.

(** We could restrict a proof to use only some signature
    (and only correctly). For that we replace unknown or incorrect
    terms by a free variable, and unknown or incorrect predicates
    by False. *)

Fixpoint restrict_term sign x t :=
 match t with
 | Fun f l =>
   match sign.(funsymbs) f with
   | None => FVar x
   | Some ar =>
     if length l =? ar then Fun f (map (restrict_term sign x) l)
     else FVar x
   end
 | _ => t
 end.

Fixpoint restrict sign x f :=
 match f with
 | True => True
 | False => False
 | Pred p l =>
   match sign.(predsymbs) p with
   | None => False
   | Some ar =>
     if length l =? ar then Pred p (map (restrict_term sign x) l)
     else False
   end
 | Not f => Not (restrict sign x f)
 | Op o f1 f2 => Op o (restrict sign x f1) (restrict sign x f2)
 | Quant q f => Quant q (restrict sign x f)
 end.

Definition restrict_ctx sign x c :=
  map (restrict sign x) c.

Definition restrict_seq sign x '(c ⊢ f) :=
  (restrict_ctx sign x c ⊢ restrict sign x f).

Definition restrict_rule sign x r :=
 match r with
 | All_e t => All_e (restrict_term sign x t)
 | Ex_i t => Ex_i (restrict_term sign x t)
 | _ => r
 end.

Fixpoint restrict_deriv sign x d :=
 let '(Rule r s l) := d in
 Rule (restrict_rule sign x r)
      (restrict_seq sign x s)
      (map (restrict_deriv sign x) l).

Lemma claim_restrict sign x d :
  claim (restrict_deriv sign x d) =
  restrict_seq sign x (claim d).
Proof.
 now destruct d.
Qed.

Lemma restrict_term_level sign x t :
  level (restrict_term sign x t) <= level t.
Proof.
 revert t.
 fix IH 1. destruct t as [ | | f l]; cbn; auto with *.
 destruct funsymbs; cbn; auto with *.
 case eqbspec; cbn; auto with *.
 intros _. clear f a.
 revert l.
 fix IH' 1. destruct l as [ |t l]; cbn; auto using Nat.max_le_compat with *.
Qed.

Lemma restrict_term_bclosed sign x t :
 BClosed t -> BClosed (restrict_term sign x t).
Proof.
 unfold BClosed. assert (H := restrict_term_level sign x t). auto with *.
Qed.

Lemma restrict_level sign x f :
  level (restrict sign x f) <= level f.
Proof.
 induction f; cbn; auto using Nat.max_le_compat with *.
 destruct predsymbs; cbn; auto with *.
 case eqbspec; cbn; auto with *.
 intros _. clear p a.
 induction l as [|t l IH]; cbn;
   auto using Nat.max_le_compat, restrict_term_level.
Qed.

Lemma restrict_bclosed sign x f :
 BClosed f -> BClosed (restrict sign x f).
Proof.
 unfold BClosed. assert (H := restrict_level sign x f). auto with *.
Qed.

Lemma restrict_term_fvars sign x t :
 Names.Subset (fvars (restrict_term sign x t))
              (Names.add x (fvars t)).
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto with *.
 destruct funsymbs; cbn; auto with *.
 case eqbspec; cbn; auto with *.
 intros _. apply subset_unionmap_map'; auto.
Qed.

Lemma restrict_form_fvars sign x f :
 Names.Subset (fvars (restrict sign x f))
              (Names.add x (fvars f)).
Proof.
 induction f; cbn; auto with *.
 destruct predsymbs; cbn; auto with *.
 case eqbspec; cbn; auto with *.
 intros _. apply subset_unionmap_map'.
 intros t _. apply restrict_term_fvars.
Qed.

Lemma restrict_ctx_fvars sign x c :
 Names.Subset (fvars (restrict_ctx sign x c))
              (Names.add x (fvars c)).
Proof.
 unfold restrict_ctx.
 apply subset_unionmap_map'.
 intros f _. apply restrict_form_fvars.
Qed.

Lemma restrict_seq_fvars sign x s :
 Names.Subset (fvars (restrict_seq sign x s))
              (Names.add x (fvars s)).
Proof.
 destruct s; cbn. rewrite restrict_ctx_fvars, restrict_form_fvars.
 namedec.
Qed.

Lemma restrict_rule_fvars sign x r :
 Names.Subset (fvars (restrict_rule sign x r))
              (Names.add x (fvars r)).
Proof.
 destruct r; cbn; rewrite ?restrict_term_fvars; auto with *.
Qed.

Lemma restrict_deriv_fvars sign x d :
 Names.Subset (fvars (restrict_deriv sign x d))
              (Names.add x (fvars d)).
Proof.
 induction d as [r s ds IH] using derivation_ind'; cbn.
 rewrite restrict_rule_fvars, restrict_seq_fvars.
 rewrite Forall_forall in IH.
 apply subset_unionmap_map' in IH. rewrite IH. namedec.
Qed.


Lemma restrict_term_bsubst sign x n (t u:term) :
  restrict_term sign x (bsubst n u t) =
  bsubst n (restrict_term sign x u) (restrict_term sign x t).
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn; auto.
 - case eqbspec; auto.
 - destruct funsymbs; cbn; auto with *.
   rewrite map_length.
   case eqbspec; cbn; auto.
   intros _.
   f_equal. rewrite !map_map. apply map_ext_iff; auto.
Qed.

Lemma restrict_lift sign x t k :
 restrict_term sign x (lift k t) = lift k (restrict_term sign x t).
Proof.
 induction t as [ | |f l IH] using term_ind'; cbn; auto.
 - case Nat.leb_spec; auto.
 - destruct funsymbs; cbn; auto with *.
   rewrite map_length.
   case eqbspec; cbn; auto.
   intros _. f_equal. rewrite !map_map. apply map_ext_iff; auto.
Qed.

Lemma restrict_bsubst sign x n t f :
  restrict sign x (bsubst n t f) =
  bsubst n (restrict_term sign x t) (restrict sign x f).
Proof.
 revert n t.
 induction f; cbn; intros; f_equal; auto.
 destruct predsymbs; cbn; auto with *.
 rewrite map_length.
 case eqbspec; cbn; auto.
 intros _.
 f_equal. rewrite !map_map.
 apply map_ext_iff; auto using restrict_term_bsubst.
 rewrite <- restrict_lift. auto.
Qed.

Ltac solver :=
  try econstructor; auto;
  try match goal with
  | H : ~Names.In _ _ -> Valid _ ?d |- Valid _ ?d => apply H; namedec end;
  try (unfold Claim; rewrite claim_restrict);
  try match goal with
  | H : claim ?d = _ |- context [claim ?d] => now rewrite H end.

Lemma restrict_valid logic sign x (d:derivation) :
 ~Names.In x (fvars d) ->
 Valid logic d ->
 Valid logic (restrict_deriv sign x d).
Proof.
 induction 2; cbn - [Names.union] in *; try (solver; fail).
  - constructor. now apply in_map.
  - constructor.
    + cbn. rewrite restrict_ctx_fvars, restrict_form_fvars. namedec.
    + apply IHValid; namedec.
    + unfold Claim. rewrite claim_restrict. rewrite H2. simpl.
      f_equal. apply restrict_bsubst.
  - rewrite restrict_bsubst.
    constructor.
    + apply IHValid; namedec.
    + unfold Claim. rewrite claim_restrict. now rewrite H1.
  - constructor.
    + apply IHValid; namedec.
    + unfold Claim. rewrite claim_restrict. rewrite H1.
      cbn. now rewrite restrict_bsubst.
  - apply V_Ex_e with (restrict sign x A).
    + cbn. rewrite restrict_ctx_fvars, !restrict_form_fvars. namedec.
    + apply IHValid1; namedec.
    + apply IHValid2; namedec.
    + unfold Claim. rewrite claim_restrict. now rewrite H1.
    + unfold Claim. rewrite claim_restrict. rewrite H2.
      cbn. f_equal. f_equal. apply restrict_bsubst.
Qed.

Lemma restrict_term_check sign x (t:term) :
 check sign (restrict_term sign x t) = true.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 destruct funsymbs eqn:E; try easy.
 case eqbspec; cbn; auto.
 intros <-.
 rewrite E, map_length, eqb_refl, forallb_map, forallb_forall; auto.
Qed.

Lemma restrict_form_check sign x (f:formula) :
 check sign (restrict sign x f) = true.
Proof.
 induction f; cbn; auto.
 - destruct predsymbs eqn:E; try easy.
   case eqbspec; cbn; auto.
   intros <-.
   rewrite E, map_length, eqb_refl, forallb_map, forallb_forall;
    auto using restrict_term_check.
 - now rewrite IHf1, IHf2.
Qed.

Lemma restrict_ctx_check sign x (c:context) :
 check sign (restrict_ctx sign x c) = true.
Proof.
 induction c as [ |f c IH]; cbn; auto.
 rewrite andb_true_iff; split; auto using restrict_form_check.
Qed.

Lemma restrict_seq_check sign x (s:sequent) :
 check sign (restrict_seq sign x s) = true.
Proof.
 destruct s. cbn.
 now rewrite restrict_ctx_check, restrict_form_check.
Qed.

Lemma restrict_rule_check sign x (r:rule_kind) :
 check sign (restrict_rule sign x r) = true.
Proof.
 destruct r; cbn; auto using restrict_term_check.
Qed.

Lemma restrict_deriv_check sign x (d:derivation) :
 check sign (restrict_deriv sign x d) = true.
Proof.
 induction d as [r s ds IH] using derivation_ind'; cbn.
 rewrite restrict_rule_check, restrict_seq_check.
 rewrite forallb_map, forallb_forall, Forall_forall in *; auto.
Qed.

Lemma restrict_term_id sign x (t:term) :
 check sign t = true -> restrict_term sign x t = t.
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 destruct funsymbs; try easy.
 rewrite lazy_andb_iff. intros (->,H). f_equal.
 rewrite forallb_forall in H.
 apply map_id_iff; auto.
Qed.

Lemma restrict_id sign x (f:formula) :
 check sign f = true -> restrict sign x f = f.
Proof.
 induction f; cbn; intros; f_equal; auto.
 - destruct predsymbs; try easy.
   rewrite lazy_andb_iff in H. destruct H as (->,H). f_equal.
   rewrite forallb_forall in H.
   apply map_id_iff; auto using restrict_term_id.
 - rewrite ?lazy_andb_iff in H; intuition.
 - rewrite ?lazy_andb_iff in H; intuition.
Qed.

Lemma restrict_ctx_id sign x (c:context) :
 check sign c = true -> restrict_ctx sign x c = c.
Proof.
 induction c as [|f c IH]; cbn; rewrite ?andb_true_iff; intros;
  f_equal; auto.
 - now apply restrict_id.
 - now apply IH.
Qed.

Lemma restrict_seq_id sign x (s:sequent) :
 check sign s = true -> restrict_seq sign x s = s.
Proof.
 destruct s as (c,f). cbn. rewrite lazy_andb_iff. intros (Hc,Hf).
 f_equal. now apply restrict_ctx_id. now apply restrict_id.
Qed.

(** When a derivation has some bounded variables, we could
    replace them by anything free. *)

Fixpoint forcelevel_term n x t :=
 match t with
 | FVar _ => t
 | BVar m => if m <? n then t else FVar x
 | Fun f l => Fun f (map (forcelevel_term n x) l)
 end.

Fixpoint forcelevel n x f :=
 match f with
 | True => True
 | False => False
 | Pred p l => Pred p (map (forcelevel_term n x) l)
 | Not f => Not (forcelevel n x f)
 | Op o f1 f2 => Op o (forcelevel n x f1) (forcelevel n x f2)
 | Quant q f => Quant q (forcelevel (S n) x f)
 end.

Definition forcelevel_ctx x (c:context) :=
  map (forcelevel 0 x) c.

Definition forcelevel_seq x '(c ⊢ f) :=
 forcelevel_ctx x c ⊢ forcelevel 0 x f.

Definition forcelevel_rule x r :=
 match r with
 | All_e wit => All_e (forcelevel_term 0 x wit)
 | Ex_i wit => Ex_i (forcelevel_term 0 x wit)
 | _ => r
 end.

Fixpoint forcelevel_deriv x d :=
 let '(Rule r s ds) := d in
 Rule (forcelevel_rule x r) (forcelevel_seq x s)
      (map (forcelevel_deriv x) ds).

Lemma claim_forcelevel x d :
 claim (forcelevel_deriv x d) = forcelevel_seq x (claim d).
Proof.
 now destruct d.
Qed.

Lemma forcelevel_term_fvars n x t :
 Names.Subset (fvars (forcelevel_term n x t)) (Names.add x (fvars t)).
Proof.
 induction t as [ | | f l IH] using term_ind';
   cbn - [Nat.ltb]; auto with *.
 - case Nat.ltb_spec; cbn; auto with *.
 - apply subset_unionmap_map'; auto.
Qed.

Lemma forcelevel_fvars n x f :
 Names.Subset (fvars (forcelevel n x f)) (Names.add x (fvars f)).
Proof.
 revert n.
 induction f; cbn; intros; auto with *.
 - apply subset_unionmap_map'.
   intros t _. apply forcelevel_term_fvars.
 - rewrite IHf1, IHf2. namedec.
Qed.

Lemma forcelevel_ctx_fvars x (c:context) :
 Names.Subset (fvars (forcelevel_ctx x c)) (Names.add x (fvars c)).
Proof.
 unfold forcelevel_ctx. unfold fvars, fvars_list.
 apply subset_unionmap_map'.
 intros f _. apply forcelevel_fvars.
Qed.

Lemma forcelevel_term_level n x t :
  level (forcelevel_term n x t) <= n.
Proof.
 induction t as [ | | f l IH] using term_ind';
   cbn - [Nat.ltb]; auto with *.
 - case Nat.ltb_spec; cbn; auto with *.
 - rewrite map_map. apply list_max_map_le; auto.
Qed.

Lemma forcelevel_term_bclosed x t :
  BClosed (forcelevel_term 0 x t).
Proof.
 assert (H := forcelevel_term_level 0 x t). auto with *.
Qed.

Lemma forcelevel_level n x f :
 level (forcelevel n x f) <= n.
Proof.
 revert n.
 induction f; cbn; intros; auto with *.
 - rewrite map_map. apply list_max_map_le.
   auto using forcelevel_term_level.
 - apply max_le; auto.
 - specialize (IHf (S n)). auto with *.
Qed.

Lemma forcelevel_bclosed x f :
 BClosed (forcelevel 0 x f).
Proof.
 assert (H := forcelevel_level 0 x f). auto with *.
Qed.

Lemma forcelevel_ctx_bclosed x c :
 BClosed (forcelevel_ctx x c).
Proof.
 induction c as [|f c IH]; cbn; auto.
 unfold BClosed, level, level_list. cbn.
 now rewrite forcelevel_bclosed, IH.
Qed.

Lemma forcelevel_seq_bclosed x s :
 BClosed (forcelevel_seq x s).
Proof.
 destruct s; cbn.
 unfold BClosed, level, level_seq.
 now rewrite forcelevel_bclosed, forcelevel_ctx_bclosed.
Qed.

Lemma forcelevel_rule_bclosed x r :
 BClosed (forcelevel_rule x r).
Proof.
 destruct r; cbn; auto.
 unfold BClosed; cbn; apply forcelevel_term_bclosed.
 unfold BClosed; cbn; apply forcelevel_term_bclosed.
Qed.

Lemma forcelevel_deriv_bclosed x d :
 BClosed (forcelevel_deriv x d).
Proof.
 induction d as [r s ds IH] using derivation_ind'.
 unfold BClosed; cbn.
 rewrite forcelevel_rule_bclosed, forcelevel_seq_bclosed.
 simpl.
 apply list_max_0.
 rewrite map_map.
 intros n. rewrite in_map_iff. intros (d & <- & IN).
 rewrite Forall_forall in IH. now apply IH.
Qed.

Lemma forcelevel_term_id n x t :
 level t <= n -> forcelevel_term n x t = t.
Proof.
 induction t as [ | | f l IH] using term_ind';
   cbn - [Nat.ltb]; intros H; auto with *.
 - case Nat.ltb_spec; cbn; auto; omega.
 - f_equal.
   rewrite list_max_map_le in H.
   apply map_id_iff; auto.
Qed.

Lemma forcelevel_id n x f :
 level f <= n -> forcelevel n x f = f.
Proof.
 revert n.
 induction f; cbn; intros; rewrite ?max_le in *; f_equal; intuition.
 apply map_id_iff. rewrite list_max_map_le in H.
 auto using forcelevel_term_id.
Qed.

Lemma forcelevel_ctx_id x c :
 BClosed c -> forcelevel_ctx x c = c.
Proof.
 induction c as [|f c IH]; cbn; auto.
 unfold BClosed, level, level_list; cbn. rewrite max_0.
 intros (Hf,Hc); f_equal; auto. apply forcelevel_id. now rewrite Hf.
Qed.

Lemma forcelevel_seq_id x s :
 BClosed s -> forcelevel_seq x s = s.
Proof.
 destruct s; cbn. unfold BClosed, level, level_seq. rewrite max_0.
 intros (Hc,Hf). f_equal. now apply forcelevel_ctx_id.
 apply forcelevel_id. now rewrite Hf.
Qed.

Lemma forcelevel_rule_id x r :
 BClosed r -> forcelevel_rule x r = r.
Proof.
 destruct r; cbn; auto.
 unfold BClosed; cbn; intros Hw. f_equal.
  apply forcelevel_term_id. now rewrite Hw.
 unfold BClosed; cbn; intros Hw. f_equal.
  apply forcelevel_term_id. now rewrite Hw.
Qed.

Lemma forcelevel_deriv_id x d :
 BClosed d -> forcelevel_deriv x d = d.
Proof.
 induction d as [r s ds IH] using derivation_ind'; cbn.
 unfold BClosed. cbn. rewrite !max_0.
 intros (Hr & Hs & Hds).
 f_equal.
 now apply forcelevel_rule_id.
 now apply forcelevel_seq_id.
 rewrite Forall_forall in IH.
 rewrite list_max_map_0 in Hds.
 apply map_id_iff. auto.
Qed.

Lemma forcelevel_bsubst_term n x (u t:term) :
  forcelevel_term n x (bsubst n u t) =
  bsubst n (forcelevel_term n x u) (forcelevel_term (S n) x t).
Proof.
 induction t as [ | | f l IH] using term_ind'; cbn; auto.
 - case eqbspec.
   + intros; subst.
     case Nat.leb_spec; try omega. cbn. now rewrite eqb_refl.
   + simpl.
     case Nat.leb_spec.
     * intros LE NE. cbn - [Nat.ltb].
       case eqbspec; [intros; exfalso; omega|intros _].
       case Nat.ltb_spec; auto; omega.
     * intros LT _. cbn - [Nat.ltb].
       case Nat.ltb_spec; auto; omega.
 - f_equal. rewrite !map_map. apply map_ext_iff; auto.
Qed.

Lemma forcelevel_lift0 n x u :
  forcelevel_term (S n) x (lift 0 u) = lift 0 (forcelevel_term n x u).
Proof.
 induction u using term_ind'; cbn -[Nat.ltb]; auto.
 - change (S n0 <? S n) with (n0 <? n).
   case Nat.ltb_spec; cbn; auto.
 - f_equal. rewrite !map_map. apply map_ext_in; auto.
Qed.

Lemma forcelevel_bsubst n x u f :
  forcelevel n x (bsubst n u f) =
  bsubst n (forcelevel_term n x u) (forcelevel (S n) x f).
Proof.
 revert n u.
 induction f; cbn; intros; f_equal; auto.
 - rewrite !map_map. apply map_ext_iff.
   auto using forcelevel_bsubst_term.
 - rewrite IHf.
   f_equal. apply forcelevel_lift0.
Qed.

Ltac solver' :=
  try econstructor; auto;
  try match goal with
  | H : ~Names.In _ _ -> Valid _ ?d |- Valid _ ?d => apply H; namedec end;
  try (unfold Claim; rewrite claim_forcelevel);
  try match goal with
  | H : claim ?d = _ |- context [claim ?d] => now rewrite H end.

Lemma forcelevel_deriv_valid logic x (d:derivation) :
 ~Names.In x (fvars d) ->
 Valid logic d ->
 Valid logic (forcelevel_deriv x d).
Proof.
 induction 2; cbn - [Names.union] in *; try (solver'; fail).
 - constructor. now apply in_map.
 - constructor.
   + cbn. rewrite forcelevel_ctx_fvars, forcelevel_fvars.
     namedec.
   + apply IHValid. namedec.
   + unfold Claim; rewrite claim_forcelevel, H2. cbn. f_equal.
     rewrite forcelevel_bsubst; auto.
 - rewrite forcelevel_bsubst.
   constructor; auto.
   + apply IHValid; namedec.
   + unfold Claim. now rewrite claim_forcelevel, H1.
 - constructor; auto.
   + apply IHValid. namedec.
   + unfold Claim; rewrite claim_forcelevel, H1. cbn. f_equal.
     apply forcelevel_bsubst.
 - apply V_Ex_e with (forcelevel 1 x A).
   + cbn. rewrite forcelevel_ctx_fvars, !forcelevel_fvars. namedec.
   + apply IHValid1. namedec.
   + apply IHValid2. namedec.
   + unfold Claim; now rewrite claim_forcelevel, H1.
   + unfold Claim; rewrite claim_forcelevel, H2. cbn. f_equal.
     f_equal. apply forcelevel_bsubst; auto.
Qed.

(** [restrict] and [forcelevel] commute *)

Lemma restrict_forcelevel_term sign x n y t :
 restrict_term sign x (forcelevel_term n y t) =
 forcelevel_term n y (restrict_term sign x t).
Proof.
 induction t as [ | | f l IH] using term_ind';
  cbn - [Nat.ltb]; auto.
 - case Nat.ltb_spec; auto.
 - destruct funsymbs as [ar|] eqn:E; auto.
   rewrite map_length.
   case eqbspec; cbn; auto.
   intros _. f_equal.
   rewrite !map_map.
   apply map_ext_iff; auto.
Qed.

Lemma restrict_forcelevel sign x n y f :
 restrict sign x (forcelevel n y f) =
 forcelevel n y (restrict sign x f).
Proof.
 revert n.
 induction f; cbn; intros; f_equal; auto.
 destruct predsymbs as [ar|] eqn:E; auto.
 rewrite map_length.
 case eqbspec; cbn; auto.
 intros _. f_equal.
 rewrite !map_map.
 apply map_ext_iff; auto using restrict_forcelevel_term.
Qed.

Lemma restrict_forcelevel_ctx sign x y c :
 restrict_ctx sign x (forcelevel_ctx y c) =
 forcelevel_ctx y (restrict_ctx sign x c).
Proof.
 induction c; cbn; f_equal; auto using restrict_forcelevel.
Qed.

Lemma restrict_forcelevel_seq sign x y s :
 restrict_seq sign x (forcelevel_seq y s) =
 forcelevel_seq y (restrict_seq sign x s).
Proof.
 destruct s; cbn; f_equal;
 auto using restrict_forcelevel, restrict_forcelevel_ctx.
Qed.

Lemma restrict_forcelevel_rule sign x y r :
 restrict_rule sign x (forcelevel_rule y r) =
 forcelevel_rule y (restrict_rule sign x r).
Proof.
 destruct r; cbn; f_equal; auto using restrict_forcelevel_term.
Qed.

Lemma restrict_forcelevel_deriv sign x y d :
 restrict_deriv sign x (forcelevel_deriv y d) =
 forcelevel_deriv y (restrict_deriv sign x d).
Proof.
 induction d as [r s ds IH] using derivation_ind'; cbn.
 f_equal.
 - apply restrict_forcelevel_rule.
 - apply restrict_forcelevel_seq.
 - rewrite !map_map. apply map_ext_iff.
   rewrite Forall_forall in IH; auto.
Qed.

(** Combining [restrict] and [forcelevel] on a derivation *)

Definition forceWF sign (d:derivation) :=
 let vars := fvars d in
 let x := fresh vars in
 let y := fresh (Names.add x vars) in
 forcelevel_deriv y (restrict_deriv sign x d).

Lemma forceWF_WF sign d : WF sign (forceWF sign d).
Proof.
 unfold forceWF. split.
 - rewrite <- restrict_forcelevel_deriv.
   apply restrict_deriv_check.
 - apply forcelevel_deriv_bclosed.
Qed.

Lemma forceWF_Valid lg sign d :
 Valid lg d -> Valid lg (forceWF sign d).
Proof.
 intros V.
 unfold forceWF.
 set (vars := fvars d) in *.
 set (x := fresh vars).
 set (y := fresh _).
 apply forcelevel_deriv_valid.
 - rewrite restrict_deriv_fvars. apply fresh_ok.
 - apply restrict_valid; auto. apply fresh_ok.
Qed.

Lemma forceWF_claim sign d :
 WF sign (claim d) -> claim (forceWF sign d) = claim d.
Proof.
 intros W.
 unfold forceWF.
 set (vars := fvars d) in *.
 set (x := fresh vars).
 set (y := fresh _).
 rewrite claim_forcelevel, claim_restrict.
 destruct d. cbn. cbn in W. rewrite restrict_seq_id by apply W.
 apply forcelevel_seq_id. apply W.
Qed.
