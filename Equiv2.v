
(** * Conversion from Named derivations to Locally Nameless derivations *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import RelationClasses Arith Omega.
Require Import Defs NameProofs Equiv Alpha Alpha2 Meta.
Require Nam Mix.
Import ListNotations.
Import Nam Nam.Form.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.

(** Contexts *)

Definition nam2mix_ctx (c:Nam.context) : Mix.context :=
 List.map (nam2mix []) c.

Definition mix2nam_ctx (c:Mix.context) : Nam.context :=
 List.map (mix2nam []) c.

Lemma nam2mix_ctx_eqb (c c' : Nam.context) :
 (nam2mix_ctx c =? nam2mix_ctx c') = (c =? c').
Proof.
 revert c'.
 induction c; destruct c'; cbn; auto.
 rewrite nam2mix_eqb. case eqb; auto.
Qed.

Lemma nam2mix_ctx_fvars (c : Nam.context) :
 Names.Equal (Mix.fvars (nam2mix_ctx c)) (Ctx.freevars c).
Proof.
 induction c as [|f c IH]; cbn; auto.
 - namedec.
 - rewrite nam2mix_fvars, IH. simpl. namedec.
Qed.

(** Sequents *)

Definition nam2mix_seq '(Nam.Seq c f) : Mix.sequent :=
  Mix.Seq (nam2mix_ctx c) (nam2mix [] f).

Definition mix2nam_seq '(Mix.Seq c f) : Nam.sequent :=
  Nam.Seq (mix2nam_ctx c) (mix2nam [] f).

Lemma nam2mix_seq_eqb (s s' : Nam.sequent) :
 (nam2mix_seq s =? nam2mix_seq s') = (s =? s').
Proof.
 destruct s as (c,f), s' as (c',f'); cbn.
 now rewrite nam2mix_ctx_eqb, nam2mix_eqb.
Qed.


(** Rule kinds *)

Definition nam2mix_rule r :=
  match r with
  | Nam.Ax => Mix.Ax
  | Nam.Tr_i => Mix.Tr_i
  | Nam.Fa_e => Mix.Fa_e
  | Nam.Not_i => Mix.Not_i
  | Nam.Not_e => Mix.Not_e
  | Nam.And_i => Mix.And_i
  | Nam.And_e1 => Mix.And_e1
  | Nam.And_e2 => Mix.And_e2
  | Nam.Or_i1 => Mix.Or_i1
  | Nam.Or_i2 => Mix.Or_i2
  | Nam.Or_e => Mix.Or_e
  | Nam.Imp_i => Mix.Imp_i
  | Nam.Imp_e => Mix.Imp_e
  | Nam.All_i v => Mix.All_i v
  | Nam.All_e t => Mix.All_e (nam2mix_term [] t)
  | Nam.Ex_i t => Mix.Ex_i (nam2mix_term [] t)
  | Nam.Ex_e v => Mix.Ex_e v
  | Nam.Absu => Mix.Absu
  end.

Definition mix2nam_rule r :=
  match r with
  | Mix.Ax => Nam.Ax
  | Mix.Tr_i => Nam.Tr_i
  | Mix.Fa_e => Nam.Fa_e
  | Mix.Not_i => Nam.Not_i
  | Mix.Not_e => Nam.Not_e
  | Mix.And_i => Nam.And_i
  | Mix.And_e1 => Nam.And_e1
  | Mix.And_e2 => Nam.And_e2
  | Mix.Or_i1 => Nam.Or_i1
  | Mix.Or_i2 => Nam.Or_i2
  | Mix.Or_e => Nam.Or_e
  | Mix.Imp_i => Nam.Imp_i
  | Mix.Imp_e => Nam.Imp_e
  | Mix.All_i v => Nam.All_i v
  | Mix.All_e t => Nam.All_e (mix2nam_term [] t)
  | Mix.Ex_i t => Nam.Ex_i (mix2nam_term [] t)
  | Mix.Ex_e v => Nam.Ex_e v
  | Mix.Absu => Nam.Absu
  end.

(** Derivations *)

Fixpoint nam2mix_deriv (d:Nam.derivation) :=
  let '(Nam.Rule r s ds) := d in
  Mix.Rule
    (nam2mix_rule r)
    (nam2mix_seq s)
    (List.map nam2mix_deriv ds).

Fixpoint mix2nam_deriv (d:Mix.derivation) :=
  let '(Mix.Rule r s ds) := d in
  Nam.Rule
    (mix2nam_rule r)
    (mix2nam_seq s)
    (List.map mix2nam_deriv ds).

Ltac break :=
 rewrite <- ?andb_lazy_alt;
 match goal with
 | |- _ = match ?f ?x with _ => _ end => destruct x
 | |- _ = match ?x with _ => _ end => destruct x
 | |- match ?f (?g ?x) with _ => _ end = _ => destruct x
 | |- match ?f ?x with _ => _ end = _ => destruct x
 | |- match ?x with _ => _ end = _ => destruct x
 end.

Lemma nam2mix_valid_deriv_step logic (d:Nam.derivation) :
  Mix.valid_deriv_step logic (nam2mix_deriv d) =
  Nam.valid_deriv_step logic d.
Proof.
 destruct d as [[ ] s ds]; cbn -[subst];
  repeat (break; cbn -[αeq subst]; auto);
  rewrite ?andb_false_r, <- ?nam2mix_seq_eqb,
          <- ?nam2mix_ctx_eqb, <- ?nam2mix_eqb; auto.
 - unfold nam2mix_ctx.
   induction c as [|A c IH]; cbn; auto.
   rewrite <-orb_lazy_alt. f_equal; auto.
   now rewrite nam2mix_eqb.
 - now destruct d.
 - now destruct d.
 - now destruct d, d0.
 - now destruct d.
 - now destruct d.
 - now destruct d, d0.
 - now destruct d.
 - now destruct d.
 - cbn.
   apply eq_true_iff_eq.
   rewrite !andb_true_iff.
   rewrite !negb_true_iff, <- !not_true_iff_false.
   rewrite !Names.mem_spec.
   rewrite !eqb_eq.
   split; intros ((U,V),W); split; try split; auto.
   + change (Mix.FVar x) with (nam2mix_term [] (Var x)) in V.
     rewrite <- nam2mix_subst_bsubst0 in V.
     apply nam2mix_rename_iff3; auto.
     rewrite nam2mix_fvars in W. simpl in W. namedec.
   + rewrite <- nam2mix_ctx_fvars. rewrite <- U. namedec.
   + rewrite V.
     change (Mix.FVar x) with (nam2mix_term [] (Nam.Var x)).
     rewrite <- nam2mix_subst_bsubst0.
     symmetry. apply nam2mix_subst_nop.
   + rewrite U, V, nam2mix_ctx_fvars.
     rewrite nam2mix_fvars. simpl. namedec.
 - rewrite nam2mix_subst_bsubst0.
   rewrite nam2mix_term_bclosed, eqb_refl.
   apply andb_true_r.
 - rewrite nam2mix_subst_bsubst0.
   rewrite nam2mix_term_bclosed, eqb_refl.
   apply andb_true_r.
 - cbn.
   apply eq_true_iff_eq.
   rewrite !andb_true_iff.
   rewrite !negb_true_iff, <- !not_true_iff_false.
   rewrite !Names.mem_spec.
   rewrite !eqb_eq.
   split.
   + intros (((U,V),W),X); repeat split; auto.
     * rewrite <-V in U; exact U.
     * change (Mix.FVar x) with (nam2mix_term [] (Var x)) in W.
       rewrite <- nam2mix_subst_bsubst0 in W.
       apply nam2mix_rename_iff3; auto.
       rewrite nam2mix_fvars in X. simpl in X. namedec.
     * revert X. destruct s. cbn in *. injection U as <- <-.
       rewrite <-!nam2mix_ctx_fvars, !nam2mix_fvars. simpl.
       clear. namedec.
   + intros ((U,(V,W)),Z); repeat split; auto.
     * rewrite U. f_equal; auto.
     * rewrite W.
       change (Mix.FVar x) with (nam2mix_term [] (Nam.Var x)).
       rewrite <- nam2mix_subst_bsubst0.
       symmetry. apply nam2mix_subst_nop.
     * revert Z. destruct s. cbn in *.
       rewrite V, W. injection U as <- <-.
       rewrite <-!nam2mix_ctx_fvars, !nam2mix_fvars.
       simpl. clear. namedec.
Qed.

Lemma nam2mix_valid_deriv logic (d:Nam.derivation) :
  Mix.valid_deriv logic (nam2mix_deriv d) =
  Nam.valid_deriv logic d.
Proof.
 revert d.
 fix IH 1. destruct d.
 cbn -[Mix.valid_deriv_step Nam.valid_deriv_step].
 rewrite <- nam2mix_valid_deriv_step.
 cbn -[Mix.valid_deriv_step Nam.valid_deriv_step].
 destruct Mix.valid_deriv_step; auto.
 revert l.
 fix IH' 1. destruct l; simpl.
 reflexivity.
 now rewrite IH, IH'.
Qed.

Lemma mix_nam_mix_rule (r:Mix.rule_kind) :
  Mix.BClosed r ->
  nam2mix_rule (mix2nam_rule r) = r.
Proof.
 unfold Mix.BClosed.
 destruct r; cbn; intros CL; auto.
 f_equal. apply mix_nam_mix_term, CL.
 f_equal. apply mix_nam_mix_term, CL.
Qed.

Lemma mix_nam_mix_ctx (c:Mix.context) :
  Mix.BClosed c ->
  nam2mix_ctx (mix2nam_ctx c) = c.
Proof.
 unfold Mix.BClosed.
 induction c as [|f c IH]; cbn; intros CL; auto.
 apply max_0 in CL. destruct CL as (CL,CL').
 f_equal; auto using mix_nam_mix.
Qed.

Lemma mix_nam_mix_seq (s:Mix.sequent) :
  Mix.BClosed s ->
  nam2mix_seq (mix2nam_seq s) = s.
Proof.
 unfold Mix.BClosed.
 destruct s; cbn. intros CL.
 apply max_0 in CL. destruct CL as (CL,CL').
 f_equal.
 - apply mix_nam_mix_ctx; auto.
 - apply mix_nam_mix; auto.
Qed.

Lemma mix_nam_mix_deriv (d:Mix.derivation) :
  Mix.BClosed d ->
  nam2mix_deriv (mix2nam_deriv d) = d.
Proof.
 unfold Mix.BClosed.
 induction d as [r s l IH] using Mix.derivation_ind'.
 cbn; intros CL.
 rewrite !max_0 in CL. destruct CL as (CL & CL' & CL'').
 f_equal.
 - now apply mix_nam_mix_rule.
 - now apply mix_nam_mix_seq.
 - rewrite map_map. apply map_id_iff. intros d Hd.
   rewrite Forall_forall in IH.
   apply IH; auto.
   rewrite list_max_map_0 in CL''; auto.
Qed.

Lemma mix2nam_valid_deriv logic (d:Mix.derivation) :
  Mix.BClosed d ->
  Nam.valid_deriv logic (mix2nam_deriv d) =
  Mix.valid_deriv logic d.
Proof.
 intros CL.
 now rewrite <- nam2mix_valid_deriv, mix_nam_mix_deriv.
Qed.

(** nam2mix and BClosed *)

Lemma nam2mix_ctx_bclosed c : Mix.BClosed (nam2mix_ctx c).
Proof.
 unfold Mix.BClosed.
 induction c; cbn; auto. rewrite nam2mix_bclosed. auto.
Qed.

Lemma nam2mix_seq_bclosed s : Mix.BClosed (nam2mix_seq s).
Proof.
 unfold Mix.BClosed.
 destruct s; cbn. now rewrite nam2mix_bclosed, nam2mix_ctx_bclosed.
Qed.

Lemma nam2mix_rule_bclosed r : Mix.BClosed (nam2mix_rule r).
Proof.
 unfold Mix.BClosed.
 destruct r; cbn; auto; apply nam2mix_term_bclosed.
Qed.

Lemma nam2mix_deriv_bclosed d : Mix.BClosed (nam2mix_deriv d).
Proof.
 unfold Mix.BClosed.
 revert d.
 fix IH 1. destruct d as (r,s,l); cbn.
 rewrite nam2mix_rule_bclosed, nam2mix_seq_bclosed. simpl.
 revert l.
 fix IH' 1. destruct l as [|d l]; cbn; trivial.
 rewrite IH. simpl. apply IH'.
Qed.

(** Alpha equivalence for contexts, sequents, rules, derivations *)

Instance eqb_rule : Eqb Nam.rule_kind :=
 fun r r' =>
   match r, r' with
   | Nam.Ax, Nam.Ax
   | Nam.Tr_i, Nam.Tr_i
   | Nam.Fa_e, Nam.Fa_e
   | Nam.Not_i, Nam.Not_i
   | Nam.Not_e, Nam.Not_e
   | Nam.And_i, Nam.And_i
   | Nam.And_e1, Nam.And_e1
   | Nam.And_e2, Nam.And_e2
   | Nam.Or_i1, Nam.Or_i1
   | Nam.Or_i2, Nam.Or_i2
   | Nam.Or_e, Nam.Or_e
   | Nam.Imp_i, Nam.Imp_i
   | Nam.Imp_e, Nam.Imp_e
   | Nam.Absu, Nam.Absu => true
   | Nam.All_i v, Nam.All_i v'
   | Nam.Ex_e v, Nam.Ex_e v' => v =? v'
   | Nam.All_e t, Nam.All_e t'
   | Nam.Ex_i t, Nam.Ex_i t' => t =? t'
   | _, _ => false
   end.

Instance eqb_deriv : Eqb Nam.derivation :=
 fix eqb_deriv d d' :=
   match d, d' with
   | Rule r s l, Rule r' s' l' =>
     (r =? r') &&& (s =? s') &&& (list_forallb2 eqb_deriv l l')
   end.

Definition AlphaEq_ctx (c c':Nam.context) := (c =? c') = true.
Definition AlphaEq_seq (s s':Nam.sequent) := (s =? s') = true.
Definition AlphaEq_rule (r r':Nam.rule_kind) := (r =? r') = true.
Definition AlphaEq_deriv (d d':Nam.derivation) := (d =? d') = true.

(** [nam2mix] is canonical for contexts, sequents, rules, derivations :
    alpha-equivalent stuffs are converted to equal things. *)

Lemma nam2mix_ctx_canonical c c' :
  nam2mix_ctx c = nam2mix_ctx c' <-> AlphaEq_ctx c c'.
Proof.
 revert c'.
 unfold AlphaEq_ctx.
 induction c as [|f c IH]; destruct c' as [|f' c']; cbn; try easy.
 rewrite !lazy_andb_iff.
 rewrite <- IH. rewrite (AlphaEq_equiv f f'), <-nam2mix_canonical.
 change (map (nam2mix [])) with nam2mix_ctx.
 split.
 - now intros [= <- <-].
 - now intros (<-,<-).
Qed.

Lemma nam2mix_seq_canonical s s' :
  nam2mix_seq s = nam2mix_seq s' <-> AlphaEq_seq s s'.
Proof.
 unfold AlphaEq_seq.
 destruct s, s'; cbn. rewrite !lazy_andb_iff.
 rewrite <- (nam2mix_ctx_canonical c c0).
 rewrite AlphaEq_equiv, <- (nam2mix_canonical f f0).
 split.
 - now intros [= <- <-].
 - now intros (<-,<-).
Qed.

Lemma nam2mix_rule_canonical r r' :
  nam2mix_rule r = nam2mix_rule r' <-> AlphaEq_rule r r'.
Proof.
 unfold AlphaEq_rule.
 destruct r, r'; cbn; try easy; rewrite ?eqb_eq.
 - split; [now intros [= <-] | now intros <-].
 - split; [intros [=]; now apply nam2mix_term_inj | now intros <-].
 - split; [intros [=]; now apply nam2mix_term_inj | now intros <-].
 - split; [now intros [= <-] | now intros <-].
Qed.

Lemma nam2mix_deriv_canonical d d' :
  nam2mix_deriv d = nam2mix_deriv d' <-> AlphaEq_deriv d d'.
Proof.
 unfold AlphaEq_deriv.
 revert d d'.
 fix IH 1. destruct d as [r s l], d' as [r' s' l']. cbn.
 rewrite !lazy_andb_iff.
 rewrite <- (nam2mix_rule_canonical r r'),
         <- (nam2mix_seq_canonical s s').
 assert (map nam2mix_deriv l = map nam2mix_deriv l' <->
         list_forallb2 eqb l l' = true).
 { revert l l'.
   fix IH' 1. destruct l as [|d l], l' as [|d' l']; cbn; try easy.
   rewrite !lazy_andb_iff.
   rewrite <- IH. rewrite <- IH'. intuition congruence. }
 rewrite <- H.
 intuition congruence.
Qed.

(** These alpha-equivalence are hence indeed equivalences *)

Lemma AlphaEq_ctx_equivalence :
  Equivalence AlphaEq_ctx.
Proof.
 constructor; [ intro | intros ? ? | intros ? ? ?];
  rewrite <-!nam2mix_ctx_canonical; eauto using eq_trans.
Qed.

Lemma AlphaEq_seq_equivalence :
  Equivalence AlphaEq_seq.
Proof.
 constructor; [ intro | intros ? ? | intros ? ? ?];
  rewrite <-!nam2mix_seq_canonical; eauto using eq_trans.
Qed.

Lemma AlphaEq_rule_equivalence :
  Equivalence AlphaEq_rule.
Proof.
 constructor; [ intro | intros ? ? | intros ? ? ?];
  rewrite <-!nam2mix_rule_canonical; eauto using eq_trans.
Qed.

Lemma AlphaEq_deriv_equivalence :
  Equivalence AlphaEq_deriv.
Proof.
 constructor; [ intro | intros ? ? | intros ? ? ?];
  rewrite <-!nam2mix_deriv_canonical; eauto using eq_trans.
Qed.

(** Starting from a named derivation [d], alpha-equivalence between
    [mix2nam_deriv (nam2mix_deriv d)] and [d] *)

Lemma nam_mix_nam_ctx c : AlphaEq_ctx (mix2nam_ctx (nam2mix_ctx c)) c.
Proof.
 apply nam2mix_ctx_canonical, mix_nam_mix_ctx, nam2mix_ctx_bclosed.
Qed.

Lemma nam_mix_nam_seq s : AlphaEq_seq (mix2nam_seq (nam2mix_seq s)) s.
Proof.
 apply nam2mix_seq_canonical, mix_nam_mix_seq, nam2mix_seq_bclosed.
Qed.

Lemma nam_mix_nam_rule r : AlphaEq_rule (mix2nam_rule (nam2mix_rule r)) r.
Proof.
 apply nam2mix_rule_canonical, mix_nam_mix_rule, nam2mix_rule_bclosed.
Qed.

Lemma nam_mix_nam_deriv d :
  AlphaEq_deriv (mix2nam_deriv (nam2mix_deriv d)) d.
Proof.
 apply nam2mix_deriv_canonical, mix_nam_mix_deriv, nam2mix_deriv_bclosed.
Qed.

(** [Nam.valid_deriv] is compatible with alpha-equivalence *)

Lemma AlphaEq_valid_deriv logic d d' :
  AlphaEq_deriv d d' ->
  Nam.valid_deriv logic d = Nam.valid_deriv logic d'.
Proof.
 rewrite <- nam2mix_deriv_canonical.
 rewrite <- !nam2mix_valid_deriv.
 now intros <-.
Qed.
