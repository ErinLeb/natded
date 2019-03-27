
(** Conversion from Named derivations to Locally Nameless derivations *)

Require Import RelationClasses Arith Omega Defs Proofs Equiv Alpha Alpha2 Meta.
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
 Vars.Equal (Mix.fvars (nam2mix_ctx c)) (Ctx.freevars c).
Proof.
 induction c as [|f c IH]; cbn; auto.
 - varsdec.
 - rewrite nam2mix_fvars, IH. simpl. varsdec.
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

Lemma nam2mix_deriv_valid_step logic (d:Nam.derivation) :
  Mix.valid_deriv_step logic (nam2mix_deriv d) =
  Nam.valid_deriv_step logic d.
Proof.
 destruct d as [[ ] s ds]; cbn.
 - repeat (break; cbn; auto).
   unfold nam2mix_ctx.
   induction c as [|A c IH]; cbn; auto.
   rewrite <- nam2mix_eqb.
   case eqbspec; auto.
 - repeat (break; cbn; auto).
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   now rewrite nam2mix_eqb, !nam2mix_ctx_eqb.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d, d0.
 - repeat (break; cbn; auto).
   now rewrite <- !nam2mix_seq_eqb.
 - repeat (break; cbn; auto).
   now rewrite <- !nam2mix_seq_eqb.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   rewrite <- nam2mix_ctx_eqb, <- !nam2mix_seq_eqb.
   now destruct d, d0.
 - repeat (break; cbn; auto).
   rewrite <- nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn; auto).
   rewrite <- !nam2mix_seq_eqb. now destruct d.
 - repeat (break; cbn - [αeq]; auto);
    rewrite ?andb_false_r; auto.
   rewrite <- nam2mix_ctx_eqb.
   case eqbspec; auto. intro Ec. simpl.
   rewrite <- nam2mix_eqb. cbn.
   apply eq_true_iff_eq.
   rewrite !andb_true_iff.
   rewrite !negb_true_iff, <- !not_true_iff_false.
   rewrite !Vars.mem_spec.
   rewrite !eqb_eq.
   split; intros (U,V); split.
   + change (Mix.FVar x) with (nam2mix_term [] (Var x)) in U.
     rewrite <- nam2mix_alt_subst_bsubst0 in U.
     apply nam2mix_rename_iff3; auto.
     rewrite nam2mix_fvars in V. simpl in V. varsdec.
   + rewrite <- nam2mix_ctx_fvars. rewrite <- Ec. varsdec.
   + rewrite U.
     change (Mix.FVar x) with (nam2mix_term [] (Nam.Var x)).
     rewrite <- nam2mix_alt_subst_bsubst0.
     symmetry. apply nam2mix_alt_subst_nop.
   + rewrite Ec, U, nam2mix_ctx_fvars.
     rewrite nam2mix_fvars. simpl. varsdec.
 - repeat (break; cbn; auto).
   rewrite !nam2mix_ctx_eqb. case eqb; simpl; auto.
   rewrite <- nam2mix_eqb.
   rewrite nam2mix_subst_alt.
   now rewrite nam2mix_alt_subst_bsubst0.
 - repeat (break; cbn; auto).
   rewrite !nam2mix_ctx_eqb. case eqb; simpl; auto.
   rewrite <- nam2mix_eqb.
   rewrite nam2mix_subst_alt.
   now rewrite nam2mix_alt_subst_bsubst0.
 - repeat (break; cbn - [αeq]; auto);
    rewrite ?andb_false_r; auto.
   rewrite <- nam2mix_seq_eqb, <- nam2mix_eqb, <- nam2mix_ctx_eqb.
   cbn.
   apply eq_true_iff_eq.
   rewrite !andb_true_iff.
   rewrite !negb_true_iff, <- !not_true_iff_false.
   rewrite !Vars.mem_spec.
   rewrite !eqb_eq.
   split.
   + intros (((U,V),W),X); repeat split; auto.
     * rewrite <-V in U; exact U.
     * change (Mix.FVar x) with (nam2mix_term [] (Var x)) in W.
       rewrite <- nam2mix_alt_subst_bsubst0 in W.
       apply nam2mix_rename_iff3; auto.
       rewrite nam2mix_fvars in X. simpl in X. varsdec.
     * revert X. destruct s. cbn in *. injection U as <- <-.
       rewrite <-!nam2mix_ctx_fvars, !nam2mix_fvars. simpl.
       clear. varsdec.
   + intros ((U,(V,W)),Z); repeat split; auto.
     * rewrite U. f_equal; auto.
     * rewrite W.
       change (Mix.FVar x) with (nam2mix_term [] (Nam.Var x)).
       rewrite <- nam2mix_alt_subst_bsubst0.
       symmetry. apply nam2mix_alt_subst_nop.
     * revert Z. destruct s. cbn in *.
       rewrite V, W. injection U as <- <-.
       rewrite <-!nam2mix_ctx_fvars, !nam2mix_fvars.
       simpl. clear. varsdec.
 - repeat (break; cbn; auto).
   case eqb; simpl; auto.
   now rewrite <- nam2mix_seq_eqb.
Qed.

Lemma nam2mix_deriv_valid logic (d:Nam.derivation) :
  Mix.valid_deriv logic (nam2mix_deriv d) =
  Nam.valid_deriv logic d.
Proof.
 revert d.
 fix IH 1. destruct d.
 cbn -[Mix.valid_deriv_step Nam.valid_deriv_step].
 rewrite <- nam2mix_deriv_valid_step.
 cbn -[Mix.valid_deriv_step Nam.valid_deriv_step].
 destruct Mix.valid_deriv_step; auto.
 revert l.
 fix IH' 1. destruct l; simpl.
 reflexivity.
 now rewrite IH, IH'.
Qed.
