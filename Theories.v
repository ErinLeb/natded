
(** Notion of 1st order theories *)

Require Import RelationClasses Arith Omega Defs Proofs Mix Meta.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope eqb_scope.
Local Open Scope string_scope.

Record theory :=
  { sign : gen_signature;
    axiom : formula -> Prop;
    axcheck : forall A, axiom A -> check sign A = true;
    axclosed : forall A, axiom A -> closed A }.

Section SomeLogic.
Variable logic : Defs.logic.

Definition theorem theory T :=
  check theory.(sign) T = true /\ closed T /\ Vars.Empty (fvars T) /\
  exists axs,
   Forall theory.(axiom) axs /\
   Pr logic (axs ⊢ T).

Definition inconsistent theory :=
 theorem theory False.

Definition consistent theory := ~theorem theory False.

Definition opt_finer {A} (o o' : option A) :=
 o=None \/ o=o'.

Definition optfun_finer {A B} (f f' : A -> option B) :=
 forall a, opt_finer (f a) (f' a).

Definition sign_extend sign sign' :=
  optfun_finer (sign.(gen_fun_symbs)) (sign'.(gen_fun_symbs)) /\
  optfun_finer (sign.(gen_pred_symbs)) (sign'.(gen_pred_symbs)).

Definition extend th1 th2 :=
 sign_extend (th1.(sign)) (th2.(sign)) /\
 forall T, theorem th1 T -> theorem th2 T.

Definition EqualityTheory th :=
 th.(sign).(gen_pred_symbs) "=" = Some 2 /\
 theorem th (∀Pred "=" [#0; #0])%form /\
 forall A z,
   check (th.(sign)) A = true /\ closed A
    /\ Vars.Equal (fvars A) (Vars.singleton z) /\
   theorem th (∀∀(Pred "=" [#1;#0] -> fsubst z (#1) A -> fsubst z (#0) A))%form.

Definition conservative_ext th1 th2 :=
 extend th1 th2 /\
 forall T, theorem th2 T -> check (th1.(sign)) T = true ->
           theorem th1 T.

Lemma consext_inconsistency th1 th2 :
 conservative_ext th1 th2 -> inconsistent th2 -> inconsistent th1.
Proof.
 unfold inconsistent. intros (U,V).
 intros H2.
 apply V; auto.
Qed.

Lemma consext_consistency th1 th2 :
 conservative_ext th1 th2 -> consistent th1 -> consistent th2.
Proof.
 unfold consistent in *. intros U V W. apply V.
 eapply consext_inconsistency; eauto.
Qed.

Lemma ext_sign_only th1 th2 :
 sign_extend th1.(sign) th2.(sign) ->
 (forall A, th1.(axiom) A <-> th2.(axiom) A) ->
 conservative_ext th1 th2.
Proof.
Admitted.

Definition Henkin_sign sign c :=
  {| gen_fun_symbs := fun f => if f =? c then Some 0 else
                                  sign.(gen_fun_symbs) f;
     gen_pred_symbs := sign.(gen_fun_symbs) |}.

Definition Henkin_axiom Ax (A:formula) c :=
  fun f => f = (bsubst 0 (Fun c []) A) \/ Ax f.

Lemma Henkin_ax_check th A c
 (E:th.(sign).(gen_fun_symbs) c = None)
 (Thm:theorem th (∃A)) :
 forall B, Henkin_axiom th.(axiom) A c B ->
           check (Henkin_sign th.(sign) c) B = true.
Proof.
Admitted.

Lemma Henkin_ax_closed th A c
 (Thm:theorem th (∃A)) :
 forall B, Henkin_axiom th.(axiom) A c B -> closed B.
Proof.
Admitted.

Definition Henkin_ext th A c
 (E:th.(sign).(gen_fun_symbs) c = None)
 (Thm:theorem th (∃A)) :=
 {| sign := Henkin_sign th.(sign) c;
    axiom := Henkin_axiom th.(axiom) A c;
    axcheck := Henkin_ax_check th A c E Thm;
    axclosed := Henkin_ax_closed th A c Thm |}.

Lemma Henkin_consext th A c
 (E:th.(sign).(gen_fun_symbs) c = None)
 (Thm:theorem th (∃A)) :
 conservative_ext th (Henkin_ext th A c E Thm).
Proof.
Admitted.

End SomeLogic.