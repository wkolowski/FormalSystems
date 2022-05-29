Require Import Bool Arith.

Require Import List.
Import ListNotations.

Parameter V : Type.
Parameter dec : V -> V -> bool.
Parameter dec_spec :
  forall x y : V, reflect (x = y) (dec x y).

Notation "x =? y" := (dec x y) (at level 70).

Inductive Formula : Type :=
    | Var : V -> Formula
    | FFalse : Formula
    | Impl : Formula -> Formula -> Formula
    | Or : Formula -> Formula -> Formula
    | And : Formula -> Formula -> Formula.

Definition Not (P : Formula) : Formula := Impl P FFalse.
Definition Iff (P Q : Formula) : Formula :=
  And (Impl P Q) (Impl Q P).
Definition FTrue : Formula := Impl FFalse FFalse.

Definition Context : Type := list Formula.

Inductive Proves : Context -> Formula -> Prop :=
    | Ax :
        forall (C : Context) (P : Formula),
          Proves (P :: C) P
    | FFalseE :
        forall (C : Context) (P : Formula),
          Proves C FFalse -> Proves C P
    | ImplI :
        forall (C : Context) (P Q : Formula),
          Proves (P :: C) Q -> Proves C (Impl P Q)
    | ImplE :
        forall (C : Context) (P Q : Formula),
          Proves C (Impl P Q) -> Proves C P -> Proves C Q
    | AndI :
        forall (C : Context) (P Q : Formula),
          Proves C P -> Proves C Q -> Proves C (And P Q)
    | AndEL :
        forall (C : Context) (P Q : Formula),
          Proves C (And P Q) -> Proves C P
    | AndER :
        forall (C : Context) (P Q : Formula),
          Proves C (And P Q) -> Proves C Q
    | OrIL :
        forall (C : Context) (P Q : Formula),
          Proves C P -> Proves C (Or P Q)
    | OrIR :
        forall (C : Context) (P Q : Formula),
          Proves C Q -> Proves C (Or P Q)
    | OrE :
        forall (C : Context) (P Q R : Formula),
          Proves (P :: C) R -> Proves (Q :: C) R -> Proves C (Or P Q) ->
            Proves C R.

#[global] Hint Constructors Proves : core.

Lemma weakening :
  forall (C : Context) (F : Formula),
    Proves C F -> forall R : Formula, Proves (R :: C) F.
Proof.
  induction 1; intros; auto.
    admit.
Admitted.

Fixpoint subst (F : Formula) (x : V) (P : Formula) : Formula :=
match F with
    | Var y => if x =? y then P else Var y
    | FFalse => FFalse
    | Impl F1 F2 => Impl (subst F1 x P) (subst F2 x P)
    | Or F1 F2 => Or (subst F1 x P) (subst F2 x P)
    | And F1 F2 => And (subst F1 x P) (subst F2 x P)
end.

Fixpoint csubst (C : Context) (x : V) (P : Formula) : Context :=
match C with
    | [] => []
    | F :: C' => subst F x P :: csubst C' x P
end.

(*
Lemma Proves_subst :
  forall (C : Context) (F : Formula),
    Proves C F -> forall (R : Formula) (x : V),
      Proves (csubst C x R) (subst F x R).
Proof.
  induction 1; cbn; intros; eauto.
Qed.
*)

Lemma ImplI' :
  forall (C : Context) (P Q : Formula),
    (In P C -> Proves C Q) -> Proves C (Impl P Q).
Proof.
  intros C P Q H. apply ImplI.
Abort.

Ltac inv H :=
  inversion H; subst; clear H; auto.

(* Definitely too hard. *)
Lemma consistent :
  forall C : Context,
    ~ Proves C FFalse.
Proof.
Abort.