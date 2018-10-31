Require Import List.
Import ListNotations.

Require Import Bool.

Parameter V : Type.
Parameter dec : V -> V -> bool.
Parameter dec_spec :
  forall x y : V, reflect (x = y) (dec x y).

Require Import Arith.

Notation "x =? y" := (dec x y) (at level 70).

Inductive Term : Type :=
    | Var : V -> Term
    | K : Term
    | S : Term
    | App : Term -> Term -> Term.

Notation "M @ N" := (App M N) (at level 50, left associativity).

Inductive WStep : Term -> Term -> Prop :=
    | WStep_K :
        forall A B : Term, WStep (K @ A @ B) A
    | WStep_S :
        forall A B C : Term,
          WStep (S @ A @ B @ C) (A @ C @ (B @ C))
    | WStep_AppL :
        forall A A' B : Term,
          WStep A A' -> WStep (App A B) (App A' B)
    | WStep_AppR :
        forall A B B' : Term,
          WStep B B' -> WStep (App A B) (App A B').

Hint Constructors WStep.

Notation "A ~> B" := (WStep A B) (at level 60).

Inductive WSteps : Term -> Term -> Prop :=
(*    | WSteps_WStep :
        forall A B : Term, WStep A B -> WSteps A B*)
    | WSteps_refl :
        forall A : Term, WSteps A A
    | WSteps_trans :
        forall A B C : Term, WStep A B -> WSteps B C -> WSteps A C.

Hint Constructors WSteps.

Notation "A ~>* B" := (WSteps A B) (at level 60).

(*
Require Import Relation_Definitions Setoid Morphisms.

Instance WStep_WSteps_L :
  forall A : Term,
    Proper (WStep ==> WSteps) (App A).
Proof.
  unfold Proper, respectful. intros A B B' HB. eauto.
Qed.

Instance WStep_WSteps_R :
  forall A : Term,
    Proper (WStep ==> WSteps) (fun B => App B A).
Proof.
  unfold Proper, respectful. intros A B B' HB. eauto.
Qed.

Instance WStep_WSteps :
  Proper (WStep ==> WStep ==> WSteps) App.
Proof.
  unfold Proper, respectful. intros A A' HA B B' HB. eauto.
Qed.

Instance WStep_WSteps' :
  Proper (WStep ==> WStep ==> Basics.flip Basics.impl) WSteps.
Proof.
  unfold Proper, respectful. intros A A' HA B B' HB.
  unfold Basics.flip, Basics.impl. intro.
  induction H.
Qed.
*)

Lemma WSteps_trans' :
  forall {A B C : Term},
    A ~>* B -> B ~>* C -> A ~>* C.
Proof.
  induction 1; eauto.
Qed.

Lemma WSteps_AppL :
  forall {A A' B : Term},
    A ~>* A' -> A @ B ~>* A' @ B.
Proof.
  induction 1; eauto.
Qed.

Lemma WSteps_AppR :
  forall {A B B' : Term},
    B ~>* B' -> A @ B ~>* A @ B'.
Proof.
  induction 1; eauto.
Qed.

Lemma WSteps_App :
  forall {A A' B B' : Term},
    A ~>* A' -> B ~>* B' -> A @ B ~>* A' @ B'.
Proof.
  induction 1; intro.
    induction H; eauto.
    eauto.
Qed.

Definition I : Term := S @ K @ K.

Lemma WStep_I :
  forall A : Term, I @ A ~>* A.
Proof.
  intros. unfold I. eauto.
Defined.

Hint Resolve WStep_I.

Fixpoint lam (x : V) (A : Term) : Term :=
match A with
    | Var y => if x =? y then I else K @ Var y
    | K => K @ K
    | S => K @ S
    | App A1 A2 => S @ lam x A1 @ lam x A2
end.

Fixpoint subst (x : V) (A B : Term) : Term :=
match A with
    | Var y => if x =? y then B else Var y
    | K => K
    | S => S
    | A1 @ A2 => subst x A1 B @ subst x A2 B
end.

(*
Lemma WStep_L :
  forall {A A' B : Term},
    A ~> A' -> A @ B 
*)

Lemma lam_WSteps :
  forall (x : V) (A : Term),
    lam x A @ Var x ~>* A.
Proof.
  induction A; cbn; intros.
    destruct (dec_spec x v); subst; eauto.
    1-2: eauto.
    eapply WSteps_trans.
      apply WStep_S.
      apply WSteps_App; assumption.
Qed.

Lemma lam_subst :
  forall (x : V) (A B : Term),
    lam x A @ B ~>* subst x A B.
Proof.
  induction A; cbn; intros.
    destruct (dec_spec x v); subst; eauto.
    1-2: eauto.
    eapply WSteps_trans.
      apply WStep_S.
      apply WSteps_App; auto.
Qed.

Parameter v : V.

Definition pair (A B : Term) : Term := lam v (Var v @ A @ B).

Definition outL (A : Term) : Term := A @ K.

Definition outR (A : Term) : Term := A @ (K @ I).

Lemma outL_pair :
  forall A B : Term, outL (pair A B) ~>* A.
Proof.
  unfold outL, pair. intros. eapply WSteps_trans'.
    apply lam_subst.
    cbn. destruct (dec_spec v v).
Abort.