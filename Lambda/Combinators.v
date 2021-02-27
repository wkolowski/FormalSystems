Require Import List.
Import ListNotations.

Require Import Bool.

Parameter V : Type.
Parameter dec : V -> V -> bool.
Parameter dec_spec :
  forall x y : V, reflect (x = y) (dec x y).

Require Import Arith.

Notation "x =? y" := (dec x y) (at level 70).

(** * Syntax of terms *)

Inductive Term : Type :=
    | Var : V -> Term
    | K : Term
    | S : Term
    | App : Term -> Term -> Term.

Notation "M @ N" := (App M N) (at level 50, left associativity).

(** * Reduction relation *)

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

Notation "A ~> B" := (WStep A B) (at level 60).

Inductive WSteps : Term -> Term -> Prop :=
    | WSteps_refl :
        forall A : Term, WSteps A A
    | WSteps_trans :
        forall A B C : Term, WStep A B -> WSteps B C -> WSteps A C.

Notation "A ~>* B" := (WSteps A B) (at level 60).

Hint Constructors WStep WSteps : core.

(** * Properties of reduction *)

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

(** * Derived combinators *)

(** Identity *)
Definition I : Term := S @ K @ K.

Lemma WStep_I :
  forall A : Term, I @ A ~>* A.
Proof.
  intros. unfold I. eauto.
Defined.

Hint Resolve WStep_I : core.

(** * Lambdas *)

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

(** * Normal forms *)

Inductive Nf : Term -> Prop :=
    | Nf_K   : Nf K
    | Nf_S   : Nf S
    | Nf_Kt  : forall t : Term, Nf t -> Nf (K @ t)
    | Nf_St  : forall t : Term, Nf t -> Nf (S @ t)
    | Nf_Stt : forall t1 t2 : Term, Nf t1 -> Nf t2 -> Nf (S @ t1 @ t2)
    | Nf_Ne  : forall t : Term, Ne t -> Nf t

with Ne : Term -> Prop :=
    | Ne_var : forall v : V, Ne (Var v)
    | Ne_App : forall t1 t2 : Term, Ne t1 -> Nf t2 -> Ne (App t1 t2).

Ltac inv H := inversion H; subst; clear H.

Lemma Nf_spec :
  forall t : Term, Nf t <-> (forall t' : Term, ~ WStep t t').
Proof.
  split.
    induction t; intros Hnf t' Hred.
      inv Hred.
      inv Hred.
      inv Hred.
      inv Hred.
        inv Hnf. inv H. inv H2. inv H1.
        inv Hnf. inv H. inv H2. inv H1. inv H2.
        eapply IHt1.
          inv Hnf.
            inv H2.
            inv H2.
            constructor. assumption.
            inv H. constructor. assumption.
          eassumption.
        eapply IHt2.
          inv Hnf; try inv H; assumption.
          eassumption.
    induction t; intros.
      do 2 constructor.
      constructor.
      constructor.
      destruct t1.
        do 2 constructor.
          constructor.
          apply IHt2. do 2 intro. eapply H.
            apply WStep_AppR. eassumption.
        constructor. apply IHt2. do 2 intro. eapply H. eauto.
        constructor. apply IHt2. do 2 intro. eapply H. eauto.
      destruct t1_1.
        do 2 constructor.
          constructor.
            constructor.
            cut (Nf (Var v @ t1_2)).
              intro. inv H0. inv H1. assumption.
              apply IHt1. do 2 intro. eapply H. eauto.
          apply IHt2. do 2 intro. eapply H. eauto.
          specialize (H t1_2). contradict H. constructor.
          constructor.
            assert (Nf (S @ t1_2)).
              apply IHt1. do 2 intro. inv H0.
                inv H4.
                eapply H. eauto.
              inv H0.
                assumption.
                inv H1. inv H3.
            apply IHt2. do 2 intro. eapply H. eauto.
          constructor. constructor.
            assert (Nf (t1_1_1 @ t1_1_2 @ t1_2)).
              apply IHt1. do 2 intro. eapply H. eauto.
              inv H0.
                specialize (H (t1_1_2 @ t2 @ (t1_2 @ t2))).
                  contradict H. constructor.
                assumption.
            apply IHt2. do 2 intro. eapply H. eauto.
Qed.

(*
Require Import Equality.

Fixpoint isProp_Nf
  (isProp_Term : forall (t1 t2 : Term) (p q : t1 = t2), p = q) (t : Term) {struct t}
    : forall nf1 nf2 : Nf t, nf1 = nf2

with isProp_Ne
  (isProp_Term : forall (t1 t2 : Term) (p q : t1 = t2), p = q) (t : Term) {struct t}
    : forall ne1 ne2 : Ne t, ne1 = ne2.
Proof.
  destruct t; intros.
    dependent destruction nf1. dependent destruction nf2.
      f_equal. dependent destruction n. dependent destruction n0. reflexivity.
    dependent destruction nf1.
      dependent destruction nf2.
        reflexivity.
        inv n.
      inv n.
    dependent destruction nf1.
      dependent destruction nf2.
        reflexivity.
        inv n.
      inv n.
    dependent destruction nf1.
      dependent destruction nf2.
        f_equal. apply isProp_Nf. assumption.
        exfalso. inv n. inv H1.
      dependent destruction nf2.
        f_equal. apply isProp_Nf. assumption.
        exfalso. inv n. inv H1.
      dependent destruction nf2.
        f_equal.
          apply isProp_Nf. assumption.
          apply isProp_Nf. assumption.
        exfalso. inv n. inv H1. inv H3.
      dependent destruction nf2.
        exfalso. inv n. inv H1.
        exfalso. inv n. inv H1.
        exfalso. inv n. inv H1. inv H3.
        f_equal. apply isProp_Ne. assumption.
  destruct t; intros.
    dependent destruction ne1. dependent destruction ne2.
      reflexivity.
    dependent destruction ne1.
    dependent destruction ne1.
    dependent destruction ne1. dependent destruction ne2. f_equal.
      apply isProp_Ne. assumption.
      apply isProp_Nf. assumption.
Qed.
*)

Print WStep.

Inductive parallel : Term -> Term -> Prop :=
    | parallel_K :
        forall t1 t2 : Term,
          parallel (K @ t1 @ t2) t1
    | parallel_S :
        forall t1 t2 t3 : Term,
          parallel (S @ t1 @ t2 @ t3) (t1 @ t3 @ (t2 @ t3))
    | parallel_AppL :
        forall t1 t1' t2 : Term,
          parallel t1 t1' -> parallel (t1 @ t2) (t1' @ t2)
    | parallel_AppR :
        forall t1 t2 t2' : Term,
          parallel t2 t2' -> parallel (t1 @ t2) (t1 @ t2')
    | parallel_App :
        forall t1 t1' t2 t2' : Term,
          parallel t1 t1' -> parallel t2 t2' -> parallel (t1 @ t2) (t1' @ t2').

Hint Constructors parallel : core.

Require Import FormalSystems.Base.

Definition parallels := rtc parallel.

Hint Unfold parallels : core.

Lemma parallels_K :
  forall t1 t2 : Term,
    parallels (K @ t1 @ t2) t1.
Proof.
  do 2 constructor.
Qed.

Lemma parallels_S :
  forall t1 t2 t3 : Term,
    parallels (S @ t1 @ t2 @ t3) (t1 @ t3 @ (t2 @ t3)).
Proof.
  do 2 constructor.
Qed.

Lemma parallels_AppL :
  forall t1 t1' t2 : Term,
    parallels t1 t1' -> parallels (t1 @ t2) (t1' @ t2).
Proof.
  unfold parallels.
  intros until 1. revert t2.
  induction H; eauto.
Qed.

Lemma parallels_AppR :
  forall t1 t2 t2' : Term,
    parallels t2 t2' -> parallels (t1 @ t2) (t1 @ t2').
Proof.
  unfold parallels.
  intros until 1. revert t1.
  induction H; eauto.
Qed.

Hint Resolve parallels_K parallels_S parallels_AppL parallels_AppR : core.

Hint Extern 0 =>
  match goal with
    | |- parallels (K @ _ @ _) _ => try apply parallels_K
  end.

Lemma parallels_App :
  forall t1 t1' t2 t2' : Term,
    parallels t1 t1' -> parallels t2 t2' ->
      parallels (t1 @ t2) (t1' @ t2').
Proof.
  unfold parallels.
  intros until 1. revert t2 t2'.
  induction H; intros.
    econstructor 3.
      do 2 constructor; eauto.
      induction H0; eauto.
    apply parallels_AppR. assumption.
    eapply rtc_trans.
      apply IHrtc1. eassumption.
      apply IHrtc2. constructor 2.
Qed.

Lemma parallel_confluent :
  forall a b c : Term,
    parallel a b -> parallel a c ->
      exists d : Term, parallels b d /\ parallels c d.
Proof.
  intros a b c Hpb Hpc.
  revert c Hpc.
  induction Hpb; intros; unfold parallels in *.
    inv Hpc; eauto.
      inv H2; eauto.
        inv H3.
        inv H1.
      inv H1; eauto.
        inv H4.
        inv H2.
    inv Hpc; eauto.
      inv H2; eauto.
        inv H3; eauto.
          inv H2. exists (t2' @ t3 @ (t2 @ t3)). auto.
          inv H1.
        exists (t1 @ t3 @ (t2' @ t3)). auto.
        inv H1; eauto.
          inv H3.
          exists (t2'0 @ t3 @ (t2' @ t3)). auto.
          inv H2.
      exists (t1 @ t2' @ (t2 @ t2')). auto.
      inv H1; eauto.
        inv H4; eauto.
          inv H2.
          exists (t2'0 @ t2' @ (t2 @ t2')). auto.
          inv H1.
        exists (t1 @ t2' @ (t2'0 @ t2')). auto.
        inv H2.
          inv H4.
          exists (t2'1 @ t2' @ (t2'0 @ t2')). auto.
          inv H1.
    inv Hpc; eauto.
      inv Hpb; eauto.
        inv H2.
        inv H1.
      inv Hpb; eauto.
        inv H2; eauto.
          inv H3.
          exists (t2' @ t2 @ (t3 @ t2)). auto.
          inv H1.
        exists (t0 @ t2 @ (t2' @ t2)). auto.
        inv H1; eauto.
          inv H4.
          exists (t2'0 @ t2 @ (t2' @ t2)). auto.
          inv H2.
      decompose [ex and] (IHHpb _ H2). exists (x @ t2). split.
        apply parallels_AppL. assumption.
        apply parallels_AppL. assumption.
      exists (t1' @ t2'). auto.
      decompose [ex and] (IHHpb _ Hpb). decompose [ex and] (IHHpb _ H1).
Abort.       