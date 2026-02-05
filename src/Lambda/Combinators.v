From Stdlib Require Import Bool Arith List Equality Setoid Morphisms Relation_Definitions.
Import ListNotations.

From FormalSystems Require Import Base.

(** * Syntax of terms *)

Inductive Term : Type :=
| K : Term
| S : Term
| App : Term -> Term -> Term.

Notation "M @ N" := (App M N) (at level 50, left associativity).

(** * Reduction relation *)

Inductive red : Term -> Term -> Prop :=
| red_K :
    forall A B : Term, red (K @ A @ B) A
| red_S :
    forall A B C : Term,
      red (S @ A @ B @ C) (A @ C @ (B @ C))
| red_AppL :
    forall A A' B : Term,
      red A A' -> red (App A B) (App A' B)
| red_AppR :
    forall A B B' : Term,
      red B B' -> red (App A B) (App A B').

Notation "A ~> B" := (red A B) (at level 60).

Inductive reds : Term -> Term -> Prop :=
| reds_refl :
    forall A : Term, reds A A
| reds_trans :
    forall A B C : Term, red A B -> reds B C -> reds A C.

Notation "A ~>* B" := (reds A B) (at level 60).

#[global] Hint Constructors red reds : core.

(** * Properties of reduction *)

#[export]
Instance red_reds_L :
  forall A : Term,
    Proper (red ==> reds) (App A).
Proof.
  now intros A B B' Hs; eauto.
Qed.

#[export]
Instance red_reds_R :
  forall A : Term,
    Proper (red ==> reds) (fun B => App B A).
Proof.
  now intros A B B' Hs; eauto.
Qed.

#[export]
Instance red_reds :
  Proper (red ==> red ==> reds) App.
Proof.
  now intros A A' HA B B' HB; eauto.
Qed.

Lemma reds_trans' :
  forall {A B C : Term},
    A ~>* B -> B ~>* C -> A ~>* C.
Proof.
  now induction 1; eauto.
Qed.

Lemma reds_AppL :
  forall {A A' B : Term},
    A ~>* A' -> A @ B ~>* A' @ B.
Proof.
  now induction 1; eauto.
Qed.

Lemma reds_AppR :
  forall {A B B' : Term},
    B ~>* B' -> A @ B ~>* A @ B'.
Proof.
  now induction 1; eauto.
Qed.

Lemma reds_App :
  forall {A A' B B' : Term},
    A ~>* A' -> B ~>* B' -> A @ B ~>* A' @ B'.
Proof.
  induction 1; intros Hs.
  - now apply reds_AppR.
  - now induction H; eauto.
Qed.

(** * Derived combinators *)

(** Identity *)
Definition I : Term := S @ K @ K.

Lemma red_I :
  forall A : Term,
    I @ A ~>* A.
Proof.
  now unfold I; eauto.
Qed.

#[global] Hint Resolve red_I : core.

(** * Normal forms *)

Inductive Nf : Term -> Prop :=
| Nf_K   : Nf K
| Nf_S   : Nf S
| Nf_Kt  : forall t : Term, Nf t -> Nf (K @ t)
| Nf_St  : forall t : Term, Nf t -> Nf (S @ t)
| Nf_Stt : forall t1 t2 : Term, Nf t1 -> Nf t2 -> Nf (S @ t1 @ t2)
| Nf_Ne  : forall t : Term, Ne t -> Nf t

with Ne : Term -> Prop :=
| Ne_App : forall t1 t2 : Term, Ne t1 -> Nf t2 -> Ne (App t1 t2).

#[global] Hint Constructors Nf Ne : core.

Definition isNormal (t : Term) : Prop :=
  forall t' : Term, ~ red t t'.

(* Lemma Nf_spec :
  forall t : Term, Nf t <-> (forall t' : Term, ~ red t t').
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
            apply red_AppR. eassumption.
        constructor. apply IHt2. do 2 intro. eapply H. eauto.
        constructor. apply IHt2. do 2 intro. eapply H. eauto.
      destruct t1_1.
        do 2 constructor.
          constructor.
            constructor.
            cut (Nf (Var v @ t1_2)).
              intro. inv H0. inv H1.
              apply IHt1. do 2 intro. eapply H. eauto.
          apply IHt2. do 2 intro. eapply H. eauto.
          specialize (H t1_2). contradict H. constructor.
          constructor.
            assert (Nf (S @ t1_2)).
              apply IHt1. do 2 intro. inv H0.
                inv H4.
                eapply H. eauto.
              inv H0. inv H1.
            apply IHt2. do 2 intro. eapply H. eauto.
          do 2 constructor.
            assert (Nf (t1_1_1 @ t1_1_2 @ t1_2)).
              apply IHt1. do 2 intro. eapply H. eauto.
              inv H0. specialize (H (t1_1_2 @ t2 @ (t1_2 @ t2))).
                contradict H. constructor.
            apply IHt2. do 2 intro. eapply H. eauto.
Qed.
 *)

Ltac wut :=
repeat match goal with
| |- forall _, _ => intro
| |- ~ _ => intro
| |- _ /\ _ => split
| H : _ /\ _ |- _ => destruct H
| H : red (_ @ _) _ |- _ => inv H
| H : red K       _ |- _ => inv H
| H : red S       _ |- _ => inv H
| H : isNormal ?t, H' : red ?t _ |- _ => destruct (H _ H')
| |- isNormal _ => do 2 intro
| H : exists _, _   |- _ => decompose [ex and] H; clear H
| H : Ne ?x      |- _ => is_var x + inv H
| _ => auto
end.

Fixpoint Nf_isNormal {t : Term} (nf : Nf t) {struct nf} : isNormal t

with     Ne_isNormal {t : Term} (ne : Ne t) {struct ne} : isNormal t.
Proof.
  - destruct nf;
      only 1-5: (now wut; eapply Nf_isNormal;
      repeat match goal with
      | |- red _ _ => eauto
      end; eauto).
    now apply Ne_isNormal.
  - destruct ne. wut.
    + now eapply Ne_isNormal; eauto.
    + now eapply Nf_isNormal; eauto.
Qed.

(*

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

#[global] Hint Constructors parallel : core.

Definition parallels := rtc parallel.

#[global] Hint Unfold parallels : core.

Lemma parallels_K :
  forall t1 t2 : Term,
    parallels (K @ t1 @ t2) t1.
Proof.
  now do 2 constructor.
Qed.

Lemma parallels_S :
  forall t1 t2 t3 : Term,
    parallels (S @ t1 @ t2 @ t3) (t1 @ t3 @ (t2 @ t3)).
Proof.
  now do 2 constructor.
Qed.

Lemma parallels_AppL :
  forall t1 t1' t2 : Term,
    parallels t1 t1' -> parallels (t1 @ t2) (t1' @ t2).
Proof.
  unfold parallels.
  intros * Hp; revert t2.
  now induction Hp; eauto.
Qed.

Lemma parallels_AppR :
  forall t1 t2 t2' : Term,
    parallels t2 t2' -> parallels (t1 @ t2) (t1 @ t2').
Proof.
  unfold parallels.
  intros * Hp; revert t1.
  now induction Hp; eauto.
Qed.

#[global] Hint Resolve parallels_K parallels_S parallels_AppL parallels_AppR : core.

#[global] Hint Extern 0 =>
  match goal with
  | |- parallels (K @ _ @ _) _ => try apply parallels_K
  end
  : core.

Lemma parallels_App :
  forall t1 t1' t2 t2' : Term,
    parallels t1 t1' -> parallels t2 t2' ->
      parallels (t1 @ t2) (t1' @ t2').
Proof.
  unfold parallels.
  intros * Hp1 Hp2; revert t2 t2' Hp2.
  induction Hp1; intros.
  - econstructor 3.
    + now do 2 constructor; eauto.
    + now induction Hp2; eauto.
  - now apply parallels_AppR.
  - eapply rtc_trans.
    + now apply IHHp1_1.
    + now apply IHHp1_2.
Qed.

Lemma parallel_not_K0 :
  forall r : Term, ~ parallel K r.
Proof.
  now inversion 1.
Qed.

Lemma parallel_not_S0 :
  forall r : Term, ~ parallel S r.
Proof.
  now inversion 1.
Qed.

Lemma parallel_confluent''' :
  forall a b c : Term,
    parallel a b -> parallel a c ->
      exists d : Term, parallels b d /\ parallels c d.
Proof.
  intros a b c Hpb Hpc.
  revert c Hpc.
  induction Hpb; intros; unfold parallels in *;
  repeat match goal with
  | H : parallel K       _ |- _ => inv H
  | H : parallel S       _ |- _ => inv H
  | H : parallel (_ @ _) _ |- _ => inv H
  | |- context [rtc parallel (S @ ?a @ ?b @ ?c) _] => exists (a @ c @ (b @ c)); split; eauto
  | |- context [rtc parallel (_ @ _) _] => eauto 7
  end;
  pose parallels_AppL;
  pose parallels_AppR;
  pose parallels_App;
  unfold parallels in *.
  - now decompose [ex and] (IHHpb _ H2); eauto 6.
  - now decompose [ex and] (IHHpb _ H1); eauto 6.
  - now decompose [ex and] (IHHpb _ H2); eauto 6.
  - now decompose [ex and] (IHHpb _ H3); eauto 6.
  - now decompose [ex and] (IHHpb1 _ H2); eauto 6.
  - now decompose [ex and] (IHHpb2 _ H2); eauto 6.
  - now decompose [ex and] (IHHpb1 _ H1); decompose [ex and] (IHHpb2 _ H3); eauto.
Qed.

(** * Lambdas *)

(*
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

Lemma lam_reds :
  forall (x : V) (A : Term),
    lam x A @ Var x ~>* A.
Proof.
  induction A; cbn; intros.
    destruct (dec_spec x v); subst; eauto.
    1-2: eauto.
    eapply reds_trans.
      apply red_S.
      apply reds_App; assumption.
Qed.

Lemma lam_subst :
  forall (x : V) (A B : Term),
    lam x A @ B ~>* subst x A B.
Proof.
  induction A; cbn; intros.
    destruct (dec_spec x v); subst; eauto.
    1-2: eauto.
    eapply reds_trans.
      apply red_S.
      apply reds_App; auto.
Qed.
*)
