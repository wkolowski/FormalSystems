From Stdlib Require Import Bool Arith List.
Import ListNotations.

From FormalSystems Require Import Base.

(** * Types and terms *)

Inductive Ty : Type :=
| TNat : Ty
| TArr : Ty -> Ty -> Ty.

Notation "a → b" := (TArr a b) (at level 60, right associativity).

Inductive Tm : Type :=
| K : Tm
| S : Tm
| App : Tm -> Tm -> Tm
| zero : Tm
| succ : Tm
| rec  : Tm.

Notation "M @ N" := (App M N) (at level 50, left associativity).

Inductive hasType : Tm -> Ty -> Prop :=
| hasType_K :
    forall a b : Ty, hasType K (a → b → a)
| hasType_S :
    forall a b c : Ty,
      hasType S ((a → b → c) → (a → b) → a → c)
| hasType_App :
    forall (a b : Ty) (f x : Tm),
      hasType f (a → b) -> hasType x a ->
        hasType (App f x) b
| hasType_zero :
    hasType zero TNat
| hasType_succ :
    hasType succ (TNat → TNat)
| hasType_rec :
    forall a : Ty,
      hasType rec (a → (TNat → a → a) → TNat → a).

Inductive red : Tm -> Tm -> Prop :=
| red_K :
    forall x y : Tm,
      red (K @ x @ y) x
| red_S :
    forall x y z : Tm,
      red (S @ x @ y @ z) (x @ z @ (y @ z))
| red_rec_zero :
    forall z s : Tm,
      red (rec @ z @ s @ zero) z
| red_rec_succ :
    forall z s n : Tm,
      red (rec @ z @ s @ (succ @ n)) (s @ n @ (rec @ z @ s @ n))
| red_AppL :
    forall t1 t1' t2 : Tm,
      red t1 t1' -> red (t1 @ t2) (t1' @ t2)
| red_AppR :
    forall t1 t2 t2' : Tm,
      red t2 t2' -> red (t1 @ t2) (t1 @ t2').

Notation "A ~> B" := (red A B) (at level 60).

#[global] Hint Constructors Ty Tm hasType red rtc : core.

Definition reds := rtc red.

#[global] Hint Unfold reds : core.

Infix "~>*" := reds (at level 50).

Definition isNormal (t : Tm) : Prop :=
  forall t' : Tm, ~ red t t'.

Inductive Nf : Tm -> Prop :=
| Nf_K0    : Nf K
| Nf_K1    : forall t : Tm, Nf t -> Nf (K @ t)
| Nf_S0    : Nf S
| Nf_S1    : forall t : Tm, Nf t -> Nf (S @ t)
| Nf_S2    : forall t1 t2 : Tm, Nf t1 -> Nf t2 -> Nf (S @ t1 @ t2)
| Nf_zero  : Nf zero
| Nf_succ0 : Nf succ
| Nf_succ1 : forall t : Tm, Nf t -> Nf (succ @ t)
| Nf_rec0  : Nf rec
| Nf_rec1  : forall t : Tm, Nf t -> Nf (rec @ t)
| Nf_rec2  : forall t1 t2 : Tm, Nf t1 -> Nf t2 -> Nf (rec @ t1 @ t2)
| Nf_Ne    : forall t : Tm, Ne t -> Nf t

with Ne : Tm -> Prop :=
| Ne_App : forall t1 t2 : Tm, Ne t1 -> Nf t2 -> Ne (t1 @ t2)
| Ne_rec : forall t1 t2 t3 : Tm, Nf t1 -> Nf t2 -> Ne t3 -> Ne (rec @ t1 @ t2 @ t3).

Inductive Nf' : Tm -> Prop :=
| Nf'K0   : Nf' K
| Nf'K1   : forall t : Tm, Nf' t -> Nf' (K @ t)
| Nf'S0   : Nf' S
| Nf'S1   : forall t : Tm, Nf' t -> Nf' (S @ t)
| Nf'S2   : forall t1 t2 : Tm, Nf' t1 -> Nf' t2 -> Nf' (S @ t1 @ t2)
| Nf'rec0 : Nf' rec
| Nf'rec1 : forall t : Tm, Nf' t -> Nf' (rec @ t)
| Nf'rec2 : forall t1 t2 : Tm, Nf' t1 -> Nf' t2 -> Nf' (rec @ t1 @ t2)
| Nf'Ne'  : forall t : Tm, Ne' t -> Nf' t

with      Ne' : Tm -> Prop :=
| Ne'zero : Ne' zero
| Ne'succ : Ne' succ
| Ne'App  : forall t1 t2 : Tm, Ne' t1 -> Nf' t2 -> Ne' (t1 @ t2).

Inductive Nf3 : Tm -> Prop :=
| Nf3K1   : forall t : Tm, Nf3 t -> Nf3 (K @ t)
| Nf3S0   : Nf3 S
| Nf3S1   : forall t : Tm, Nf3 t -> Nf3 (S @ t)
| Nf3S2   : forall t1 t2 : Tm, Nf3 t1 -> Nf3 t2 -> Nf3 (S @ t1 @ t2)
| Nf3rec0 : Nf3 rec
| Nf3rec1 : forall t : Tm, Nf3 t -> Nf3 (rec @ t)
| Nf3rec2 : forall t1 t2 : Tm, Nf3 t1 -> Nf3 t2 -> Nf3 (rec @ t1 @ t2)
| Nf3Ne'  : forall t : Tm, Ne3 t -> Nf3 t

     with Ne3 : Tm -> Prop :=
| Ne3K0   : Ne3 K
| Ne3zero : Ne3 zero
| Ne3succ : Ne3 succ
| Ne3App  : forall t1 t2 : Tm, Ne3 t1 -> Nf3 t2 -> Ne3 (t1 @ t2).

#[global] Hint Constructors Nf Ne Nf' Ne' Nf3 Ne3 : core.

Ltac wut :=
repeat match goal with
| |- forall _, _ => intro
| |- ~ _ => intro
| |- _ /\ _ => split
| H : _ /\ _ |- _ => destruct H
| H : red (_ @ _) _ |- _ => inv H
| H : red K       _ |- _ => inv H
| H : red S       _ |- _ => inv H
| H : red zero    _ |- _ => inv H
| H : red succ    _ |- _ => inv H
| H : red rec     _ |- _ => inv H
| H : isNormal ?t, H' : red ?t _ |- _ => destruct (H _ H')
| |- isNormal _ => do 2 intro
| H : exists _, _   |- _ => decompose [ex and] H; clear H
| H : Ne ?x      |- _ => is_var x + inv H
| H : Ne' ?x      |- _ => is_var x + inv H
| _ => auto
end.

Fixpoint Nf_isNormal {t : Tm} (nf : Nf t) {struct nf} : isNormal t

with     Ne_isNormal {t : Tm} (ne : Ne t) {struct ne} : isNormal t.
Proof.
  - destruct nf;
      only 1-11: (wut; eapply Nf_isNormal;
        repeat match goal with
        | |- red _ _ => eauto
        end; eauto).
    apply Ne_isNormal. assumption.
  - destruct ne.
    + wut.
      * eapply Ne_isNormal; eauto.
      * eapply Nf_isNormal; eauto.
    + wut.
     * eapply Nf_isNormal; cycle 1; eauto.
     * eapply Nf_isNormal; cycle 1; eauto.
     * eapply Ne_isNormal; cycle 1; eauto.
Qed.

Fixpoint Nf'_isNormal {t : Tm} (nf : Nf' t) {struct nf} : isNormal t

with     Ne'_isNormal {t : Tm} (ne : Ne' t) {struct ne} : isNormal t.
Proof.
  - now destruct nf; wut;
      [eapply Nf'_isNormal; cycle 1; eauto.. | eapply Ne'_isNormal; eauto].
  - destruct ne; wut.
    + now eapply Ne'_isNormal; eauto.
    + now eapply Nf'_isNormal; eauto.
Qed.

Ltac hehe :=
repeat match goal with
| H : forall _, ~ _ |- False => eapply H; eauto
| H : _ -> Nf' _ |- Nf' _ => apply H; do 2 intro
| |- Nf' (_ @ _) => constructor; auto
| |- Ne' (_ @ _) => constructor; auto
| H : Nf' (_ @ _) |- _ => inv H
| H : Ne' (_ @ _) |- _ => inv H
end.

Lemma isNormal_Nf' :
  forall {t : Tm}, isNormal t -> Nf' t.
Proof.
Abort.

Goal
  forall t : Tm,
    Nf' t -> hasType t TNat -> t = zero \/ exists t' : Tm, t = succ @ t' /\ hasType t' TNat.
Proof.
  induction 1; intros HT; inv HT.
Abort.

Lemma isNormal_Nf' :
  forall {t : Tm} {a : Ty}, hasType t a -> isNormal t -> Nf' t.
Proof.
Abort.

Definition hasNormal (t : Tm) : Prop :=
  exists t' : Tm, reds t t' /\ isNormal t'.

Definition WN (t : Tm) (a : Ty) : Prop :=
  exists t' : Tm, hasType t' a /\ rtc red t t' /\ isNormal t'.

Fixpoint Reducible (t : Tm) (ty : Ty) : Prop :=
match ty with
| TNat     => WN t TNat
| TArr a b =>
  WN t (TArr a b) /\
  forall t' : Tm,
    hasType t' a -> Reducible t' a -> Reducible (t @ t') b
end.

Fixpoint R' (t : Tm) (ty : Ty) : Prop :=
match ty with
| TNat     => True
| TArr a b => forall t' : Tm, hasType t' a -> R' t' a -> R' (t @ t') b
end.

Goal
  forall t ty,
    Reducible t ty <-> WN t ty /\ R' t ty.
Proof.
Abort.

Lemma reds_AppL :
  forall t1 t1' t2 : Tm,
    reds t1 t1' -> reds (t1 @ t2) (t1' @ t2).
Proof.
  unfold reds.
  now induction 1; eauto.
Qed.

Lemma reds_AppR :
  forall t1 t2 t2' : Tm,
    reds t2 t2' -> reds (t1 @ t2) (t1 @ t2').
Proof.
  unfold reds.
  now induction 1; eauto.
Qed.

Lemma reds_App :
  forall t1 t1' t2 t2' : Tm,
    reds t1 t1' -> reds t2 t2' -> reds (t1 @ t2) (t1' @ t2').
Proof.
  intros.
  eapply rtc_trans.
  - now apply reds_AppL; eassumption.
  - now apply reds_AppR.
Qed.

Lemma hasType_Reducible :
  forall {a : Ty} {t : Tm},
    hasType t a -> Reducible t a.
Proof.
Abort.
