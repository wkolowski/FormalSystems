Require Import List Bool Arith.
Import ListNotations.

Require Import FormalSystems.Base.

(** * Types and terms *)

Inductive Ty : Type :=
    | TNat : Ty
    | TArr : Ty -> Ty -> Ty.

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
        forall a b : Ty, hasType K (TArr a (TArr b a))
    | hasType_S :
        forall a b c : Ty,
          hasType S (TArr (TArr a (TArr b c))
                          (TArr (TArr a b)
                                (TArr a c)))
    | hasType_App :
        forall (a b : Ty) (f x : Tm),
          hasType f (TArr a b) -> hasType x a ->
            hasType (App f x) b
    | hasType_zero :
        hasType zero TNat
    | hasType_succ :
        hasType succ (TArr TNat TNat)
    | hasType_rec :
        forall a : Ty,
          hasType rec (TArr a
                      (TArr (TArr TNat (TArr a a))
                            (TArr TNat a))).

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

Hint Constructors Ty Tm hasType red rtc : core.

Definition reds := rtc red.

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
    | Nf'App  : forall t1 t2 : Tm, Ne' t1 -> Nf' t2 -> Nf' (t1 @ t2)
    | Nf'Ne'  : forall t : Tm, Ne' t -> Nf' t

with      Ne' : Tm -> Prop :=
    | Ne'K    : Ne' K
    | Ne'S0   : Ne' S
    | Ne'S1   : forall t : Tm, Nf' t -> Ne' (S @ t)
    | Ne'zero : Ne' zero
    | Ne'succ : Ne' succ
    | Ne'rec0 : Ne' rec
    | Ne'rec1 : forall t : Tm, Nf' t -> Ne' (rec @ t).

Hint Constructors Nf Ne Nf' Ne' : core.

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
    | H : Ne ?x          |- _ => is_var x + inv H
    | H : Ne' ?x          |- _ => is_var x + inv H
    | _ => auto
end.

Fixpoint Nf_isNormal {t : Tm} (nf : Nf t) {struct nf} : isNormal t

with     Ne_isNormal {t : Tm} (ne : Ne t) {struct ne} : isNormal t.
Proof.
  destruct nf.
    1-11: wut; eapply Nf_isNormal;
      repeat match goal with
          | |- red _ _ => eauto
      end; eauto.
    apply Ne_isNormal. assumption.
  destruct ne.
    wut.
      eapply Ne_isNormal; eauto.
      eapply Nf_isNormal; eauto.
    wut.
      eapply Nf_isNormal. 2: eauto. eauto.
      eapply Nf_isNormal. 2: eauto. eauto.
      eapply Ne_isNormal. 2: eauto. eauto.
Qed.

Fixpoint Nf'_isNormal {t : Tm} (nf : Nf' t) {struct nf} : isNormal t

with     Ne'_isNormal {t : Tm} (ne : Ne' t) {struct ne} : isNormal t.
Proof.
  destruct nf; wut.
    eapply Ne'_isNormal; eauto.
    eapply Nf'_isNormal; eauto.
    eapply Ne'_isNormal; eauto.
  destruct ne; wut.
    eapply Nf'_isNormal; eauto.
    eapply Nf'_isNormal; eauto.
Qed.

Lemma isNormal_Nf' :
  forall t : Tm, isNormal t -> Nf' t.
Proof.
  unfold isNormal.
  induction t; intros; auto.
  destruct t1. all: cycle 3.
    constructor; auto. apply IHt2. wut. eapply H. eauto.
    constructor; auto. apply IHt2. wut. eapply H. eauto.
    constructor; auto. apply IHt2. wut. eapply H. eauto.
    constructor; auto. apply IHt2. wut. eapply H. eauto.
    constructor; auto. apply IHt2. wut. eapply H. eauto.
    destruct t1_1. all: cycle 3.
      repeat constructor. auto.
Abort.

Definition hasNormal (t : Tm) : Prop :=
  exists t' : Tm, reds t t' /\ isNormal t'.

Definition WN (t : Tm) (a : Ty) : Prop :=
  exists t' : Tm, hasType t' a /\ rtc red t t' /\ isNormal t'.

Fixpoint Reducible (t : Tm) (ty : Ty) : Prop :=
match ty with
    | TNat     => WN t TNat
    | TArr a b => WN t (TArr a b) /\
                  forall t' : Tm,
                    hasType t' a -> Reducible t' a -> Reducible (t @ t') b
end.

Fixpoint R' (t : Tm) (ty : Ty) : Prop :=
match ty with
    | TNat     => True
    | TArr a b => forall t' : Tm,
                    hasType t' a -> R' t' a -> R' (t @ t') b
end.

Goal
  forall t ty,
    Reducible t ty <-> WN t ty /\ R' t ty.
Proof.
  split.
    revert t. induction ty; cbn; intros.
      auto.
      firstorder. destruct ty2; cbn.
        trivial.
        intros. cbn in *. edestruct IHty2.
Abort.

Lemma reds_AppL :
  forall t1 t1' t2 : Tm,
    reds t1 t1' -> reds (t1 @ t2) (t1' @ t2).
Proof.
  unfold reds.
  induction 1; eauto.
Qed.

Lemma reds_AppR :
  forall t1 t2 t2' : Tm,
    reds t2 t2' -> reds (t1 @ t2) (t1 @ t2').
Proof.
  unfold reds.
  induction 1; eauto.
Qed.

Lemma reds_App :
  forall t1 t1' t2 t2' : Tm,
    reds t1 t1' -> reds t2 t2' -> reds (t1 @ t2) (t1' @ t2').
Proof.
  intros.
  eapply rtc_trans.
    apply reds_AppL. eassumption.
    apply reds_AppR. eassumption.
Qed.

Lemma hasType_Reducible :
  forall {a : Ty} {t : Tm},
    hasType t a -> Reducible t a.
Proof.
  induction 1.
    cbn. split.
      red. exists K. repeat split; auto. wut.
      split; intros.
        red. destruct a; cbn in *; unfold WN in *.
          decompose [ex and] H0; clear H0. exists (K @ x). split; eauto. split.
            apply reds_AppR. assumption.
            wut.
          decompose [ex and] H0; clear H0. exists (K @ x). split; eauto. split.
            apply reds_AppR. assumption.
            wut.
        clear -a H0. induction a; cbn in *; unfold WN in *; intros.
          wut. exists x. wut. constructor 3 with (K @ x @ t'0).
            apply reds_AppL, reds_AppR. assumption.
            auto.
          wut.
            exists x. wut. constructor 3 with (K @ x @ t'0).
              apply reds_AppL, reds_AppR. assumption.
              auto.
            admit.
    admit.
    cbn in *. wut.
    cbn. wut. red. exists zero. wut.
    cbn. wut.
      red. exists succ. wut.
      unfold WN in *. wut. exists (succ @ x). wut.
        eauto.
        apply reds_AppR. assumption.
    cbn. unfold WN. wut.
      exists rec. wut.
      destruct a; cbn in *; unfold WN in *; wut.
        exists (rec @ x). wut.
          eauto.
          apply reds_AppR. assumption.
        exists (rec @ x). wut.
          eauto.
          apply reds_AppR. assumption.
      destruct a; cbn in *; unfold WN in *; wut.
        exists (rec @ x0 @ x). wut.
          eauto.
          repeat apply reds_App; unfold reds; auto.
        exists (rec @ x0 @ x). wut.
          eauto.
          repeat apply reds_App; unfold reds; auto.
      edestruct (H5 _ H7).
        exists x. wut.
        wut. destruct a; cbn.
Restart.
  induction a; cbn; intros.
    red. remember TNat as n. revert Heqn. induction H; inversion 1; subst.
      admit.
      admit.
    wut.
      red. exists t. wut.
Abort.