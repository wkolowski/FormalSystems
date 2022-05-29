Require Import List Bool Arith.
Import ListNotations.

Require Import FormalSystems.Base.

(** * Types and terms *)

Inductive Ty : Type :=
    | TNat : Ty
    | TArr : Ty -> Ty -> Ty.

Notation "a → b" := (TArr a b) (at level 60, right associativity).

Inductive Tm : Ty -> Type :=
    | K : forall {a b : Ty}, Tm (a → b → a)
    | S : forall {a b c : Ty}, Tm ((a → b → c) → (a → b) → a → c)
    | App : forall {a b : Ty}, Tm (a → b) -> Tm a -> Tm b
    | zero : Tm TNat
    | succ : Tm (TNat → TNat)
    | rec  : forall {a : Ty}, Tm (a → (TNat → a → a) → TNat → a).

Notation "M @ N" := (App M N) (at level 50, left associativity).

Inductive red : forall {A : Ty}, Tm A -> Tm A -> Prop :=
    | red_K :
        forall {A B : Ty} (f : Tm (A → B → A)) (a : Tm A) (b : Tm B),
          red (K @ a @ b) a
    | red_S :
        forall {A B C : Ty} (f : Tm (A → B → C)) (g : Tm (A → B)) (a : Tm A),
          red (S @ f @ g @ a) (f @ a @ (g @ a))
    | red_rec_zero :
        forall {A : Ty} (z : Tm A) (s : Tm (TNat → A → A)),
          red (rec @ z @ s @ zero) z
    | red_rec_succ :
        forall {A : Ty} (z : Tm A) (s : Tm (TNat → A → A)) (n : Tm TNat),
          red (rec @ z @ s @ (succ @ n)) (s @ n @ (rec @ z @ s @ n))
    | red_AppL :
        forall {A B : Ty} (f f' : Tm (A → B)) (a : Tm A),
          red f f' -> red (f @ a) (f @ a)
    | red_AppR :
        forall {A B : Ty} (f : Tm (A → B)) (a a' : Tm A),
          red a a' -> red (f @ a) (f @ a').

Notation "A ~> B" := (red A B) (at level 60).

#[global] Hint Constructors Ty Tm red rtc : core.

Definition reds {A : Ty} (t1 t2 : Tm A) : Prop := rtc (@red A) t1 t2.

Notation "A ~> B" := (red A B) (at level 60).

Definition isNormal {A : Ty} (a : Tm A) : Prop :=
  forall a' : Tm A, ~ a ~> a'.

Inductive Nf : forall {A : Ty}, Tm A -> Prop :=
    | Nf_K0    : forall {A B : Ty}, Nf (@K A B)
    | Nf_K1    : forall {A B : Ty} (a : Tm A), Nf a -> Nf (@K A B @ a)
    | Nf_S0    : forall {A B C : Ty}, Nf (@S A B C)
    | Nf_S1    : forall {A B C : Ty} (f : Tm (A → B → C)), Nf f -> Nf (S @ f)
    | Nf_S2    : forall {A B C : Ty} (f : Tm (A → B → C)) (g : Tm (A → B)), Nf f -> Nf g -> Nf (S @ f @ g)
    | Nf_zero  : Nf zero
    | Nf_succ0 : Nf succ
    | Nf_succ1 : forall n : Tm TNat, Nf n -> Nf (succ @ n)
    | Nf_rec0  : forall {A : Ty}, Nf (@rec A)
    | Nf_rec1  : forall {A : Ty} (z : Tm A), Nf z -> Nf (rec @ z)
    | Nf_rec2  : forall {A : Ty} (z : Tm A) (s : Tm (TNat → A → A)), Nf z -> Nf s -> Nf (rec @ z @ s).

#[global] Hint Constructors Nf : core.

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
(*     | H : Ne ?x          |- _ => is_var x + inv H *)
(*     | H : Ne' ?x          |- _ => is_var x + inv H *)
    | _ => auto
end.

Require Import Equality.

Lemma Nf_isNormal :
  forall {A : Ty} {a : Tm A},
    Nf a -> isNormal a.
Proof.
  unfold isNormal.
  induction 1.
    wut.
    do 2 intro. inv H0.
Abort.

(*
Fixpoint Nf'_isNormal {t : Tm} (nf : Nf' t) {struct nf} : isNormal t

with     Ne'_isNormal {t : Tm} (ne : Ne' t) {struct ne} : isNormal t.
Proof.
  destruct nf; wut.
    eapply Nf'_isNormal; eauto.
    eapply Nf'_isNormal; eauto.
    eapply Nf'_isNormal. 2: eauto. eauto.
    eapply Nf'_isNormal; eauto.
    eapply Nf'_isNormal; eauto.
    eapply Nf'_isNormal. 2: eauto. eauto.
    eapply Nf'_isNormal; eauto.
    eapply Ne'_isNormal; eauto.
  destruct ne; wut.
    eapply Ne'_isNormal; eauto.
    eapply Nf'_isNormal; eauto.
Qed.

Lemma isNormal_Nf' :
  forall {t : Tm}, isNormal t -> Nf' t.
Proof.
  
      Ltac hehe :=
      repeat match goal with
          | H : forall _, ~ _ |- False => eapply H; eauto
          | H : _ -> Nf' _ |- Nf' _ => apply H; do 2 intro
          | |- Nf' (_ @ _) => constructor; auto
          | |- Ne' (_ @ _) => constructor; auto
          | H : Nf' (_ @ _) |- _ => inv H
          | H : Ne' (_ @ _) |- _ => inv H
      end.

  unfold isNormal.
  induction t; intros; auto.
  destruct t1.
    1-2, 4-6: hehe.
    destruct t1_1. all: cycle 3.
      do 2 constructor.
        assert (Nf' (zero @ t1_2)).
          apply IHt1. wut. eapply H. eauto.
          inv H0.
        apply IHt2. do 2 intro. eapply H. eauto.
      do 2 constructor.
        assert (Nf' (succ @ t1_2)).
          apply IHt1. wut. eapply H. eauto.
          inv H0.
        apply IHt2. do 2 intro. eapply H. eauto.
      constructor.
        assert (Nf' (rec @ t1_2)).
          apply IHt1. wut. eapply H. eauto.
          inv H0. inv H1.
        apply IHt2. do 2 intro. eapply H. eauto.
      specialize (H t1_2). contradict H. eauto.
      constructor.
        assert (Nf' (S @ t1_2)).
          apply IHt1. wut. eapply H. eauto.
          inv H0. inv H1.
        apply IHt2. do 2 intro. eapply H. eauto.
      assert (Nf' (t1_1_1 @ t1_1_2 @ t1_2)).
        apply IHt1. do 2 intro. eapply H. eauto.
        inv H0.
          specialize (H (t1_1_2 @ t2 @ (t1_2 @ t2))). contradict H. eauto.
          exfalso. eapply H.
Abort.

Goal
  forall t : Tm,
    Nf' t -> hasType t TNat -> t = zero \/ exists t' : Tm, t = succ @ t' /\ hasType t' TNat.
Proof.
  induction 1; intros HT; inv HT.
    inv H2.
    inv H2.
    inv H3. inv H4.
    inv H2.
    inv H3. inv H4.
    revert x a H0 H1 H. induction f; intros.
      inv H0.
      inv H0.
      inv H0. inv H4.
        inv H. inv H3. inv H2.
        inv H. inv H5. inv H4.
  inv H0; inv H3.
    inv H1.
    inv H1.
    inv H. inv H4. inv H3; inv H0. inv H. inv H8. inv H8.
    
  
Lemma isNormal_Nf' :
  forall {t : Tm} {a : Ty}, hasType t a -> isNormal t -> Nf' t.
Proof.
  unfold isNormal.
  induction 1; intros; auto.
  inv H; cycle 3.
    do 2 constructor; auto. apply IHhasType2. wut. eapply H1. eauto.
    constructor; auto. apply IHhasType2. wut. eapply H1. eauto.
    constructor; auto. apply IHhasType2. wut. eapply H1. eauto.
    constructor; auto. apply IHhasType2. wut. eapply H1. eauto.
    inv H2. all: cycle 3.
      constructor.
        assert (Nf' (rec @ x0)).
          apply IHhasType1. wut. eapply H1. eauto.
          inv H. inv H2.
        apply IHhasType2. wut. eapply H1. eauto.
      specialize (H1 x0). contradict H1. eauto.
      constructor; auto.
        assert (Nf' (S @ x0)).
          apply IHhasType1. wut. eapply H1. eauto.
          inv H. inv H2.
        apply IHhasType2. wut. eapply H1. eauto.
      assert (Nf' (f @ x1 @ x0)).
        apply IHhasType1. do 2 intro. eapply H1. eauto.
        inv H2.
          specialize (H1 (x1 @ x @ (x0 @ x))). contradict H1. eauto.
          assert (Nf' x).
            apply IHhasType2. do 2 intro. eapply H1. eauto.
            inv H. inv H0; try inv H6; try inv H8; try inv H6.
              inv H.
                inv H2.
                  inv H0.
                  inv H0.
                  inv H. inv H10. inv H8.
                    inv H0. inv H0. inv 

 inv H2. inv H8; inv H.
                exfalso. eapply H1. eauto.
                




    constructor; auto. apply IHhasType2. wut. eapply H1. eauto.
    constructor; auto. apply IHhasType2. wut. eapply H1. eauto.
    inv H2.
      admit.
      constructor.
        constructor.
      assert (Nf' (S @ x0)).
        admit.
        inv H.
          repeat constructor. inv H6. econstructor. auto.
      constructor. auto.
        assert (Nf'
        constructor; auto. apply IHhasType2. wut. eapply H1. eauto.
    constructor; auto. apply IHhasType2. wut. eapply H1. eauto. constructor.
  destruct f. all: cycle 3.
    constructor; auto. apply IHt2. wut. eapply H. eauto.
    constructor; auto. apply IHt2. wut. eapply H. eauto.
    constructor; auto. apply IHt2. wut. eapply H. eauto.
    constructor; auto. apply IHt2. wut. eapply H. eauto.
    constructor; auto. apply IHt2. wut. eapply H. eauto.
    destruct t1_1. all: cycle 3.
      repeat constructor. constructor. auto.
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
Abort.
*)