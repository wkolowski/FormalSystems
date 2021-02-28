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

Hint Constructors Ty Tm hasType red rtc : core.

Definition reds := rtc red.

Definition isNormal (t : Tm) : Prop :=
  forall t' : Tm, ~ red t t'.

Definition hasNormal (t : Tm) : Prop :=
  exists t' : Tm, reds t t' /\ isNormal t'.

Definition WN (t : Tm) (a : Ty) : Prop :=
  exists t' : Tm, hasType t' a /\ rtc red t t' /\ isNormal t'.

(* Inductive Reducible : Tm -> Ty -> Prop :=
    | Reducible_TNat :
        forall t : Tm, WN t TNat -> Reducible t TNat
    | Reducible_TArr :
        forall (t : Tm) (a b : Ty),
          WN t (TArr a b) ->
          (forall t' : Tm, hasType t' a -> Reducible t' a -> Reducible (App t t') b) ->
            Reducible t (TArr a b).
 *)

Fixpoint Reducible (ty : Ty) (t : Tm) : Prop :=
match ty with
    | TNat     => WN t TNat
    | TArr a b => WN t (TArr a b) /\
                  forall t' : Tm,
                    hasType t' a -> Reducible a t' -> Reducible b (App t t')
end.

Lemma hasType_Reducible :
  forall {a : Ty} {t : Tm},
    hasType t a -> Reducible a t.
Proof.
  induction 1.
    cbn. split.
      red. exists K. repeat split; auto. red. do 2 intro. inv H.
      split; intros.
        red. destruct a; cbn in *; unfold WN in *.
          decompose [ex and] H0; clear H0. exists (K @ x). split; eauto. split.
            admit. (* rtc_AppR *)
            red. do 2 intro. inv H0.
              inv H7.
Abort.