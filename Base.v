Require Export Bool.

Require Export List.
Export ListNotations.

Parameter Loc : Type.
Parameter dec : Loc -> Loc -> bool.
Parameter dec_spec :
  forall x y : Loc, reflect (x = y) (dec x y).

Require Export Arith.

Notation "x =? y" := (dec x y) (at level 70).

Ltac inv H :=
  inversion H; subst; clear H.

(** * Stuff for dealing with [option]. *)

Definition omap {A B : Type}
  (f : A -> B) (oa : option A) : option B :=
match oa with
    | None => None
    | Some a => Some (f a)
end.

Definition liftM2 {A B C : Type}
  (f : A -> B -> C) (oa : option A) (ob : option B) : option C :=
match oa, ob with
    | Some a, Some b => Some (f a b)
    | _, _ => None
end.

Definition obind {A B : Type}
  (oa : option A) (f : A -> option B) : option B :=
match oa with
    | None => None
    | Some a => f a
end.

(** * Reflexive-transitive closures *)

Inductive rtc {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
    | rtc_step :
        forall x y : A, R x y -> rtc R x y
    | rtc_refl :
        forall x : A, rtc R x x
    | rtc_trans :
        forall x y z : A, rtc R x y -> rtc R y z -> rtc R x z.

Hint Constructors rtc.

Inductive rtc' {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
    | rtc'_refl :
        forall x : A, rtc' R x x
    | rtc'_steptrans :
        forall x y z : A, R x y -> rtc' R y z -> rtc' R x z.

Hint Constructors rtc'.

Lemma rtc'_trans :
  forall {A : Type} {R : A -> A -> Prop} {x y z : A},
    rtc' R x y -> rtc' R y z -> rtc' R x z.
Proof.
  intros until 1. revert z.
  induction H; intros.
    assumption.
    eauto.
Qed.