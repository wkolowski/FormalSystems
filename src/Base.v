From Stdlib Require Export
  Bool Arith List
  Equality Recdef
  Setoid Morphisms Classes.RelationClasses Classes.DecidableClass Relation_Definitions.
Export ListNotations.

Arguments decide : simpl never.

(* The type of atoms, i.e. names of variables. *)
Definition Atom : Type := nat.

(** * Stuff for dealing with [option]. *)

Definition omap {A B : Type} (f : A -> B) (oa : option A) : option B :=
match oa with
| None => None
| Some a => Some (f a)
end.

Definition liftM2 {A B C : Type} (f : A -> B -> C) (oa : option A) (ob : option B) : option C :=
match oa, ob with
| Some a, Some b => Some (f a b)
| _, _ => None
end.

Definition obind {A B : Type} (oa : option A) (f : A -> option B) : option B :=
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

#[global] Hint Constructors rtc : core.

Inductive rtc' {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| rtc'_refl :
    forall x : A, rtc' R x x
| rtc'_steptrans :
    forall x y z : A, R x y -> rtc' R y z -> rtc' R x z.

#[global] Hint Constructors rtc' : core.

#[export]
Instance Reflexive_rtc' {A : Type} (R : A -> A -> Prop) : Reflexive (rtc' R).
Proof.
  now red; constructor.
Defined.

#[export]
Instance Transitive_rtc' {A : Type} (R : A -> A -> Prop) : Transitive (rtc' R).
Proof.
  red; intros x y z Hxy Hyz; revert z Hyz.
  induction Hxy; intros; [easy |].
  now econstructor; [| apply IHHxy].
Defined.

Definition rtc'_trans := @Transitive_rtc'.

(** * Transitive closure *)

Inductive tc {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| tc_singl :
    forall x y : A, R x y -> tc R x y
| tc_cons  :
    forall x y z : A, R x y -> tc R y z -> tc R x z.

Lemma tc_trans :
  forall {A : Type} {R : A -> A -> Prop} {x y z : A},
    tc R x y -> tc R y z -> tc R x z.
Proof.
  intros * Hxy Hyz.
  revert z Hyz.
  induction Hxy; intros.
  - now apply tc_cons with y.
  - now apply tc_cons with y; auto.
Qed.
