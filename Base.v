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