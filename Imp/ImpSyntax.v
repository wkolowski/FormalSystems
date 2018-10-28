Require Export Bool.

Require Export List.
Export ListNotations.

Require Import Arith.

Parameter Loc : Type.
Parameter dec : Loc -> Loc -> bool.
Parameter dec_spec :
  forall x y : Loc, reflect (x = y) (dec x y).

Notation "x =? y" := (dec x y) (at level 70).

Ltac inv H :=
  inversion H; subst; clear H.

Inductive AExp : Type :=
    | AConst : nat -> AExp
    | Var : Loc -> AExp
    | Add : AExp -> AExp -> AExp
    | Sub : AExp -> AExp -> AExp
    | Mul : AExp -> AExp -> AExp.

Inductive BExp : Type :=
    | BConst : bool -> BExp
    | Eq : AExp -> AExp -> BExp
    | Le : AExp -> AExp -> BExp
    | Not : BExp -> BExp
    | And : BExp -> BExp -> BExp
    | Or : BExp -> BExp -> BExp.

Inductive Com : Type :=
    | Skip : Com
    | Asgn : Loc -> AExp -> Com
    | Seq : Com -> Com -> Com
    | If : BExp -> Com -> Com -> Com
    | While : BExp -> Com -> Com.

Definition State : Type := Loc -> nat.

Definition initialState : State := fun _ => 0.

Definition changeState (s : State) (x : Loc) (n : nat) : State :=
  fun y : Loc => if x =? y then n else s y.