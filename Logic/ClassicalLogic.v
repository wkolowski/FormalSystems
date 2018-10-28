Require Import List.
Import ListNotations.

Require Import Bool.

Parameter V : Type.
Parameter dec : V -> V -> bool.
Parameter dec_spec :
  forall x y : V, reflect (x = y) (dec x y).

Require Import Arith.

Notation "x =? y" := (dec x y) (at level 70).

Inductive Formula : Type :=
    | Var : V -> Formula
    | FFalse : Formula
    | FTrue : Formula
    | Not : Formula -> Formula
    | Impl : Formula -> Formula -> Formula
    | Or : Formula -> Formula -> Formula
    | And : Formula -> Formula -> Formula.

Definition Iff (P Q : Formula) : Formula :=
  And (Impl P Q) (Impl Q P).

Definition Valuation : Type := V -> bool.

Fixpoint value (f : Valuation) (F : Formula) : bool :=
match F with
    | Var x => f x
    | FFalse => false
    | FTrue => true
    | Not F' => negb (value f F')
    | Impl F1 F2 => orb (negb (value f F1)) (value f F2)
    | Or F1 F2 => orb (value f F1) (value f F2)
    | And F1 F2 => andb (value f F1) (value f F2)
end.

Definition valid (v : Valuation) (F : Formula) : Prop :=
  value v F = true.

Definition tautology (F : Formula) : Prop :=
  forall v : Valuation, valid v F.

Lemma LEM_tautology :
  forall P : Formula, tautology (Or P (Not P)).
Proof.
  unfold tautology, valid, Valuation; cbn; intros.
  destruct (value v P); cbn; reflexivity.
Qed.