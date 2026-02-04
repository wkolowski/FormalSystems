From Stdlib Require Import Recdef.

From FormalSystems Require Import Imp.Syntax.
From FormalSystems Require Imp.Smallstep.

(** * Structural operational semantics for IMP using (evaluation) contexts *)

Inductive AStep (s : State) : AExp -> AExp -> Prop :=
| AStep_Var :
    forall x : Loc, AStep s (Var x) (AConst (s x))
| AStep_ABinOp :
    forall (f : nat -> nat -> nat) (n1 n2 : nat),
      AStep s (ABinOp f (AConst n1) (AConst n2)) (AConst (f n1 n2)).

Inductive AContext : Type :=
| AC_Var : AContext
| AC_L : (nat -> nat -> nat) -> AContext -> AExp -> AContext
| AC_R : (nat -> nat -> nat) -> nat -> AContext -> AContext.

Fixpoint aput (G : AContext) (a : AExp) : AExp :=
match G with
| AC_Var => a
| AC_L f G' a' => ABinOp f (aput G' a) a'
| AC_R f n G' => ABinOp f (AConst n) (aput G' a)
end.

Inductive AEval (s : State) : AExp -> AExp -> Prop :=
| AEval_aput :
    forall (a1 a2 : AExp) (G : AContext),
      AStep s a1 a2 -> AEval s (aput G a1) (aput G a2).

#[global] Hint Constructors AStep AEval : core.

(*
Function AExp_to_AContext (a : AExp) : AContext * AExp :=
match a with
| AConst n => (AC_Var, AConst n)
| Var x => (AC_Var, Var x)
| ABinOp f (AConst n) a2 =>
        let '(G, a) := AExp_to_AContext a2 in (AC_R f n G, a)
| ABinOp f a1 a2 =>
        let '(G, a) := AExp_to_AContext a1 in (AC_L f G a2, a)
end.

Lemma AExp_to_AContext_aput :
  forall (a1 a2 : AExp) (G : AContext),
    AExp_to_AContext a1 = (G, a2) -> aput G a2 = a1.
Proof.
  intros a1.
  functional induction AExp_to_AContext a1;
    intros; inv H; cbn; f_equal; auto.
Qed.

Lemma AExp_to_AContext_aput' :
  forall a : AExp,
    aput (fst (AExp_to_AContext a)) (snd (AExp_to_AContext a)) = a.
Proof.
  intros. apply AExp_to_AContext_aput.
  destruct AExp_to_AContext. cbn. reflexivity.
Qed.
*)

Lemma AEval_Smallstep_AEval :
  forall (s : State) (a1 a2 : AExp),
    AEval s a1 a2 <-> Smallstep.AEval s a1 a2.
Proof.
  split.
    intro. inv H. induction G; cbn; auto. induction H0; auto.
    induction 1.
      change (Var x)
        with (aput AC_Var (Var x));
      change (AConst (s x))
        with (aput AC_Var (AConst (s x))).
        constructor. constructor.
      inv IHAEval.
        change (ABinOp f (aput G a0) a2)
          with (aput (AC_L f G a2) a0).
        change (ABinOp f (aput G a3) a2)
          with (aput (AC_L f G a2) a3).
        constructor. assumption.
      inv IHAEval.
        change (ABinOp f (AConst n) (aput G a1))
          with (aput (AC_R f n G) a1).
        change (ABinOp f (AConst n) (aput G a0))
          with (aput (AC_R f n G) a0).
        constructor. assumption.
      change (ABinOp f (AConst n1) (AConst n2))
        with (aput AC_Var (ABinOp f (AConst n1) (AConst n2)));
      change (AConst (f n1 n2))
        with (aput AC_Var (AConst (f n1 n2))).
        constructor. constructor.
Qed.

Inductive BStep : BExp -> BExp -> Prop :=
| BStep_BRelOp :
    forall (f : nat -> nat -> bool) (n1 n2 : nat),
      BStep (BRelOp f (AConst n1) (AConst n2)) (BConst (f n1 n2))
| BStep_Not :
    forall b : bool, BStep (Not (BConst b)) (BConst (negb b))
| BStep_BBinOp :
    forall (f : bool -> bool -> bool) (b1 b2 : bool),
      BStep (BBinOp f (BConst b1) (BConst b2)) (BConst (f b1 b2)).

Inductive BContext : Type :=
| BC_Hole : BContext
(*
| BC_BRelOp_L : (nat -> nat -> bool) -> BContext -> AExp -> BContext
| BC_BRelOp_R : (nat -> nat -> bool) -> nat -> BContext -> BContext
*)
| BC_Not : BContext -> BContext
| BC_BBinOp_L : (bool -> bool -> bool) -> BContext -> BExp -> BContext
| BC_BBinOp_R : (bool -> bool -> bool) -> bool -> BContext -> BContext.

Fixpoint bput (G : BContext) (e : BExp) : BExp :=
match G with
| BC_Hole => e
(*
| BC_BRelOp_L f G' a => BRelOp f (bput G' e) a
| BC_BRelOp_R f n G' => BRelOp f (AConst n) (bput G' e)
*)
| BC_Not G' => Not (bput G' e)
| BC_BBinOp_L f G' e' => BBinOp f (bput G' e) e'
| BC_BBinOp_R f b G' => BBinOp f (BConst b) (bput G' e)
end.

Inductive BEval : BExp -> BExp -> Prop :=
| BEval_bput :
    forall (G : BContext) (b1 b2 : BExp),
      BStep b1 b2 -> BEval (bput G b1) (bput G b2).

Lemma BEval_Smallstep_BEval :
  forall (s : State) (b1 b2 : BExp),
    BEval b1 b2 <-> Smallstep.BEval s b1 b2.
Proof.
  split.
    intro. inv H. induction G; cbn; auto. inv H0; auto.
    induction 1.
      admit.
      admit.
      {
        change (BRelOp f (AConst n1) (AConst n2))
          with (bput BC_Hole (BRelOp f (AConst n1) (AConst n2))).
        change (BConst (f n1 n2 ))
          with (bput BC_Hole (BConst (f n1 n2))).
        constructor. constructor.
      }
      {
        inv IHBEval.
        change (Not (bput G b1)) with (bput (BC_Not G) b1).
        change (Not (bput G b2)) with (bput (BC_Not G) b2).
        constructor. assumption.
      }
      {
        change (Not (BConst b))
          with (bput BC_Hole (Not (BConst b))).
        change (BConst (negb b))
          with (bput BC_Hole (BConst (negb b))).
        constructor. constructor.
      }
      {
        inv IHBEval.
        change (BBinOp f (bput G b1) e2)
          with (bput (BC_BBinOp_L f G e2) b1).
        change (BBinOp f (bput G b2) e2)
          with (bput (BC_BBinOp_L f G e2) b2).
        constructor. assumption.
      }
      {
        inv IHBEval.
        change (BBinOp f (BConst b) (bput G b1))
          with (bput (BC_BBinOp_R f b G) b1).
        change (BBinOp f (BConst b) (bput G b2))
          with (bput (BC_BBinOp_R f b G) b2).
        constructor. assumption.
      }
      {
        change (BBinOp f (BConst b1) (BConst b2))
          with (bput BC_Hole (BBinOp f (BConst b1) (BConst b2))).
        change (BConst (f b1 b2))
          with (bput BC_Hole (BConst (f b1 b2))).
        constructor. constructor.
      }
Admitted.
