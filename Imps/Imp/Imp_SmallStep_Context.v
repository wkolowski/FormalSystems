Add Rec LoadPath "~/Code/Coq".

Require Import ImpSyntax.

(** * Structural operational semantics for IMP using contexts *)

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

Fixpoint put (G : AContext) (a : AExp) : AExp :=
match G with
    | AC_Var => a
    | AC_L f G' a' => ABinOp f (put G' a) a'
    | AC_R f n G' => ABinOp f (AConst n) (put G' a)
end.

Inductive AEval (s : State) : AExp -> AExp -> Prop :=
    | AEval_put :
        forall (a1 a2 : AExp) (G : AContext),
          AStep s a1 a2 -> AEval s (put G a1) (put G a2).

Hint Constructors AStep AEval.

Require Import Recdef.

Function AExp_to_AContext (a : AExp) : AContext * AExp :=
match a with
    | AConst n => (AC_Var, AConst n)
    | Var x => (AC_Var, Var x)
    | ABinOp f (AConst n) a2 =>
        let '(G, a) := AExp_to_AContext a2 in (AC_R f n G, a)
    | ABinOp f a1 a2 =>
        let '(G, a) := AExp_to_AContext a1 in (AC_L f G a2, a)
end.

Lemma AExp_to_AContext_put :
  forall (a1 a2 : AExp) (G : AContext),
    AExp_to_AContext a1 = (G, a2) -> put G a2 = a1.
Proof.
  intros a1.
  functional induction AExp_to_AContext a1;
    intros; inv H; cbn; f_equal; auto.
Qed.

Lemma AExp_to_AContext_put' :
  forall a : AExp,
    put (fst (AExp_to_AContext a)) (snd (AExp_to_AContext a)) = a.
Proof.
  intros. apply AExp_to_AContext_put.
  destruct AExp_to_AContext. cbn. reflexivity.
Qed.

Require Imp.Imp_SmallStep.

Lemma AEval_AEval :
  forall (s : State) (a1 a2 : AExp),
    AEval s a1 a2 <-> Imp_SmallStep.AEval s a1 a2.
Proof.
  split.
    intro. inv H. induction G; cbn; auto. induction H0; auto.
    rewrite <- (AExp_to_AContext_put' a1) at 2.
    rewrite <- (AExp_to_AContext_put' a2) at 2.
    induction 1.
      constructor; cbn; auto.
Admitted.
(*
apply AExp_to_AContext_put in x.
 destruct x as [G1 a1'].
    pose (x := AExp_to_AContext a2). destruct x as [G2 a2'].
    
    induction 1.
      change (Var x) with (put ACVar (Var x)).
      change (AConst (s x)) with (put ACVar (AConst (s x))). auto.
*)