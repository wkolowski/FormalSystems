Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import ImpSyntax.

(** * Structural operational semantics for IMP using contexts *)

Inductive AStep (s : State) : AExp -> AExp -> Prop :=
    | AStepVar :
        forall x : Loc, AStep s (Var x) (AConst (s x))
    | AStepAdd :
        forall n1 n2 : nat,
          AStep s (Add (AConst n1) (AConst n2)) (AConst (n1 + n2))
    | AStepSub :
        forall n1 n2 : nat,
          AStep s (Sub (AConst n1) (AConst n2)) (AConst (n1 - n2))
    | AStepMul :
        forall n1 n2 : nat,
          AStep s (Mul (AConst n1) (AConst n2)) (AConst (n1 * n2)).

Inductive AContext : Type :=
    | ACVar : AContext
    | ACAddL : AContext -> AExp -> AContext
    | ACAddR : nat -> AContext -> AContext
    | ACSubL : AContext -> AExp -> AContext
    | ACSubR : nat -> AContext -> AContext
    | ACMulL : AContext -> AExp -> AContext
    | ACMulR : nat -> AContext -> AContext.

Fixpoint put (G : AContext) (a : AExp) : AExp :=
match G with
    | ACVar => a
    | ACAddL G' a' => Add (put G' a) a'
    | ACAddR n G' => Add (AConst n) (put G' a)
    | ACSubL G' a' => Sub (put G' a) a'
    | ACSubR n G' => Sub (AConst n) (put G' a)
    | ACMulL G' a' => Mul (put G' a) a'
    | ACMulR n G' => Mul (AConst n) (put G' a)
end.

Inductive AEval (s : State) : AExp -> AExp -> Prop :=
    | AEval' :
        forall (a1 a2 : AExp) (G : AContext),
          AStep s a1 a2 -> AEval s (put G a1) (put G a2).

Hint Constructors AStep AEval.

(*
Fixpoint AExp_to_AContext (a : AExp) : AContext :=
match a with
    | AConst _ => ACVar
    | Var x => ACVar
    | Add (AConst n) a2 => ACAddR n (AExp_to_AContext a2)
    | Add a1 a2 => ACAddL (AExp_to_AContext a1) a2
    | Sub (AConst n) a2 => ACSubR n (AExp_to_AContext a2)
    | Sub a1 a2 => ACSubL (AExp_to_AContext a1) a2
    | Mul (AConst n) a2 => ACMulR n (AExp_to_AContext a2)
    | Mul a1 a2 => ACMulL (AExp_to_AContext a1) a2
end.
*)

Require Import Recdef.

Function AExp_to_AContext (a : AExp) : AContext * AExp :=
match a with
    | AConst n => (ACVar, AConst n)
    | Var x => (ACVar, Var x)
    | Add (AConst n) a2 =>
        let '(G, a) := AExp_to_AContext a2 in (ACAddR n G, a)
    | Add a1 a2 =>
        let '(G, a) := AExp_to_AContext a1 in (ACAddL G a2, a)
    | Sub (AConst n) a2 =>
        let '(G, a) := AExp_to_AContext a2 in (ACSubR n G, a)
    | Sub a1 a2 =>
        let '(G, a) := AExp_to_AContext a1 in (ACSubL G a2, a)
    | Mul (AConst n) a2 =>
        let '(G, a) := AExp_to_AContext a2 in (ACMulR n G, a)
    | Mul a1 a2 =>
        let '(G, a) := AExp_to_AContext a1 in (ACMulL G a2, a)
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

Require Imp_SOS.

Lemma AEval_AEval :
  forall (s : State) (a1 a2 : AExp),
    AEval s a1 a2 <-> Imp_SOS.AEval s a1 a2.
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