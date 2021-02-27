Require Import FormalSystems.Base.

Inductive AExp : Type :=
    | AConst : nat -> AExp
    | Var : Loc -> AExp
    | Add : AExp -> AExp -> AExp
    | Sub : AExp -> AExp -> AExp
    | Mul : AExp -> AExp -> AExp
    | ACond : BExp -> AExp -> AExp -> AExp

with BExp : Type :=
    | BTrue : BExp
    | BFalse : BExp
    | Eq : AExp -> AExp -> BExp
    | Le : AExp -> AExp -> BExp
    | Not : BExp -> BExp
    | And : BExp -> BExp -> BExp
    | Or : BExp -> BExp -> BExp
    | BCond : BExp -> BExp -> BExp -> BExp.

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

Inductive AEval : AExp -> State -> nat -> Prop :=
    | EvalAConst :
        forall (n : nat) (s : State), AEval (AConst n) s n
    | EvalVar :
        forall (v : Loc) (s : State), AEval (Var v) s (s v)
    | EvalAdd :
        forall (a1 a2 : AExp) (s : State) (n1 n2 : nat),
          AEval a1 s n1 -> AEval a2 s n2 -> AEval (Add a1 a2) s (n1 + n2)
    | EvalSub :
        forall (a1 a2 : AExp) (s : State) (n1 n2 : nat),
          AEval a1 s n1 -> AEval a2 s n2 -> AEval (Sub a1 a2) s (n1 - n2)
    | EvalMul :
        forall (a1 a2 : AExp) (s : State) (n1 n2 : nat),
          AEval a1 s n1 -> AEval a2 s n2 -> AEval (Mul a1 a2) s (n1 * n2)
    | EvalACondTrue :
        forall (b : BExp) (s : State) (a1 a2 : AExp) (n : nat),
          BEval b s true -> AEval a1 s n -> AEval (ACond b a1 a2)s  n
    | EvalACondFalse :
        forall (b : BExp) (s : State) (a1 a2 : AExp) (n : nat),
          BEval b s false -> AEval a2 s n -> AEval (ACond b a1 a2) s n

with BEval : BExp -> State -> bool -> Prop :=
    | EvalTrue :
        forall s : State, BEval BTrue s true
    | EvalFalse :
        forall s : State, BEval BFalse s false
    | EvalEq :
        forall (a1 a2 : AExp) (s : State) (n m : nat),
          AEval a1 s n -> AEval a2 s m -> BEval (Eq a1 a2) s (Nat.eqb n m)
    | EvalLe :
        forall (a1 a2 : AExp) (s : State) (n m : nat),
          AEval a1 s n -> AEval a2 s m -> BEval (Le a1 a2) s (Nat.leb n m)
    | EvalNot :
        forall (e : BExp) (s : State) (b : bool),
          BEval e s b -> BEval (Not e) s (negb b)
    | EvalAnd :
        forall (e1 e2 : BExp) (s : State) (b1 b2 : bool),
          BEval e1 s b1 -> BEval e2 s b2 -> BEval (And e1 e2) s (andb b1 b2)
    | EvalOr :
        forall (e1 e2 : BExp) (s : State) (b1 b2 : bool),
          BEval e1 s b1 -> BEval e2 s b2 -> BEval (Or e1 e2) s (orb b1 b2)
    | EvalBCondTrue :
        forall (e e1 e2 : BExp) (s : State) (b : bool),
          BEval e s true -> BEval e1 s b -> BEval (BCond e e1 e2) s b
    | EvalBCondFalse :
        forall (e e1 e2 : BExp) (s : State) (b : bool),
          BEval e s false -> BEval e2 s b -> BEval (BCond e e1 e2) s b.

Hint Constructors AEval BEval.

Inductive CEval : Com -> State -> State -> Prop :=
    | EvalSkip :
        forall s : State, CEval Skip s s
    | EvalAsgn :
        forall (v : Loc) (a : AExp) (s : State) (n : nat),
          AEval a s n -> CEval (Asgn v a) s (changeState s v n)
    | EvalSeq :
        forall (c1 c2 : Com) (s1 s2 s3 : State),
          CEval c1 s1 s2 -> CEval c2 s2 s3 -> CEval (Seq c1 c2) s1 s3
    | EvalIfFalse :
        forall (b : BExp) (c1 c2 : Com) (s1 s2 : State),
          BEval b s1 false -> CEval c2 s1 s2 -> CEval (If b c1 c2) s1 s2
    | EvalIfTrue :
        forall (b : BExp) (c1 c2 : Com) (s1 s2 : State),
          BEval b s1 true -> CEval c1 s1 s2 -> CEval (If b c1 c2) s1 s2
    | EvalWhileFalse :
        forall (b : BExp) (c : Com) (s : State),
          BEval b s false -> CEval (While b c) s s
    | EvalWhileTrue :
        forall (b : BExp) (c : Com) (s1 s2 s3 : State),
          BEval b s1 true ->
          CEval c s1 s2 -> CEval (While b c) s2 s3 ->
            CEval (While b c) s1 s3.

Hint Constructors CEval.

Require Import Recdef.

Function desugara (a : AExp) : AExp :=
match a with
    | AConst n => AConst n
    | Var v => Var v
    | Add a1 a2 =>
        match desugara a1, desugara a2 with
            | ACond b1 a11 a12, ACond b2 a21 a22 =>
                ACond b1 (ACond b2 (Add a11 a21) (Add a11 a22))
                         (ACond b2 (Add a12 a21) (Add a12 a22))
            | ACond b1 a11 a12, a2 =>
                ACond b1 (Add a11 a2) (Add a12 a2)
            | a1, ACond b2 a21 a22 =>
                ACond b2 (Add a1 a21) (Add a1 a22)
            | a1, a2 => Add a1 a2
        end
    | Sub a1 a2 => Sub a1 a2
    | Mul a1 a2 => Mul a1 a2
    | ACond b1 a1 a2 => ACond (desugarb b1) (desugara a1) (desugara a2)
end

with desugarb (b : BExp) : BExp :=
match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | Eq a1 a2 =>
        match desugara a1, desugara a2 with
            | ACond b1 a11 a12, ACond b2 a21 a22 =>
                BCond b1 (BCond b2 (Eq a11 a21) (Eq a11 a22))
                         (BCond b2 (Eq a12 a21) (Eq a12 a22))
            | ACond b1 a11 a12, a2 =>
                BCond b1 (Eq a11 a2) (Eq a12 a2)
            | a1, ACond b2 a21 a22 =>
                BCond b2 (Eq a1 a21) (Eq a1 a22)
            | a1, a2 => Eq a1 a2
        end
    | Le a1 a2 => Le a1 a2
    | Not b' => Not (desugarb b')
    | And b1 b2 => And (desugarb b1) (desugarb b2)
    | Or b1 b2 => Or (desugarb b1) (desugarb b2)
    | BCond b1 b2 b3 => Or (And b1 b2) (And (Not b1) b3)
end.

Lemma AEval_desugara :
  forall (a : AExp) (s : State) (n : nat),
    AEval a s n -> AEval (desugara a) s n

with BEval_desugarb :
  forall (e : BExp) (s : State) (b : bool),
    BEval e s b -> BEval (desugarb e) s b.
Proof.
  intro a. functional induction desugara a; cbn; intros.
    1-2: assumption.
    inv H. specialize (IHa0 _ _ H2). rewrite e0 in IHa0. admit.
    inv H.
    Ltac wut :=
    repeat match goal with
        | IH : forall _ _ , AEval _ _ _ -> _, H : AEval _ _ _ |- _ =>
            specialize (IH _ _ H)
        | H : match ?x with _ => _ end |- _ => destruct x
        | H : AEval (desugara _) _ _, H' : desugara _ = _ |- _ =>
            rewrite H' in H; inv H; auto
    end.
    wut.
    inv H. wut.
    inv H. auto.
    1-2: assumption.
    inv H; auto.
  intro e. functional induction desugarb e; cbn; intros; auto.
    inv H.
    apply AEval_desugara in H2. rewrite e0 in H2.
      apply AEval_desugara in H5. rewrite e1 in H5.
      inv H2; inv H5; auto.
    admit.
    admit.
    inv H. auto.
    inv H. auto.
    inv H. auto.
    inv H. auto.
    inv H. destruct b; auto.

    repeat match goal with
        | H : forall _ _ _ , AEval _ _ _ -> _,
          H' : AEval ?a _ _ |- _ => idtac H; idtac H';
            is_var a; let H'' := fresh "H" in pose (H'' := H _ _ _ H');
            clearbody H''; clear H'
        | H : AEval ?a _ _, H' : ?a = _ |- _ =>
            rewrite H' in H; clear H'; inv H; auto
    end.
Abort.