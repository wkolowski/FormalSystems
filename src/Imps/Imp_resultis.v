From Stdlib Require Import Recdef.

From FormalSystems Require Import Base.

Inductive AExp : Type :=
| AConst : nat -> AExp
| Var : Loc -> AExp
| Add : AExp -> AExp -> AExp
| Sub : AExp -> AExp -> AExp
| Mul : AExp -> AExp -> AExp
| ResultIs : Com -> AExp -> AExp

with BExp : Type :=
| BTrue : BExp
| BFalse : BExp
| Eq : AExp -> AExp -> BExp
| Le : AExp -> AExp -> BExp
| Not : BExp -> BExp
| And : BExp -> BExp -> BExp
| Or : BExp -> BExp -> BExp

with Com : Type :=
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
| EvalResultIs :
    forall (c : Com) (a : AExp) (s1 s2 : State) (n : nat),
      CEval c s1 s2 -> AEval a s2 n -> AEval (ResultIs c a) s1 n

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

with CEval : Com -> State -> State -> Prop :=
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

#[global] Hint Constructors AEval BEval CEval : core.

Ltac inv H :=
  inversion H; subst; clear H; auto.

Lemma AEval_det :
  forall {a : AExp} {s : State} {n m : nat},
    AEval a s n -> AEval a s m -> n = m

with BEval_det :
  forall {e : BExp} {s : State} {b1 : bool},
    BEval e s b1 -> forall {b2 : bool}, BEval e s b2 -> b1 = b2

with CEval_det :
  forall (c : Com) (s s1 : State),
    CEval c s s1 -> forall s2 : State, CEval c s s2 -> s1 = s2.
Proof.
  destruct 1; intros * HI *; inv HI.
    rewrite (AEval_det _ _ _ _ H H3), (AEval_det _ _ _ _ H0 H6). reflexivity.
    rewrite (AEval_det _ _ _ _ H H3), (AEval_det _ _ _ _ H0 H6). reflexivity.
    rewrite (AEval_det _ _ _ _ H H3), (AEval_det _ _ _ _ H0 H6). reflexivity.
    specialize (CEval_det _ _ _ H _ H3). subst.
      rewrite (AEval_det _ _ _ _ H0 H6). reflexivity.
  destruct 1; intros * HI *; inv HI.
    rewrite (AEval_det _ _ _ _ H H3), (AEval_det _ _ _ _ H0 H6). reflexivity.
    rewrite (AEval_det _ _ _ _ H H3), (AEval_det _ _ _ _ H0 H6). reflexivity.
    rewrite (BEval_det _ _ _ H _ H1). reflexivity.
    rewrite (BEval_det _ _ _ H _ H3), (BEval_det _ _ _ H0 _ H6). reflexivity.
    rewrite (BEval_det _ _ _ H _ H3), (BEval_det _ _ _ H0 _ H6). reflexivity.
  destruct 1; intros * HI *; inv HI.
    rewrite (AEval_det _ _ _ _ H H4). reflexivity.
    destruct (CEval_det _ _ _ H _ H3), (CEval_det _ _ _ H0 _ H6). reflexivity.
    rewrite (CEval_det _ _ _ H0 _ H7). reflexivity.
    specialize (BEval_det _ _ _ H _ H6). congruence.
    specialize (BEval_det _ _ _ H _ H6). congruence.
    rewrite (CEval_det _ _ _ H0 _ H7). reflexivity.
    specialize (BEval_det _ _ _ H _ H2). congruence.
    specialize (BEval_det _ _ _ H _ H6). congruence.
    destruct (CEval_det _ _ _ H0 _ H5), (CEval_det _ _ _ H1 _ H8). reflexivity.
Qed.

Set Warnings "-funind-cannot-define-graph".
Set Warnings "-funind-cannot-build-inversion".
Function aeval (n : nat) (a : AExp) (s : State) : option nat := 
match n with
| 0 => None
| S n' =>
  match a with
  | AConst n => Some n
  | Var v => Some (s v)
  | Add a1 a2 => liftM2 plus (aeval n' a1 s) (aeval n' a2 s)
  | Sub a1 a2 => liftM2 minus (aeval n' a1 s) (aeval n' a2 s)
  | Mul a1 a2 => liftM2 mult (aeval n' a1 s) (aeval n' a2 s)
  | ResultIs c a' =>
    match ceval n' c s with
    | None => None
    | Some s' => aeval n' a' s'
    end
  end
end

with beval (n : nat) (e : BExp) (s : State) : option bool :=
match n with
| 0 => None
| S n' =>
  match e with
  | BTrue => Some true
  | BFalse => Some false
  | Eq a1 a2 => liftM2 Nat.eqb (aeval n' a1 s) (aeval n' a2 s)
  | Le a1 a2 => liftM2 Nat.leb (aeval n' a1 s) (aeval n' a2 s)
  | Not e' => omap negb (beval n' e' s)
  | And e1 e2 => liftM2 andb (beval n' e1 s) (beval n' e2 s)
  | Or e1 e2 => liftM2 orb (beval n' e1 s) (beval n' e2 s)
  end
end

with ceval (n : nat) (c : Com) (s : State) : option State :=
match n with
| 0 => None
| S n' =>
  match c with
  | Skip => Some s
  | Asgn x a => omap (changeState s x) (aeval n' a s)
  | Seq c1 c2 => obind (ceval n' c1 s) (ceval n' c2)
  | If b c1 c2 =>
    match beval n' b s with
    | None => None
    | Some true => ceval n' c1 s
    | Some false => ceval n' c2 s
    end
  | While b c =>
    match beval n' b s with
    | None => None
    | Some true => obind (ceval n' c s) (ceval n' (While b c))
    | Some false => Some s
    end
  end
end.
Set Warnings "funind-cannot-define-graph".
Set Warnings "funind-cannot-build-inversion".

Fixpoint aeval_AEval (fuel : nat) :
  forall {a : AExp} {s : State} {n : nat},
    aeval fuel a s = Some n -> AEval a s n

with beval_BEval (fuel : nat) :
  forall {e : BExp} {s : State} {b : bool},
    beval fuel e s = Some b -> BEval e s b

with ceval_CEval (fuel : nat) :
  forall {c : Com} {s1 s2 : State},
    ceval fuel c s1 = Some s2 -> CEval c s1 s2.
Proof.
  destruct fuel as [| fuel']; cbn; intros.
    inv H.
    destruct a.
      1-2: inv H.
      destruct (aeval fuel' a1 s) eqn: H1,
               (aeval fuel' a2 s) eqn: H2; inv H; eauto.
      destruct (aeval fuel' a1 s) eqn: H1,
               (aeval fuel' a2 s) eqn: H2; inv H; eauto.
      destruct (aeval fuel' a1 s) eqn: H1,
               (aeval fuel' a2 s) eqn: H2; inv H; eauto.
      destruct (ceval fuel' c s) eqn: H1; inv H; eauto.
  destruct fuel as [| fuel']; cbn; intros.
    inv H.
    destruct e.
      1-2: inv H; auto.
      destruct (aeval fuel' a s) eqn: H1,
               (aeval fuel' a0 s) eqn: H2; inv H; eauto.
      destruct (aeval fuel' a s) eqn: H1,
               (aeval fuel' a0 s) eqn: H2; inv H; eauto.
      destruct (beval fuel' e s) eqn: H1; inv H; eauto.
      destruct (beval fuel' e1 s) eqn: H1,
               (beval fuel' e2 s) eqn: H2; inv H; eauto.
      destruct (beval fuel' e1 s) eqn: H1,
               (beval fuel' e2 s) eqn: H2; inv H; eauto.
  destruct fuel as [| fuel']; cbn; intros.
    inv H.
    destruct c.
      inv H.
      destruct (aeval fuel' a s1) eqn: H1; inv H; eauto.
      destruct (ceval fuel' c1 s1) eqn: H1; inv H; eauto.
      destruct (beval fuel' b s1) eqn: H1.
        destruct b0; eauto.
        inv H.
      destruct (beval fuel' b s1) eqn: H1; inv H.
        destruct b0; inv H2; eauto.
        destruct (ceval fuel' c s1) eqn: H; inv H0; eauto.
Qed.

(*
Lemma AEval_aeval :
  forall {fuel : nat} {a : AExp} {s : State} {n : nat},
    AEval a s n -> aeval fuel a s = n

with BEval_beval :
  forall {n : nat} {e : BExp} {s : State} {b : bool},
    BEval e s b -> beval n e s = b
*)
