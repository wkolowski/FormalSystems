Require Import List.
Import ListNotations.

Require Import Bool.

Parameter Loc : Type.
Parameter dec : Loc -> Loc -> bool.
Parameter dec_spec :
  forall x y : Loc, reflect (x = y) (dec x y).

Require Import Arith.

Notation "x =? y" := (dec x y) (at level 70).

Inductive AExp : Type :=
    | Const : nat -> AExp
    | Var : Loc -> AExp
    | Add : AExp -> AExp -> AExp
    | Sub : AExp -> AExp -> AExp
    | Mul : AExp -> AExp -> AExp.

Inductive BExp : Type :=
    | BTrue : BExp
    | BFalse : BExp
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

Inductive AEval : AExp -> State -> nat -> Prop :=
    | EvalConst :
        forall (n : nat) (s : State), AEval (Const n) s n
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
          AEval a1 s n1 -> AEval a2 s n2 -> AEval (Mul a1 a2) s (n1 * n2).

Hint Constructors AEval.

Ltac inv H :=
  inversion H; subst; clear H.

Lemma AEval_det :
  forall {a : AExp} {s : State} {n m : nat},
    AEval a s n -> AEval a s m -> n = m.
Proof.
  intros a s n m H. revert m.
  induction H; inversion 1; subst; clear H.
    1-2: reflexivity.
    rewrite (IHAEval1 _ H4), (IHAEval2 _ H7). reflexivity.
    rewrite (IHAEval1 _ H4), (IHAEval2 _ H7). reflexivity.
    rewrite (IHAEval1 _ H4), (IHAEval2 _ H7). reflexivity.
Defined.

Fixpoint aeval (a : AExp) (s : State) : nat :=
match a with
    | Const n => n
    | Var v => s v
    | Add a1 a2 => aeval a1 s + aeval a2 s
    | Sub a1 a2 => aeval a1 s - aeval a2 s
    | Mul a1 a2 => aeval a1 s * aeval a2 s
end.

Lemma AEval_aeval :
  forall {a : AExp} {s : State} {n : nat},
    AEval a s n -> aeval a s = n.
Proof.
  induction 1; cbn; rewrite ?IHAEval1, ?IHAEval2; reflexivity.
Qed.

Lemma aeval_AEval :
  forall {a : AExp} {s : State} {n : nat},
    aeval a s = n -> AEval a s n.
Proof.
  induction a; cbn; intros; rewrite <- H; auto.
Defined.

Inductive BEval : BExp -> State -> bool -> Prop :=
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
          BEval e1 s b1 -> BEval e2 s b2 -> BEval (Or e1 e2) s (orb b1 b2).

Hint Constructors BEval.

Lemma BEval_det :
  forall {e : BExp} {s : State} {b1 : bool},
    BEval e s b1 -> forall {b2 : bool}, BEval e s b2 -> b1 = b2.
Proof.
  induction 1; intros.
    inv H. reflexivity.
    inv H. reflexivity.
    inv H1. rewrite (AEval_det H H4), (AEval_det H0 H7). reflexivity.
    inv H1. rewrite (AEval_det H H4), (AEval_det H0 H7). reflexivity.
    inv H0. rewrite (IHBEval _ H2). reflexivity.
    inv H1. rewrite (IHBEval1 _ H4), (IHBEval2 _ H7). reflexivity.
    inv H1. rewrite (IHBEval1 _ H4), (IHBEval2 _ H7). reflexivity.
Qed.

Fixpoint beval (e : BExp) (s : State) : bool :=
match e with
    | BTrue => true
    | BFalse => false
    | Eq a1 a2 => Nat.eqb (aeval a1 s) (aeval a2 s)
    | Le a1 a2 => Nat.leb (aeval a1 s) (aeval a2 s)
    | Not e' => negb (beval e' s)
    | And e1 e2 => andb (beval e1 s) (beval e2 s)
    | Or e1 e2 => orb (beval e1 s) (beval e2 s)
end.

Lemma BEval_beval :
  forall {e : BExp} {s : State} {b : bool},
    BEval e s b -> beval e s = b.
Proof.
  induction 1; cbn.
    1-2: reflexivity.
    rewrite (AEval_aeval H), (AEval_aeval H0). reflexivity.
    rewrite (AEval_aeval H), (AEval_aeval H0). reflexivity.
    rewrite IHBEval. reflexivity.
    rewrite IHBEval1, IHBEval2. reflexivity.
    rewrite IHBEval1, IHBEval2. reflexivity.
Qed.

Lemma beval_BEval :
  forall {e : BExp} {s : State} {b : bool},
    beval e s = b -> BEval e s b.
Proof.
  induction e; cbn; intros; subst; auto.
    constructor; apply aeval_AEval; reflexivity.
    constructor; apply aeval_AEval; reflexivity.
Qed.

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

Lemma CEval_det :
  forall (c : Com) (s s1 : State),
    CEval c s s1 -> forall s2 : State, CEval c s s2 -> s1 = s2.
Proof.
  induction 1; intros.
    inv H. reflexivity.
    inv H0. rewrite (AEval_det H H5). reflexivity.
    inv H1. specialize (IHCEval1 _ H4). subst.
      specialize (IHCEval2 _ H7). subst. reflexivity.
    inv H1.
      rewrite (IHCEval _ H8). reflexivity.
      pose (BEval_det H H7). congruence.
    inv H1.
      pose (BEval_det H H7). congruence.
      rewrite (IHCEval _ H8). reflexivity.
    inv H0.
      reflexivity.
      pose (BEval_det H H3). congruence.
    inv H2.
      pose (BEval_det H H7). congruence.
      specialize (IHCEval1 _ H6). subst.
        specialize (IHCEval2 _ H9). subst. reflexivity.
Defined.

Lemma while_true_do_skip :
  forall s1 s2 : State,
    ~ CEval (While BTrue Skip) s1 s2.
Proof.
  intros s1 s2 H.
  remember (While BTrue Skip) as w. revert Heqw.
  induction H; intros; inv Heqw.
    inv H.
    apply IHCEval2. reflexivity.
Qed.

Definition equivalent (c1 c2 : Com) : Prop :=
  forall s1 s2 : State,
    CEval c1 s1 s2 <-> CEval c2 s1 s2.

Notation "c1 ~ c2" := (equivalent c1 c2) (at level 50).

Example equivalent_ex1 :
  forall (b : BExp) (c : Com),
    While b c ~ If b (Seq c (While b c)) Skip.
Proof.
  unfold equivalent. split; intros.
    remember (While b c) as w. revert b c Heqw.
      induction H; intros; inv Heqw; eauto.
    inv H; inv H6; eauto.
Defined.

(* Let's prove that ~ is a congruence. *)

Print Com.

Inductive Context : Type :=
    | CContext : Context
    | CSeqL : Context -> Com -> Context
    | CSeqR : Com -> Context -> Context
    | CIfL : BExp -> Context -> Com -> Context
    | CIfR : BExp -> Com -> Context -> Context
    | CWhile : BExp -> Context -> Context.

Fixpoint put (G : Context) (c : Com) : Com :=
match G with
    | CContext => c
    | CSeqL G' c' => Seq (put G' c) c'
    | CSeqR c' G' => Seq c' (put G' c)
    | CIfL b G' c' => If b (put G' c) c'
    | CIfR b c' G' => If b c' (put G' c)
    | CWhile b G' => While b (put G' c)
end.

Lemma equivalent_in_Context :
  forall c1 c2 : Com,
    c1 ~ c2 -> forall G : Context, put G c1 ~ put G c2.
Proof.
  unfold equivalent. intros c1 c2 H G. revert c1 c2 H.
  induction G; cbn; intros.
    rewrite H. reflexivity.
    split; intro; inv H0.
      econstructor; eauto. rewrite <- IHG; eauto.
      econstructor; eauto. rewrite IHG; eauto.
    split; intro; inv H0.
      econstructor; eauto. rewrite <- IHG; eauto.
      econstructor; eauto. rewrite IHG; eauto.
    split; intro; inv H0; eauto.
      apply EvalIfTrue; auto. rewrite <- IHG; eauto.
      apply EvalIfTrue; auto. rewrite IHG; eauto.
    split; intro; inv H0; eauto.
      constructor; auto. rewrite <- IHG; eauto.
      constructor; auto. rewrite IHG; eauto.
    split; intro.
Abort.