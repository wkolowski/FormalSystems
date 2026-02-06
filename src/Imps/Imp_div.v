From Stdlib Require Import Recdef.

From FormalSystems Require Import Base.

Inductive AExp : Type :=
| AConst : nat -> AExp
| Var : Loc -> AExp
| Add : AExp -> AExp -> AExp
| Sub : AExp -> AExp -> AExp
| Mul : AExp -> AExp -> AExp
| Div : AExp -> AExp -> AExp.

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
| EvalDiv :
    forall (a1 a2 : AExp) (s : State) (n1 n2 : nat),
      AEval a1 s n1 -> AEval a2 s n2 -> n2 <> 0 ->
        AEval (Div a1 a2) s (n1 / n2).

#[global] Hint Constructors AEval : core.

Fixpoint aeval (a : AExp) (s : State) : option nat :=
match a with
| AConst n => Some n
| Var v => Some (s v)
| Add a1 a2 => liftM2 plus (aeval a1 s) (aeval a2 s)
| Sub a1 a2 => liftM2 minus (aeval a1 s) (aeval a2 s)
| Mul a1 a2 => liftM2 mult (aeval a1 s) (aeval a2 s)
| Div a1 a2 =>
  match aeval a1 s, aeval a2 s with
  | _, Some 0 => None
  | Some n, Some m => Some (n / m)
  | _, _ => None
  end
end.

Lemma AEval_aeval :
  forall {a : AExp} {s : State} {n : nat},
    AEval a s n -> aeval a s = Some n.
Proof.
  induction 1; cbn; rewrite ?IHAEval1, ?IHAEval2; [easy.. |].
  now destruct n2.
Qed.

Lemma aeval_AEval :
  forall {a : AExp} {s : State} {n : nat},
    aeval a s = Some n -> AEval a s n.
Proof.
  induction a; cbn; inversion 1; subst;
    [now constructor | now constructor |
      destruct (aeval a1 s) eqn: Ha1, (aeval a2 s) eqn: Ha2; inv H1..].
  - destruct n1; [easy |].
    assert (n0 / S n1 = n) by (inv H; auto).
    now rewrite <- H0; auto.
  - now destruct n0.
Qed.

Lemma AEval_det :
  forall {a : AExp} {s : State} {n m : nat},
    AEval a s n -> AEval a s m -> n = m.
Proof.
  intros.
  apply AEval_aeval in H, H0.
  now congruence.
Qed.

Fixpoint loca (a : AExp) : list Loc :=
match a with
| AConst _ => []
| Var x => [x]
| Add a1 a2 => loca a1 ++ loca a2
| Sub a1 a2 => loca a1 ++ loca a2
| Mul a1 a2 => loca a1 ++ loca a2
| Div a1 a2 => loca a1 ++ loca a2
end.

Definition acompatible (a : AExp) (s1 s2 : State) : Prop :=
  forall x : Loc, In x (loca a) -> s1 x = s2 x.

#[global] Hint Resolve in_or_app : core.

Lemma AEval_acompatible :
  forall {a : AExp} {s1 : State} {n : nat},
    AEval a s1 n -> forall {s2 : State},
      acompatible a s1 s2 ->
        AEval a s2 n.
Proof.
  unfold acompatible.
  induction 1; cbn in *; intros; try rewrite H; auto 6.
Qed.

Lemma AEval_acompatible_det :
  forall {a : AExp} {s1 : State} {n1 : nat},
    AEval a s1 n1 ->
    forall {s2 : State} {n2 : nat},
      AEval a s2 n2 ->
      (forall x : Loc, In x (loca a) -> s1 x = s2 x) ->
        n1 = n2.
Proof.
  now induction 1; cbn; intros;
    match goal with
    | H : AEval ?a _ _ |- _ => is_var a + inv H
    end; eauto 10.
Qed.

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

#[global] Hint Constructors BEval : core.

Fixpoint beval (e : BExp) (s : State) : option bool :=
match e with
| BTrue => Some true
| BFalse => Some false
| Eq a1 a2 => liftM2 Nat.eqb (aeval a1 s) (aeval a2 s)
| Le a1 a2 => liftM2 Nat.leb (aeval a1 s) (aeval a2 s)
| Not e' => omap negb (beval e' s)
| And e1 e2 => liftM2 andb (beval e1 s) (beval e2 s)
| Or e1 e2 => liftM2 orb (beval e1 s) (beval e2 s)
end.

Lemma BEval_beval :
  forall {e : BExp} {s : State} {b : bool},
    BEval e s b -> beval e s = Some b.
Proof.
  induction 1; cbn.
  - easy.
  - easy.
  - now rewrite (AEval_aeval H), (AEval_aeval H0).
  - now rewrite (AEval_aeval H), (AEval_aeval H0).
  - now rewrite IHBEval.
  - now rewrite IHBEval1, IHBEval2.
  - now rewrite IHBEval1, IHBEval2.
Qed.

#[global] Hint Resolve aeval_AEval : core.

Lemma beval_BEval :
  forall {e : BExp} {s : State} {b : bool},
    beval e s = Some b -> BEval e s b.
Proof.
  induction e; cbn; intros; inv H; auto.
  - destruct (aeval a s) eqn: Ha1, (aeval a0 s) eqn: Ha2; inv H1; auto.
  - destruct (aeval a s) eqn: Ha1, (aeval a0 s) eqn: Ha2; inv H1; auto.
  - destruct (beval e s) eqn: He; inv H1; auto.
  - destruct (beval e1 s) eqn: He1, (beval e2 s) eqn: He2; inv H1; auto.
  - destruct (beval e1 s) eqn: He1, (beval e2 s) eqn: He2; inv H1; auto.
Qed.

Lemma BEval_det :
  forall {e : BExp} {s : State} {b1 : bool},
    BEval e s b1 -> forall {b2 : bool}, BEval e s b2 -> b1 = b2.
Proof.
  intros.
  apply BEval_beval in H, H0.
  now congruence.
Qed.

Fixpoint locb (b : BExp) : list Loc :=
match b with
| BTrue => []
| BFalse => []
| Eq a1 a2 => loca a1 ++ loca a2
| Le a1 a2 => loca a1 ++ loca a2
| Not b' => locb b'
| And b1 b2 => locb b1 ++ locb b2
| Or b1 b2 => locb b1 ++ locb b2
end.

Definition bcompatible (b : BExp) (s1 s2 : State) : Prop :=
  forall x : Loc, In x (locb b) -> s1 x = s2 x.

#[global] Hint Resolve AEval_acompatible : core.
#[global] Hint Unfold acompatible : core.

Lemma BEval_bcompatible :
  forall {e : BExp} {s1 : State} {b : bool},
    BEval e s1 b -> forall {s2 : State},
      bcompatible e s1 s2 -> BEval e s2 b.
Proof.
  unfold bcompatible.
  induction 1; cbn in *; intros; constructor; eauto 6.
Qed.

Lemma BEval_bcompatible_det :
  forall {e : BExp} {s1 : State} {b1 : bool},
    BEval e s1 b1 -> forall {s2 : State} {b2 : bool},
    BEval e s2 b2 ->
      bcompatible e s1 s2 -> b1 = b2.
Proof.
  intros.
  assert (BEval e s2 b1) by (eapply BEval_bcompatible; eauto).
  now eapply BEval_det; eauto.
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

#[global] Hint Constructors CEval : core.

#[global] Hint Rewrite @AEval_det : core.
#[global] Hint Resolve AEval_det BEval_det : core.

Lemma CEval_det :
  forall (c : Com) (s s1 : State),
    CEval c s s1 -> forall s2 : State, CEval c s s2 -> s1 = s2.
Proof.
  induction 1; intros;
    match goal with
    | H : CEval ?c _ _ |- _ => is_var c + inv H
    end;
    repeat match goal with
    | IH : forall _, CEval _ _ _ -> _, H : CEval _ _ _ |- _ =>
        let H' := fresh "H" in
          assert (H' := IH _ H); clear H; rename H' into H; subst
    | H : BEval ?b ?s _, H' : BEval ?b ?s _ |- _ =>
        let H'' := fresh "H" in
          assert (H'' := BEval_det H H'); clear H H'
    end; eauto; try congruence.
Qed.

Function ceval (n : nat) (c : Com) (s : State) : option State :=
match n with
| 0 => None
| S n' =>
  match c with
  | Skip => Some s
  | Asgn x a => omap (changeState s x) (aeval a s)
  | Seq c1 c2 =>
    match ceval n' c1 s with
    | None => None
    | Some s' => ceval n' c2 s'
    end
  | If b c1 c2 =>
    match beval b s with
    | None => None
    | Some true => ceval n' c1 s
    | Some false => ceval n' c2 s
    end
  | While b c =>
    match beval b s with
    | None => None
    | Some false => Some s
    | Some true =>
      match ceval n' c s with
      | None => None
      | Some s' => ceval n' (While b c) s'
      end
    end
  end
end.

#[global] Hint Immediate aeval_AEval beval_BEval : core.

Lemma ceval_CEval :
  forall (n : nat) (c : Com) (s1 s2 : State),
    ceval n c s1 = Some s2 -> CEval c s1 s2.
Proof.
  intros n c s1.
  functional induction ceval n c s1; intros; inv H; eauto.
  destruct (aeval a s) eqn: Ha; inv H1; auto.
Qed.

Lemma while_true_do_skip :
  forall s1 s2 : State,
    ~ CEval (While BTrue Skip) s1 s2.
Proof.
  intros s1 s2 H.
  remember (While BTrue Skip) as w. revert Heqw.
  induction H; intros; inv Heqw. inv H.
Qed.

Lemma div_0 :
  forall (a1 a2 : AExp) (s : State),
    AEval a2 s 0 -> forall m : nat, ~ AEval (Div a1 a2) s m.
Proof.
  inversion 2; subst.
  cut (n2 = 0); [easy |].
  now eapply AEval_det; eauto.
Qed.
