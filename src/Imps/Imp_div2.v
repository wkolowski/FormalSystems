From FormalSystems Require Export Base.

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
  fun y : Loc => if decide (x = y) then n else s y.

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

Lemma aeval_acompatible :
  forall {a : AExp} {s1 s2 : State},
    acompatible a s1 s2 -> aeval a s1 = aeval a s2.
Proof.
  unfold acompatible.
  induction a; cbn; intros; try f_equal; auto.
  now rewrite (IHa1 s1 s2), (IHa2 s1 s2); auto.
Qed.

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

#[global] Hint Resolve aeval_acompatible : core.
#[global] Hint Unfold acompatible : core.

Lemma beval_bcompatible :
  forall {e : BExp} {s1 s2 : State},
    bcompatible e s1 s2 -> beval e s1 = beval e s2.
Proof.
  unfold bcompatible.
  induction e; cbn; intros; try f_equal; auto 7.
Qed.

Inductive CEval : Com -> State -> option State -> Prop :=
| EvalSkip :
    forall s : State, CEval Skip s (Some s)
| EvalAsgnNone :
    forall (v : Loc) (a : AExp) (s : State),
      aeval a s = None -> CEval (Asgn v a) s None
| EvalAsgnSome :
    forall (v : Loc) (a : AExp) (s : State) (n : nat),
      aeval a s = Some n -> CEval (Asgn v a) s (Some (changeState s v n))
| EvalSeqNone :
    forall (c1 c2 : Com) (s1 : State),
      CEval c1 s1 None -> CEval (Seq c1 c2) s1 None
| EvalSeqSome :
    forall (c1 c2 : Com) (s1 s2 : State) (s3 : option State),
      CEval c1 s1 (Some s2) -> CEval c2 s2 s3 -> CEval (Seq c1 c2) s1 s3
| EvalIfNone :
    forall (b : BExp) (c1 c2 : Com) (s1 : State),
      beval b s1 = None -> CEval (If b c1 c2) s1 None
| EvalIfTrue :
    forall (b : BExp) (c1 c2 : Com) (s1 : State) (s2 : option State),
      beval b s1 = Some true -> CEval c1 s1 s2 ->
        CEval (If b c1 c2) s1 s2
| EvalIfFalse :
    forall (b : BExp) (c1 c2 : Com) (s1 : State) (s2 : option State),
      beval b s1 = Some false -> CEval c2 s1 s2 ->
        CEval (If b c1 c2) s1 s2
| EvalWhileNone :
    forall (b : BExp) (c : Com) (s : State),
      beval b s = None -> CEval (While b c) s None
| EvalWhileFalse :
    forall (b : BExp) (c : Com) (s : State),
      beval b s = Some false -> CEval (While b c) s (Some s)
| EvalWhileTrueNone :
    forall (b : BExp) (c : Com) (s1 : State),
      beval b s1 = Some true ->
      CEval c s1 None ->
        CEval (While b c) s1 None
| EvalWhileTrueSome :
    forall (b : BExp) (c : Com) (s1 s2 : State) (s3 : option State),
      beval b s1 = Some true ->
      CEval c s1 (Some s2) -> CEval (While b c) s2 s3 ->
        CEval (While b c) s1 s3.

#[global] Hint Constructors CEval : core.

Lemma CEval_det :
  forall (c : Com) (s : State) (s1 : option State),
    CEval c s s1 -> forall s2 : option State, CEval c s s2 -> s1 = s2.
Proof.
  now induction 1; intros;
    match goal with
    | H : CEval ?c _ _ |- _ => is_var c + inv H
    end;
    repeat match goal with
    | IH : forall _, CEval _ _ _ -> _, H : CEval _ _ _ |- _ =>
      let H' := fresh "H" in
        assert (H' := IH _ H); clear H; rename H' into H; subst
    | H : Some _ = Some _ |- _ => inv H
    end; eauto; try congruence.
Qed.

Inductive E : Type :=
| NoFuel : E
| Div0 : E.

Function ceval (n : nat) (c : Com) (s : State) : E + State :=
match n with
| 0 => inl NoFuel
| S n' =>
  match c with
  | Skip => inr s
  | Asgn x a =>
    match aeval a s with
    | None => inl Div0
    | Some n => inr (changeState s x n)
    end
  | Seq c1 c2 =>
    match ceval n' c1 s with
    | inr s' => ceval n' c2 s'
    | x => x
    end
  | If b c1 c2 =>
    match beval b s with
    | None => inl Div0
    | Some true => ceval n' c1 s
    | Some false => ceval n' c2 s
    end
  | While b c =>
    match beval b s with
    | None => inl Div0
    | Some false => inr s
    | Some true =>
      match ceval n' c s with
      | inr s' => ceval n' (While b c) s'
      | x => x
      end
    end
  end
end.

Lemma ceval_CEval_inr :
  forall (n : nat) (c : Com) (s1 s2 : State),
    ceval n c s1 = inr s2 -> CEval c s1 (Some s2).
Proof.
  intros n c s1.
  functional induction ceval n c s1; intros; inv H; eauto.
  - specialize (IHs _ H1).
    econstructor; eauto.
    now destruct (ceval n' c1 s) eqn: Heq.
  - now destruct (ceval n' c0 s).
Qed.

#[global] Hint Resolve ceval_CEval_inr : core.

Lemma ceval_CEval_Div0 :
  forall (n : nat) (c : Com) (s1 : State),
    ceval n c s1 = inl Div0 -> CEval c s1 None.
Proof.
  intros n c s1.
  functional induction ceval n c s1; intros; inv H; eauto.
Qed.

Lemma while_true_do_skip :
  forall (s1 : State) (s2 : option State),
    ~ CEval (While BTrue Skip) s1 s2.
Proof.
  intros s1 s2 H.
  remember (While BTrue Skip) as w; revert Heqw.
  now induction H; intros; inv Heqw.
Qed.
