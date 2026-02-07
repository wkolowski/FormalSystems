From FormalSystems Require Export Imp.Syntax.
From FormalSystems Require Import Imp.Denotational.

Inductive AEval : AExp -> State -> nat -> Prop :=
| EvalAConst :
    forall (n : nat) (s : State), AEval (AConst n) s n
| EvalVar :
    forall (v : Atom) (s : State), AEval (Var v) s (s v)
| EvalABinOp :
    forall (f : nat -> nat -> nat) (a1 a2 : AExp) (s : State) (n1 n2 : nat),
      AEval a1 s n1 -> AEval a2 s n2 ->
        AEval (ABinOp f a1 a2) s (f n1 n2).

#[global] Hint Constructors AEval : core.

Lemma AEval_det :
  forall {a : AExp} {s : State} {n m : nat},
    AEval a s n -> AEval a s m -> n = m.
Proof.
  intros a s n m H; revert m.
  induction H; inversion 1; subst; clear H; [easy.. |].
  now rewrite (IHAEval1 _ H7), (IHAEval2 _ H8).
Qed.

#[global] Hint Resolve in_or_app : core.

Lemma AEval_acompatible :
  forall {a : AExp} {s1 : State} {n : nat},
    AEval a s1 n -> forall {s2 : State},
      acompatible a s1 s2 ->
        AEval a s2 n.
Proof.
  unfold acompatible.
  now induction 1; cbn in *; intros s2 Heq; rewrite ?Heq; auto 6.
Qed.

Lemma AEval_acompatible_det :
  forall {a : AExp} {s1 : State} {n1 : nat},
    AEval a s1 n1 ->
    forall {s2 : State} {n2 : nat},
      AEval a s2 n2 ->
      (forall x : Atom, In x (fva a) -> s1 x = s2 x) ->
        n1 = n2.
Proof.
  induction 1; cbn; intros.
  - now inversion H; subst.
  - now inversion H; subst; auto.
  - inversion H1; subst.
    now erewrite IHAEval1, IHAEval2; eauto.
Qed.

Inductive BEval : BExp -> State -> bool -> Prop :=
| EvalBConst :
    forall (s : State) (b : bool), BEval (BConst b) s b
| BEval_BRelOp :
    forall (f : nat -> nat -> bool) (a1 a2 : AExp) (s : State) (n1 n2 : nat),
      AEval a1 s n1 -> AEval a2 s n2 ->
        BEval (BRelOp f a1 a2) s (f n1 n2)
| EvalNot :
    forall (e : BExp) (s : State) (b : bool),
      BEval e s b -> BEval (Not e) s (negb b)
| BEval_BBinOp :
    forall (f : bool -> bool -> bool) (e1 e2 : BExp) (s : State) (b1 b2 : bool),
      BEval e1 s b1 -> BEval e2 s b2 ->
        BEval (BBinOp f e1 e2) s (f b1 b2).

#[global] Hint Constructors BEval : core.

Lemma BEval_det :
  forall {e : BExp} {s : State} {b1 : bool},
    BEval e s b1 -> forall {b2 : bool}, BEval e s b2 -> b1 = b2.
Proof.
  induction 1; intros.
  - now inversion H; subst.
  - inversion H1; subst.
    now rewrite (AEval_det H H7), (AEval_det H0 H8).
  - inversion H0; subst.
    now rewrite (IHBEval _ H2).
  - inversion H1; subst.
    now rewrite (IHBEval1 _ H7), (IHBEval2 _ H8).
Qed.

#[global] Hint Resolve AEval_acompatible : core.
#[global] Hint Unfold acompatible : core.

Lemma BEval_bcompatible :
  forall {e : BExp} {s1 : State} {b : bool},
    BEval e s1 b -> forall {s2 : State},
      bcompatible e s1 s2 -> BEval e s2 b.
Proof.
  unfold bcompatible.
  now induction 1; cbn; intros s2 Heq; constructor; eauto 6.
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
    forall (v : Atom) (a : AExp) (s : State) (n : nat),
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

Example while_true_do_skip :
  forall s1 s2 : State,
    ~ CEval (While (BConst true) Skip) s1 s2.
Proof.
  intros s1 s2 H.
  remember (While (BConst true) Skip) as w; revert Heqw.
  now induction H; intros; inversion Heqw; subst; auto.
Qed.

#[global] Hint Rewrite @AEval_det : core.
#[global] Hint Resolve AEval_det BEval_det : core.

Lemma CEval_det :
  forall (c : Com) (s s1 : State),
    CEval c s s1 -> forall s2 : State, CEval c s s2 -> s1 = s2.
Proof.
  now induction 1; intros;
    match goal with
    | H : CEval ?c _ _ |- _ => is_var c + (inversion H; subst; clear H)
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

(** * Equivalence of big step and denotational semantics *)

Lemma AEval_aeval :
  forall {a : AExp} {s : State} {n : nat},
    AEval a s n -> aeval s a = n.
Proof.
  now induction 1; cbn; rewrite ?IHAEval1, ?IHAEval2.
Qed.

Lemma aeval_AEval :
  forall {a : AExp} {s : State} {n : nat},
    aeval s a = n -> AEval a s n.
Proof.
  now induction a; cbn; intros; rewrite <- H; auto.
Qed.

Lemma BEval_beval :
  forall {e : BExp} {s : State} {b : bool},
    BEval e s b -> beval s e = b.
Proof.
  induction 1; cbn.
  - easy.
  - now rewrite (AEval_aeval H), (AEval_aeval H0).
  - now rewrite IHBEval.
  - now rewrite IHBEval1, IHBEval2.
Qed.

Lemma beval_BEval :
  forall {e : BExp} {s : State} {b : bool},
    beval s e = b -> BEval e s b.
Proof.
  induction e; cbn; intros; subst; only 1, 3-4: now auto.
  now constructor; apply aeval_AEval.
Qed.

#[global] Hint Immediate aeval_AEval beval_BEval : core.

Lemma ceval_CEval :
  forall (n : nat) (c : Com) (s1 s2 : State),
    ceval n c s1 = Some s2 -> CEval c s1 s2.
Proof.
  now intros n c s1; functional induction (ceval n c s1); inversion 1; subst; eauto.
Qed.

Lemma CEval_ceval :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 -> exists n : nat, ceval n c s1 = Some s2.
Proof.
  induction 1.
  - now exists 1; cbn.
  - exists 1; cbn.
    do 2 f_equal.
    now apply AEval_aeval.
  - destruct IHCEval1 as [n1 IH1], IHCEval2 as [n2 IH2].
    exists (S (n1 + n2)); cbn.
    rewrite (ceval_plus n1 n2 _ _ _ IH1), Nat.add_comm.
    now apply ceval_plus.
  - destruct IHCEval as [n IH].
    exists (S n); cbn.
    now apply BEval_beval in H as ->.
  - destruct IHCEval as [n IH].
    exists (S n); cbn.
    now apply BEval_beval in H as ->.
  - exists 1; cbn.
    now apply BEval_beval in H as ->.
  - destruct IHCEval1 as [n1 IH1], IHCEval2 as [n2 IH2].
    exists (S (n1 + n2)); cbn.
    apply BEval_beval in H as ->.
    rewrite (ceval_plus _ _ _ _ _ IH1), Nat.add_comm.
    now apply ceval_plus.
Qed.
