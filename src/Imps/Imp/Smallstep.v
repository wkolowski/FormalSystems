From FormalSystems Require Export Imp.Syntax.
From FormalSystems Require Import Imp.Denotational.

Inductive AEval (s : State) : AExp -> AExp -> Prop :=
| AEval_Var :
    forall x : Atom, AEval s (Var x) (AConst (s x))
| AEval_ABinOp_L :
    forall (f : nat -> nat -> nat) (a1 a1' a2 : AExp),
      AEval s a1 a1' -> AEval s (ABinOp f a1 a2) (ABinOp f a1' a2)
| AEval_ABinOp_R :
    forall (f : nat -> nat -> nat) (n : nat) (a2 a2' : AExp),
      AEval s a2 a2' ->
        AEval s (ABinOp f (AConst n) a2) (ABinOp f (AConst n) a2')
| AEval_ABinOp :
    forall (f : nat -> nat -> nat) (n1 n2 : nat),
      AEval s (ABinOp f (AConst n1) (AConst n2)) (AConst (f n1 n2)).

#[global] Hint Constructors AEval : core.

Lemma AEval_det :
  forall {s : State} {a a1 a2 : AExp},
    AEval s a a1 -> AEval s a a2 -> a1 = a2.
Proof.
  intros s a a1 a2 H; revert a2.
  now induction H; intros; repeat
    match goal with
    | H : AEval _ (?f _) _ |- _ => inversion H; subst; clear H
    | |- ?f _ _ = ?f _ _ => f_equal
    end; auto.
Qed.

Ltac adet := repeat
match goal with
| H1 : AEval ?s ?a ?a1, H2 : AEval ?s ?a ?a2 |- _ =>
  assert (a1 = a2) by (eapply AEval_det; eauto); subst; clear H2
end.

Inductive AEvals (s : State) : AExp -> AExp -> Prop :=
| AEvals_step :
    forall a1 a2 : AExp,
      AEval s a1 a2 -> AEvals s a1 a2
| AEvals_refl :
    forall a : AExp, AEvals s a a
| AEvals_trans :
    forall a1 a2 a3 : AExp,
      AEvals s a1 a2 -> AEvals s a2 a3 -> AEvals s a1 a3.

#[global] Hint Constructors AEvals : core.

Lemma AEval_AEvals :
  forall (s : State) (a1 a1' a2 : AExp),
    AEval s a1 a1' -> AEvals s a1' a2 -> AEvals s a1 a2.
Proof.
  now induction 1; intros; eauto.
Qed.

Lemma AEvalsVar :
  forall (s : State) (x : Atom), AEvals s (Var x) (AConst (s x)).
Proof.
  now eauto.
Qed.

Lemma AEvals_ABinOp_L :
  forall (s : State) (f : nat -> nat -> nat) (a1 a1' a2 : AExp),
    AEvals s a1 a1' -> AEvals s (ABinOp f a1 a2) (ABinOp f a1' a2).
Proof.
  now induction 1; eauto.
Qed.

Lemma AEvals_ABinOp_R :
  forall (s : State) (f : nat -> nat -> nat) (n : nat) (a2 a2' : AExp),
    AEvals s a2 a2' ->
      AEvals s (ABinOp f (AConst n) a2) (ABinOp f (AConst n) a2').
Proof.
  now induction 1; eauto.
Qed.

Lemma AEvals_ABinOp :
  forall (s : State) (f : nat -> nat -> nat) (n1 n2 : nat),
    AEvals s (ABinOp f (AConst n1) (AConst n2)) (AConst (f n1 n2)).
Proof.
  now eauto.
Qed.

#[global] Hint Resolve in_or_app : core.

Lemma AEval_acompatible_det :
  forall {s1 : State} {a a1 : AExp},
    AEval s1 a a1 -> forall {s2 : State},
      acompatible a s1 s2 -> forall {a2 : AExp},
        AEval s2 a a2 -> a1 = a2.
Proof.
  unfold acompatible.
  now induction 1; cbn in *; intros; repeat
    match goal with
    | H : AEval _ (?f _) _ |- _ => inversion H; subst; clear H
    | |- ?f _ _ = ?f _ _ => f_equal
    end; eauto.
Qed.

Inductive BEval (s : State) : BExp -> BExp -> Prop :=
| BEval_BRelOp_L :
    forall (f : nat -> nat -> bool) (a1 a1' a2 : AExp),
      AEval s a1 a1' -> BEval s (BRelOp f a1 a2) (BRelOp f a1' a2)
| BEval_BRelOp_R :
    forall (f : nat -> nat -> bool) (n : nat) (a2 a2' : AExp),
      AEval s a2 a2' ->
        BEval s (BRelOp f (AConst n) a2) (BRelOp f (AConst n) a2')
| BEval_BRelOp :
    forall (f : nat -> nat -> bool) (n1 n2 : nat),
      BEval s (BRelOp f (AConst n1) (AConst n2)) (BConst (f n1 n2))
| BEval_Not_Step :
    forall e e' : BExp,
      BEval s e e' -> BEval s (Not e) (Not e')
| BEval_Not :
    forall b : bool, BEval s (Not (BConst b)) (BConst (negb b))
| BEval_BBinOp_L :
    forall (f : bool -> bool -> bool) (e1 e1' e2 : BExp),
      BEval s e1 e1' -> BEval s (BBinOp f e1 e2) (BBinOp f e1' e2)
| BEval_BBinOp_R :
    forall (f : bool -> bool -> bool) (b : bool) (e2 e2' : BExp),
      BEval s e2 e2' ->
        BEval s (BBinOp f (BConst b) e2) (BBinOp f (BConst b) e2')
| BEval_BBinOp :
    forall (f : bool -> bool -> bool) (b1 b2 : bool),
      BEval s (BBinOp f (BConst b1) (BConst b2)) (BConst (f b1 b2)).

#[global] Hint Constructors BEval : core.

#[global] Hint Resolve AEval_det : core.

Lemma BEval_det :
  forall {s : State} {e e1 : BExp},
    BEval s e e1 -> forall {e2 : BExp}, BEval s e e2 -> e1 = e2.
Proof.
  now induction 1; intros; repeat
    match goal with
    | H : AEval _ (?f _) _ |- _ => inversion H; subst; clear H
    | H : BEval _ (?f _) _ |- _ => inversion H; subst; clear H
    | |- ?f _ = ?f _ => f_equal
    | |- ?f _ _ = ?f _ _ => f_equal
    end; eauto.
Qed.

Ltac bdet := repeat
match goal with
| H1 : BEval ?s ?e ?e1, H2 : BEval ?s ?e ?e2 |- _ =>
  assert (e1 = e2) by (eapply BEval_det; eauto); subst; clear H2
end.

Definition BEvals (s : State) (e1 e2 : BExp) : Prop :=
  rtc (BEval s) e1 e2.

#[global] Hint Unfold BEvals : core.

Lemma BEvals_BRelOp_L :
  forall (s : State) (f : nat -> nat -> bool) (a1 a1' a2 : AExp),
    AEvals s a1 a1' -> BEvals s (BRelOp f a1 a2) (BRelOp f a1' a2).
Proof.
  now induction 1; eauto.
Qed.

Lemma BEvals_BRelOp_R :
  forall (s : State) (f : nat -> nat -> bool) (n : nat) (a2 a2' : AExp),
    AEvals s a2 a2' ->
      BEvals s (BRelOp f (AConst n) a2) (BRelOp f (AConst n) a2').
Proof.
  now induction 1; intros; eauto.
Qed.

Lemma BEvals_BRelOp :
  forall (s : State) (f : nat -> nat -> bool) (n1 n2 : nat),
    BEvals s (BRelOp f (AConst n1) (AConst n2)) (BConst (f n1 n2)).
Proof.
  now eauto.
Qed.

Lemma BEvals_Not_Step :
  forall (s : State) (e e' : BExp),
    BEvals s e e' -> BEvals s (Not e) (Not e').
Proof.
  now induction 1; eauto.
Qed.

Lemma BEvals_Not :
  forall (s : State) (b : bool),
    BEvals s (Not (BConst b)) (BConst (negb b)).
Proof.
  now eauto.
Qed.

Lemma BEvals_BBinOp_L :
  forall (s : State) (f : bool -> bool -> bool) (e1 e1' e2 : BExp),
    BEvals s e1 e1' -> BEvals s (BBinOp f e1 e2) (BBinOp f e1' e2).
Proof.
  now induction 1; eauto.
Qed.

Lemma BEvals_BBinOp_R :
  forall (s : State) (f : bool -> bool -> bool) (b : bool) (e2 e2' : BExp),
    BEvals s e2 e2' ->
      BEvals s (BBinOp f (BConst b) e2) (BBinOp f (BConst b) e2').
Proof.
  now induction 1; eauto.
Qed.

Lemma BEvals_BBinOp :
  forall (s : State) (f : bool -> bool -> bool) (b1 b2 : bool),
    BEvals s (BBinOp f (BConst b1) (BConst b2)) (BConst (f b1 b2)).
Proof.
  now eauto.
Qed.

#[global] Hint Resolve
  BEvals_BRelOp_L BEvals_BRelOp_R BEvals_BRelOp
  BEvals_Not_Step BEvals_Not
  BEvals_BBinOp_L BEvals_BBinOp_R BEvals_BBinOp
    : core.

#[global] Hint Unfold acompatible : core.
#[global] Hint Resolve AEval_acompatible_det : core.

Lemma BEval_bcompatible_det :
  forall {s1 : State} {e e1 : BExp},
    BEval s1 e e1 -> forall {s2 : State},
    bcompatible e s1 s2 -> forall {e2 : BExp},
      BEval s2 e e2 -> e1 = e2.
Proof.
  unfold bcompatible.
  now induction 1; cbn in *; intros; repeat
    match goal with
    | H : AEval _ (?f _) _ |- _ => inversion H; subst; clear H
    | H : BEval _ (?f _) _ |- _ => inversion H; subst; clear H
    | |- ?f _ = ?f _ => f_equal
    | |- ?f _ _ = ?f _ _ => f_equal
    end; eauto 6.
Qed.

Inductive CEval : Com * State -> Com * State -> Prop :=
| CEval_Asgn_Step :
    forall (s : State) (a a' : AExp) (x : Atom),
      AEval s a a' -> CEval (Asgn x a, s) (Asgn x a', s)
| CEval_Asgn_Val :
    forall (s : State) (n : nat) (x : Atom),
      CEval (Asgn x (AConst n), s) (Skip, changeState s x n)
| CEval_Seq_L :
    forall (c1 c1' c2 : Com) (s s' : State),
      CEval (c1, s) (c1', s') ->
        CEval (Seq c1 c2, s) (Seq c1' c2, s')
| CEval_Seq_R :
    forall (c : Com) (s : State),
      CEval (Seq Skip c, s) (c, s)
| CEval_If_Step :
    forall (b b' : BExp) (c1 c2 : Com) (s : State),
      BEval s b b' -> CEval (If b c1 c2, s) (If b' c1 c2, s)
| CEval_If_True :
    forall (s : State) (c1 c2 : Com),
      CEval (If (BConst true) c1 c2, s) (c1, s)
| CEval_If_False :
    forall (s : State) (c1 c2 : Com),
      CEval (If (BConst false) c1 c2, s) (c2, s)
| CEval_While :
    forall (b : BExp) (c : Com) (s : State),
      CEval (While b c, s) (If b (Seq c (While b c)) Skip, s).

#[global] Hint Constructors CEval : core.

Example while_true_do_skip :
  forall s1 s2 : State,
    ~ CEval (While (BConst true) Skip, s1) (Skip, s2).
Proof.
  intros s1 s2 H.
  remember (While (BConst true) Skip, s1) as cs1.
  remember (Skip, s2) as cs2.
  revert s1 s2 Heqcs1 Heqcs2.
  now induction H; intros.
Qed.

Lemma CEval_det :
  forall {cs cs1 : Com * State},
    CEval cs cs1 -> forall {cs2 : Com * State},
      CEval cs cs2 -> cs1 = cs2.
Proof.
  now induction 1; intros; repeat
    match goal with
    | H : AEval _ ?x _ |- _ => tryif is_var x then fail else (inversion H; subst; clear H)
    | H : BEval _ ?x _ |- _ => tryif is_var x then fail else (inversion H; subst; clear H)
    | H : CEval (?x, _) _ |- _ => tryif is_var x then fail else (inversion H; subst; clear H)
    | IH : forall _, CEval _ _ -> _, H : CEval _ _ |- _ =>
        let H' := fresh "H" in
          pose (H' := IH _ H); inversion H'; subst; clear H'; clear H
    | _ => adet; bdet; auto
    end.
Qed.

Ltac cdet := repeat
match goal with
| H1 : CEval ?cs ?cs1, H2 : CEval ?cs ?cs2 |- _ =>
  assert (cs1 = cs2) by (eapply CEval_det; eauto); subst; clear H2
end.

Definition CEvals (cs1 cs2 : Com * State) : Prop :=
  rtc CEval cs1 cs2.

#[global] Hint Unfold CEvals : core.

Lemma CEvals_Asgn_Step :
  forall (s : State) (a a' : AExp) (x : Atom),
    AEvals s a a' -> CEvals (Asgn x a, s) (Asgn x a', s).
Proof.
  now induction 1; eauto.
Qed.

Lemma CEvals_Asgn_Val :
  forall (s : State) (n : nat) (x : Atom),
    CEvals (Asgn x (AConst n), s) (Skip, changeState s x n).
Proof.
  now eauto.
Qed.

Lemma CEvals_Seq_L :
  forall (c1 c1' c2 : Com) (s s' : State),
    CEvals (c1, s) (c1', s') ->
      CEvals (Seq c1 c2, s) (Seq c1' c2, s').
Proof.
  intros.
  remember (c1, s) as cs1.
  remember (c1', s') as cs1'.
  revert c1 s c1' s' Heqcs1 Heqcs1'.
  induction H; intros; subst.
  - now do 2 constructor.
  - now inversion Heqcs1'; subst; constructor.
  - destruct y.
    specialize (IHrtc1 _ _ _ _ eq_refl eq_refl).
    specialize (IHrtc2 _ _ _ _ eq_refl eq_refl).
    now eauto.
Qed.

Lemma CEvals_Seq_R :
  forall (c : Com) (s : State),
    CEvals (Seq Skip c, s) (c, s).
Proof.
  now eauto.
Qed.

Lemma CEvals_If_Step :
  forall (b b' : BExp) (c1 c2 : Com) (s : State),
    BEvals s b b' -> CEvals (If b c1 c2, s) (If b' c1 c2, s).
Proof.
  now induction 1; eauto.
Qed.

Lemma CEvals_If_True :
  forall (s : State) (c1 c2 : Com),
    CEvals (If (BConst true) c1 c2, s) (c1, s).
Proof.
  now eauto.
Qed.

Lemma CEvals_If_False :
  forall (s : State) (c1 c2 : Com),
    CEvals (If (BConst false) c1 c2, s) (c2, s).
Proof.
  now eauto.
Qed.

Lemma CEvals_While :
  forall (b : BExp) (c : Com) (s : State),
    CEvals (While b c, s) (If b (Seq c (While b c)) Skip, s).
Proof.
  now eauto.
Qed.

Definition CEvals' (cs1 cs2 : Com * State) : Prop :=
  rtc' CEval cs1 cs2.

#[global] Hint Unfold CEvals' : core.

Lemma CEvals_CEvals' :
  forall cs1 cs2 : Com * State,
    CEvals cs1 cs2 -> CEvals' cs1 cs2.
Proof.
  unfold CEvals; unfold CEvals'.
  induction 1; [now eauto.. |].
  now eapply rtc'_trans; eauto.
Qed.

Lemma aeval_AEvals :
  forall (s : State) (a : AExp) (n : nat),
    aeval s a = n -> AEvals s a (AConst n).
Proof.
  induction a; cbn; intros.
  - now inversion H; subst; constructor.
  - now inversion H; subst; constructor.
  - specialize (IHa1 _ eq_refl).
    specialize (IHa2 _ eq_refl).
    eapply AEvals_trans.
    + eapply AEvals_trans.
      * now apply AEvals_ABinOp_L, IHa1.
      * now apply AEvals_ABinOp_R, IHa2.
    + now rewrite <- H; apply AEvals_ABinOp.
Qed.

Lemma AEval_aevals :
  forall {s : State} {a1 a2 : AExp},
    AEval s a1 a2 -> aeval s a1 = aeval s a2.
Proof.
  now induction 1; cbn; auto.
Qed.

Lemma AEvals_aevals :
  forall (s : State) (a1 a2 : AExp),
    AEvals s a1 a2 -> aeval s a1 = aeval s a2.
Proof.
  induction 1; cbn; intros.
  - now apply AEval_aevals.
  - easy.
  - now rewrite IHAEvals1.
Qed.

Lemma AEvals_aeval :
  forall (s : State) (a : AExp) (n : nat),
    AEvals s a (AConst n) -> aeval s a = n.
Proof.
  now intros; apply AEvals_aevals in H; cbn in H.
Qed.

#[global] Hint Resolve AEval_aevals : core.

Lemma BEval_bevals :
  forall {s : State} {e1 e2 : BExp},
    BEval s e1 e2 -> beval s e1 = beval s e2.
Proof.
  now induction 1; cbn;
    rewrite ?(AEval_aevals H), ?IHBEval, ?IHBEval1, ?IHBEval2.
Qed.

#[global] Hint Unfold BEvals : core.

Lemma beval_BEvals :
  forall (s : State) (e : BExp) (b : bool),
    beval s e = b -> BEvals s e (BConst b).
Proof.
  induction e; cbn; intros; subst.
  - now constructor.
  - eapply rtc_trans.
    + now apply BEvals_BRelOp_L, aeval_AEvals.
    + eapply rtc_trans.
      * now apply BEvals_BRelOp_R, aeval_AEvals.
      * now apply BEvals_BRelOp.
  - eapply rtc_trans.
    + now apply BEvals_Not_Step, IHe.
    + now apply BEvals_Not.
  - eapply rtc_trans.
    + now apply BEvals_BBinOp_L, IHe1.
    + eapply rtc_trans.
      * now apply BEvals_BBinOp_R, IHe2.
      * now apply BEvals_BBinOp.
Qed.

Lemma BEvals_bevals :
  forall {s : State} {e1 e2 : BExp},
    BEvals s e1 e2 -> beval s e1 = beval s e2.
Proof.
  induction 1; cbn; intros.
  - now apply BEval_bevals.
  - easy.
  - now rewrite IHrtc1, IHrtc2.
Qed.

Lemma BEvals_beval :
  forall (s : State) (e : BExp) (b : bool),
    BEvals s e (BConst b) -> beval s e = b.
Proof.
  now intros; apply BEvals_bevals in H; cbn in H.
Qed.

Lemma CEval_cevals :
  forall {cs1 cs2 : Com * State},
    CEval cs1 cs2 -> forall (n : nat) (s : State),
      ceval n (fst cs2) (snd cs2) = Some s ->
      ceval (S n) (fst cs1) (snd cs1) = Some s.
Proof.
  induction 1; cbn; intros [| fuel] final Heq; cbn in Heq;
    try (now cbn in *; congruence).
  - rewrite <- Heq.
    do 2 f_equal.
    now apply AEval_aevals.
  - unfold fst, snd in *.
    destruct (ceval fuel c1' s') eqn: Heq'; [| easy].
    rewrite (IHCEval _ _ Heq').
    change (S fuel) with (1 + fuel).
    now rewrite (ceval_plus' Heq 1).
  - apply BEval_bevals in H.
    rewrite <- Heq, H.
    now destruct (beval s b');
      rewrite Heq; change (S fuel) with (1 + fuel); rewrite Nat.add_comm;
      apply ceval_plus.
  - destruct (beval s b); destruct fuel; cbn in Heq; [easy | | easy..].
    destruct (ceval fuel c s) eqn: Heq'; [| easy].
    change (S (S fuel)) with (2 + fuel).
    now rewrite (ceval_plus' Heq' 2), (ceval_plus' Heq 2).
Qed.

Lemma ceval_CEvals :
  forall (n : nat) (c : Com) (s s' : State),
    ceval n c s = Some s' -> CEvals (c, s) (Skip, s').
Proof.
  intros n c s.
  functional induction ceval n c s; cbn; intros.
  - easy.
  - now injection H as [= ->]; constructor.
  - injection H as [= <-].
    eapply rtc_trans.
    + now apply CEvals_Asgn_Step, aeval_AEvals.
    + now eauto.
  - easy.
  - eapply rtc_trans; [now apply CEvals_Seq_L; eauto |].
    eapply rtc_trans.
    + now apply CEvals_Seq_R.
    + now apply IHo0.
  - eapply rtc_trans.
    + now apply CEvals_If_Step, beval_BEvals; eassumption.
    + eapply rtc_trans.
      * now apply CEvals_If_True.
      * now apply IHo.
  - eapply rtc_trans.
    + now apply CEvals_If_Step, beval_BEvals; eassumption.
    + eapply rtc_trans.
      * now apply CEvals_If_False.
      * now apply IHo.
  - easy.
  - eapply rtc_trans; [now apply CEvals_While |].
    eapply rtc_trans; [now eapply CEvals_If_Step, beval_BEvals; now eassumption |].
    eapply rtc_trans; [now apply CEvals_If_True |].
    eapply rtc_trans; [now apply CEvals_Seq_L; eauto |].
    eapply rtc_trans; [now apply CEvals_Seq_R |].
    now apply IHo0.
  - eapply rtc_trans; [now apply CEvals_While |].
    eapply rtc_trans; [now eapply CEvals_If_Step, beval_BEvals; eassumption |].
    eapply rtc_trans; [now apply CEvals_If_False |].
    now injection H as [= ->]; constructor.
Qed.

Lemma CEvals'_ceval :
  forall (c : Com) (s1 s2 : State),
    CEvals' (c, s1) (Skip, s2) -> exists n : nat,
      ceval n c s1 = Some s2.
Proof.
  intros c s1 s2 H.
  remember (c, s1) as cs1.
  remember (Skip, s2) as cs2.
  revert c s1 s2 Heqcs1 Heqcs2.
  induction H; intros; subst.
  - inversion Heqcs2; subst.
    now exists 1; cbn.
  - inversion H; subst; destruct (IHrtc' _ _ _ eq_refl eq_refl) as [fuel IH].
    + exists fuel.
      rewrite <- IH.
      destruct fuel; cbn; [easy |].
      do 2 f_equal.
      now apply AEval_aevals.
    + exists fuel.
      rewrite <- IH.
      now destruct fuel; cbn.
    + rewrite <- IH.
      destruct fuel; cbn in *; [easy |].
      destruct (ceval fuel c1' s') eqn: Heq; [| easy].
      exists (S fuel + 1); cbn.
      rewrite Nat.add_comm.
      pose (CEval_cevals H4 (fuel) s Heq).
      unfold fst, snd in e.
      unfold plus.
      rewrite e.
      change (S fuel) with (1 + fuel).
      now rewrite Nat.add_comm, IH, (ceval_plus _ 1 _ _ _ IH).
    + exists (S fuel); cbn.
      destruct fuel; [easy |].
      now rewrite ceval_equation.
    + exists fuel.
      rewrite <- IH.
      destruct fuel; cbn; [easy |].
      apply BEval_bevals in H4.
      now rewrite H4.
    + now exists (S fuel); cbn.
    + now exists (S fuel); cbn.
    + exists (S fuel).
      now apply ceval_plus' with 2 in IH; cbn in *.
Qed.

Lemma CEvals_ceval :
  forall (c : Com) (s1 s2 : State),
    CEvals (c, s1) (Skip, s2) -> exists n : nat,
      ceval n c s1 = Some s2.
Proof.
  now intros; apply CEvals'_ceval, CEvals_CEvals'.
Qed.
