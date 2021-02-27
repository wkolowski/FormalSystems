Require Export Syntax.

Inductive AEval (s : State) : AExp -> AExp -> Prop :=
    | AEval_Var :
        forall x : Loc, AEval s (Var x) (AConst (s x))
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

Hint Constructors AEval.

Lemma AEval_det :
  forall {s : State} {a a1 a2 : AExp},
    AEval s a a1 -> AEval s a a2 -> a1 = a2.
Proof.
  intros s a a1 a2 H. revert a2.
  induction H; intros; repeat
  match goal with
      | H : AEval _ (?f _) _ |- _ => inv H
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

Hint Constructors AEvals.

Lemma AEval_AEvals :
  forall (s : State) (a1 a1' a2 : AExp),
    AEval s a1 a1' -> AEvals s a1' a2 -> AEvals s a1 a2.
Proof.
  induction 1; intros; eauto.
Qed.

Lemma AEvalsVar :
  forall (s : State) (x : Loc), AEvals s (Var x) (AConst (s x)).
Proof. eauto. Qed.

Lemma AEvals_ABinOp_L :
  forall (s : State) (f : nat -> nat -> nat) (a1 a1' a2 : AExp),
    AEvals s a1 a1' -> AEvals s (ABinOp f a1 a2) (ABinOp f a1' a2).
Proof.
  induction 1; eauto.
Qed.

Lemma AEvals_ABinOp_R :
  forall (s : State) (f : nat -> nat -> nat) (n : nat) (a2 a2' : AExp),
    AEvals s a2 a2' ->
      AEvals s (ABinOp f (AConst n) a2) (ABinOp f (AConst n) a2').
Proof.
  induction 1; eauto.
Qed.

Lemma AEvals_ABinOp :
  forall (s : State) (f : nat -> nat -> nat) (n1 n2 : nat),
    AEvals s (ABinOp f (AConst n1) (AConst n2)) (AConst (f n1 n2)).
Proof. eauto. Qed.

Lemma AEval_acompatible_det :
  forall {s1 : State} {a a1 : AExp},
    AEval s1 a a1 -> forall {s2 : State},
      acompatible a s1 s2 -> forall {a2 : AExp},
        AEval s2 a a2 -> a1 = a2.
Proof.
  Hint Resolve in_or_app.
  unfold acompatible.
  induction 1; cbn in *; intros; repeat
  match goal with
      | H : AEval _ (?f _) _ |- _ => inv H
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

Hint Constructors BEval.

Lemma BEval_det :
  forall {s : State} {e e1 : BExp},
    BEval s e e1 -> forall {e2 : BExp}, BEval s e e2 -> e1 = e2.
Proof.
  Hint Resolve AEval_det.
  induction 1; intros; repeat
  match goal with
      | H : AEval _ (?f _) _ |- _ => inv H
      | H : BEval _ (?f _) _ |- _ => inv H
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

Hint Unfold BEvals.

Lemma BEvals_BRelOp_L :
  forall (s : State) (f : nat -> nat -> bool) (a1 a1' a2 : AExp),
    AEvals s a1 a1' -> BEvals s (BRelOp f a1 a2) (BRelOp f a1' a2).
Proof.
  induction 1; eauto.
Qed.

Lemma BEvals_BRelOp_R :
  forall (s : State) (f : nat -> nat -> bool) (n : nat) (a2 a2' : AExp),
    AEvals s a2 a2' ->
      BEvals s (BRelOp f (AConst n) a2) (BRelOp f (AConst n) a2').
Proof.
  induction 1; intros; eauto.
Qed.

Lemma BEvals_BRelOp :
  forall (s : State) (f : nat -> nat -> bool) (n1 n2 : nat),
    BEvals s (BRelOp f (AConst n1) (AConst n2)) (BConst (f n1 n2)).
Proof. eauto. Qed.

Lemma BEvals_Not_Step :
  forall (s : State) (e e' : BExp),
    BEvals s e e' -> BEvals s (Not e) (Not e').
Proof.
  induction 1; eauto.
Qed.

Lemma BEvals_Not :
  forall (s : State) (b : bool),
    BEvals s (Not (BConst b)) (BConst (negb b)).
Proof. eauto. Qed.

Lemma BEvals_BBinOp_L :
  forall (s : State) (f : bool -> bool -> bool) (e1 e1' e2 : BExp),
    BEvals s e1 e1' -> BEvals s (BBinOp f e1 e2) (BBinOp f e1' e2).
Proof.
  induction 1; eauto.
Qed.

Lemma BEvals_BBinOp_R :
  forall (s : State) (f : bool -> bool -> bool) (b : bool) (e2 e2' : BExp),
    BEvals s e2 e2' ->
      BEvals s (BBinOp f (BConst b) e2) (BBinOp f (BConst b) e2').
Proof.
  induction 1; eauto.
Qed.

Lemma BEvals_BBinOp :
  forall (s : State) (f : bool -> bool -> bool) (b1 b2 : bool),
    BEvals s (BBinOp f (BConst b1) (BConst b2)) (BConst (f b1 b2)).
Proof. eauto. Qed.

Hint Resolve
  BEvals_BRelOp_L BEvals_BRelOp_R BEvals_BRelOp
  BEvals_Not_Step BEvals_Not
  BEvals_BBinOp_L BEvals_BBinOp_R BEvals_BBinOp.

Lemma BEval_bcompatible_det :
  forall {s1 : State} {e e1 : BExp},
    BEval s1 e e1 -> forall {s2 : State},
    bcompatible e s1 s2 -> forall {e2 : BExp},
      BEval s2 e e2 -> e1 = e2.
Proof.
  Hint Unfold acompatible.
  Hint Resolve AEval_acompatible_det.
  unfold bcompatible.
  induction 1; cbn in *; intros; repeat
  match goal with
      | H : AEval _ (?f _) _ |- _ => inv H
      | H : BEval _ (?f _) _ |- _ => inv H
      | |- ?f _ = ?f _ => f_equal
      | |- ?f _ _ = ?f _ _ => f_equal
  end; eauto 6.
Qed.

Inductive CEval : Com * State -> Com * State -> Prop :=
    | CEval_Asgn_Step :
        forall (s : State) (a a' : AExp) (x : Loc),
          AEval s a a' -> CEval (Asgn x a, s) (Asgn x a', s)
    | CEval_Asgn_Val :
        forall (s : State) (n : nat) (x : Loc),
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

Hint Constructors CEval.

Example while_true_do_skip :
  forall s1 s2 : State,
    ~ CEval (While (BConst true) Skip, s1) (Skip, s2).
Proof.
  intros s1 s2 H.
  remember (While (BConst true) Skip, s1) as cs1.
  remember (Skip, s2) as cs2.
  revert s1 s2 Heqcs1 Heqcs2.
  induction H; intros; inv Heqcs1; inv Heqcs2.
Qed.

Lemma CEval_det :
  forall {cs cs1 : Com * State},
    CEval cs cs1 -> forall {cs2 : Com * State},
      CEval cs cs2 -> cs1 = cs2.
Proof.
  induction 1; intros; repeat
  match goal with
      | H : AEval _ ?x _ |- _ => tryif is_var x then fail else inv H
      | H : BEval _ ?x _ |- _ => tryif is_var x then fail else inv H
      | H : CEval (?x, _) _ |- _ => tryif is_var x then fail else inv H
      | IH : forall _, CEval _ _ -> _, H : CEval _ _ |- _ =>
          let H' := fresh "H" in
            pose (H' := IH _ H); inv H'; clear H
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

Hint Unfold CEvals.

Lemma CEvals_Asgn_Step :
  forall (s : State) (a a' : AExp) (x : Loc),
    AEvals s a a' -> CEvals (Asgn x a, s) (Asgn x a', s).
Proof.
  induction 1; eauto.
Qed.

Lemma CEvals_Asgn_Val :
  forall (s : State) (n : nat) (x : Loc),
    CEvals (Asgn x (AConst n), s) (Skip, changeState s x n).
Proof. eauto. Qed.

Lemma CEvals_Seq_L :
  forall (c1 c1' c2 : Com) (s s' : State),
    CEvals (c1, s) (c1', s') ->
      CEvals (Seq c1 c2, s) (Seq c1' c2, s').
Proof.
  intros.
  remember (c1, s) as cs1.
  remember (c1', s') as cs1'.
  revert c1 s c1' s' Heqcs1 Heqcs1'.
  induction H; intros.
    inv Heqcs1. auto.
    inv Heqcs1. inv Heqcs1'. auto.
    inv Heqcs1. destruct y.
      specialize (IHrtc1 _ _ _ _ eq_refl eq_refl).
      specialize (IHrtc2 _ _ _ _ eq_refl eq_refl). eauto.
Qed.

Lemma CEvals_Seq_R :
  forall (c : Com) (s : State),
    CEvals (Seq Skip c, s) (c, s).
Proof. eauto. Qed.

Lemma CEvals_If_Step :
  forall (b b' : BExp) (c1 c2 : Com) (s : State),
    BEvals s b b' -> CEvals (If b c1 c2, s) (If b' c1 c2, s).
Proof.
  induction 1; eauto.
Qed.

Lemma CEvals_If_True :
  forall (s : State) (c1 c2 : Com),
    CEvals (If (BConst true) c1 c2, s) (c1, s).
Proof. eauto. Qed.

Lemma CEvals_If_False :
  forall (s : State) (c1 c2 : Com),
    CEvals (If (BConst false) c1 c2, s) (c2, s).
Proof. eauto. Qed.

Lemma CEvals_While :
  forall (b : BExp) (c : Com) (s : State),
    CEvals (While b c, s) (If b (Seq c (While b c)) Skip, s).
Proof. eauto. Qed.

Definition CEvals' (cs1 cs2 : Com * State) : Prop :=
  rtc' CEval cs1 cs2.

Hint Unfold CEvals'.

Lemma CEvals_CEvals' :
  forall cs1 cs2 : Com * State,
    CEvals cs1 cs2 -> CEvals' cs1 cs2.
Proof.
  unfold CEvals; unfold CEvals'.
  induction 1; eauto.
  eapply rtc'_trans; eauto.
Qed.

Require Import Denotational.

Lemma aeval_AEvals :
  forall (s : State) (a : AExp) (n : nat),
    aeval s a = n -> AEvals s a (AConst n).
Proof.
  induction a; cbn; intros.
    inv H. auto.
    inv H. eauto.
    specialize (IHa1 _ eq_refl). specialize (IHa2 _ eq_refl).
      eapply AEvals_trans.
        Focus 2. rewrite <- H. apply AEvals_ABinOp.
      eapply AEvals_trans.
        apply AEvals_ABinOp_L. eassumption.
      apply AEvals_ABinOp_R. assumption.
Qed.

Lemma AEval_aevals :
  forall {s : State} {a1 a2 : AExp},
    AEval s a1 a2 -> aeval s a1 = aeval s a2.
Proof.
  induction 1; cbn; auto.
Qed.

Lemma AEvals_aevals :
  forall (s : State) (a1 a2 : AExp),
    AEvals s a1 a2 -> aeval s a1 = aeval s a2.
Proof.
  induction 1; cbn; intros.
    apply AEval_aevals. assumption.
    reflexivity.
    rewrite IHAEvals1. assumption.
Qed.

Lemma AEvals_aeval :
  forall (s : State) (a : AExp) (n : nat),
    AEvals s a (AConst n) -> aeval s a = n.
Proof.
  intros. apply AEvals_aevals in H. cbn in H. assumption.
Qed.

Lemma BEval_bevals :
  forall {s : State} {e1 e2 : BExp},
    BEval s e1 e2 -> beval s e1 = beval s e2.
Proof.
  Hint Resolve AEval_aevals.
  induction 1; cbn;
  rewrite ?(AEval_aevals H), ?IHBEval, ?IHBEval1, ?IHBEval2; auto.
Qed.

Lemma beval_BEvals :
  forall (s : State) (e : BExp) (b : bool),
    beval s e = b -> BEvals s e (BConst b).
Proof.
  Hint Unfold BEvals.
  induction e; cbn; intros.
    inv H. auto.
    inv H. eapply rtc_trans.
      apply BEvals_BRelOp_L. apply aeval_AEvals. reflexivity.
      eapply rtc_trans.
        apply BEvals_BRelOp_R. apply aeval_AEvals. reflexivity.
        apply BEvals_BRelOp.
    inv H. eapply rtc_trans.
      apply BEvals_Not_Step. apply IHe. reflexivity.
      apply BEvals_Not.
    inv H. eapply rtc_trans.
      apply BEvals_BBinOp_L. apply IHe1. reflexivity.
      eapply rtc_trans.
        apply BEvals_BBinOp_R. apply IHe2. reflexivity.
        apply BEvals_BBinOp.
Qed.

Lemma BEvals_bevals :
  forall {s : State} {e1 e2 : BExp},
    BEvals s e1 e2 -> beval s e1 = beval s e2.
Proof.
  induction 1; cbn; intros.
    apply BEval_bevals. assumption.
    reflexivity.
    rewrite IHrtc1, IHrtc2. reflexivity.
Qed.

Lemma BEvals_beval :
  forall (s : State) (e : BExp) (b : bool),
    BEvals s e (BConst b) -> beval s e = b.
Proof.
  intros. apply BEvals_bevals in H. cbn in H. assumption.
Qed.

Lemma CEval_cevals :
  forall {cs1 cs2 : Com * State},
    CEval cs1 cs2 -> forall (n : nat) (s : State),
      ceval n (fst cs2) (snd cs2) = Some s ->
      ceval (S n) (fst cs1) (snd cs1) = Some s.
Proof.
  induction 1; cbn; intros [| fuel] final Heq;
  try (cbn in *; congruence; fail).
    cbn in *. rewrite <- Heq. do 2 f_equal. apply AEval_aevals. assumption.
    Focus 2. cbn in Heq. apply BEval_bevals in H. rewrite <- Heq, H.
      destruct (beval s b').
        all: rewrite Heq; change (S fuel) with (1 + fuel); rewrite plus_comm;
          apply ceval_plus; assumption.
    Focus 2. cbn in Heq. destruct (beval s b).
      destruct fuel; cbn in Heq.
        inv Heq.
        destruct (ceval fuel c s) eqn: Heq'.
          change (S (S fuel)) with (2 + fuel).
            rewrite (ceval_plus' Heq' 2).
            rewrite (ceval_plus' Heq 2). reflexivity.
          inv Heq.
      destruct fuel; inv Heq. reflexivity.
    cbn in Heq. unfold fst, snd in *.
      destruct (ceval fuel c1' s') eqn: Heq'.
        specialize (IHCEval _ _ Heq'). rewrite IHCEval.
          change (S fuel) with (1 + fuel). rewrite (ceval_plus' Heq 1).
          reflexivity.
        inv Heq.
Qed.

Lemma ceval_CEvals :
  forall (n : nat) (c : Com) (s s' : State),
    ceval n c s = Some s' -> CEvals (c, s) (Skip, s').
Proof.
  intros n c s. functional induction ceval n c s; cbn; intros.
    inv H.
    inv H. auto.
    inv H. eapply rtc_trans.
      apply CEvals_Asgn_Step. apply aeval_AEvals. reflexivity.
      eauto.
    inv H.
    eapply rtc_trans.
      apply CEvals_Seq_L. eauto.
      eapply rtc_trans.
        apply CEvals_Seq_R. apply IHo0. assumption.
    eapply rtc_trans.
      apply CEvals_If_Step. apply beval_BEvals. eassumption.
      eapply rtc_trans.
        apply CEvals_If_True.
        apply IHo. assumption.
    eapply rtc_trans.
      apply CEvals_If_Step. apply beval_BEvals. eassumption.
      eapply rtc_trans.
        apply CEvals_If_False.
        apply IHo. assumption.
    inv H.
    eapply rtc_trans.
      apply CEvals_While. eapply rtc_trans.
        eapply CEvals_If_Step. apply beval_BEvals. eassumption.
        eapply rtc_trans.
          apply CEvals_If_True.
          eapply rtc_trans.
            apply CEvals_Seq_L. eauto.
            eapply rtc_trans.
              apply CEvals_Seq_R.
              apply IHo0. assumption.
    eapply rtc_trans.
      apply CEvals_While. eapply rtc_trans.
        eapply CEvals_If_Step. apply beval_BEvals. eassumption.
        eapply rtc_trans.
          apply CEvals_If_False.
          inv H. auto.
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
  induction H; intros.
    inv Heqcs1. inv Heqcs2. exists 1. cbn. reflexivity.
    inv Heqcs1. clear H1.
    inv H; destruct (IHrtc' _ _ _ eq_refl eq_refl) as [fuel IH].
      exists fuel. rewrite <- IH. destruct fuel; cbn.
          reflexivity.
          do 2 f_equal. apply AEval_aevals. assumption.
      exists fuel. rewrite <- IH. destruct fuel; cbn; reflexivity.
      rewrite <- IH. destruct fuel; cbn in *.
        inv IH.
        destruct (ceval fuel c1' s') eqn: Heq.
          Focus 2. inv IH.
          exists (S fuel + 1). cbn. rewrite plus_comm.
            pose (CEval_cevals H4 (fuel) s Heq). unfold fst, snd in e.
            unfold plus. rewrite e. change (S fuel) with (1 + fuel).
            rewrite plus_comm. rewrite IH, (ceval_plus _ 1 _ _ _ IH).
            reflexivity.
      exists (S fuel). cbn. destruct fuel. cbn in *.
        assumption. rewrite ceval_equation. assumption.
      exists fuel. rewrite <- IH. destruct fuel; cbn.
        reflexivity.
        apply BEval_bevals in H4. rewrite H4. reflexivity.
      exists (S fuel). cbn. assumption.
      exists (S fuel). cbn. assumption.
      exists (S fuel).
        apply ceval_plus' with 2 in IH. cbn in IH. cbn. assumption.
Qed.

Lemma CEvals_ceval :
  forall (c : Com) (s1 s2 : State),
    CEvals (c, s1) (Skip, s2) -> exists n : nat,
      ceval n c s1 = Some s2.
Proof.
  intros. apply CEvals'_ceval, CEvals_CEvals'. assumption.
Qed.