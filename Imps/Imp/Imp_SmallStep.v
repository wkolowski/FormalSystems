Add Rec LoadPath "~/Code/Coq".

Require Import ImpSyntax.

(** * Structural operational semantics for IMP *)

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

Inductive rtc {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
    | rtc_step :
        forall x y : A, R x y -> rtc R x y
    | rtc_refl :
        forall x : A, rtc R x x
    | rtc_trans :
        forall x y z : A, rtc R x y -> rtc R y z -> rtc R x z.

Hint Constructors rtc.

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

Require Imp_BigStep.

Lemma Imp_BigStep_SmallStep :
  forall (s : State) (a : AExp) (n : nat),
    Imp_BigStep.AEval a s n <-> AEvals s a (AConst n).
Proof.
  split; intro.
    apply Imp_BigStep.AEval_aeval in H. apply aeval_AEvals. assumption.
    apply AEvals_aeval in H. apply Imp_BigStep.aeval_AEval. assumption.
Qed.

(*
Inductive AEvals (s : State) : AExp -> nat -> Prop :=
    | AEval'_step :
        forall n : nat, AEval' s (AConst n) n
    | AEval'_more :
        forall (a1 a2 : AExp) (n : nat),
          AEval s a1 a2 -> AEval' s a2 n -> AEval' s a1 n.

Hint Constructors AEval'.

Lemma AEval_AEval' :
  forall {s : State} {a1 a2 : AExp},
    AEval s a1 a2 ->
    forall {n : nat}, AEval' s a1 n -> AEval' s a2 n.
Proof.
  induction 1; cbn; intros; repeat (
  match goal with
      | H : AEval ?s ?a ?a1, H' : AEval ?s ?a ?a2 |- _ =>
        assert (a1 = a2) by (eapply AEval_det; eauto); subst; clear H'
      | H : AEval _ ?x _ |- _ =>
          tryif is_var x then fail else inv H
      | H : AEval' _ ?x _ |- _ =>
          tryif is_var x then fail else inv H
  end; eauto).
Qed.

Lemma AEval_aeval :
  forall {s : State} {a1 a2 : AExp},
    AEval s a1 a2 -> aeval s a1 = aeval s a2.
Proof.
  induction 1; cbn; auto.
Qed.

Lemma AEval_aeval' :
  forall {s : State} {a : AExp} {n : nat},
    AEval s a (AConst n) -> aeval s a = n.
Proof.
  intros. change n with (aeval s (AConst n)).
  apply AEval_aeval. assumption.
Qed.

Lemma aeval_AEval' :
  forall {s : State} {a : AExp} {n : nat},
    aeval s a = n -> AEval' s a n.
Proof.
  induction a; cbn; intros.
    inv H. eauto.
    inv H. eauto.
    rewrite <- H. specialize (IHa1 _ eq_refl). specialize (IHa2 _ eq_refl).
      inv IHa1.
Admitted.
*)

(*
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
*)

Print BExp.

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

Lemma BEval_bevals :
  forall {s : State} {e1 e2 : BExp},
    BEval s e1 e2 -> beval s e1 = beval s e2.
Proof.
  Hint Resolve AEval_aevals.
  induction 1; cbn;
  rewrite ?(AEval_aevals H), ?IHBEval, ?IHBEval1, ?IHBEval2; auto.
Qed.

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

(*
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
*)

Lemma Imp_BigStep_SmallStep_logic :
  forall (s : State) (e : BExp) (b : bool),
    Imp_BigStep.BEval e s b <-> BEvals s e (BConst b).
Proof.
  split; intro.
    apply Imp_BigStep.BEval_beval in H. apply beval_BEvals. assumption.
    apply BEvals_beval in H. apply Imp_BigStep.beval_BEval. assumption.
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

Lemma CEval_cevals :
  forall {cs1 cs2 : Com * State},
    CEval cs1 cs2 -> forall {n : nat} {s : State},
      ceval n (fst cs2) (snd cs2) = Some s ->
      ceval (S n) (fst cs1) (snd cs2) = Some s.
Proof.
  induction 1; cbn.
    destruct n; cbn; intros.
      inv H0.
      inv H0. do 2 f_equal. apply AEval_aevals. assumption.
    destruct n0; cbn; intros; auto.
      inv H.
      inv H. compute. f_equal. admit.
    all: destruct n as [| n']; cbn in *; intros; eauto.
      Focus 2. inv H0.
      Focus 2. apply BEval_bevals in H. rewrite H. destruct (beval s b').
        destruct c1; inv H0.
Restart.
  intros. revert cs1 H s H0.
  functional induction ceval n (fst cs2) (snd cs2); intros; try congruence.
    inv H0.
Admitted.

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
Admitted.

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

Inductive rtc' {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
    | rtc'_refl :
        forall x : A, rtc' R x x
    | rtc'_steptrans :
        forall x y z : A, R x y -> rtc' R y z -> rtc' R x z.

Hint Constructors rtc'.

Definition CEvals' (cs1 cs2 : Com * State) : Prop :=
  rtc' CEval cs1 cs2.

Hint Unfold CEvals'.

Lemma rtc'_trans :
  forall {A : Type} {R : A -> A -> Prop} {x y z : A},
    rtc' R x y -> rtc' R y z -> rtc' R x z.
Proof.
  intros until 1. revert z.
  induction H; intros.
    assumption.
    eauto.
Qed.

Lemma CEvals_CEvals' :
  forall cs1 cs2 : Com * State,
    CEvals cs1 cs2 -> CEvals' cs1 cs2.
Proof.
  unfold CEvals; unfold CEvals'.
  induction 1; eauto.
  eapply rtc'_trans; eauto.
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
    inv Heqcs1. destruct y.
      destruct  (IHrtc' _ _ _ eq_refl eq_refl) as [n IH].
      exists (S n). cbn. inv H. cbn in *.
Admitted.

Lemma CEvals_ceval :
  forall (c : Com) (s1 s2 : State),
    CEvals (c, s1) (Skip, s2) -> exists n : nat,
      ceval n c s1 = Some s2.
Proof.
  intros c s1 s2 H.
  remember (c, s1) as cs1.
  remember (Skip, s2) as cs2.
  revert c s1 s2 Heqcs1 Heqcs2.
  induction H; intros.
    inv Heqcs1. inv H.
      exists 1. cbn. reflexivity.
      1-3: exists 2; cbn; reflexivity.
    inv Heqcs1. inv Heqcs2. exists 1. cbn. reflexivity.
    inv Heqcs1. inv H.
Admitted.

Lemma Imp_BigStep_SmallStep_Com :
  forall (c : Com) (s1 s2 : State),
    Imp_BigStep.CEval c s1 s2 <-> CEvals (c, s1) (Skip, s2).
Proof.
  split; intro.
    apply Imp_BigStep.CEval_ceval in H. destruct H as [n H].
      eapply ceval_CEvals. eassumption.
    apply CEvals_ceval in H. destruct H as [n H].
      apply Imp_BigStep.ceval_CEval with n. assumption.
Qed.

Lemma while_true_do_skip :
  forall s1 s2 : State,
    ~ CEval (While (BConst true) Skip, s1) (Skip, s2).
Proof.
  intros s1 s2 H.
  remember (While (BConst true) Skip, s1) as cs1.
  remember (Skip, s2) as cs2.
  revert s1 s2 Heqcs1 Heqcs2.
  induction H; intros; inv Heqcs1; inv Heqcs2.
Qed.

(*
Lemma CEval_not_In_locw_eq :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 -> forall x : Loc, ~ In x (locw c) -> s1 x = s2 x.
Proof.
  induction 1; cbn in *; intros; auto.
    unfold changeState. destruct (dec_spec v x).
      subst. contradiction H0. left. reflexivity.
      reflexivity.
    all: rewrite ?IHCEval, ?IHCEval1, ?IHCEval2; auto.
Qed.


Lemma CEval_not_In_loc_eq :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 -> forall x : Loc, ~ In x (loc c) -> s1 x = s2 x.
Proof.
  induction 1; cbn in *; intros; auto.
    unfold changeState. destruct (dec_spec v x).
      subst. contradiction H0. left. reflexivity.
      reflexivity.
    all: rewrite ?IHCEval, ?IHCEval1, ?IHCEval2; auto 7.
Qed.

Lemma CEval_ccompatible :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 ->
    forall {s1' s2' : State},
      CEval c s1' s2' ->
        ccompatible c s1 s1' -> ccompatible c s2 s2'.
Proof.
  unfold ccompatible.
  Hint Unfold bcompatible.
  induction 1; cbn; intros.
    inv H1.
    inv H0. unfold changeState. inv H2.
      destruct (dec_spec x x).
        eapply AEval_acompatible_det; eauto.
        contradiction.
      destruct (dec_spec v x).
        eapply AEval_acompatible_det; eauto.
        auto.
    Focus 4. inv H0.
      apply H1. assumption.
      assert (false = true).
        eapply BEval_bcompatible_det; eauto. congruence.
(* If *)
(*
    Focus 2. inv H1.
      eapply IHCEval; eauto 6.
*)
(* Seq *)
(*
    inv H1. apply in_app_or in H3. destruct H3.
      assert (In x (loc c2) \/ ~ In x (loc c2)).
        admit.
        destruct H3.
          assert (ccompatible c1 s2 s4).
            red. intros. eapply IHCEval1; eauto.
            red in H4. eapply IHCEval2; eauto. intros.
              apply H4. assumption.
*)
(* While *)
(*
    Focus 4. inv H2; cbn in *.
      assert (false = true); try congruence.
        eapply BEval_bcompatible_det; eauto. unfold bcompatible.
          intros. symmetry. auto.
      assert (s1 x = s1' x).
        apply H3. assumption.
        assert (s3 x = s2' x).
          eapply IHCEval2; eauto. intros. apply in_app_or in H5. inv H5.
*)
Abort.
*)