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

(*
Lemma AEvals_ABinOp' :
  forall (s : State) (f : nat -> nat -> nat) (a1 a1' a2 a2' : AExp),
    AEvals s a1 a1' -> AEvals s a2 a2' ->
      AEvals s (ABinOp f a1 a2) (ABinOp f a1' a2').
Proof.
  intros.
  eapply AEvals_trans.
    apply AEvals_ABinOp_L. eassumption.
  eapply AEvals_trans.
    apply AEvals_ABinOp_L. eassumption.
      
  induction 1. Focus 2. eauto. induction 1; eauto.
    eapply AEvals_trans.
      apply AEvals_step. apply AEval_ABinOp_L. eassumption.
      apply AEvals_step.
Admitted.
*)

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
  forall (s : State) (a1 a2 : AExp),
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
Definition acompatible (a : AExp) (s1 s2 : State) : Prop :=
  forall x : Loc, In x (loca a) -> s1 x = s2 x.

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
        forall (f : nat -> nat -> bool) (n : nat) (a1 a2 a2' : AExp),
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
          BEval s (BBinOp f (BConst b1) (BConst b2)) (BConst (andb b1 b2)).

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

(*
Lemma BEval_beval :
  forall {s : State} {e1 e2 : BExp},
    BEval s e1 e2 -> beval s e1 = beval s e2.
Proof.
  induction 1; cbn.
  rewrite ?(AEval_aeval H), ?IHBEval, ?IHBEval1, ?IHBEval2; auto.
Qed.

Lemma BEval_beval' :
  forall {s : State} {e : BExp} {b : bool},
    BEval s e (BConst b) -> beval s e = b.
Proof.
  intros. change b with (beval s (BConst b)).
  apply BEval_beval. assumption.
Qed.
*)

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

Inductive CEval : Com * State -> Com * State + State -> Prop :=
    | EvalSkip :
        forall s : State, CEval (Skip, s) (inr s)
    | EvalAsgnStep :
        forall (s : State) (a a' : AExp) (x : Loc),
          AEval s a a' -> CEval (Asgn x a, s) (inl (Asgn x a', s))
    | EvalAsgnVal :
        forall (s : State) (n : nat) (x : Loc),
          CEval (Asgn x (AConst n), s) (inr (changeState s x n))
    | EvalSeqL :
        forall (c1 c1' c2 : Com) (s s' : State),
          CEval (c1, s) (inl (c1', s')) ->
            CEval (Seq c1 c2, s) (inl (Seq c1' c2, s'))
    | EvalSeqR :
        forall (c1 c2 : Com) (s s' : State),
          CEval (c1, s) (inr s') -> CEval (Seq c1 c2, s) (inl (c2, s'))
    | EvalIfCond :
        forall (b b' : BExp) (c1 c2 : Com) (s : State),
          BEval s b b' -> CEval (If b c1 c2, s) (inl (If b' c1 c2, s))
    | EvalIfTrue :
        forall (s : State) (c1 c2 : Com),
          CEval (If (BConst true) c1 c2, s) (inl (c1, s))
    | EvalIfFalse :
        forall (s : State) (c1 c2 : Com),
          CEval (If (BConst false) c1 c2, s) (inl (c2, s))
    | EvalWhile :
        forall (b : BExp) (c : Com) (s : State),
          CEval (While b c, s) (inl (If b (Seq c (While b c)) Skip, s)).

Hint Constructors CEval.

Lemma CEval_det :
  forall {cs : Com * State} {cs1 : Com * State + State},
    CEval cs cs1 -> forall {cs2 : Com * State + State},
      CEval cs cs2 -> cs1 = cs2.
Proof.
  Hint Resolve AEval_det BEval_det.
  induction 1; intros; repeat
  match goal with
      | IH : forall _, CEval _ _ -> _, H : CEval _ _ |- _ =>
          let H' := fresh "H" in
            pose (H' := IH _ H); inv H'; clear H
      | |- ?f _ = ?f _ => f_equal; eauto
      | |- ?f _ _ = ?f _ _ => f_equal; eauto
      | |- ?f _ _ _ = ?f _ _ _ => f_equal; eauto
      | H : AEval _ (?f _) _ |- _ => inv H
      | H : BEval _ (?f _) _ |- _ => inv H
      | H : CEval (?f _ _) _ |- _ => inv H
  end.
Qed.

(*Hint Immediate aeval_AEval beval_BEval.*)

Inductive CEval' : Com * State -> State -> Prop :=
    | CEval'_step :
        forall (cs : Com * State) (s : State),
          CEval cs (inr s) -> CEval' cs s
    | CEval'_more :
        forall (cs1 cs2 : Com * State) (s : State),
          CEval cs1 (inl cs2) -> CEval' cs2 s -> CEval' cs1 s.

Hint Constructors CEval'.

(*
Lemma ceval_CEval' :
  forall (n : nat) (c : Com) (s1 s2 : State),
    ceval n c s1 = Some s2 -> CEval' (c, s1) s2.
Proof.
  intros n c s1.
  functional induction ceval n c s1; intros; inv H; eauto.
    constructor. Print CEval.
Qed.

Lemma ceval_plus :
  forall (n k : nat) (c : Com) (s1 s2 : State),
    ceval n c s1 = Some s2 -> ceval (n + k) c s1 = Some s2.
Proof.
  induction n as [| n']; cbn; intros.
    inv H.
    destruct c; auto.
      destruct (ceval n' c1 s1) eqn: Heq.
        erewrite IHn'; eauto.
        inv H.
      destruct (beval b s1) eqn: Hb; eauto.
      destruct (beval b s1) eqn: Hb; eauto.
        destruct (ceval n' c s1) eqn: Heq.
          erewrite IHn'; eauto.
          inv H.
Qed.

Lemma CEval_ceval :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 -> exists n : nat, ceval n c s1 = Some s2.
Proof.
  induction 1.
    exists 1. cbn. reflexivity.
    exists 1. cbn. do 2 f_equal. apply AEval_aeval. assumption.
    destruct IHCEval1 as [n1 IH1], IHCEval2 as [n2 IH2].
      exists (S (n1 + n2)). (* Should be S (max n1 n2) *)
      cbn. rewrite (ceval_plus n1 n2 _ _ _ IH1), plus_comm.
        apply ceval_plus. assumption.
    destruct IHCEval as [n IH]. exists (S n). cbn.
      apply BEval_beval in H. rewrite H. assumption.
    destruct IHCEval as [n IH]. exists (S n). cbn.
      apply BEval_beval in H. rewrite H. assumption.
    exists 1. cbn. apply BEval_beval in H. rewrite H. reflexivity.
    destruct IHCEval1 as [n1 IH1], IHCEval2 as [n2 IH2].
      exists (S (n1 + n2)). cbn. (* Should be S (max n1 n2) *)
      apply BEval_beval in H. rewrite H.
      rewrite (ceval_plus _ _ _ _ _ IH1), plus_comm.
      apply ceval_plus. assumption.
Qed.

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

(* Program equivalence. *)

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

(* TODO: for loop *)

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
  intros c1 c2 H G. revert c1 c2 H.
  induction G; cbn; intros.
    assumption.
    all: unfold equivalent in *; split; intros.
      inv H0. econstructor.
        rewrite IHG; eauto. firstorder.
        assumption.
      inv H0. econstructor; rewrite 1?IHG; eauto.
      inv H0. econstructor; rewrite 1?IHG; eauto. firstorder.
      inv H0. econstructor; rewrite 1?IHG; eauto.
      inv H0.
        econstructor; rewrite 1?IHG; eauto.
        apply EvalIfTrue; eauto. rewrite IHG; eauto. firstorder.
      inv H0.
        econstructor; rewrite 1?IHG; eauto.
        apply EvalIfTrue; eauto. rewrite IHG; eauto.
      inv H0.
        econstructor; rewrite 1?IHG; eauto. firstorder.
        apply EvalIfTrue; eauto.
      inv H0.
        econstructor; rewrite 1?IHG; eauto.
        firstorder.
      remember (While b (put G c1)) as w. revert Heqw.
      induction H0; intro; inv Heqw.
        eauto.
        econstructor; eauto. rewrite IHG; eauto. firstorder.
      remember (While b (put G c2)) as w. revert Heqw.
      induction H0; intro; inv Heqw.
        eauto.
        econstructor; eauto. rewrite IHG; eauto.
Restart.
  intros c1 c2 H G. revert c1 c2 H.
  induction G; cbn; intros; eauto;
  unfold equivalent in *; split; intros;
  match goal with
      | H : CEval ?c _ _ |- _ =>
          let c' := fresh "c" in
          let Heqc' := fresh "Heq" c' in
            remember c as c'; revert Heqc';
            induction H; intros; inv Heqc'
  end; eauto.
    5-6: apply EvalIfTrue; rewrite 1?IHG; eauto; firstorder.
    all: econstructor; rewrite 1?IHG; eauto; firstorder.
Qed.

(** [equivalent] is a congruence *)

Lemma equivalent_Seq_l :
  forall c c1 c2 : Com,
    c1 ~ c2 -> Seq c1 c ~ Seq c2 c.
Proof.
  unfold equivalent. split; intros.
    inv H0. econstructor.
      rewrite <- H. eassumption.
      assumption.
    inv H0. econstructor.
      rewrite H. eassumption.
      assumption.
Qed.

Lemma equivalent_Seq_r :
  forall c c1 c2 : Com,
    c1 ~ c2 -> Seq c c1 ~ Seq c c2.
Proof.
  unfold equivalent. split; intros.
    inv H0. econstructor.
      eassumption.
      rewrite <- H. eassumption.
    inv H0. econstructor.
      eassumption.
      rewrite H. eassumption.
Qed.

Lemma equivalent_If_l :
  forall (b : BExp) (c c1 c2 : Com),
    c1 ~ c2 -> If b c1 c ~ If b c2 c.
Proof.
  unfold equivalent. split; intros.
    inv H0.
      constructor; assumption.
      apply EvalIfTrue.
        assumption.
        rewrite <- H. assumption.
    inv H0.
      constructor; assumption.
      apply EvalIfTrue.
        assumption.
        rewrite H. assumption.
Qed.

Lemma equivalent_If_r :
  forall (b : BExp) (c c1 c2 : Com),
    c1 ~ c2 -> If b c c1 ~ If b c c2.
Proof.
  unfold equivalent. split; intros.
    inv H0.
      constructor.
        assumption.
        rewrite <- H. assumption.
      apply EvalIfTrue; assumption.
    inv H0.
      constructor.
        assumption.
        rewrite H. assumption.
      apply EvalIfTrue; assumption.
Qed.

Lemma equivalent_While :
  forall (b : BExp) (c c1 c2 : Com),
    c1 ~ c2 -> While b c1 ~ While b c2.
Proof.
  unfold equivalent. split; intros.
    remember (While b c1) as w. revert Heqw. induction H0; intro; inv Heqw.
      constructor. assumption.
      eapply EvalWhileTrue.
        assumption.
        rewrite <- H. eassumption.
        apply IHCEval2. reflexivity.
    remember (While b c2) as w. revert Heqw. induction H0; intro; inv Heqw.
      constructor. assumption.
      eapply EvalWhileTrue.
        assumption.
        rewrite H. eassumption.
        apply IHCEval2. reflexivity.
Qed.

(** * Observational equivalence *)

Definition Observation (A : Type) : Type := Com -> A.

Definition oequiv {A : Type} (c1 c2 : Com) : Prop :=
  forall (G : Context) (f : Observation A),
    f (put G c1) = f (put G c2).
*)

*)