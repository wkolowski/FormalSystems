Require Export Bigstep.

(** Compatibility (acompatible, bcompatible, wcompatible, ccompatible) *)

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

Global Hint Unfold bcompatible : core.

Lemma CEval_ccompatible :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 ->
    forall {s1' s2' : State},
      CEval c s1' s2' ->
        ccompatible c s1 s1' -> ccompatible c s2 s2'.
Proof.
  unfold ccompatible.
  induction 1; cbn; intros.
    inv H1.
    inv H0. unfold changeState. inv H2.
      destruct (dec_spec x x).
        eapply AEval_acompatible_det; eauto.
        contradiction.
      destruct (dec_spec v x).
        eapply AEval_acompatible_det; eauto.
        auto.
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
      apply EvalIfTrue.
        assumption.
        rewrite <- H. assumption.
    inv H0.
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
    inv H0.
      constructor.
        assumption.
        rewrite H. assumption.
Qed.

Lemma equivalent_While :
  forall (b : BExp) (c c1 c2 : Com),
    c1 ~ c2 -> While b c1 ~ While b c2.
Proof.
  unfold equivalent. split; intros.
    remember (While b c1) as w. revert Heqw. induction H0; intro; inv Heqw.
      eapply EvalWhileTrue.
        assumption.
        rewrite <- H. eassumption.
        apply IHCEval2. reflexivity.
    remember (While b c2) as w. revert Heqw. induction H0; intro; inv Heqw.
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

(** * Nontermination *)

CoInductive NonTerm : Com -> State -> Prop :=
    | NT_SeqL :
        forall (c1 c2 : Com) (s : State),
          NonTerm c1 s -> NonTerm (Seq c1 c2) s
    | NT_SeqR :
        forall (c1 c2 : Com) (s1 s2 : State),
          CEval c1 s1 s2 -> NonTerm c2 s2 -> NonTerm (Seq c1 c2) s1
    | NT_IfTrue :
        forall (b : BExp) (c1 c2 : Com) (s : State),
          BEval b s true -> NonTerm c1 s -> NonTerm (If b c1 c2) s
    | NT_IfFalse :
        forall (b : BExp) (c1 c2 : Com) (s : State),
          BEval b s false -> NonTerm c2 s -> NonTerm (If b c1 c2) s
    | NT_WhileBody :
        forall (b : BExp) (c : Com) (s : State),
          BEval b s true -> NonTerm c s -> NonTerm (While b c) s
    | NT_WhileSelf :
        forall (b : BExp) (c : Com) (s1 s2 : State),
          BEval b s1 true -> CEval c s1 s2 -> NonTerm (While b c) s2 ->
            NonTerm (While b c) s1.

Lemma NT_While_true_do_Skip :
  forall s : State,
    NonTerm (While (BConst true) Skip) s.
Proof.
  intro. cofix IH. eapply NT_WhileSelf.
    auto.
    auto.
    assumption.
Qed.