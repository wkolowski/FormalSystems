From FormalSystems Require Export Bigstep.

(** Compatibility (acompatible, bcompatible, wcompatible, ccompatible) *)

Lemma CEval_not_In_fvw_eq :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 -> forall x : Atom, ~ In x (fvw c) -> s1 x = s2 x.
Proof.
  induction 1; cbn in *; intros;
    rewrite ?IHCEval, ?IHCEval1, ?IHCEval2; try now auto.
  unfold changeState.
  now decide (v = x); firstorder.
Qed.

Lemma CEval_not_In_fv_eq :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 -> forall x : Atom, ~ In x (fv c) -> s1 x = s2 x.
Proof.
  induction 1; cbn in *; intros;
    rewrite ?IHCEval, ?IHCEval1, ?IHCEval2; try now auto 7.
  unfold changeState.
  now decide (v = x); firstorder.
Qed.

#[global] Hint Unfold bcompatible : core.

Lemma CEval_ccompatible :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 ->
    forall {s1' s2' : State},
      CEval c s1' s2' ->
        ccompatible c s1 s1' -> ccompatible c s2 s2'.
Proof.
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
  unfold equivalent.
  split; intros.
  - remember (While b c) as w; revert b c Heqw.
    now induction H; intros; inversion Heqw; subst; eauto.
  - now inversion H; subst; inversion H6; subst; eauto.
Defined.

(** [equivalent] is an equivalence relation. *)

#[global] Instance Equivalence_equivalent :
  Equivalence equivalent.
Proof.
  split; [easy .. |].
  unfold equivalent.
  intros c1 c2 c3 H12 H23 s1 s2.
  now rewrite H12, H23.
Qed.

(** [equivalent] is a congruence. *)

Lemma equivalent_Skip :
  Skip ~ Skip.
Proof.
  easy.
Qed.

Lemma equivalent_Seq_l :
  forall c c1 c2 : Com,
    c1 ~ c2 -> Seq c1 c ~ Seq c2 c.
Proof.
  unfold equivalent.
  intros c c1 c2 Hequiv s1 s2.
  split; inversion 1; subst.
  - econstructor; [| now eauto].
    now rewrite <- Hequiv.
  - econstructor; [| now eauto].
    now rewrite Hequiv.
Qed.

Lemma equivalent_Seq_r :
  forall c c1 c2 : Com,
    c1 ~ c2 -> Seq c c1 ~ Seq c c2.
Proof.
  unfold equivalent.
  intros c c1 c2 Hequiv s1 s2.
  split; inversion 1; subst.
  - econstructor; [now eauto |].
    now rewrite <- Hequiv.
  - econstructor; [now eauto |].
    now rewrite Hequiv.
Qed.

Lemma equivalent_If_l :
  forall (b : BExp) (c c1 c2 : Com),
    c1 ~ c2 -> If b c1 c ~ If b c2 c.
Proof.
  unfold equivalent.
  intros b c c1 c2 Hequiv s1 s2.
  split.
  - inversion 1; subst; [now auto |].
    apply EvalIfTrue; [easy |].
    now rewrite <- Hequiv.
  - inversion 1; subst; [now auto |].
    apply EvalIfTrue; [easy |].
    now rewrite Hequiv.
Qed.

Lemma equivalent_If_r :
  forall (b : BExp) (c c1 c2 : Com),
    c1 ~ c2 -> If b c c1 ~ If b c c2.
Proof.
  unfold equivalent.
  intros b c c1 c2 Hequiv s1 s2.
  split.
  - inversion 1; subst; [| now auto].
    apply EvalIfFalse; [easy |].
    now rewrite <- Hequiv.
  - inversion 1; subst; [| now auto].
    apply EvalIfFalse; [easy |].
    now rewrite Hequiv.
Qed.

Lemma equivalent_While :
  forall (b : BExp) (c1 c2 : Com),
    c1 ~ c2 -> While b c1 ~ While b c2.
Proof.
  unfold equivalent.
  intros b c1 c2 Hequiv s1 s2.
  split; intros Heval.
  - remember (While b c1) as w; revert Heqw.
    induction Heval; inversion 1; subst; [now auto |].
    eapply EvalWhileTrue; [easy | |].
    + now apply Hequiv, Heval1.
    + now apply IHHeval2.
  - remember (While b c2) as w; revert Heqw.
    induction Heval; inversion 1; subst; [now auto |].
    eapply EvalWhileTrue; [easy | |].
    + now apply Hequiv, Heval1.
    + now apply IHHeval2.
Qed.

(** * Evaluation contexts *)

Inductive Context : Type :=
| CContext : Context
| CSeqL : Context -> Com -> Context
| CSeqR : Com -> Context -> Context
| CIfL : BExp -> Context -> Com -> Context
| CIfR : BExp -> Com -> Context -> Context
| CWhile : BExp -> Context -> Context.

Fixpoint put (G : Context) (c : Com) : Com :=
match G with
| CContext     => c
| CSeqL G' c'  => Seq (put G' c) c'
| CSeqR c' G'  => Seq c' (put G' c)
| CIfL b G' c' => If b (put G' c) c'
| CIfR b c' G' => If b c' (put G' c)
| CWhile b G'  => While b (put G' c)
end.

Lemma equivalent_in_Context :
  forall c1 c2 : Com,
    c1 ~ c2 -> forall G : Context, put G c1 ~ put G c2.
Proof.
  intros c1 c2 H G; revert c1 c2 H.
  induction G; cbn; intros; [easy | ..].
  - now apply equivalent_Seq_l, IHG.
  - now apply equivalent_Seq_r, IHG.
  - now apply equivalent_If_l, IHG.
  - now apply equivalent_If_r, IHG.
  - now apply equivalent_While, IHG.
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
  intros s.
  cofix IH.
  now eapply NT_WhileSelf.
Qed.
