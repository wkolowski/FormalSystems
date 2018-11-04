Add Rec LoadPath "~/Code/Coq".

Require Export Syntax.

Require Imp.Smallstep.
Require Imp.Bigstep.

Lemma Bigstep_Smallstep_AExp :
  forall (s : State) (a : AExp) (n : nat),
    Bigstep.AEval a s n <-> Smallstep.AEvals s a (AConst n).
Proof.
  split; intro.
    apply Bigstep.AEval_aeval in H. apply Smallstep.aeval_AEvals. assumption.
    apply Smallstep.AEvals_aeval in H. apply Bigstep.aeval_AEval. assumption.
Qed.

Lemma Bigstep_Smallstep_BExp :
  forall (s : State) (e : BExp) (b : bool),
    Bigstep.BEval e s b <-> Smallstep.BEvals s e (BConst b).
Proof.
  split; intro.
    apply Bigstep.BEval_beval in H. apply Smallstep.beval_BEvals. assumption.
    apply Smallstep.BEvals_beval in H. apply Bigstep.beval_BEval. assumption.
Qed.

Lemma Bigstep_Smallstep_Com :
  forall (c : Com) (s1 s2 : State),
    Bigstep.CEval c s1 s2 <-> Smallstep.CEvals (c, s1) (Skip, s2).
Proof.
  split; intro.
    apply Bigstep.CEval_ceval in H. destruct H as [n H].
      eapply Smallstep.ceval_CEvals. eassumption.
    apply Smallstep.CEvals_ceval in H. destruct H as [n H].
      apply Bigstep.ceval_CEval with n. assumption.
Qed.