From FormalSystems Require Export Imp.Syntax.
From FormalSystems Require Imp.Smallstep.
From FormalSystems Require Imp.Bigstep.

Lemma Bigstep_Smallstep_AExp :
  forall (s : State) (a : AExp) (n : nat),
    Bigstep.AEval a s n <-> Smallstep.AEvals s a (AConst n).
Proof.
  split; intros.
  - apply Bigstep.AEval_aeval in H.
    now apply Smallstep.aeval_AEvals.
  - apply Smallstep.AEvals_aeval in H.
    now apply Bigstep.aeval_AEval.
Qed.

Lemma Bigstep_Smallstep_BExp :
  forall (s : State) (e : BExp) (b : bool),
    Bigstep.BEval e s b <-> Smallstep.BEvals s e (BConst b).
Proof.
  split; intros.
  - apply Bigstep.BEval_beval in H.
    now apply Smallstep.beval_BEvals.
  - apply Smallstep.BEvals_beval in H.
    now apply Bigstep.beval_BEval.
Qed.

Lemma Bigstep_Smallstep_Com :
  forall (c : Com) (s1 s2 : State),
    Bigstep.CEval c s1 s2 <-> Smallstep.CEvals (c, s1) (Skip, s2).
Proof.
  split; intro.
  - apply Bigstep.CEval_ceval in H as [n H].
    now apply Smallstep.ceval_CEvals in H.
  - apply Smallstep.CEvals_ceval in H as [n H].
    now apply Bigstep.ceval_CEval with n.
Qed.
