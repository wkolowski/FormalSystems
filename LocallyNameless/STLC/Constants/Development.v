From FormalSystems Require Export LocallyNameless.STLC.Constants.Confluence.

Axiom Development : Tm -> Tm -> Prop.

Axiom Development_spec :
  forall t1 t2 t3 : Tm,
    Development t1 t3 ->
    ParallelStep t1 t2 -> ParallelStep t2 t3.

Lemma confluent_ParallelStep :
  forall t t' t1 t2 : Tm,
    Development t t' ->
    ParallelStep t t1 -> ParallelStep t t2 ->
      ParallelStep t1 t' /\ ParallelStep t2 t'.
Proof.
  intros t t' t1 t2 Hd Hps1 Hps2.
  now split; eapply Development_spec; eauto.
Qed.

Inductive ParallelMultiStep : Tm -> Tm -> Prop :=
| ParallelMultiStep_refl :
  forall (t : Tm),
    lc t ->
    ParallelMultiStep t t
| ParallelMultiStep_step_trans :
  forall (t1 t2 t3 : Tm),
    ParallelStep t1 t2 ->
    ParallelMultiStep t2 t3 ->
    ParallelMultiStep t1 t3.

#[export] Hint Constructors ParallelMultiStep : core.

Require Import Coq.Classes.RelationClasses.

#[export] Instance Transitive_ParallelMultiStep : Transitive ParallelMultiStep.
Proof.
  now induction 1; eauto.
Qed.

Lemma lc_ParallelMultiStep_l :
  forall t t' : Tm,
    ParallelMultiStep t t' -> lc t.
Proof.
  now induction 1; eauto.
Qed.

Lemma lc_ParallelMultiStep_r :
  forall t t' : Tm,
    ParallelMultiStep t t' -> lc t'.
Proof.
  now induction 1; eauto.
Qed.

Lemma ParallelMultiStep_ParallelStep :
  forall t1 t2 : Tm,
    ParallelStep t1 t2 -> ParallelMultiStep t1 t2.
Proof.
  now eauto.
Qed.

#[export] Hint Resolve
  lc_ParallelMultiStep_l lc_ParallelMultiStep_r
  ParallelMultiStep_ParallelStep
    : core.

Lemma ParallelMultiStep_app_l :
  forall t1 t1' t2 : Tm,
    ParallelMultiStep t1 t1' ->
    lc t2 ->
      ParallelMultiStep (app t1 t2) (app t1' t2).
Proof.
  now induction 1; eauto.
Qed.

Lemma ParallelMultiStep_app_r :
  forall t1 t2 t2' : Tm,
    lc t1 ->
    ParallelMultiStep t2 t2' ->
      ParallelMultiStep (app t1 t2) (app t1 t2').
Proof.
  now induction 2; eauto.
Qed.

Lemma ParallelMultiStep_app :
  forall t1 t1' t2 t2' : Tm,
    ParallelMultiStep t1 t1' ->
    ParallelMultiStep t2 t2' ->
      ParallelMultiStep (app t1 t2) (app t1' t2').
Proof.
  intros.
  transitivity (app t1' t2).
  - now apply ParallelMultiStep_app_l; eauto.
  - now apply ParallelMultiStep_app_r; eauto.
Qed.

#[export] Hint Resolve
  ParallelMultiStep_app_l ParallelMultiStep_app_r ParallelMultiStep_app
    : core.

Lemma MultiStep_ParallelMultiStep :
  forall t1 t2 : Tm,
    MultiStep t1 t2 <-> ParallelMultiStep t1 t2.
Proof.
  split.
  - now induction 1; eauto.
  - induction 1; [now eauto |].
    now transitivity t2; eauto.
Qed.

Lemma confluent_ParallelStep_ParallelMultiStep :
  forall t t1 t2 : Tm,
    ParallelStep t t1 -> ParallelMultiStep t t2 ->
      exists t3 : Tm, ParallelMultiStep t1 t3 /\ ParallelMultiStep t2 t3.
Proof.
  intros t t1 t2 H1 H2; revert t1 H1.
  induction H2; intros; [now exists t1; eauto |].
  edestruct (IHParallelMultiStep (Development t1)) as [t4 [IH1 IH2] ].
  - now apply Development_spec.
  - exists t4; split; [| easy].
    transitivity (Development t1); [| easy].
    now apply ParallelMultiStep_ParallelStep, Development_spec.
Qed.

Lemma confluent_ParallelMultiStep :
  forall t t1 t2 : Tm,
    ParallelMultiStep t t1 -> ParallelMultiStep t t2 ->
      exists t3 : Tm, ParallelMultiStep t1 t3 /\ ParallelMultiStep t2 t3.
Proof.
  intros t t1 t2 H1 H2; revert t2 H2.
  induction H1; intros; [now exists t2; eauto |].
  destruct (confluent_ParallelStep_ParallelMultiStep _ _ _ H H2) as [t4 [H24 H04] ].
  edestruct (IHParallelMultiStep _ H24) as [t5 [H35 H45] ].
  exists t5; split; [easy |].
  now transitivity t4.
Qed.

Lemma confluent_Step :
  forall t t1 t2 : Tm,
    MultiStep t t1 -> MultiStep t t2 ->
      exists t3 : Tm, MultiStep t1 t3 /\ MultiStep t2 t3.
Proof.
  setoid_rewrite MultiStep_ParallelMultiStep.
  now apply confluent_ParallelMultiStep.
Qed.

Print Assumptions confluent_Step.
Print Assumptions ParallelStep_refl.
Print Assumptions MultiStep_abs.
Print Assumptions confluent_Step.


