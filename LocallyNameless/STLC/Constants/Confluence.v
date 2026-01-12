From FormalSystems Require Export LocallyNameless.STLC.Constants.

(* * Confluence *)

(* ** Contraction *)

Inductive FullContraction : Tm -> Tm -> Prop :=
| FullContraction_app_abs :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : forall x : Atom, x # l -> lc (t1 {{ 0 ~> x }}))
    (Hlc2 : lc t2),
    FullContraction (app (abs t1) t2) (t1 {[ 0 ~> t2 ]}).

#[export] Hint Constructors FullContraction : core.

Lemma lc_FullContraction_l :
  forall t t' : Tm,
    FullContraction t t' -> lc t.
Proof.
  now inversion 1; eauto.
Qed.

Lemma lc_FullContraction_r :
  forall t t' : Tm,
    FullContraction t t' -> lc t'.
Proof.
  now inversion 1; eauto.
Qed.

#[export] Hint Immediate lc_FullContraction_l lc_FullContraction_r : core.

Lemma FullContraction_det :
  forall t t1 t2 : Tm,
    FullContraction t t1 -> FullContraction t t2 -> t1 = t2.
Proof.
  now induction 1; inversion 1; auto.
Qed.

Lemma FullContraction_subst :
  forall (t t' u : Tm) (x : Atom),
    lc u ->
    FullContraction t t' ->
    FullContraction (t [[ x := u ]]) (t' [[ x := u]]).
Proof.
  inversion 2; cbn.
  rewrite open'_subst by easy.
  constructor 1 with (x :: l); [| now apply lc_subst].
  now intros y Hy; rewrite subst_open; auto.
Qed.

#[export] Hint Resolve FullContraction_det FullContraction_subst : core.

Inductive FullStep : Tm -> Tm -> Prop :=
| FullStep_FullContraction :
  forall t t' : Tm,
    FullContraction t t' ->
    FullStep t t'
| FullStep_abs :
  forall (t t' : Tm) (l : list Atom)
    (Hfs' : forall x : Atom, x # l -> FullStep (t {{ 0 ~> x }}) (t' {{ 0 ~> x }})),
    FullStep (abs t) (abs t')
| FullStep_app_l :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    FullStep t1 t1' ->
    FullStep (app t1 t2) (app t1' t2)
| FullStep_app_r :
  forall (t1 t1 t2 t2' : Tm),
    lc t1 ->
    FullStep t2 t2' ->
    FullStep (app t1 t2) (app t1 t2').

#[export] Hint Constructors FullStep : core.

Lemma lc_FullStep_l :
  forall t t' : Tm,
    FullStep t t' -> lc t.
Proof.
  now induction 1; eauto.
Qed.

Lemma lc_FullStep_r :
  forall t t' : Tm,
    FullStep t t' -> lc t'.
Proof.
  now induction 1; eauto.
Qed.

#[export] Hint Resolve lc_FullStep_l lc_FullStep_r : core.

Lemma FullStep_subst :
  forall (t t' u : Tm) (x : Atom),
    lc u ->
    FullStep t t' ->
    FullStep (t [[ x := u ]]) (t' [[ x := u]]).
Proof.
  intros t t' u x Hlc Hfs; revert u x Hlc.
  induction Hfs; cbn; intros.
  - constructor.
    now apply FullContraction_subst.
  - constructor 2 with (x :: l); intros y Hy.
    now rewrite !subst_open; auto.
  - now constructor 3; eauto.
  - now constructor 4; eauto.
Restart.
  intros t t' u x Hlc Hfs; revert u x Hlc.
  induction Hfs; cbn; intros; only 1, 3-4: eauto.
  constructor 2 with (x :: l); intros y Hy.
  now rewrite !subst_open; auto.
Qed.

Lemma FullStep_rename :
  forall (t t' : Tm) (i : nat) (x y : Atom),
    x # fv t ++ fv t' ->
    FullStep (t {{ i ~> x }}) (t' {{ i ~> x }}) ->
      FullStep (t {{ i ~> y }}) (t' {{ i ~> y }}).
Proof.
  intros t t' i x y Hx Hfs.
  rewrite <- 2!open'_atom, 2!open'_spec with (x := x) by auto.
  now apply FullStep_subst.
Qed.

#[export] Hint Resolve FullStep_subst FullStep_rename : core.

Inductive FullStep' : Tm -> Tm -> Prop :=
| FullStep'_FullContraction :
  forall t t' : Tm,
    FullContraction t t' ->
    FullStep' t t'
| FullStep'_abs :
  forall (t t' : Tm) (l : list Atom)
    (Hfs' : forall x : Atom, x # l -> FullStep' (t {{ 0 ~> x }}) t'),
    forall x : Atom, x # l ->
    FullStep' (abs t) (abs (t {{ 0 <~ x }}))
| FullStep'_app_l :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    FullStep' t1 t1' ->
    FullStep' (app t1 t2) (app t1' t2)
| FullStep'_app_r :
  forall (t1 t1 t2 t2' : Tm),
    lc t1 ->
    FullStep' t2 t2' ->
    FullStep' (app t1 t2) (app t1 t2').

#[export] Hint Constructors FullStep' : core.

Lemma FullStep'_spec :
  forall (t1 t2 : Tm),
    FullStep' t1 t2 <-> FullStep t1 t2.
Proof.
  split.
  - induction 1; only 1, 3-4: now auto.
    apply FullStep_abs with l; intros y Hy.
    admit.
  - induction 1; only 1, 3-4: now auto.
    admit.
Abort.

Inductive MultiStep : Tm -> Tm -> Prop :=
| MultiStep_refl :
  forall (t : Tm),
    lc t ->
    MultiStep t t
| MultiStep_step_trans :
  forall (t1 t2 t3 : Tm),
    FullStep t1 t2 ->
    MultiStep t2 t3 ->
    MultiStep t1 t3.

#[export] Hint Constructors MultiStep : core.

Require Import Coq.Classes.RelationClasses.

#[export] Instance Transitive_MultiStep : Transitive MultiStep.
Proof.
  now induction 1; eauto.
Qed.

Lemma lc_MultiStep_l :
  forall t t' : Tm,
    MultiStep t t' -> lc t.
Proof.
  now induction 1; eauto.
Qed.

Lemma lc_MultiStep_r :
  forall t t' : Tm,
    MultiStep t t' -> lc t'.
Proof.
  now induction 1; eauto.
Qed.

#[export] Hint Resolve lc_MultiStep_l lc_MultiStep_r : core.

Lemma MultiStep_subst :
  forall (t t' u : Tm) (x : Atom),
    lc u ->
    MultiStep t t' ->
    MultiStep (t [[ x := u ]]) (t' [[ x := u]]).
Proof.
  intros t t' u x Hlc Hms; revert u x Hlc.
  induction Hms; cbn; intros; [now eauto |].
  constructor 2 with (t2 [[ x := u ]]).
  - now apply FullStep_subst.
  - now apply IHHms.
Restart.
  now induction 2; eauto.
Qed.

Lemma MultiStep_rename :
  forall (t t' : Tm) (i : nat) (x y : Atom),
    x # fv t ++ fv t' ->
    MultiStep (t {{ i ~> x }}) (t' {{ i ~> x }}) ->
      MultiStep (t {{ i ~> y }}) (t' {{ i ~> y }}).
Proof.
  intros t t' i x y Hx Hfs.
  rewrite <- 2!open'_atom, 2!open'_spec with (x := x) by auto.
  now apply MultiStep_subst.
Qed.

#[export] Hint Resolve MultiStep_subst MultiStep_rename : core.

Lemma MultiStep_FullStep :
  forall t1 t2 : Tm,
    FullStep t1 t2 -> MultiStep t1 t2.
Proof.
  now eauto.
Qed.


Lemma standardize_FullContraction :
  forall (t1 t2 : Tm) (i : nat) (x : Atom),
    FullContraction (t1 {{ i ~> x }}) t2 ->
      exists t2' : Tm, t2 = t2' {{ i ~> x }}.
Proof.
  intros * Hfc.
  inversion Hfc; subst; clear Hfc.
  destruct t1; cbn in H0; try easy; [now decide_all |].
  injection H0 as [= H1 ->].
  exists (t0 {[ 0 ~> t1_2 {{ i ~> x }} ]} {{ i <~ x }}).
  rewrite close_open_LocallyClosed; [easy |].
  apply LocallyClosed_le with 0; [now lia |].
  apply LocallyClosed_lc.
  rewrite (open'_spec _ _ (fresh (l ++ fv t0))) by auto.
  now apply lc_subst; auto.
Qed.

Check FullStep_rename.

Lemma standardize_FullStep :
  forall (t1 t2 : Tm) (i : nat) (x : Atom),
    FullStep (t1 {{ i ~> x }}) t2 ->
      exists t2' : Tm, t2 = t2' {{ i ~> x }}.
Proof.
  intros.
  exists (t2 {{ i <~ x }}).
  rewrite close_open_eq.
  now rewrite open_lc; eauto.
Qed.

Lemma standardize_FullStep' :
  forall (t1 t2 : Tm) (i : nat) (x : Atom),
    FullStep (t1 {{ i ~> x }}) t2 ->
    FullStep (t1 {{ i ~> x }}) (t2 {{ i ~> x }}).
Proof.
  now intros; rewrite (open_lc t2); eauto.
Qed.

Lemma subst_atom :
  forall (t : Tm) (i : nat) (x y : Atom),
    lc t -> t [[ x := y ]] = t {{ i <~ x }} {{ i ~> y }}.
Proof.
  intros t i x y Hlc; revert i x y.
  induction Hlc; cbn; intros;
    rewrite <- ?IHHlc, <- ?IHHlc1, <- ?IHHlc2; try now auto.
  pose (l' := (x :: y :: l ++ fv t' ++
    fv (t' [[x := y]]) ++ fv (t' {{S i <~ x}} {{S i ~> y}}))).
  assert (Hl' := fresh_spec l').
  apply (abs_eq _ _ (fresh l')); subst l'; [now auto |].
  rewrite subst_open by auto.
  rewrite open_open_neq by auto.
  rewrite <- (open_close_neq _ 0 (S i)); [now auto.. |].
  now rewrite Fresh_cons in Hl'.
Qed.

Lemma fv_close :
  forall (t : Tm) (i : nat) (x : Atom),
    x # fv (t {{ i <~ x }}).
Proof.
  induction t; cbn; intros; auto.
  - decide_all.
    now apply Fresh_singl.
  - now apply Fresh_nil.
  - now apply Fresh_app; auto.
  - now apply Fresh_nil.
Qed.

Lemma MultiStep_abs :
  forall t t' : Tm,
    (exists l : list Atom, forall x : Atom, x # l ->
      MultiStep (t {{ 0 ~> x }}) (t' {{ 0 ~> x }})) ->
        MultiStep (abs t) (abs t').
Proof.
  intros t t' [l Hms].
  pose (x := fresh (l ++ fv t ++ fv t')).
  assert (Hx : x # l ++ fv t ++ fv t') by apply fresh_spec.
  specialize (Hms x ltac:(auto)) as Hms'.
  clearbody x.
  remember (t {{ 0 ~> x }}) as u.
  remember (t' {{ 0 ~> x }}) as u'.
  clear Hms.
  revert t t' Hx Hequ Hequ'.
  induction Hms'; intros; subst.
  - replace (abs t') with (abs t0).
    + apply MultiStep_refl.
      apply lc_abs with l; intros y Hy.
      now apply lc_open_invariant with x.
    + now eapply abs_eq; cycle 1; eauto.
  - constructor 2 with (abs (t2 {{ 0 <~ x }})).
    + constructor 2 with l.
      intros y Hy.
      rewrite <- (subst_atom _ 0) by eauto.
      apply (FullStep_subst _ _ y x) in H; [| easy].
      now rewrite <- !open'_spec, !open'_atom in H by auto.
    + apply IHHms'.
      * rewrite !Fresh_app.
        repeat split; try now auto.
        now apply fv_close.
      * rewrite close_open_eq.
        now rewrite (open_lc t2); eauto.
      * easy.
Qed.

Print Assumptions MultiStep_abs.

Lemma MultiStep_abs' :
  forall t t' : Tm,
    MultiStep t t' -> MultiStep (abs t) (abs t').
Proof.
  induction 1.
  - apply MultiStep_refl.
    now apply lc_abs with []; eauto.
  - transitivity (abs t2); [| easy].
    apply MultiStep_FullStep.
    apply FullStep_abs with []; intros x _.
    now rewrite 2!open_lc by eauto.
Qed.

Lemma MultiStep_app_l :
  forall t1 t1' t2 : Tm,
    lc t2 ->
    MultiStep t1 t1' ->
    MultiStep (app t1 t2) (app t1' t2).
Proof.
  now induction 2; eauto.
Qed.

Lemma MultiStep_app_r :
  forall t1 t2 t2' : Tm,
    lc t1 ->
    MultiStep t2 t2' ->
    MultiStep (app t1 t2) (app t1 t2').
Proof.
  now induction 2; eauto.
Qed.

Lemma MultiStep_app :
  forall t1 t1' t2 t2' : Tm,
    MultiStep t1 t1' ->
    MultiStep t2 t2' ->
    MultiStep (app t1 t2) (app t1' t2').
Proof.
  induction 2.
  - now apply MultiStep_app_l.
  - transitivity (app t1 t2); [| easy].
    apply MultiStep_app_r; [| now eauto].
    now apply lc_MultiStep_l in H.
Qed.

Lemma MultiStep_app_abs :
  forall (t1 t2 t3 : Tm) (l : list Atom),
    (forall x : Atom, x # l -> lc (t1 {{ 0 ~> x }})) ->
    lc t2 ->
    MultiStep (t1 {[ 0 ~> t2 ]}) t3 ->
    MultiStep (app (abs t1) t2) t3.
Proof.
  intros t1 t2 t3 l Hlc1 Hlc2 Hms.
  remember (t1 {[ 0 ~> t2 ]}) as t1'.
  revert t1 t2 Hlc1 Hlc2 Heqt1'.
  now induction Hms; intros; subst; eauto.
Qed.

#[export] Hint Resolve
  MultiStep_FullStep
  MultiStep_abs MultiStep_abs'
  MultiStep_app_l MultiStep_app_r MultiStep_app
    : core.

Inductive ParallelStep : Tm -> Tm -> Prop :=
| ParallelStep_fvar :
  forall (x : Atom),
    ParallelStep x x
| ParallelStep_abs :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hps' : forall x : Atom, x # l -> ParallelStep (t1 {{ 0 ~> x }}) (t2 {{ 0 ~> x }})),
    ParallelStep (abs t1) (abs t2)
| ParallelStep_app :
  forall (t1 t1' t2 t2' : Tm),
    ParallelStep t1 t1' ->
    ParallelStep t2 t2' ->
    ParallelStep (app t1 t2) (app t1' t2')
| ParallelStep_app_abs :
  forall (t1 t1' t2 t2' : Tm) (l : list Atom)
    (Hps1 : forall x : Atom, x # l -> ParallelStep (t1 {{ 0 ~> x }}) (t1' {{ 0 ~> x }}))
    (Hps2 : ParallelStep t2 t2'),
    ParallelStep (app (abs t1) t2) (t1' {[ 0 ~> t2' ]}).

#[export] Hint Constructors ParallelStep : core.

Lemma ParallelStep_refl :
  forall t : Tm,
    lc t ->
    ParallelStep t t.
Proof.
  induction 1; eauto.
Admitted. (* Will work after we add more cases/remove terms *)

Lemma lc_ParallelStep_l :
  forall t t' : Tm,
    ParallelStep t t' -> lc t.
Proof.
  now induction 1; eauto.
Qed.

Lemma lc_ParallelStep_r :
  forall t t' : Tm,
    ParallelStep t t' -> lc t'.
Proof.
  now induction 1; eauto.
Qed.

#[export] Hint Resolve ParallelStep_refl lc_ParallelStep_l lc_ParallelStep_r : core.

Lemma ParallelStep_subst :
  forall (t t' u : Tm) (x : Atom),
    lc u ->
    ParallelStep t t' ->
    ParallelStep (t [[ x := u ]]) (t' [[ x := u]]).
Proof.
  intros t t' u x Hlc Hps; revert u x Hlc.
  induction Hps; cbn; intros.
  - now decide_all; eauto.
  - constructor 2 with (x :: l); intros y Hy.
    now rewrite !subst_open; auto.
  - now constructor 3; eauto.
  - rewrite open'_subst by easy.
    constructor 4 with (x :: l); [| now apply IHHps].
    now intros y Hy; rewrite 2!subst_open; auto.
Qed.

Lemma ParallelStep_rename :
  forall (t t' : Tm) (i : nat) (x y : Atom),
    x # fv t ++ fv t' ->
    ParallelStep (t {{ i ~> x }}) (t' {{ i ~> x }}) ->
      ParallelStep (t {{ i ~> y }}) (t' {{ i ~> y }}).
Proof.
  intros t t' i x y Hx Hfs.
  rewrite <- 2!open'_atom, 2!open'_spec with (x := x) by auto.
  now apply ParallelStep_subst.
Qed.

#[export] Hint Resolve ParallelStep_subst ParallelStep_rename : core.

Lemma ParallelStep_FullContraction :
  forall t1 t2 : Tm,
    FullContraction t1 t2 -> ParallelStep t1 t2.
Proof.
  now inversion 1; eauto.
Qed.

Lemma ParallelStep_FullStep :
  forall t1 t2 : Tm,
    FullStep t1 t2 -> ParallelStep t1 t2.
Proof.
  induction 1; try now eauto.
  now apply ParallelStep_FullContraction.
Qed.

Lemma MultiStep_ParallelStep :
  forall t1 t2 : Tm,
    ParallelStep t1 t2 -> MultiStep t1 t2.
Proof.
  induction 1; eauto.
  transitivity (app (abs t1') t2); [now apply MultiStep_app; eauto |].
  transitivity (app (abs t1') t2'); [now apply MultiStep_app; eauto |].
  now eauto 7.
Qed.

#[export] Hint Resolve ParallelStep_FullStep MultiStep_ParallelStep : core.

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

Axiom development : Tm -> Tm.

Axiom development_spec :
  forall t1 t2 : Tm,
    ParallelStep t1 t2 -> ParallelStep t2 (development t1).

Lemma confluent_ParallelStep :
  forall t t1 t2 : Tm,
    ParallelStep t t1 -> ParallelStep t t2 ->
      ParallelStep t1 (development t) /\ ParallelStep t2 (development t).
Proof.
  intros t t1 t2 Hps1 Hps2.
  now split; apply development_spec.
Qed.

Lemma confluent_ParallelStep_ParallelMultiStep :
  forall t t1 t2 : Tm,
    ParallelStep t t1 -> ParallelMultiStep t t2 ->
      exists t3 : Tm, ParallelMultiStep t1 t3 /\ ParallelMultiStep t2 t3.
Proof.
  intros t t1 t2 H1 H2; revert t1 H1.
  induction H2; intros; [now exists t1; eauto |].
  edestruct (IHParallelMultiStep (development t1)) as [t4 [IH1 IH2] ].
  - now apply development_spec.
  - exists t4; split; [| easy].
    transitivity (development t1); [| easy].
    now apply ParallelMultiStep_ParallelStep, development_spec.
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
