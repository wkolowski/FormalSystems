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

Lemma MultiStep_abs :
  forall t t' : Tm,
    (exists l : list Atom, forall x : Atom, x # l ->
      MultiStep (t {{ 0 ~> x }}) (t' {{ 0 ~> x }})) ->
        MultiStep (abs t) (abs t').
Proof.
  intros t t' [l Hms].
  pose (x := fresh (l ++ fv t ++ fv t')).
  specialize (Hms x ltac:(auto)) as Hms'.
  clearbody x.
  remember (t {{ 0 ~> x }}) as u.
  remember (t' {{ 0 ~> x }}) as u'.
  clear Hms.
  revert t t' Hequ Hequ'.
  induction Hms'; intros; subst.
  - replace (abs t') with (abs t0).
    + apply MultiStep_refl.
      apply lc_abs with l; intros y Hy.
      now apply lc_open_invariant with x.
    + eapply abs_eq; cycle 1; eauto. admit.
  - constructor 2 with (abs (t2 {{ 0 <~ x }})).
    + constructor 2 with l. 
      intros y Hy.
      admit.
    + apply IHHms'; [| easy].
      
specialize (IHHms' (t2 {{ 0 <~ x }}) t').
Admitted.

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

Module development_try1.

Fixpoint development (t : Tm) : Tm :=
match t with
| fvar x          => fvar x
| bvar i          => bvar i
| abs t'          => abs (development t' {{ 0 ~> fresh (fv t') }})
| app (abs t1) t2 => development t1 {[ 0 ~> development t2 ]}
| app t1 t2       => app (development t1) (development t2)
| _               => unit
end.

Lemma development_open :
  forall (t : Tm) (i : nat) (a : Atom),
    lc t ->
    development t {{ i ~> a }} = development (t {{ i ~> a }}).
Proof.
  intros.
  rewrite (open_lc t i a) by easy.
Abort.

Lemma lc_development :
  forall (t : Tm),
    lc t -> lc (development t).
Proof.
  induction 1; cbn; auto.
  - admit.
Abort.

End development_try1.

Module development_try2.

Unset Guard Checking.
Fixpoint development (t : Tm) : Tm :=
match t with
| fvar x          => fvar x
| bvar i          => bvar i
| abs t'          => abs (development t')
| app (abs t1) t2 =>
  let x := fresh (fv t1) in
    development (t1 {{ 0 ~> x }}) [[ x := development t2 ]]
| app t1 t2       => app (development t1) (development t2)
| _               => unit
end.
Set Guard Checking.

Lemma development_open :
  forall (t : Tm) (i : nat) (a : Atom),
    development t {{ i ~> a }} = development (t {{ i ~> a }}).
Proof.
  induction t; cbn; intros; try now auto.
  - now rewrite IHt.
  - destruct t1; cbn in *; rewrite 1?IHt1, 1?IHt2; auto.
    +
Admitted.

Lemma lc_development :
  forall (t : Tm),
    lc t -> lc (development t).
Proof.
  induction 1; cbn; auto.
  - constructor 2 with l; intros x Hx.
Admitted.

Lemma development_spec :
  forall t1 t2 : Tm,
    ParallelStep t1 t2 -> ParallelStep t2 (development t1).
Proof.
  intros t1 t2 Hps.
  assert (lc t2) by eauto.
  induction Hps; cbn.
  - now eauto.
  - apply ParallelStep_abs with l; intros x Hx.
    now rewrite development_open; eauto.
  - destruct t1; cbn in *; try now auto.
    inversion H; subst.
Admitted.

End development_try2.

Module development_try3.

Unset Guard Checking.
Fixpoint development (t : Tm) : Tm :=
match t with
| fvar x          => fvar x
| bvar i          => bvar i
| abs t'          => abs (development t')
| app (abs t1) t2 =>
  let x := fresh (fv t1) in
    development t1 {[ 0 ~> development t2 ]}
| app t1 t2       => app (development t1) (development t2)
| _               => unit
end.
Set Guard Checking.

Lemma development_open :
  forall (t : Tm) (i : nat) (a : Atom),
    development t {{ i ~> a }} = development (t {{ i ~> a }}).
Proof.
  induction t; cbn; intros; auto.
  - now rewrite IHt.
  - destruct t1; cbn in *; rewrite 1?IHt1, 1?IHt2; auto.
    + injection (IHt1 i a) as [= <-].
      rewrite <- IHt2.
Admitted.

Lemma development_spec :
  forall t1 t2 : Tm,
    ParallelStep t1 t2 -> ParallelStep t2 (development t1).
Proof.
  induction 1; cbn.
  - now eauto.
  - apply ParallelStep_abs with l; intros x Hx.
    now rewrite development_open; auto.
  - destruct t1; cbn in *; try now auto.
    inversion H; subst.
    inversion IHParallelStep1; subst; eauto.
  - 
Admitted.

End development_try3.

Module development_try4.

Fixpoint development (i : nat) (t : Tm) : Tm :=
match t with
| fvar x          => fvar x
| bvar j          => bvar j
| abs t'          => abs (development (S i) t')
| app (abs t1) t2 => development (S i) t1 {[ 0 ~> development i t2 ]}
| app t1 t2       => app (development i t1) (development i t2)
| _               => unit
end.

End development_try4.

Module development_try5.

Unset Guard Checking.
Fixpoint development (t : Tm) : Tm :=
match t with
| fvar x          => fvar x
| bvar i          => bvar i
| abs t'          =>
  let x := fresh (fv t') in
    abs (development (t' {{ 0 ~> x }}) {{ 0 <~ x }})
| app (abs t1) t2 =>
  let x := fresh (fv t1) in
    development (t1 {{ 0 ~> x }}) [[ x := development t2 ]]
| app t1 t2       => app (development t1) (development t2)
| _               => unit
end.
Set Guard Checking.

Lemma development_open :
  forall (t : Tm) (i : nat) (a : Atom),
    development t {{ i ~> a }} = development (t {{ i ~> a }}).
Proof.
  induction t; cbn; intros i x; try now auto.
  - admit.
  - destruct t1; cbn in *; rewrite 1?IHt1, 1?IHt2; auto.
    + 
Admitted.

Lemma development_spec :
  forall t1 t2 : Tm,
    ParallelStep t1 t2 -> ParallelStep t2 (development t1).
Proof.
  induction 1; cbn.
  - now eauto.
  - apply ParallelStep_abs with l; intros x Hx.
    apply ParallelStep_rename with (fresh (fv t1 ++ fv t2)).
Admitted.

End development_try5.

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

Inductive Development : Tm -> Tm -> Prop :=
| Development_fvar :
  forall (x : Atom),
    Development x x
| Development_abs :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hps' : forall x : Atom, x # l -> Development (t1 {{ 0 ~> x }}) (t2 {{ 0 ~> x }})),
    Development (abs t1) (abs t2)
| Development_app :
  forall (t1 t1' t2 t2' : Tm),
    (forall u, t1 <> abs u) ->
    Development t1 t1' ->
    Development t2 t2' ->
    Development (app t1 t2) (app t1' t2')
| Development_app_abs :
  forall (t1 t1' t2 t2' : Tm) (l : list Atom)
    (Hps1 : forall x : Atom, x # l -> Development (t1 {{ 0 ~> x }}) (t1' {{ 0 ~> x }}))
    (Hps2 : Development t2 t2'),
    Development (app (abs t1) t2) (t1' {[ 0 ~> t2' ]}).

#[export] Hint Constructors Development : core.

Lemma lc_Development_l :
  forall t t' : Tm,
    Development t t' -> lc t.
Proof.
  now induction 1; eauto.
Qed.

Lemma lc_Development_r :
  forall t t' : Tm,
    Development t t' -> lc t'.
Proof.
  now induction 1; eauto.
Qed.

#[export] Hint Resolve lc_Development_l lc_Development_r : core.

Lemma Development_det :
  forall t t1 t2 : Tm,
    Development t t1 -> Development t t2 -> t1 = t2.
Proof.
  intros t t1 t2 Hd1 Hd2; revert t2 Hd2.
  induction Hd1; inversion 1; subst.
  - easy.
  - now apply abs_eq with (fresh (l ++ l0 ++ fv t2 ++ fv t4)); auto.
  - now erewrite IHHd1_1, IHHd1_2; eauto.
  - now contradiction (H t3).
  - now contradiction (H2 t1).
  - rewrite !(open'_spec _ 0 (fresh (l ++ l0 ++ fv t1' ++ fv t1'0))) by auto.
    now f_equal; auto.
Qed.

Lemma Development_FullContraction :
  forall t1 t2 t3 : Tm,
    FullContraction t1 t2 -> Development t2 t3 -> Development t1 t3.
Proof.
  do 2 inversion 1; subst.
  - rewrite H4.
    constructor 4 with l.
Restart.
  intros t1 t2 t3 H12 H23; revert t1 H12.
  induction H23; intros.
  - admit.
  - inversion H12; subst.
Admitted.

Lemma FullStep_Development :
  forall t1 t2 t3 : Tm,
    FullStep t1 t2 -> Development t2 t3 -> Development t1 t3.
Proof.
  intros t1 t2 t3 Hfs Hd; revert t3 Hd.
  induction Hfs; intros.
  - now eapply Development_FullContraction; eauto.
  - inversion Hd; subst.
    constructor 2 with (l ++ l0); intros x Hx.
    now eapply H; auto.
  - inversion Hd; subst.
    + constructor; [| now auto..].
      intros u [= ->].
      inversion Hfs; subst; [now inversion H0 |].
      now contradiction (H2 t').
    + inversion Hd; subst.
      * now contradiction (H3 t0).
      * 
Restart.
  intros t1 t2 t3 Hfs Hd; revert t1 Hfs.
  induction Hd; intros.
  - inversion Hfs; inversion H; subst.
    destruct t0; cbn in H4; inversion H4; subst; cbn.
Abort.

Lemma MultiStep_Development :
  forall t1 t2 : Tm,
    Development t1 t2 -> MultiStep t1 t2.
Proof.
  induction 1; eauto.
  transitivity (app (abs t1') t2); [now eapply MultiStep_app; eauto |].
  transitivity (app (abs t1') t2'); [now eapply MultiStep_app; eauto |].
  now apply MultiStep_FullStep; constructor; eauto.
Qed.

#[export] Hint Resolve MultiStep_Development : core.
