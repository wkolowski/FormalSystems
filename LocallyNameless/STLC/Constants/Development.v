From FormalSystems Require Export LocallyNameless.STLC.Constants.Confluence.

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
  forall (t1 t1' t1'' t2 t2' : Tm) (l : list Atom)
    (Hps1 : forall x : Atom, x # l -> Development (t1 {{ 0 ~> x }}) (t1' {{ 0 ~> x }}))
    (Hps2 : Development t2 t2')
    (Heq : t1'' = t1' {[ 0 ~> t2' ]}),
    Development (app (abs t1) t2) t1''.
(*
| Development_annot :
  forall (t1 t2 : Tm) (A : Ty)
    (Hd : Development t1 t2),
    Development (annot t1 A) t2
| Development_const :
  forall (c : Const),
    Development c c.
*)

#[export] Hint Constructors Development : core.

Goal Development (app (app (abs 0) (abs 0)) (abs 0)) (app (abs 0) (abs 0)).
Proof.
  constructor; [now congruence | | now eauto].
  now apply Development_app_abs with (t1' := 0) (t2' := abs 0) (l := []); eauto.
  Unshelve.
  exact [].
  exact [].
Qed.

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
  now induction 1; subst; eauto.
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

Lemma ParallelStep_Development :
  forall t1 t2 : Tm,
    Development t1 t2 -> ParallelStep t1 t2.
Proof.
  now induction 1; subst; eauto.
Qed.

Lemma MultiStep_Development :
  forall t1 t2 : Tm,
    Development t1 t2 -> MultiStep t1 t2.
Proof.
  now intros; apply MultiStep_ParallelStep, ParallelStep_Development.
Qed.

#[export] Hint Resolve MultiStep_Development ParallelStep_Development : core.

Lemma Development_spec :
  forall t1 t2 t3 : Tm,
    Development t1 t3 ->
    ParallelStep t1 t2 ->
    ParallelStep t2 t3.
Proof.
  intros t1 t2 t3 Hd Hps; revert t2 Hps.
  induction Hd; intros; inversion Hps; subst; clear Hps.
  - now auto.
  - now apply ParallelStep_abs with (l ++ l0); eauto.
  - now auto.
  - now contradiction (H t3).
  - inversion H2; subst; clear H2.
    now apply ParallelStep_app_abs with (l ++ l0); eauto.
  - pose (x := fresh (l ++ l0 ++ fv t1' ++ fv t1'0)).
    rewrite !(open'_spec _ _ x ) by auto.
    now apply ParallelStep_subst''; eauto.
Qed.

Lemma confluent_ParallelStep_Development :
  forall t t' t1 t2 : Tm,
    Development t t' ->
    ParallelStep t t1 -> ParallelStep t t2 ->
      ParallelStep t1 t' /\ ParallelStep t2 t'.
Proof.
  intros t t' t1 t2 Hd Hps1 Hps2.
  now split; eapply Development_spec; eauto.
Qed.

Require Import Recdef.

(*
Function development (t : Tm) : Tm :=
match t with
| fvar x => fvar x
| bvar i => bvar i
| abs t' => abs (development t')
| app (abs t1) t2 =>
  let t1' := development t1 in
    t1' {[ 0 ~> development t2 ]}
| app t1 t2 => app (development t1) (development t2)
| _ => t
end.
*)

(*
Function dev' (env : list Tm) (t : Tm) : Tm :=
match t with
| fvar x => fvar x
| bvar i =>
  match nth_option i env with
  | None => bvar i
  | Some t => t
  end
| abs t' =>
  let x := fresh (fv t) in
    abs (development (t' {{ 0 ~> x }}) {{ 0 <~ x }})
| app (abs t1) t2 =>
  let x := fresh (fv t) in
  let t1' := development (t1 {{ 0 ~> x }}) in
    t1' [[ x := development t2 ]]
| app t1 t2 => app (development t1) (development t2)
| _ => t
end.
*)

Module wut.

Function development (t : Tm): Tm :=
match t with
| fvar x => fvar x
| bvar i => bvar i
| abs t' => abs (development t')
| app (abs t1) t2 => development t1 {[ 0 ~> development t2 ]}
| app t1 t2 => app (development t1) (development t2)
| _ => t
end.

Lemma lc_development0 :
  forall t : Tm,
    lc t -> lc (development t).
Proof.
  induction 1; cbn; try now auto.
  - apply lc_abs with l; intros x Hx.
    admit.
  - inversion H; subst; cbn; try now auto.
    apply lc_open'; [| easy].
    inversion IHlc1; subst.
    now eauto.
Admitted.
    
Lemma open_development0 :
  forall (t : Tm) (i : nat) (x : Atom),
    lc t -> development t {{ i ~> x }} = development t.
Proof.
  intros t i x Hlc; revert i x.
  induction Hlc; cbn in *; intros; try easy.
  - admit.
  - destruct t1; cbn in *; rewrite ?IHHlc1, ?IHHlc2; try now auto.
    inversion Hlc1; subst.
    rewrite open_lc; [easy |].
    apply lc_open'; [| now apply lc_development0].
    admit.
  - now rewrite open_lc.
Admitted.

Lemma open_development :
  forall (t : Tm) (i : nat) (x : Atom),
    lc t -> development t {{ i ~> x }} = development (t {{ i ~> x }})

with lc_development :
  forall (t : Tm),
    lc t -> lc (development t).
Proof.
  - intros.
    rewrite open_lc; [| now apply lc_development].
    now rewrite open_lc.
  - induction 1; cbn; only 1, 4-5: now auto.
    + apply lc_abs with l; intros x Hx.
      specialize (H x Hx).
      rewrite <- open_development in H; [easy |].
      admit.
    + inversion H; subst; cbn; try now auto.
      apply lc_open'; [| easy].
      inversion IHlc1; subst.
      now eauto.
Admitted.

Lemma development_spec :
  forall t : Tm,
    lc t -> Development t (development t).
Proof.
  induction 1; cbn.
  - now constructor.
  - apply Development_abs with l; intros x Hx.
    rewrite open_development.
    now apply H.
    admit.
  - inversion IHlc1; subst; clear IHlc1; try easy.
    + now econstructor; [congruence | eauto..].
    + now eapply Development_app_abs; eauto.
    + cbn; rewrite <- H1.
      now econstructor; [congruence | eauto..].
    + now econstructor; [congruence | eauto..].
  - admit.
  - admit.
Admitted.

End wut.

Function development (t : Tm) {measure size t} : Tm :=
match t with
| fvar x => fvar x
| bvar i => bvar i
| abs t' =>
  let x := fresh (fv t) in
    abs (development (t' {{ 0 ~> x }}) {{ 0 <~ x }})
| app (abs t1) t2 =>
  let x := fresh (fv t) in
  let t1' := development (t1 {{ 0 ~> x }}) in
    t1' [[ x := development t2 ]]
| app t1 t2 => app (development t1) (development t2)
| _ => t
end.
Proof.
  all: now intros; subst; cbn; rewrite ?size_close, ?size_open; lia.
Defined.

Lemma development_spec :
  forall t : Tm,
    lc t -> Development t (development t).
Proof.
  induction 1; cbn.
  - now constructor.
  - apply Development_abs with l; intros x Hx.
    rewrite open_development.
    now apply H.
  - inversion IHlc1; subst; clear IHlc1; try easy.
    + now econstructor; [congruence | eauto..].
    + now eapply Development_app_abs; eauto.
    + cbn; rewrite <- H1.
      now econstructor; [congruence | eauto..].
    + now econstructor; [congruence | eauto..].
  - admit.
  - admit.
Admitted.

Lemma confluent_ParallelStep_ParallelMultiStep :
  forall t t1 t2 : Tm,
    ParallelStep t t1 -> ParallelMultiStep t t2 ->
      exists t3 : Tm, ParallelMultiStep t1 t3 /\ ParallelMultiStep t2 t3.
Proof.
  intros t t1 t2 H1 H2; revert t1 H1.
  induction H2; intros; [now exists t1; eauto |].
  edestruct (IHParallelMultiStep (development t1)) as [t4 [IH1 IH2] ].
  - eapply Development_spec; [| now eauto].
    now apply development_spec; eauto.
  - exists t4; split; [| easy].
    transitivity (development t1); [| easy].
    eapply ParallelMultiStep_ParallelStep, Development_spec; [| now eauto].
    now apply development_spec; eauto.
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

Lemma confluent_MultiStep :
  forall t t1 t2 : Tm,
    MultiStep t t1 -> MultiStep t t2 ->
      exists t3 : Tm, MultiStep t1 t3 /\ MultiStep t2 t3.
Proof.
  setoid_rewrite MultiStep_ParallelMultiStep.
  now apply confluent_ParallelMultiStep.
Qed.
