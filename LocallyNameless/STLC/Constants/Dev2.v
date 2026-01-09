From FormalSystems Require Export LocallyNameless.STLC.Constants.Confluence.

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
