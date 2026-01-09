From FormalSystems Require Export LocallyNameless.STLC.Constants.Confluence.

Unset Guard Checking.
Fixpoint development (t : Tm) : Tm :=
match t with
| fvar x          => fvar x
| bvar i          => bvar i
| abs t'          => abs (development t')
| app (abs t1) t2 => development t1 {[ 0 ~> development t2 ]}
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
