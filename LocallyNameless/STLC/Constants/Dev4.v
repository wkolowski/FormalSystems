From FormalSystems Require Export LocallyNameless.STLC.Constants.Confluence.

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
