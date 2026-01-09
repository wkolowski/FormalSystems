From FormalSystems Require Export LocallyNameless.STLC.Constants.Confluence.

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
