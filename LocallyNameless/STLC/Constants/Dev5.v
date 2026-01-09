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
