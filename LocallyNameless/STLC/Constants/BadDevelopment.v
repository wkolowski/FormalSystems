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
  forall (t1 t1' t2 t2' : Tm)
    (Hd1 : Development t1 t1')
    (Hd2 : Development t2 t2')
    (Hneq : forall u : Tm, t1' <> abs u),
    Development (app t1 t2) (app t1' t2')
| Development_app_abs :
  forall (t1 t1' t1'' t2 t2' t3 : Tm)
    (Hd1 : Development t1 t1')
    (Hd2 : Development t2 t2')
    (Heq : t1' = abs t1'')
    (Hd' : Development (t1'' {[ 0 ~> t2' ]}) t3),
    Development (app t1 t2) t3.

#[export] Hint Constructors Development : core.

Lemma Development_abs0 :
  Development (abs 0) (abs 0).
Proof.
  now unshelve eauto; exact [].
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
  - contradiction (Hneq t1'').
    now apply IHHd1_1.
  - contradiction (Hneq t1''); symmetry.
    now apply IHHd1_1.
  - apply IHHd1_3.
    injection (IHHd1_1 _ Hd1) as [= ->].
    now rewrite (IHHd1_2 _ Hd0).
Qed.

Lemma Dev_abs0_abs0_abs0 : Development (app (app (abs 0) (abs 0)) (abs 0)) (abs 0).
Proof.
  eauto using Development_abs0.
Qed.

Goal ~ Development (app (app (abs 0) (abs 0)) (abs 0)) (app (abs 0) (abs 0)).
Proof.
  intros Hd.
  pose (Development_det _ _ _ Dev_abs0_abs0_abs0 Hd).
  inversion e.
Qed.

Lemma Development_Nf :
  forall t1 t2 : Tm,
    Development t1 t2 -> forall t : Tm, ~ FullContraction t2 t.
Proof.
  induction 1; intros t Hfc; subst.
  - now inversion Hfc.
  - now inversion Hfc; subst.
  - inversion Hfc; subst.
    now contradiction (Hneq t0).
  - now apply IHDevelopment3 in Hfc.
Qed.

Lemma Development_FullContraction :
  forall t1 t2 t3 : Tm,
    FullContraction t1 t2 -> Development t2 t3 -> Development t1 t3.
Proof.
  intros t1 t2 t3 [] Hd23.
  eapply Development_app_abs with (t1' := abs t0) (t2' := t4).
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
      now apply IHHfs.
    + apply Development_app_abs with (t1' := abs t1'') (t2' := t2') (t1'' := t1''); try easy.
      now apply IHHfs.
  - inversion Hd; subst.
    + now constructor; auto.
    + apply Development_app_abs with (t1' := abs t1'') (t2' := t2'0) (t1'' := t1''); try easy.
      now apply IHHfs.
Qed.

Lemma MultiStep_Development :
  forall t1 t2 : Tm,
    Development t1 t2 -> MultiStep t1 t2.
Proof.
  induction 1; eauto.
  transitivity (app t1' t2); [now eapply MultiStep_app; eauto |].
  transitivity (app t1' t2'); [now eapply MultiStep_app; eauto |].
  subst.
  apply lc_Development_r in H; inversion H; subst.
  now apply MultiStep_app_abs with l; eauto.
Qed.

#[export] Hint Resolve MultiStep_Development : core.
