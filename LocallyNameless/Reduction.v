From FormalSystems Require Export LocallyNameless.STLC.

(** * Experiments with the definition of reduction *)

(** ** Contraction *)

Inductive Contraction : Tm -> Tm -> Prop :=
| Contraction_Fun :
  forall (t1 t2 : Tm),
    lc (abs t1) ->
    Value t2 ->
    Contraction (app (abs t1) t2) (t1 {[ 0 ~> t2 ]}).

#[export] Hint Constructors Contraction : core.

Lemma lc_Contraction_l :
  forall t t' : Tm,
    Contraction t t' -> lc t.
Proof.
  intros t t'; destruct 1 as [t t' Hlc Hv].
  constructor; [easy |].
  now apply lc_Value.
Qed.

Lemma lc_Contraction_r :
  forall t t' : Tm,
    Contraction t t' -> lc t'.
Proof.
  intros t t'; destruct 1 as [t t' Hlc Hv].
  apply lc_open; [easy |].
  now apply lc_Value.
Qed.

(** ** A more modular definition *)

Module modular.

Inductive Step' : Tm -> Tm -> Prop :=
| Step'_Contraction :
  forall t t' : Tm,
    Contraction t t' ->
    Step' t t'
| Step'_FunCongrL :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    Step' t1 t1' ->
    Step' (app t1 t2) (app t1' t2)
| Step'_FunCongrR :
  forall (t1 t2 t2' : Tm),
    Value t1 ->
    Step' t2 t2' ->
    Step' (app t1 t2) (app t1 t2').

#[export] Hint Constructors Step' : core.

Lemma Step'_spec :
  forall t t' : Tm,
    Step' t t' <-> Step t t'.
Proof.
  split.
  - induction 1.
    + destruct H.
      now constructor.
    + now constructor.
    + now constructor.
  - induction 1.
    + now constructor.
    + now constructor 2.
    + now constructor 3.
Qed.

Lemma lc_Step'_l :
  forall t t' : Tm,
    Step' t t' -> lc t.
Proof.
  induction 1.
  - now apply lc_Contraction_l in H.
  - now constructor.
  - constructor; [| easy ].
    now apply lc_Value.
Qed.

Lemma lc_Step'_r :
  forall t t' : Tm,
    Step' t t' -> lc t'.
Proof.
  induction 1.
  - now apply lc_Contraction_r in H.
  - now constructor.
  - constructor; [| easy ].
    now apply lc_Value.
Qed.

Lemma preservation :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    Step t1 t2 ->
    Typing Γ t1 A ->
    Typing Γ t2 A.
Proof.
  intros * Hs Ht; revert t2 Hs.
  induction Ht; intros; inversion Hs; subst.
  - inversion Ht1; subst.
    rewrite open'_spec with (x := fresh (l ++ fv t3)) by solve_fresh.
    apply Typing_subst with A; [| easy].
    apply Hcof.
    now solve_fresh.
  - now econstructor; eauto.
  - now econstructor; eauto.
Qed.

Lemma progress :
  forall (t : Tm) (A : Ty),
    Typing [] t A ->
      Value t \/ exists t' : Tm, Step t t'.
Proof.
  intros t A Ht.
  remember [] as Γ.
  induction Ht; subst.
  - now inversion H0.
  - left; constructor.
    apply lc_abs with l; intros x Hx.
    now eapply lc_Typing, Hcof.
  - destruct (IHHt1 eq_refl) as [ [t1' Hlc1] | [t1' Hs1] ].
    + now destruct (IHHt2 eq_refl) as [ [t2' Hlc2] | [t2' Hs2] ]; eauto.
    + now apply lc_Typing in Ht2; eauto.
Qed.

End modular.

(** ** Definitions based on evaluation contexts *)

Inductive EvalCtx : Type :=
| Hole : EvalCtx
| FunCongrL :
  forall (E : EvalCtx) (t2 : Tm) (Hlc2 : lc t2), EvalCtx
| FunCongrR :
  forall (t1 : Tm) (v1 : Value t1) (E : EvalCtx), EvalCtx.

Fixpoint plug (E : EvalCtx) (t : Tm) : Tm :=
match E with
| Hole => t
| FunCongrL E' t2 _ => app (plug E' t) t2
| FunCongrR t1 _ E' => app t1 (plug E' t)
end.

Lemma plug_Hole :
  forall t : Tm,
    plug Hole t = t.
Proof.
  easy.
Qed.

Lemma preservation_Contraction :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    Contraction t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  induction 1; inversion 1; subst.
  inversion H5; subst.
  rewrite open'_spec with (x := fresh (l ++ fv t1)) by solve_fresh.
  apply Typing_subst with A0; [| easy].
  apply Hcof.
  now solve_fresh.
Qed.

(** *** Definition of reduction as an inductive type *)

Module inductive.

Inductive Step' : Tm -> Tm -> Prop :=
| mkStep' :
  forall (E : EvalCtx) (t t' : Tm),
    Contraction t t' -> Step' (plug E t) (plug E t').

#[export] Hint Constructors Step' : core.

Lemma Step'_spec :
  forall t t' : Tm,
    Step' t t' <-> Step t t'.
Proof.
  split.
  - destruct 1 as [E t t' [] ].
    induction E; cbn; intros.
    + now constructor.
    + now constructor; [| apply IHE].
    + now constructor; [| apply IHE].
  - induction 1.
    + now apply (mkStep' Hole _ (t1 {{ 0 ~> t2 }})).
    + destruct IHStep as [E u u' HC].
      now apply (mkStep' (FunCongrL E t2 H)).
    + destruct IHStep as [E u u' HC].
      now apply (mkStep' (FunCongrR t1 H E)).
Qed.

Lemma lc_Step'_l :
  forall t t' : Tm,
    Step' t t' -> lc t.
Proof.
  intros t t'; destruct 1 as [E t t' Hc].
  induction E; cbn.
  - now apply lc_Contraction_l in Hc.
  - now constructor.
  - constructor; [| easy].
    now apply lc_Value.
Qed.

Lemma lc_Step'_r :
  forall t t' : Tm,
    Step' t t' -> lc t'.
Proof.
  intros t t'; destruct 1 as [E t t' Hc].
  induction E; cbn.
  - now apply lc_Contraction_r in Hc.
  - now constructor.
  - constructor; [| easy].
    now apply lc_Value.
Qed.

Lemma preservation :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    Step' t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  intros Γ t t' A; destruct 1 as [E t t' Hc].
  revert A.
  induction E; cbn; intros.
  - now eapply preservation_Contraction; eauto.
  - now inversion H; subst; econstructor; eauto.
  - now inversion H; subst; econstructor; eauto.
Qed.

Lemma progress :
  forall (t : Tm) (A : Ty),
    Typing [] t A ->
      Value t \/ exists t' : Tm, Step' t t'.
Proof.
  intros t A Ht.
  remember [] as Γ.
  induction Ht; subst.
  - now inversion H0.
  - left; constructor.
    apply lc_abs with l.
    intros x Hx.
    now eapply lc_Typing, Hcof.
  - destruct (IHHt1 eq_refl) as [ [t1' Hlc1] | [t1' Hs1] ].
    + destruct (IHHt2 eq_refl) as [ [t2' Hlc2] | [t2' Hs2] ].
      * right.
        exists (plug Hole (t1' {[ 0 ~> abs t2' ]})).
        now rewrite <- plug_Hole at 1.
      * right.
        destruct Hs2 as [E t2 t2' Hc].
        exists (plug (FunCongrR (abs t1') ltac:(easy) E) t2').
        change (app (abs t1') (plug E t2)) with (plug (FunCongrR (abs t1') ltac:(easy) E) t2).
        easy.
    + destruct Hs1 as [E t1 t1' Hc].
      apply lc_Typing in Ht2.
      right.
      exists (plug (FunCongrL E t2 Ht2) t1').
      change (app (plug E t1) t2) with (plug (FunCongrL E t2 Ht2) t1).
      easy.
Qed.

End inductive.

(** *** Definition of reduction with an existential quantifier *)

Module ex.

Definition Step' (t t' : Tm) : Prop :=
  exists (E : EvalCtx) (u u' : Tm),
    t = plug E u /\
    t' = plug E u' /\
    Contraction u u'.

Lemma Step'_spec :
  forall t t' : Tm,
    Step' t t' <-> Step t t'.
Proof.
  split.
  - intros (E & u & u' & -> & -> & []); clear u u'.
    induction E; cbn; intros.
    + now constructor.
    + now constructor; [| apply IHE].
    + now constructor; [| apply IHE].
  - induction 1.
    + exists Hole.
      now do 2 eexists.
    + destruct IHStep as (E & u & u' & -> & -> & HC).
      exists (FunCongrL E t2 H).
      now do 2 eexists.
    + destruct IHStep as (E & u & u' & -> & -> & HC).
      exists (FunCongrR t1 H E).
      now do 2 eexists.
Qed.

Lemma lc_Step'_l :
  forall t t' : Tm,
    Step' t t' -> lc t.
Proof.
  intros ? ? (E & t & t' & -> & -> & Hc).
  induction E; cbn.
  - now apply lc_Contraction_l in Hc.
  - now constructor.
  - constructor; [| easy].
    now apply lc_Value.
Qed.

Lemma lc_Step'_r :
  forall t t' : Tm,
    Step' t t' -> lc t'.
Proof.
  intros ? ? (E & t & t' & -> & -> & Hc).
  induction E; cbn.
  - now apply lc_Contraction_r in Hc.
  - now constructor.
  - constructor; [| easy].
    now apply lc_Value.
Qed.

Lemma preservation :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    Step' t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  intros * (E & u & u' & -> & -> & HC).
  revert A.
  induction E; cbn; intros.
  - now eapply preservation_Contraction; eauto.
  - now inversion H; subst; econstructor; eauto.
  - now inversion H; subst; econstructor; eauto.
Qed.

Lemma progress :
  forall (t : Tm) (A : Ty),
    Typing [] t A ->
      Value t \/ exists t' : Tm, Step' t t'.
Proof.
  intros t A Ht.
  remember [] as Γ.
  induction Ht; subst.
  - now inversion H0.
  - left; constructor.
    apply lc_abs with l.
    intros x Hx.
    now eapply lc_Typing, Hcof.
  - destruct (IHHt1 eq_refl) as [ [t1' Hlc1] | [t1' Hs1] ].
    + destruct (IHHt2 eq_refl) as [ [t2' Hlc2] | [t2' Hs2] ].
      * right; unfold Step'.
        exists (t1' {[ 0 ~> abs t2' ]}).
        now exists Hole, (app (abs t1') (abs t2')), (t1' {[ 0 ~> abs t2' ]}); cbn.
      * right; unfold Step'.
        destruct Hs2 as (E & u & u' & -> & -> & Hc).
        now exists
          (plug (FunCongrR (abs t1') ltac:(easy) E) u'),
          (FunCongrR (abs t1') ltac:(easy) E),
          u, u'; cbn.
    + destruct Hs1 as (E & u & u' & -> & -> & Hc).
      apply lc_Typing in Ht2.
      right; unfold Step'.
      now exists (plug (FunCongrL E t2 Ht2) u'), (FunCongrL E t2 Ht2), u, u'; cbn.
Qed.

End ex.

(** *** Definition of reduction as a record *)

Module record.

Record Step' (t t' : Tm) : Prop := mkStep'
{
  E : EvalCtx;
  u : Tm;
  u' : Tm;
  Ht : t = plug E u;
  Ht' : t' = plug E u';
  HC : Contraction u u';
}.

Lemma Step'_spec :
  forall t t' : Tm,
    Step' t t' <-> Step t t'.
Proof.
  split.
  - intros [E u u' -> -> [] ].
    induction E; cbn; intros.
    + now constructor.
    + now constructor; [| apply IHE].
    + now constructor; [| apply IHE].
  - induction 1.
    + now eapply (mkStep' _ _ Hole).
    + destruct IHStep as [E u u' -> -> HC].
      now eapply (mkStep' _ _ (FunCongrL E t2 H)).
    + destruct IHStep as [E u u' -> -> HC].
      now eapply (mkStep' _ _ (FunCongrR t1 H E)).
Qed.

Lemma lc_Step'_l :
  forall t t' : Tm,
    Step' t t' -> lc t.
Proof.
  intros ? ? [E t t' -> -> Hc].
  induction E; cbn.
  - now apply lc_Contraction_l in Hc.
  - now constructor.
  - constructor; [| easy].
    now apply lc_Value.
Qed.

Lemma lc_Step'_r :
  forall t t' : Tm,
    Step' t t' -> lc t'.
Proof.
  intros ? ? [E t t' -> -> Hc].
  induction E; cbn.
  - now apply lc_Contraction_r in Hc.
  - now constructor.
  - constructor; [| easy].
    now apply lc_Value.
Qed.

Lemma preservation :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    Step' t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  intros * [E t t' -> -> Hc].
  revert A.
  induction E; cbn; intros.
  - now eapply preservation_Contraction; eauto.
  - now inversion H; subst; econstructor; eauto.
  - now inversion H; subst; econstructor; eauto.
Qed.

Lemma progress :
  forall (t : Tm) (A : Ty),
    Typing [] t A ->
      Value t \/ exists t' : Tm, Step' t t'.
Proof.
  intros t A Ht.
  remember [] as Γ.
  induction Ht; subst.
  - now inversion H0.
  - left; constructor.
    apply lc_abs with l.
    intros x Hx.
    now eapply lc_Typing, Hcof.
  - destruct (IHHt1 eq_refl) as [ [t1' Hlc1] | [t1' Hs1] ].
    + destruct (IHHt2 eq_refl) as [ [t2' Hlc2] | [t2' Hs2] ].
      * right.
        exists (t1' {[ 0 ~> abs t2' ]}).
        now eapply (mkStep' _ _ Hole (app (abs t1') (abs t2'))); cbn; eauto.
      * right.
        destruct Hs2 as [E u u' -> -> Hc].
        exists (app (abs t1') (plug E u')).
        now eapply (mkStep' _ _ (FunCongrR (abs t1') ltac:(easy) E)); cbn; eauto.
    + destruct Hs1 as [E u u' -> -> Hc].
      apply lc_Typing in Ht2.
      right.
      exists (app (plug E u') t2).
      now eapply (mkStep' _ _ (FunCongrL E t2 Ht2)); cbn; eauto.
Qed.

End record.
