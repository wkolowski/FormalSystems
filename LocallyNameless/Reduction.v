From FormalSystems Require Export LocallyNameless.STLC.

(** * Old definition of reduction *)

(*
Inductive Step : Tm -> Tm -> Prop :=
| Step_FunComp :
  forall (t1 t2 : Tm),
    lc (abs t1) ->
    Value t2 ->
    Step (app (abs t1) t2) (t1 {[ 0 ~> t2 ]})
| Step_FunCompAbort :
  forall (t1 t2 : Tm),
    lc t1 ->
    lc t2 ->
    Step (app (abort t1) t2) (abort t1)
| Step_FunCongrL :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    Step t1 t1' ->
    Step (app t1 t2) (app t1' t2)
| Step_FunCongrR :
  forall (t1 t2 t2' : Tm),
    Value t1 ->
    Step t2 t2' ->
    Step (app t1 t2) (app t1 t2')
| Step_OutlPair :
  forall v1 v2 : Tm,
    Value v1 ->
    Value v2 ->
    Step (outl (pair v1 v2)) v1
| Step_OutlAbort :
  forall t : Tm,
    lc t ->
    Step (outl (abort t)) (abort t)
| Step_OutrPair :
  forall v1 v2 : Tm,
    Value v1 ->
    Value v2 ->
    Step (outr (pair v1 v2)) v2
| Step_OutrAbort :
  forall t : Tm,
    lc t ->
    Step (outr (abort t)) (abort t)
| Step_PairCongrL :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    Step t1 t1' ->
    Step (pair t1 t2) (pair t1' t2)
| Step_PairCongrR :
  forall (t1 t2 t2' : Tm),
    Value t1 ->
    Step t2 t2' ->
    Step (pair t1 t2) (pair t1 t2')
| Step_OutlCongr :
  forall (t t' : Tm),
    Step t t' ->
    Step (outl t) (outl t')
| Step_OutrCongr :
  forall (t t' : Tm),
    Step t t' ->
    Step (outr t) (outr t').

#[export] Hint Constructors Step : core.

*)

(** * Experiments with the definition of reduction *)

(*
Lemma Step_spec :
  forall t t' : Tm,
    STLC.Step t t' <-> Step t t'.
Proof.
  split.
  - induction 1; [| | now constructor..].
    + now inversion H; subst; constructor.
    + now inversion H; subst; constructor.
  - induction 1; eauto.
Qed.

Lemma lc_Step_l :
  forall t t' : Tm,
    Step t t' -> lc t.
Proof.
  induction 1.
  - constructor; [easy |].
    now apply lc_Value.
  - constructor; [| easy].
    now constructor.
  - now constructor.
  - constructor; [| easy ].
    now apply lc_Value.
  - now do 2 constructor; apply lc_Value.
  - now do 2 constructor.
  - now do 2 constructor; apply lc_Value.
  - now do 2 constructor.
  - now constructor.
  - constructor; [| easy].
    now apply lc_Value.
  - now constructor.
  - now constructor.
Qed.

Lemma lc_Step_r :
  forall t t' : Tm,
    Step t t' -> lc t'.
Proof.
  induction 1.
  - apply lc_open; [easy |].
    now apply lc_Value.
  - now constructor.
  - now constructor.
  - constructor; [| easy ].
    now apply lc_Value.
  - now apply lc_Value.
  - now constructor.
  - now apply lc_Value.
  - now constructor.
  - now constructor.
  - constructor; [| easy].
    now apply lc_Value.
  - now constructor.
  - now constructor.
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
  - now constructor; inversion Ht1.
  - now econstructor; eauto.
  - now econstructor; eauto.
  - now econstructor; eauto.
  - now econstructor; eauto.
  - now inversion Ht; subst.
  - now constructor; inversion Ht.
  - now econstructor; eauto.
  - now inversion Ht; subst.
  - now constructor; inversion Ht.
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
    apply lc_abs with l.
    intros x Hx.
    now eapply lc_Typing, Hcof.
  - destruct (IHHt1 eq_refl) as [ Hv | [t1' Hs1] ].
    + inversion Hv; subst; inversion Ht1; subst.
      * now destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; eauto.
      * now apply lc_Typing in H2, Ht2; eauto.
    + right.
      destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ].
      * now apply lc_Value in Hv2; eauto.
      * now apply lc_Step_l in Hs2; eauto.
  - destruct (IHHt eq_refl) as [Hv | [t'' Hs] ].
    + now apply lc_Value in Hv; eauto.
    + now apply lc_Step_l in Hs; eauto.
  - destruct (IHHt1 eq_refl) as [Hv1 | [t1' Hs1] ].
    + now destruct (IHHt2 eq_refl) as [Hv2 | [t2' Hs1] ]; eauto.
    + destruct (IHHt2 eq_refl) as [Hv2 | [t2' Hs2] ].
      * now apply lc_Value in Hv2; eauto.
      * now apply lc_Step_l in Hs2; eauto.
  - destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht; subst; eauto.
  - destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht; subst; eauto.
Qed.
*)

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

(** *** Definition of reduction as an inductive type *)

Module inductive.

Inductive Step' : Tm -> Tm -> Prop :=
| Step_Contraction :
  forall (E : EvalCtx) (t t' : Tm),
    Contraction t t' -> Step' (plug E t) (plug E t')
| Step'_Abortion :
  forall (E : EvalCtx) (t t' : Tm),
    Abortion t t' -> Step' (plug E t) (plug E t').

#[export] Hint Constructors Step' : core.

Lemma Step'_det :
  forall t t1 t2 : Tm,
    Step' t t1 -> Step' t t2 -> t1 = t2.
Proof.
  destruct 1; inversion 1; subst.
Abort.

Lemma Step'_spec :
  forall t t' : Tm,
    Step' t t' <-> Step t t'.
Proof.
  split.
  - destruct 1 as [E t t' Hc | E t t' Ha].
    + induction E; cbn; intros; [| now eauto..].
      now inversion Hc; constructor; eauto.
    + induction E; cbn; intros; [| now eauto..].
      now inversion Ha; constructor; eauto.
  - induction 1.
    + now apply (mkStep' Hole _ (t1 {{ 0 ~> t2 }})); constructor.
    + 
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
