Require Import
  List
  Coq.Classes.DecidableClass.

Import ListNotations.

From FormalSystems Require Export LocallyNameless.OC.

Inductive Ty : Type :=
| TyUnit : Ty
| TyFun  : Ty -> Ty -> Ty.

Fixpoint eq_dec_Ty (A B : Ty) : bool :=
match A, B with
| TyUnit, TyUnit => true
| TyFun A1 A2, TyFun B1 B2 => andb (eq_dec_Ty A1 B1) (eq_dec_Ty A2 B2)
| _, _ => false
end.

#[export, refine] Instance Decidable_eq_Ty :
  forall A B : Ty, Decidable (A = B) :=
{
  Decidable_witness := eq_dec_Ty A B;
}.
Proof.
  revert B.
  induction A as [| A1 IH1 A2 IH2]; cbn; intros [| B1 B2];
    only 1-3: now firstorder congruence.
  split.
  - intros [H1 H2]%andb_prop.
    now f_equal; [apply IH1 | apply IH2].
  - intros [= -> ->].
    apply andb_true_intro.
    now rewrite IH1, IH2.
Defined.

Inductive Tm : Type :=
| fvar (a : Atom) : Tm
| bvar : nat -> Tm
| abs  : Tm -> Tm
| app  : Tm -> Tm -> Tm.

Coercion fvar : Atom >-> Tm.
Coercion bvar : nat >-> Tm.

#[export] Instance Open_Tm : Open nat Atom Tm :=
  fix open (t : Tm) (i : nat) (a : Atom) : Tm :=
    match t with
    | fvar a    => fvar a
    | bvar j    => if decide (i = j) then a else bvar j
    | abs t'    => abs (open t' (S i) a)
    | app t1 t2 => app (open t1 i a) (open t2 i a)
    end.

#[export] Instance Close_Tm : Close nat Atom Tm :=
  fix close (t : Tm) (i : nat) (a : Atom) : Tm :=
    match t with
    | fvar x    => if decide (a = x) then bvar i else fvar x
    | bvar n    => bvar n
    | abs t'    => abs (close t' (S i) a)
    | app t1 t2 => app (close t1 i a) (close t2 i a)
    end.

#[export, refine] Instance OC_Tm :
  OC nat Atom Tm Open_Tm Close_Tm := {}.
Proof.
  all: induction t; cbn; intros;
    [now decide_all | now decide_all | now rewrite IHt; congruence | now rewrite IHt1, IHt2].
Qed.

Fixpoint subst (x : Atom) (u t : Tm) : Tm :=
match t with
| fvar y    => if decide (x = y) then u else fvar y
| bvar n    => bvar n
| abs t'    => abs (subst x u t')
| app t1 t2 => app (subst x u t1) (subst x u t2)
end.

Notation "t [[ x := u ]]" := (subst x u t) (at level 68).

Fixpoint fv (t : Tm) : list Atom :=
match t with
| fvar x    => [x]
| bvar _    => []
| abs t'    => fv t'
| app t1 t2 => fv t1 ++ fv t2
end.

Lemma subst_fv :
  forall (x : Atom) (u t : Tm),
    x # fv t -> t [[ x := u ]] = t.
Proof.
  induction t; cbn; intros.
  - decide (x = a); [| easy].
    now firstorder congruence.
  - easy.
  - now rewrite IHt.
  - red in H; rewrite in_app_iff in H.
    now firstorder congruence.
Qed.

Fixpoint open' (t : Tm) (i : nat) (u : Tm) : Tm :=
match t with
| fvar a    => fvar a
| bvar j    => if decide (i = j) then u else bvar j
| abs t'    => abs (open' t' (S i) u)
| app t1 t2 => app (open' t1 i u) (open' t2 i u)
end.

Notation "t {[ i ~> u ]}" := (open' t i u) (at level 68).

Lemma open'_from_subst :
  forall (t : Tm) (i : nat) (x : Atom) (u : Tm),
    x # fv t ->
      t {[ i ~> u ]} = t {{ i ~> x }} [[ x := u ]].
Proof.
  induction t; cbn; intros.
  - now decide (x = a); subst; firstorder.
  - now decide_all.
  - now rewrite <- IHt.
  - red in H; rewrite in_app_iff in H.
    now rewrite <- IHt1, <- IHt2; firstorder.
Qed.

Lemma Fresh'_spec :
  forall (x : Atom) (t : Tm),
    Fresh' x t <-> x # fv t.
Proof.
  split; unfold Fresh, Fresh'.
  - intros H.
    induction t; cbn; intros.
    + intros [-> |]; [| easy].
      cbn in H.
      now decide (x = x).
    + easy.
    + apply IHt.
      cbn in H; inversion H; subst.
      now rewrite close_close_eq.
    + cbn in H; inversion H; subst.
      rewrite H1, H2, in_app_iff.
      now firstorder.
  - induction t; cbn.
    + now decide_all; firstorder.
    + easy.
    + intros Hfresh.
      now rewrite <- IHt, close_close_eq by easy.
    + rewrite in_app_iff.
      now firstorder congruence.
Qed.

Lemma open'_open' :
  forall (t : Tm) (i j : nat) (u1 u2 : Tm),
    i <> j ->
    t {[ i ~> u1 ]} {[ j ~> u2 ]} = t {[ i ~> u1 ]} ->
      t {[ j ~> u2 ]} = t.
Proof.
  induction t; cbn; intros * Hneq H.
  - easy.
  - decide (i = n); subst; cbn; [| easy].
    decide (j = n); [| easy].
    now congruence.
  - inversion H.
    f_equal.
    eapply IHt, H1.
    now congruence.
  - inversion H.
    f_equal.
    + now eapply IHt1, H1.
    + now eapply IHt2, H2.
Qed.

Inductive lc : Tm -> Prop :=
| lc_fvar :
  forall x : Atom,
    lc x
| lc_abs :
  forall (t : Tm) (l : list Atom)
    (Hcof : forall x, x # l -> lc (t {{ 0 ~> x }})),
    lc (abs t)
| lc_app :
  forall t1 t2 : Tm,
    lc t1 ->
    lc t2 ->
    lc (app t1 t2).

#[export] Hint Constructors lc : core.

Lemma open'_atom :
  forall (t : Tm) (i : nat) (a : Atom),
    t {[ i ~> a ]} = t {{ i ~> a }}.
Proof.
  now induction t; cbn; firstorder congruence.
Qed.

Lemma open'_lc :
  forall (t : Tm) (i : nat) (u : Tm),
    lc t -> t {[ i ~> u ]} = t.
Proof.
  intros t i u Hlc; revert i u.
  induction Hlc; cbn; intros; [easy | | now congruence].
  f_equal.
  eapply open'_open' with (i := 0); [easy |].
  rewrite open'_atom.
  apply (H (fresh l)).
  now solve_fresh.
Qed.

Lemma subst_open' :
  forall (t : Tm) (i : nat) (u1 : Tm) (x : Atom) (u2 : Tm),
    lc u2 ->
    t {[ i ~> u1 ]} [[ x := u2 ]]
      =
    t [[ x := u2 ]] {[ i ~> u1 [[ x := u2 ]] ]}.
Proof.
  induction t; cbn; intros.
  - rewrite open'_lc; [easy |].
    now decide (x = a).
  - now decide (i = n).
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Qed.

Lemma open_open :
  forall (t : Tm) (i j : nat) (a b : Atom),
    i <> j ->
    t {{ i ~> a }} {{ j ~> b }} = t {{ i ~> a }} ->
      t {{ j ~> b }} = t.
Proof.
  induction t; cbn; intros * Hneq H.
  - easy.
  - now revert H; decide_all.
  - f_equal.
    eapply IHt; cycle 1; cbn.
    + inversion H; cbn in *.
      now apply H1.
    + now congruence.
  - inversion H.
    f_equal.
    + now apply IHt1 in H1.
    + now apply IHt2 in H2.
Restart.
  intros t i j a b Hneq.
  rewrite open_open_neq by easy.
  intros Heq.
  rewrite <- close_open_eq in Heq.
  rewrite <- close_open_eq.
  rewrite (open_close_neq t j i b a) in Heq.
Admitted.

Lemma open_lc :
  forall (t : Tm) (i : nat) (a : Atom),
    lc t -> t {{ i ~> a }} = t.
Proof.
  intros t i a Hlc; revert i a.
  induction Hlc; cbn; intros; [easy | | now congruence].
  f_equal.
  eapply open_open with (i := 0); [easy |].
  apply (H (fresh l)).
  now solve_fresh.
Qed.

Lemma subst_open :
  forall (t : Tm) (i : nat) (a b x : Atom),
    t {{ i ~> a }} [[ x := b ]]
      =
    t [[ x := b ]] {{ i ~> if decide (a = x) then b else a }}.
Proof.
  induction t; cbn; intros.
  - now decide_all.
  - now decide_all.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Qed.

Lemma open_subst' :
  forall (t : Tm) (a b : Atom) (i : nat) (u : Tm),
    a <> b -> lc u ->
    t [[ a := u ]] {{ i ~> b }} = t {{ i ~> b }} [[ a := u ]].
Proof.
  induction t; cbn; intros.
  - decide_all.
    now rewrite open_lc.
  - now decide_all.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Qed.

Lemma open_subst :
  forall (t : Tm) (a b : Atom) (u : Tm),
    a <> b -> lc u ->
    t [[ a := u ]] {{ 0 ~> b }} = t {{ 0 ~> b }} [[ a := u ]].
Proof.
  now intros; apply open_subst'.
Qed.

Lemma lc_subst :
  forall (t : Tm) (x : Atom) (u : Tm),
    lc t -> lc u -> lc (t [[ x := u ]]).
Proof.
  intros t x u Ht Hu; revert x u Hu.
  induction Ht; cbn; intros.
  - now decide (x0 = x).
  - apply lc_abs with (x :: l).
    intros y Hin.
    rewrite open_subst; [| now firstorder | easy].
    apply H; [| easy].
    now firstorder.
  - now constructor; [apply IHHt1 | apply IHHt2].
Qed.

Definition lci' (i : nat) (t : Tm) : Prop :=
  forall j : nat, i <= j -> t {{ j ~> fresh (fv t) }} = t.

Lemma lci'_spec :
  forall t : Tm,
    lc t -> lci' 0 t.
Proof.
  unfold lci'.
  induction 1; cbn; intros j Hle; [easy | |].
  - f_equal.
    specialize (Hcof (fresh l) (fresh_spec l)).
    rewrite <- open'_atom.
    rewrite open'_lc; [easy |].
    admit.
  - f_equal.
    +
Abort.

Lemma lci_spec :
  forall t : Tm,
    lc t -> lci 0 t.
Proof.
  unfold lci.
  induction 1; cbn; intros j Hle.
  - now exists x.
  - destruct (H (fresh l) (fresh_spec l) (S j) ltac:(lia)) as [a Heq].
    exists a.
    f_equal.
    apply open_open with 0 (fresh l); [easy |].
    apply Heq.
  - destruct (IHlc1 j Hle) as [a1 IH1].
    destruct (IHlc2 j Hle) as [a2 IH2].
    exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
    f_equal.
    + now rewrite Fresh'_invariant_aux_open; [apply IH1 | typeclasses eauto].
    + now rewrite Fresh'_invariant_aux_open; [apply IH2 | typeclasses eauto].
Qed.

Definition Ctx : Type := list (Atom * Ty).

Inductive WfCtx : Ctx -> Prop :=
| WfCtx_nil  :
  WfCtx []
| WfCtx_cons :
    forall (Γ : Ctx) (x : Atom) (A : Ty),
      WfCtx Γ -> x # map fst Γ -> WfCtx ((x, A) :: Γ).

#[export] Hint Constructors WfCtx : core.

Lemma WfCtx_app_cons :
  forall (Γ1 Γ2 : Ctx) (x : Atom) (A : Ty),
    WfCtx (Γ2 ++ (x, A) :: Γ1) -> WfCtx (Γ2 ++ Γ1).
Proof.
  induction Γ2 as [| [y B] Γ2' IH]; cbn; inversion 1; [easy |].
  constructor.
  - now apply IH in H2.
  - unfold Fresh in *; rewrite map_app, !in_app_iff in *; cbn in *.
    now firstorder.
Qed.

Definition Binds (Γ : Ctx) (x : Atom) (A : Ty) : Prop :=
  In (x, A) Γ.

Inductive Typing : Ctx -> Tm -> Ty -> Prop :=
| Typing_fvar :
  forall (Γ : Ctx) (x : Atom) (A : Ty),
    WfCtx Γ ->
    Binds Γ x A ->
    Typing Γ x A
| Typing_abs :
  forall (Γ : Ctx) (t : Tm) (A B : Ty) (l : list Atom),
    (forall x : Atom, x # l -> Typing ((x, A) :: Γ) (t {{ 0 ~> x }}) B) ->
    Typing Γ (abs t) (TyFun A B)
| Typing_app :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty),
    Typing Γ t1 (TyFun A B) ->
    Typing Γ t2 A ->
    Typing Γ (app t1 t2) B.

#[export] Hint Constructors Typing : Core.

Lemma weakening_aux :
  forall (Γ1 Γ2 Δ : Ctx) (t : Tm) (A : Ty),
    Typing (Γ1 ++ Γ2) t A ->
    WfCtx (Γ1 ++ Δ ++ Γ2) ->
    Typing (Γ1 ++ Δ ++ Γ2) t A.
Proof.
  intros * Ht.
  remember (Γ1 ++ Γ2) as G.
  revert Γ1 Γ2 Δ HeqG.
  induction Ht; intros; subst.
  - constructor; [easy |].
    unfold Binds in *.
    rewrite !in_app_iff; rewrite in_app_iff in H0.
    now firstorder.
  - apply Typing_abs with (l ++ map fst Γ1 ++ map fst Δ ++ map fst Γ2).
    intros.
    red in H2; rewrite !in_app_iff in H2.
    rewrite app_comm_cons.
    apply H0; [now firstorder | easy |].
    cbn; constructor; [easy |].
    red; rewrite !map_app, !in_app_iff.
    now firstorder.
  - apply Typing_app with A.
    + now apply IHHt1.
    + now apply IHHt2.
Qed.

Lemma weakening :
  forall (Γ Δ : Ctx) (t : Tm) (A : Ty),
    WfCtx (Δ ++ Γ) ->
    Typing Γ t A ->
    Typing (Δ ++ Γ) t A.
Proof.
  now intros; apply weakening_aux with (Γ1 := []); cbn.
Qed.

Lemma lc_Typing :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Typing Γ t A -> lc t.
Proof.
  induction 1; only 1, 3: now constructor.
  apply lc_abs with l.
  intros x Hx.
  now apply H0.
Qed.

Lemma Binds_inv :
  forall (Γ : Ctx) (x : Atom) (A B : Ty),
    WfCtx Γ -> Binds Γ x A -> Binds Γ x B -> A = B.
Proof.
  induction 1; cbn; [easy |].
  intros [ [= -> ->] |].
  - intros [ [= ->] |]; [easy |].
    contradiction H0.
    rewrite in_map_iff.
    now exists (x, B).
  - intros [ [= -> ->] |].
    + contradiction H0.
      rewrite in_map_iff.
      now exists (x, A).
    + now apply IHWfCtx.
Qed.

Lemma Binds_app_cons_inv :
  forall (Γ Δ : Ctx) (x y : Atom) (A B : Ty),
    Binds (Δ ++ (x, A) :: Γ) y B ->
      (x = y /\ A = B)
        \/
      Binds (Δ ++ Γ) y B.
Proof.
  induction Δ; cbn.
  - now firstorder congruence.
  - inversion 1; subst; [now firstorder |].
    apply IHΔ in H0.
    now firstorder.
Qed.

Lemma Typing_subst_aux :
  forall (Γ Δ : Ctx) (x : Atom) (t u : Tm) (A B : Ty),
    Typing (Δ ++ (x, A) :: Γ) t B ->
    Typing Γ u A ->
    Typing (Δ ++ Γ) (t [[ x := u ]]) B.
Proof.
  intros * Ht Hu.
  remember (Δ ++ (x, A) :: Γ) as G.
  revert Δ x A Γ HeqG Hu.
  induction Ht as [? y B Hwf HB | ? t' B1 B2 l Hcof IH | ? t1 t2 B1 B2 Ht1 IH1 Ht2 IH2];
    cbn; intros; subst.
  - apply WfCtx_app_cons in Hwf as Hwf'.
    decide (x = y); subst.
    + replace B with A.
      * now apply weakening.
      * symmetry.
        eapply (Binds_inv _ _ _ _ Hwf HB).
        red; rewrite in_app_iff; cbn.
        now firstorder.
    + apply Binds_app_cons_inv in HB as [ [-> ->] |]; [easy |].
      now constructor.
  - apply Typing_abs with (x :: l).
    intros y Hy; cbn in Hy.
    assert (x <> y /\ y # l) as [Hxy Hyl] by firstorder.
    rewrite open_subst; [| now firstorder | now apply lc_Typing in Hu].
    now eapply (IH y Hyl ((y, B1) :: Δ)).
  - econstructor.
    + now eapply IH1.
    + now eapply IH2.
Qed.

Lemma Typing_subst :
  forall (Γ : Ctx) (x : Atom) (t u : Tm) (A B : Ty),
    Typing ((x, A) :: Γ) t B ->
    Typing Γ u A ->
    Typing Γ (t [[ x := u ]]) B.
Proof.
  now intros; eapply Typing_subst_aux with (Δ := []) (A := A).
Qed.

Inductive Value : Tm -> Prop :=
| Value_abs : forall t : Tm, lc (abs t) -> Value (abs t).

#[export] Hint Constructors Value : core.

Inductive Step : Tm -> Tm -> Prop :=
| Step_FunComp :
  forall (t1 t2 : Tm),
    lc (abs t1) ->
    Value t2 ->
    Step (app (abs t1) t2) (t1 {[ 0 ~> t2 ]})
| Step_FunCongrL :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    Step t1 t1' ->
    Step (app t1 t2) (app t1' t2)
| Step_FunCongrR :
  forall (t1 t2 t2' : Tm),
    Value t1 ->
    Step t2 t2' ->
    Step (app t1 t2) (app t1 t2').

#[export] Hint Constructors Step : core.

Lemma preservation :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    Step t1 t2 ->
    Typing Γ t1 A ->
    Typing Γ t2 A.
Proof.
  intros * Hs Ht; revert t2 Hs.
  induction Ht; intros; inversion Hs; subst.
  - inversion Ht1; subst.
    rewrite open'_from_subst with (x := fresh (l ++ fv t3)) by solve_fresh.
    apply Typing_subst with A; [| easy].
    apply H4.
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
    apply lc_abs with l.
    intros x Hx.
    now eapply lc_Typing, H.
  - destruct (IHHt1 eq_refl) as [ [t1' Hlc1] | [t1' Hs1] ].
    + now destruct (IHHt2 eq_refl) as [ [t2' Hlc2] | [t2' Hs2] ]; eauto.
    + now apply lc_Typing in Ht2; eauto.
Qed.

Lemma lc_open :
  forall (t u : Tm),
    lc (abs t) -> lc u ->
      lc (t {[ 0 ~> u ]}).
Proof.
  inversion 1; intros Hu.
  rewrite (open'_from_subst _ _ (fresh (l ++ fv t))) by solve_fresh.
  apply lc_subst; [| easy].
  apply Hcof.
  now solve_fresh.
Qed.

Lemma lc_Value :
  forall t : Tm,
    Value t -> lc t.
Proof.
  now inversion 1.
Qed.

Lemma lc_Step_l :
  forall t t' : Tm,
    Step t t' -> lc t.
Proof.
  induction 1.
  - constructor; [easy |].
    now apply lc_Value.
  - now constructor.
  - constructor; [| easy ].
    now apply lc_Value.
Qed.

Lemma lc_Step_r :
  forall t t' : Tm,
    Step t t' -> lc t'.
Proof.
  induction 1.
  - apply lc_open; [easy |].
    now apply lc_Value.
  - now constructor.
  - constructor; [| easy ].
    now apply lc_Value.
Qed.

Lemma WfCtx_Typing :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Typing Γ t A -> WfCtx Γ.
Proof.
  induction 1; [easy | | easy].
  specialize (H0 (fresh l) (fresh_spec l)).
  now inversion H0.
Qed.

Inductive Infer : Ctx -> Tm -> Ty -> Prop :=
| Infer_fvar :
  forall (Γ : Ctx) (x : Atom) (A : Ty),
    Binds Γ x A -> Infer Γ x A
| Infer_app  :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty),
    Infer Γ t1 (TyFun A B) ->
    Check Γ t2 A ->
    Infer Γ (app t1 t2) B

with Check : Ctx -> Tm -> Ty -> Prop :=
| Check_Infer :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Infer Γ t A ->
    Check Γ t A
| Check_abs :
  forall (Γ : Ctx) (t : Tm) (A B : Ty) (l : list Atom)
    (Hcof : forall x : Atom, x # l -> Check ((x, A) :: Γ) (t {{0 ~> x}}) B),
    Check Γ (abs t) (TyFun A B).

#[export] Hint Constructors Infer Check : core.

Lemma Typing_Infer :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> Infer Γ t A -> Typing Γ t A

with Typing_Check :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> Check Γ t A -> Typing Γ t A.
Proof.
  - intros Γ t A Hwf; destruct 1 as [Γ x A HB | Γ t1 t2 A B HI1 HC2].
    + now constructor.
    + apply Typing_app with A.
      * now apply Typing_Infer.
      * now apply Typing_Check.
  - intros Γ t A Hwf; destruct 1 as [Γ t A Hi | Γ t A B l Hcof].
    + now apply Typing_Infer.
    + apply Typing_abs with (l ++ map fst Γ); intros x Hx.
      red in Hx; rewrite in_app_iff in Hx.
      apply Typing_Check.
      * now firstorder.
      * now apply Hcof; firstorder.
Qed.

Inductive Contraction : Tm -> Tm -> Prop :=
| Contraction_Fun :
  forall (t1 t2 : Tm),
    lc (abs t1) ->
    Value t2 ->
    Contraction (app (abs t1) t2) (t1 {[ 0 ~> t2 ]}).

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

Module inductive.

Inductive Step' : Tm -> Tm -> Prop :=
| mkStep' :
  forall (E : EvalCtx) (t t' : Tm),
    Contraction t t' -> Step' (plug E t) (plug E t').

Hint Constructors Step' : core.

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

End inductive.

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

Lemma preservation_Contraction :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    Contraction t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  induction 1; inversion 1; subst.
  inversion H5; subst.
  rewrite open'_from_subst with (x := fresh (l ++ fv t1)) by solve_fresh.
  apply Typing_subst with A0; [| easy].
  apply H6.
  now solve_fresh.
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

End ex.

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

End record.
