From FormalSystems Require Export LocallyNameless.LocallyNameless.

(** * Types *)

Inductive Ty : Type :=
| TyFun   : Ty -> Ty -> Ty
| TyUnit  : Ty
| TyEmpty : Ty
| TyProd  : Ty -> Ty -> Ty
| TySum   : Ty -> Ty -> Ty.

Fixpoint eq_dec_Ty (A B : Ty) : {A = B} + {A <> B}.
Proof.
  decide equality.
Defined.

#[export, refine] Instance Decidable_eq_Ty :
  forall A B : Ty, Decidable (A = B) :=
{
  Decidable_witness :=
    match eq_dec_Ty A B with
    | left _  => true
    | right _ => false
    end
}.
Proof.
  now destruct (eq_dec_Ty A B).
Defined.

(** * Terms *)

Inductive Tm : Type :=
| fvar       : Atom -> Tm
| bvar       : nat -> Tm
| abs        : Tm -> Tm
| app        : Tm -> Tm -> Tm
| unit       : Tm
| elimUnit   : Tm -> Tm -> Tm
| elimUnit'  : Tm -> Tm -> Tm
| elimUnit'' : Tm
| abort      : Tm -> Tm
| pair       : Tm -> Tm -> Tm
| outl       : Tm -> Tm
| outr       : Tm -> Tm
| inl        : Tm -> Tm
| inr        : Tm -> Tm
| case       : Tm.

Coercion fvar : Atom >-> Tm.
Coercion bvar : nat >-> Tm.

Fixpoint eq_dec_Tm (t u : Tm) : {t = u} + {t <> u}.
Proof.
  decide equality.
  - exact (eq_dec_Atom a a0).
  - exact (PeanoNat.Nat.eq_dec n n0).
Defined.

#[export, refine] Instance Decidable_eq_Tm :
  forall t u : Tm, Decidable (t = u) :=
{
  Decidable_witness :=
    match eq_dec_Tm t u with
    | left _  => true
    | right _ => false
    end
}.
Proof.
  now destruct (eq_dec_Tm t u).
Defined.

(** ** Opening and closing *)

#[export] Instance Open_Tm : Open nat Atom Tm :=
  fix open (t : Tm) (i : nat) (a : Atom) : Tm :=
    match t with
    | fvar a          => fvar a
    | bvar j          => if decide (i = j) then a else bvar j
    | abs t'          => abs (open t' (S i) a)
    | app t1 t2       => app (open t1 i a) (open t2 i a)
    | unit            => unit
    | elimUnit t1 t2  => elimUnit (open t1 i a) (open t2 (S i) a)
    | elimUnit' t1 t2 => elimUnit' (open t1 i a) (open t2 i a)
    | elimUnit''      => elimUnit''
    | abort t'        => abort (open t' i a)
    | pair t1 t2      => pair (open t1 i a) (open t2 i a)
    | outl t'         => outl (open t' i a)
    | outr t'         => outr (open t' i a)
    | inl t'          => inl (open t' i a)
    | inr t'          => inr (open t' i a)
    | case            => case
    end.

#[export] Instance Close_Tm : Close nat Atom Tm :=
  fix close (t : Tm) (i : nat) (a : Atom) : Tm :=
    match t with
    | fvar x          => if decide (a = x) then bvar i else fvar x
    | bvar n          => bvar n
    | abs t'          => abs (close t' (S i) a)
    | app t1 t2       => app (close t1 i a) (close t2 i a)
    | unit            => unit
    | elimUnit t1 t2  => elimUnit (close t1 i a) (close t2 (S i) a)
    | elimUnit' t1 t2 => elimUnit' (close t1 i a) (close t2 i a)
    | elimUnit''      => elimUnit''
    | abort t'        => abort (close t' i a)
    | pair t1 t2      => pair (close t1 i a) (close t2 i a)
    | outl t'         => outl (close t' i a)
    | outr t'         => outr (close t' i a)
    | inl t'          => inl (close t' i a)
    | inr t'          => inr (close t' i a)
    | case            => case
    end.

#[export, refine] Instance OC_Tm :
  OC nat Atom Tm Open_Tm Close_Tm := {}.
Proof.
  all: induction t; cbn; intros;
    decide_all; rewrite 1?IHt, 1?IHt1, 1?IHt2; congruence.
Qed.

Lemma open_open :
  forall (t : Tm) (i j : nat) (a b : Atom),
    i <> j ->
    t {{ i ~> a }} {{ j ~> b }} = t {{ i ~> a }} ->
      t {{ j ~> b }} = t.
Proof.
  now induction t; cbn; intros i j u1 u2 Hij [=]; f_equal; [decide_all | eauto..].
Qed.

(** ** Locally nameless *)

Fixpoint fv (t : Tm) : list Atom :=
match t with
| fvar x     => [x]
| bvar _     => []
| abs t'     => fv t'
| app t1 t2  => fv t1 ++ fv t2
| unit       => []
| elimUnit t1 t2 => fv t1 ++ fv t2
| elimUnit' t1 t2 => fv t1 ++ fv t2
| elimUnit'' => []
| abort t'   => fv t'
| pair t1 t2 => fv t1 ++ fv t2
| outl t'    => fv t'
| outr t'    => fv t'
| inl t'     => fv t'
| inr t'     => fv t'
| case       => []
end.

#[export, refine] Instance LocallyNameless_Tm :
  LocallyNameless Atom Tm Open_Tm Close_Tm OC_Tm :=
{
  fv := fv;
}.
Proof.
  - unfold supports, Fresh'.
    induction t; cbn; only 1: rename a into b; intros a Ha;
      try (now rewrite 1?IHt, 1?IHt1, 1?IHt2 by solve_fresh).
    + now firstorder decide_all.
    + now f_equal; rewrite close_invariant, IHt.
    + rewrite IHt1 by solve_fresh; f_equal.
      now rewrite close_invariant, IHt2 by solve_fresh.
  - intros t.
    setoid_rewrite LocallyClosed_forall.
    induction t; cbn;
      try (now exists 0);
      try (now destruct IHt as [i IH]; exists i; intros j a Hij; rewrite IH; [| lia]);
      try (now destruct IHt1 as [i1 IH1], IHt2 as [i2 IH2];
        exists (max i1 i2); intros j a Hle; rewrite IH1, IH2; [| lia..]).
    exists (S n); intros j a Hij.
    now decide_all; lia.
Defined.

(** ** Characterization of local closure *)

Inductive LocallyClosed' : nat -> Tm -> Prop :=
| LocallyClosed'_fvar :
  forall (i : nat) (x : Atom),
    LocallyClosed' i x
| LocallyClosed'_bvar :
  forall (i n : nat),
    n < i -> LocallyClosed' i (bvar n)
| LocallyClosed'_abs :
  forall (i : nat) (t' : Tm),
    LocallyClosed' (S i) t' -> LocallyClosed' i (abs t')
| LocallyClosed'_app :
  forall (i : nat) (t1 t2 : Tm),
    LocallyClosed' i t1 -> LocallyClosed' i t2 -> LocallyClosed' i (app t1 t2)
| LocallyClosed'_unit :
  forall i : nat,
    LocallyClosed' i unit
| LocallyClosed'_elimUnit :
  forall (i : nat) (t1 t2 : Tm),
    LocallyClosed' i t1 ->
    LocallyClosed' (S i) t2 ->
    LocallyClosed' i (elimUnit t1 t2)
| LocallyClosed'_elimUnit' :
  forall (i : nat) (t1 t2 : Tm),
    LocallyClosed' i t1 ->
    LocallyClosed' i t2 ->
    LocallyClosed' i (elimUnit' t1 t2)
| LocallyClosed'_elimUnit'' :
  forall (i : nat),
    LocallyClosed' i elimUnit''
| LocallyClosed'_abort :
  forall (i : nat) (t' : Tm),
    LocallyClosed' i t' -> LocallyClosed' i (abort t')
| LocallyClosed'_pair :
  forall (i : nat) (t1 t2 : Tm),
    LocallyClosed' i t1 -> LocallyClosed' i t2 -> LocallyClosed' i (pair t1 t2)
| LocallyClosed'_outl :
  forall (i : nat) (t' : Tm),
    LocallyClosed' i t' -> LocallyClosed' i (outl t')
| LocallyClosed'_outr :
  forall (i : nat) (t' : Tm),
    LocallyClosed' i t' -> LocallyClosed' i (outr t')
| LocallyClosed'_inl :
  forall (i : nat) (t' : Tm),
    LocallyClosed' i t' -> LocallyClosed' i (inl t')
| LocallyClosed'_inr :
  forall (i : nat) (t' : Tm),
    LocallyClosed' i t' -> LocallyClosed' i (inr t')
| LocallyClosed'_case :
  forall (i : nat),
    LocallyClosed' i case.


#[export] Hint Constructors LocallyClosed' : core.

Lemma LocallyClosed'_spec :
  forall (i : nat) (t : Tm),
    LocallyClosed' i t <-> LocallyClosed i t.
Proof.
  setoid_rewrite LocallyClosed_forall.
  split.
  - induction 1; intros j a Hij; cbn; try (now f_equal; eauto).
    + now decide_all; lia.
    + now rewrite IHLocallyClosed'; [| lia].
    + now rewrite IHLocallyClosed'1, IHLocallyClosed'2; [| lia..].
  - revert i.
    induction t; cbn; intros i Hlc; constructor; try easy;
    try match goal with
    | IH : forall _, _ -> LocallyClosed' _ ?t  |- LocallyClosed' _ ?t =>
      now apply IH; intros j a Hij; injection (Hlc j a Hij)
    end.
    + destruct (PeanoNat.Nat.lt_ge_cases n i); [easy |].
      specialize (Hlc n (fresh []) H).
      now decide_all.
    + apply IHt; intros [| j'] a Hle; [now lia |].
      now injection (Hlc j' a ltac:(lia)).
    + apply IHt2; intros [| j'] a Hle; [now lia |].
      now injection (Hlc j' a ltac:(lia)).
Qed.

Lemma open_LocallyClosed' :
  forall (t : Tm) (i j : nat) (a : Atom),
    i <= j -> LocallyClosed' i t -> t {{ j ~> a }} = t.
Proof.
  intros t i j a Hij Hlc.
  apply open_LocallyClosed with j; [| now lia].
  now eapply LocallyClosed_le, LocallyClosed'_spec; eauto.
Qed.

(** ** Characterization of freshness *)

Lemma Fresh'_spec :
  forall (x : Atom) (t : Tm),
    Fresh' x t <-> x # fv t.
Proof.
  split; [| now rapply supports_fv].
  unfold Fresh, Fresh'.
  induction t; cbn; intros [=]; rewrite ?in_app_iff;
    try now firstorder congruence.
  - now firstorder decide_all.
  - apply IHt.
    now rewrite (close_invariant _ 0 1).
  - intros []; [now apply IHt1; congruence |].
    apply IHt2; [| easy].
    now rewrite (close_invariant _ 0 1).
Qed.

(** ** Substitution *)

Fixpoint subst (t : Tm) (x : Atom) (u : Tm) : Tm :=
match t with
| fvar y     => if decide (x = y) then u else fvar y
| bvar n     => bvar n
| abs t'     => abs (subst t' x u)
| app t1 t2  => app (subst t1 x u) (subst t2 x u)
| unit       => unit
| elimUnit t1 t2 => elimUnit (subst t1 x u) (subst t2 x u)
| elimUnit' t1 t2 => elimUnit' (subst t1 x u) (subst t2 x u)
| elimUnit'' => elimUnit''
| abort t'   => abort (subst t' x u)
| pair t1 t2 => pair (subst t1 x u) (subst t2 x u)
| outl t'    => outl (subst t' x u)
| outr t'    => outr (subst t' x u)
| inl t'     => inl (subst t' x u)
| inr t'     => inr (subst t' x u)
| case       => case
end.

Notation "t [[ x := u ]]" := (subst t x u) (at level 68).

Lemma subst_fv :
  forall (t : Tm) (x : Atom) (u : Tm),
    x # fv t -> t [[ x := u ]] = t.
Proof.
  now induction t; cbn; intros;
    [firstorder decide_all | rewrite 1?IHt, 1?IHt1, 1?IHt2 by solve_fresh..].
Qed.

(** ** Opening with a term *)

Fixpoint open' (t : Tm) (i : nat) (u : Tm) : Tm :=
match t with
| fvar a     => fvar a
| bvar j     => if decide (i = j) then u else bvar j
| abs t'     => abs (open' t' (S i) u)
| app t1 t2  => app (open' t1 i u) (open' t2 i u)
| unit       => unit
| elimUnit t1 t2 => elimUnit (open' t1 i u) (open' t2 (S i) u)
| elimUnit' t1 t2 => elimUnit' (open' t1 i u) (open' t2 i u)
    | elimUnit'' => elimUnit''
| abort t'   => abort (open' t' i u)
| pair t1 t2 => pair (open' t1 i u) (open' t2 i u)
| outl t'    => outl (open' t' i u)
| outr t'    => outr (open' t' i u)
| inl t'     => inl (open' t' i u)
| inr t'     => inr (open' t' i u)
| case       => case
end.

Notation "t {[ i ~> u ]}" := (open' t i u) (at level 68).

Lemma open'_atom :
  forall (t : Tm) (i : nat) (a : Atom),
    t {[ i ~> a ]} = t {{ i ~> a }}.
Proof.
  now induction t; cbn; firstorder congruence.
Qed.

Lemma open'_spec :
  forall (t : Tm) (i : nat) (x : Atom) (u : Tm),
    x # fv t ->
      t {[ i ~> u ]} = t {{ i ~> x }} [[ x := u ]].
Proof.
  induction t; cbn; intros;
    try now rewrite <- 1?IHt, 1?(IHt1 _ x), 1?(IHt2 _ x) by solve_fresh.
  - now firstorder decide_all.
  - now decide_all.
Qed.

Lemma open'_open' :
  forall (t : Tm) (i j : nat) (u1 u2 : Tm),
    i <> j ->
    t {[ i ~> u1 ]} {[ j ~> u2 ]} = t {[ i ~> u1 ]} ->
      t {[ j ~> u2 ]} = t.
Proof.
  now induction t; cbn; intros i j u1 u2 Hij [=]; f_equal; [decide_all | eauto..].
Qed.

(** ** Local closure *)

Inductive lc : Tm -> Prop :=
| lc_fvar :
  forall x : Atom,
    lc x
| lc_abs :
  forall (t' : Tm) (l : list Atom)
    (Hlc' : forall x : Atom, x # l -> lc (t' {{ 0 ~> x }})),
    lc (abs t')
| lc_app :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    lc (app t1 t2)
| lc_unit : lc unit
| lc_elimUnit :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }})),
    lc (elimUnit t1 t2)
| lc_elimUnit' :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    lc (elimUnit' t1 t2)
| lc_elimUnit'' : lc elimUnit''
| lc_abort :
  forall (t' : Tm)
    (Hlc' : lc t'),
    lc (abort t')
| lc_pair :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    lc (pair t1 t2)
| lc_outl :
  forall (t' : Tm)
    (Hlc' : lc t'),
    lc (outl t')
| lc_outr :
  forall (t' : Tm)
    (Hlc' : lc t'),
    lc (outr t')
| lc_inl :
  forall (t' : Tm)
    (Hlc' : lc t'),
    lc (inl t')
| lc_inr :
  forall (t' : Tm)
    (Hlc' : lc t'),
    lc (inr t')
| lc_case : lc case.

#[export] Hint Constructors lc : core.

Lemma LocallyClosed_lc :
  forall t : Tm,
    lc t -> LocallyClosed 0 t.
Proof.
  setoid_rewrite LocallyClosed_forall.
  induction 1; cbn; intros j a Hle; f_equal; try now unshelve eauto.
  - now eapply open_open, (H _ (fresh_spec l)); lia.
  - now eapply open_open, (H0 _ (fresh_spec l)); lia.
Qed.

Lemma open_lc :
  forall (t : Tm) (i : nat) (a : Atom),
    lc t -> t {{ i ~> a }} = t.
Proof.
  intros.
  apply open_LocallyClosed with i; [| now lia].
  now eapply LocallyClosed_le, LocallyClosed_lc; [lia |].
Qed.

Lemma lc_open :
  forall (t : Tm) (i : nat) (a : Atom),
    lc t -> lc (t {{ i ~> a }}).
Proof.
  now intros; rewrite open_lc.
Qed.

Lemma open_subst :
  forall (t : Tm) (i : nat) (a b x : Atom),
    t {{ i ~> a }} [[ x := b ]]
      =
    t [[ x := b ]] {{ i ~> if decide (a = x) then b else a }}.
Proof.
  now induction t; cbn; intros;
    [decide_all | decide_all | rewrite 1?IHt, 1?IHt1, 1?IHt2..].
Qed.

Lemma subst_open :
  forall (t : Tm) (a b : Atom) (i : nat) (u : Tm),
    a <> b -> lc u ->
    t [[ a := u ]] {{ i ~> b }} = t {{ i ~> b }} [[ a := u ]].
Proof.
  induction t; cbn; intros; [| | now rewrite 1?IHt, 1?IHt1, 1?IHt2..].
  - decide_all.
    now rewrite open_lc.
  - now decide_all.
Qed.

Lemma lc_subst :
  forall (t : Tm) (x : Atom) (u : Tm),
    lc t -> lc u -> lc (t [[ x := u ]]).
Proof.
  intros t x u Ht Hu; revert x u Hu.
  induction Ht; cbn; intros; try now eauto.
  - now decide_all.
  - apply lc_abs with (x :: l).
    intros y Hy.
    now rewrite subst_open; firstorder.
  - apply lc_elimUnit with (x :: l); [now apply IHHt |].
    intros y Hy.
    now rewrite subst_open; firstorder.
Qed.

Lemma open'_lc :
  forall (t : Tm) (i : nat) (u : Tm),
    lc t -> t {[ i ~> u ]} = t.
Proof.
  intros t i u Hlc.
  rewrite (open'_spec _ _ (fresh (fv t))) by solve_fresh.
  rewrite (open_LocallyClosed t i); [.. | now lia].
  - now rewrite subst_fv by solve_fresh.
  - apply LocallyClosed_le with 0; [now lia |].
    now apply LocallyClosed_lc.
Qed.

Lemma lc_open' :
  forall (t u : Tm),
    lc (abs t) -> lc u ->
      lc (t {[ 0 ~> u ]}).
Proof.
  inversion 1; intros Hu.
  rewrite (open'_spec _ _ (fresh (l ++ fv t))) by solve_fresh.
  apply lc_subst; [| easy].
  apply Hlc'.
  now solve_fresh.
Qed.

Lemma lc_open'' :
  forall (t : Tm) (i : nat) (u : Tm),
    lc t -> lc (t {[ i ~> u ]}).
Proof.
  now intros; rewrite open'_lc.
Qed.

Lemma open'_subst :
  forall (t : Tm) (i : nat) (u1 : Tm) (x : Atom) (u2 : Tm),
    lc u2 ->
    t {[ i ~> u1 ]} [[ x := u2 ]]
      =
    t [[ x := u2 ]] {[ i ~> u1 [[ x := u2 ]] ]}.
Proof.
  induction t; cbn; intros; [| | now rewrite 1?IHt, 1?IHt1, 1?IHt2..].
  - decide_all.
    now rewrite open'_lc.
  - now decide_all.
Qed.

(** * Contexts *)

Definition Ctx : Type := list (Atom * Ty).

Inductive WfCtx : Ctx -> Prop :=
| WfCtx_nil  : WfCtx []
| WfCtx_cons :
    forall (Γ : Ctx) (x : Atom) (A : Ty)
      (Hwf : WfCtx Γ)
      (Hdom : x # map fst Γ),
      WfCtx ((x, A) :: Γ).

#[export] Hint Constructors WfCtx : core.

Lemma WfCtx_app_cons :
  forall (Γ1 Γ2 : Ctx) (x : Atom) (A : Ty),
    WfCtx (Γ2 ++ (x, A) :: Γ1) -> WfCtx (Γ2 ++ Γ1).
Proof.
  induction Γ2 as [| [y B] Γ2' IH]; cbn; inversion 1; [easy |].
  constructor.
  - now apply IH in Hwf.
  - unfold Fresh in *; rewrite map_app, !in_app_iff in *; cbn in *.
    now firstorder.
Qed.

#[export] Hint Resolve WfCtx_app_cons : core.

(** * Binding variables in context *)

Definition Binds (Γ : Ctx) (x : Atom) (A : Ty) : Prop :=
  In (x, A) Γ.

Lemma Binds_inv :
  forall (Γ : Ctx) (x : Atom) (A B : Ty),
    WfCtx Γ -> Binds Γ x A -> Binds Γ x B -> A = B.
Proof.
  induction 1; cbn; [easy |].
  intros [ [= -> ->] |] [ [= ->] |]; [easy | ..].
  - contradiction Hdom.
    rewrite in_map_iff.
    now exists (x, B).
  - contradiction Hdom.
    rewrite in_map_iff.
    now exists (x, A).
  - now apply IHWfCtx.
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
  - intros x y A B [ [= ->] | ]; [now firstorder |].
    apply IHΔ in H.
    now firstorder.
Qed.

(** * Typing *)

Inductive Typing : Ctx -> Tm -> Ty -> Prop :=
| Typing_fvar :
  forall (Γ : Ctx) (x : Atom) (A : Ty)
    (Hwf : WfCtx Γ)
    (HB : Binds Γ x A),
    Typing Γ x A
| Typing_abs :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty) (l : list Atom)
    (Ht' : forall x : Atom, x # l -> Typing ((x, A) :: Γ) (t' {{ 0 ~> x }}) B),
    Typing Γ (abs t') (TyFun A B)
| Typing_app :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty)
    (Ht1 : Typing Γ t1 (TyFun A B))
    (Ht2 : Typing Γ t2 A),
    Typing Γ (app t1 t2) B
| Typing_unit :
  forall (Γ : Ctx)
    (Hwf : WfCtx Γ),
    Typing Γ unit TyUnit
| Typing_elimUnit :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty) (l : list Atom)
    (Ht1 : Typing Γ t1 TyUnit)
    (Ht2 : forall x : Atom, x # l -> Typing ((x, TyUnit) :: Γ) (t2 {{ 0 ~> x }}) A),
    Typing Γ (elimUnit t1 t2) A
| Typing_elimUnit' :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty)
    (Ht1 : Typing Γ t1 TyUnit)
    (Ht2 : Typing Γ t2 (TyFun TyUnit A)),
    Typing Γ (elimUnit' t1 t2) A
| Typing_elimUnit'' :
  forall (Γ : Ctx) (A : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ elimUnit'' (TyFun (TyFun TyUnit A) (TyFun TyUnit A))
| Typing_abort :
  forall (Γ : Ctx) (t' : Tm) (A : Ty)
    (Ht' : Typing Γ t' TyEmpty),
    Typing Γ (abort t') A
| Typing_pair :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty)
    (Ht1 : Typing Γ t1 A)
    (Ht2 : Typing Γ t2 B),
    Typing Γ (pair t1 t2) (TyProd A B)
| Typing_outl :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Ht' : Typing Γ t' (TyProd A B)),
    Typing Γ (outl t') A
| Typing_outr :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Ht' : Typing Γ t' (TyProd A B)),
    Typing Γ (outr t') B
| Typing_inl :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Ht' : Typing Γ t' A),
    Typing Γ (inl t') (TySum A B)
| Typing_inr :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Ht' : Typing Γ t' B),
    Typing Γ (inr t') (TySum A B)
| Typing_case :
  forall (Γ : Ctx) (A B C : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ case (TyFun (TyFun A C) (TyFun (TyFun B C) (TyFun (TySum A B) C))).

#[export] Hint Constructors Typing : core.

Lemma lc_Typing :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Typing Γ t A -> lc t.
Proof.
  now induction 1; eauto.
Qed.

Lemma WfCtx_Typing :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Typing Γ t A -> WfCtx Γ.
Proof.
  induction 1; try easy.
  apply (WfCtx_app_cons _ [] (fresh l) A), H.
  now solve_fresh.
Qed.

#[export] Hint Resolve lc_Typing WfCtx_Typing : core.

(** ** Weakening *)

Lemma weakening_aux :
  forall (Γ1 Γ2 Δ : Ctx) (t : Tm) (A : Ty),
    Typing (Γ1 ++ Γ2) t A ->
    WfCtx (Γ1 ++ Δ ++ Γ2) ->
    Typing (Γ1 ++ Δ ++ Γ2) t A.
Proof.
  intros * Ht.
  remember (Γ1 ++ Γ2) as G.
  revert Γ1 Γ2 Δ HeqG.
  induction Ht; intros; subst; try now unshelve eauto.
  - constructor; [easy |].
    unfold Binds in *.
    rewrite !in_app_iff; rewrite in_app_iff in HB.
    now firstorder.
  - apply Typing_abs with (l ++ map fst Γ1 ++ map fst Δ ++ map fst Γ2).
    intros x Hx.
    rewrite app_comm_cons.
    apply H; [now solve_fresh | easy |].
    cbn; constructor; [easy |].
    rewrite !map_app.
    now solve_fresh.
  - apply Typing_elimUnit with (l ++ map fst Γ1 ++ map fst Δ ++ map fst Γ2);
      [now apply IHHt |].
    intros x Hx.
    rewrite app_comm_cons.
    apply H; [now solve_fresh | easy |].
    cbn; constructor; [easy |].
    rewrite !map_app.
    now solve_fresh.
Qed.

Lemma weakening :
  forall (Γ Δ : Ctx) (t : Tm) (A : Ty),
    WfCtx (Δ ++ Γ) ->
    Typing Γ t A ->
    Typing (Δ ++ Γ) t A.
Proof.
  now intros; apply weakening_aux with (Γ1 := []); cbn.
Qed.

#[export] Hint Resolve weakening_aux weakening : core.

(** ** Substitution *)

Lemma Typing_subst_aux :
  forall (Γ Δ : Ctx) (x : Atom) (t u : Tm) (A B : Ty),
    Typing (Δ ++ (x, A) :: Γ) t B ->
    Typing Γ u A ->
    Typing (Δ ++ Γ) (t [[ x := u ]]) B.
Proof.
  intros * Ht Hu.
  remember (Δ ++ (x, A) :: Γ) as G.
  revert Δ x A Γ HeqG Hu.
  induction Ht; cbn; intros; subst; try now unshelve eauto.
  - apply WfCtx_app_cons in Hwf as Hwf'.
    decide (x0 = x); subst.
    + replace A with A0; [now apply weakening |].
      symmetry.
      eapply (Binds_inv _ _ _ _ Hwf HB).
      red; rewrite in_app_iff; cbn.
      now firstorder.
    + apply Binds_app_cons_inv in HB as [ [-> ->] |]; [easy |].
      now constructor.
  - apply Typing_abs with (x :: l).
    intros y Hy.
    assert (x <> y /\ y # l) as [Hxy Hyl] by firstorder.
    rewrite subst_open by eauto.
    now eapply (H y Hyl ((y, A) :: Δ)).
  - apply Typing_elimUnit with (x :: l); [now eapply IHHt |].
    intros y Hy.
    assert (x <> y /\ y # l) as [Hxy Hyl] by firstorder.
    rewrite subst_open; [| now firstorder | now eauto].
    now eapply (H y Hyl ((y, TyUnit) :: Δ)).
Qed.

Lemma Typing_subst :
  forall (Γ : Ctx) (x : Atom) (t u : Tm) (A B : Ty),
    Typing ((x, A) :: Γ) t B ->
    Typing Γ u A ->
    Typing Γ (t [[ x := u ]]) B.
Proof.
  now intros; eapply Typing_subst_aux with (Δ := []) (A := A).
Qed.

#[export] Hint Resolve Typing_subst_aux Typing_subst : core.

(** * Computation *)

(** ** Values *)

Inductive Value : Tm -> Prop :=
| Value_abs  :
  forall t : Tm,
    lc (abs t) ->
    Value (abs t)
| Value_unit : Value unit
| Value_elimUnit'' : Value elimUnit''
| Value_abort :
  forall t' : Tm,
    lc t' ->
    Value (abort t')
| Value_pair :
  forall t1 t2 : Tm,
    Value t1 ->
    Value t2 ->
    Value (pair t1 t2)
| Value_inl :
  forall v : Tm,
    Value v ->
    Value (inl v)
| Value_inr :
  forall v : Tm,
    Value v ->
    Value (inr v)
| Value_case : Value case
| Value_case1 :
  forall (t1 : Tm),
    lc t1 ->
    Value (app case t1)
| Value_case2 :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    Value (app (app case t1) t2).

#[export] Hint Constructors Value : core.

Lemma lc_Value :
  forall t : Tm,
    Value t -> lc t.
Proof.
  now induction 1; eauto.
Qed.

#[export] Hint Resolve lc_Value : core.

(** * Computation *)

(** ** Contraction *)

Inductive Contraction : Tm -> Tm -> Prop :=
| Contraction_Fun :
  forall (t1 t2 : Tm)
    (Hlc1 : lc (abs t1))
    (Hv2 : Value t2),
    Contraction (app (abs t1) t2) (t1 {[ 0 ~> t2 ]})
| Contraction_Unit :
  forall (t : Tm) (l : list Atom)
    (Hlc : forall x : Atom, x # l -> lc (t {{0 ~> x}})),
    Contraction (elimUnit unit t) (t {[ 0 ~> unit ]})
| Contraction_Unit' :
  forall (t : Tm)
    (Hlc : lc t),
    Contraction (elimUnit' unit t) (app t unit)
| Contraction_Unit'' :
  forall (t : Tm)
    (Hlc : lc t),
    Contraction (app elimUnit'' t) t
| Contraction_OutlPair :
  forall (v1 v2 : Tm)
    (Hv1 : Value v1)
    (Hv2 : Value v2),
    Contraction (outl (pair v1 v2)) v1
| Contraction_OutrPair :
  forall (v1 v2 : Tm)
    (Hv1 : Value v1)
    (Hv2 : Value v2),
    Contraction (outr (pair v1 v2)) v2
| Contraction_CaseInl :
  forall (t1 t2 v : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv : Value v),
    Contraction (app (app (app case t1) t2) (inl v)) (app t1 v)
| Contraction_CaseInr :
  forall (t1 t2 v : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv : Value v),
    Contraction (app (app (app case t1) t2) (inr v)) (app t2 v).

#[export] Hint Constructors Contraction : core.

Lemma lc_Contraction_l :
  forall t t' : Tm,
    Contraction t t' -> lc t.
Proof.
  now inversion 1; subst; eauto 6.
Qed.

Lemma lc_Contraction_r :
  forall t t' : Tm,
    Contraction t t' -> lc t'.
Proof.
  inversion 1; subst; try now unshelve eauto.
  - now apply lc_open'; eauto.
  - rewrite (open'_spec _ _ (fresh (l ++ fv t0))) by solve_fresh.
    apply lc_subst; [| easy].
    apply Hlc.
    now solve_fresh.
Qed.

#[export] Hint Resolve lc_Contraction_l lc_Contraction_r : core.

Lemma preservation_Contraction :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    Contraction t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  induction 1; inversion 1; subst.
  - inversion Ht1; subst.
    rewrite open'_spec with (x := fresh (l ++ fv t1)) by solve_fresh.
    apply Typing_subst with A0; [| easy].
    apply Ht'.
    now solve_fresh.
  - rewrite open'_spec with (x := fresh (l0 ++ fv t)) by solve_fresh.
    apply Typing_subst with TyUnit; [| easy].
    apply Ht2.
    now solve_fresh.
  - now apply Typing_app with TyUnit.
  - now inversion Ht1; subst.
  - now inversion Ht'.
  - now inversion Ht'.
  - now inversion Ht1; inversion Ht2; inversion Ht0; inversion Ht4; subst;
      inversion H15; subst; eauto.
  - now inversion Ht1; inversion Ht2; inversion Ht0; inversion Ht4; subst;
      inversion H15; subst; eauto.
Qed.

Inductive Abortion : Tm -> Tm -> Prop :=
| Abortion_Fun :
  forall (t1 t2 : Tm),
    lc t1 ->
    lc t2 ->
    Abortion (app (abort t1) t2) (abort t1)
| Abortion_Unit :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hcof : forall x : Atom, x # l -> lc (t2 {{0 ~> x}})),
    Abortion (elimUnit (abort t1) t2) (abort t1)
| Abortion_Unit' :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    Abortion (elimUnit' (abort t1) t2) (abort t1)
| Abortion_OutlPair :
  forall t : Tm,
    lc t ->
    Abortion (outl (abort t)) (abort t)
| Abortion_OutrPair :
  forall t : Tm,
    lc t ->
    Abortion (outr (abort t)) (abort t)
| Abortion_Inl :
  forall (t : Tm)
    (Hlc : lc t),
    Abortion (inl (abort t)) (abort t)
| Abortion_Inr :
  forall (t : Tm)
    (Hlc : lc t),
    Abortion (inr (abort t)) (abort t)
| Abort_Case :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    Abortion (app (app (app case t1) t2) (abort t3)) (abort t3).

#[export] Hint Constructors Abortion : core.

Lemma lc_Abortion_l :
  forall t t' : Tm,
    Abortion t t' -> lc t.
Proof.
  now inversion 1; subst; eauto.
Qed.

Lemma lc_Abortion_r :
  forall t t' : Tm,
    Abortion t t' -> lc t'.
Proof.
  now inversion 1; subst; eauto.
Qed.

#[export] Hint Resolve lc_Abortion_l lc_Abortion_r : core.

Lemma preservation_Abortion :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    Abortion t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  induction 1; inversion 1; subst; constructor.
  - now inversion Ht1.
  - now inversion Ht1.
  - now inversion Ht1.
  - now inversion Ht'.
  - now inversion Ht'.
  - now inversion Ht'.
  - now inversion Ht'.
  - now inversion Ht2.
Qed.

(** ** Reduction *)

Inductive Step : Tm -> Tm -> Prop :=
| Step_Contraction :
  forall t t' : Tm,
    Contraction t t' ->
    Step t t'
| Step_Abortion :
  forall t t' : Tm,
    Abortion t t' ->
    Step t t'
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
| Step_ElimUnitCongr :
  forall (t1 t1' t2 : Tm) (l : list Atom)
    (Hcof : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }})),
    Step t1 t1' ->
    Step (elimUnit t1 t2) (elimUnit t1' t2)
| Step_ElimUnitCongr' :
  forall (t1 t1' t2 : Tm)
    (Hlc2 : lc t2),
    Step t1 t1' ->
    Step (elimUnit' t1 t2) (elimUnit' t1' t2)
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
    Step (outr t) (outr t')
| Step_InlCongr :
  forall t t' : Tm,
    Step t t' ->
    Step (inl t) (inl t')
| Step_InrCongr :
  forall t t' : Tm,
    Step t t' ->
    Step (inr t) (inr t').

#[export] Hint Constructors Step : core.

Lemma lc_Step_l :
  forall t t' : Tm,
    Step t t' -> lc t.
Proof.
  now induction 1; eauto.
Qed.

Lemma lc_Step_r :
  forall t t' : Tm,
    Step t t' -> lc t'.
Proof.
  now induction 1; eauto.
Qed.

#[export] Hint Resolve lc_Step_l lc_Step_r : core.

(** ** Progress and preservation *)

Lemma preservation :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    Step t1 t2 ->
    Typing Γ t1 A ->
    Typing Γ t2 A.
Proof.
  intros Γ t1 t2 A Hstep; revert A.
  induction Hstep; intros A; [| | now inversion 1; subst; eauto..].
  - now eapply preservation_Contraction.
  - now eapply preservation_Abortion.
Qed.

Lemma progress :
  forall (t : Tm) (A : Ty),
    Typing [] t A ->
      Value t \/ exists t' : Tm, Step t t'.
Proof.
  intros t A Ht.
  remember [] as Γ.
  induction Ht; subst.
  - now inversion Hwf.
  - now left; eauto.
  - destruct (IHHt1 eq_refl) as [ Hv | [t1' Hs1] ]; [| now eauto].
    inversion Hv; subst; inversion Ht1; subst; try now eauto 6.
    + now destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; eauto.
    + destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; [| now eauto].
      inversion Ht0; inversion Ht4; subst.
      inversion Ht2; subst; inversion Hv2; subst; eauto.
      * inversion Ht2; subst; inversion Ht6.
      * inversion Ht2; subst; inversion Ht6; subst; inversion Ht10.
  - now left.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    inversion Hv; subst; inversion Ht; subst; eauto 6.
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt1 eq_refl) as [ Hv | [t1' Hs1] ]; [| now eauto].
    inversion Hv; subst; inversion Ht1; subst; eauto.
    + now inversion Ht1.
    + now inversion Ht0.
  - now left.
  - now left; eauto.
  - now destruct (IHHt1 eq_refl) as [| [] ], (IHHt2 eq_refl) as [| [] ]; eauto.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    inversion Hv; subst; inversion Ht; subst; eauto.
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    inversion Hv; subst; inversion Ht; subst; eauto.
    + now inversion Ht1.
    + now inversion Ht1.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - now left.
Qed.

(** * Bidirectional typing *)

Inductive Infer : Ctx -> Tm -> Ty -> Prop :=
| Infer_fvar :
  forall (Γ : Ctx) (x : Atom) (A : Ty)
    (HB : Binds Γ x A),
    Infer Γ x A
| Infer_app  :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty)
    (Hi1 : Infer Γ t1 (TyFun A B))
    (Hc2 : Check Γ t2 A),
    Infer Γ (app t1 t2) B
| Infer_unit :
  forall (Γ : Ctx),
    Infer Γ unit TyUnit
| Infer_elimUnit :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty) (l : list Atom)
    (Hc1 : Check Γ t1 TyUnit)
    (Hi2 : forall x : Atom, x # l -> Infer ((x, TyUnit) :: Γ) (t2 {{ 0 ~> x }}) A),
    Infer Γ (elimUnit t1 t2) A
| Infer_pair :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty)
    (Hi1 : Infer Γ t1 A)
    (Hi2 : Infer Γ t2 B),
    Infer Γ (pair t1 t2) (TyProd A B)
| Infer_outl :
  forall (Γ : Ctx) (t : Tm) (A B : Ty)
    (Hi : Infer Γ t (TyProd A B)),
    Infer Γ (outl t) A
| Infer_outr :
  forall (Γ : Ctx) (t : Tm) (A B : Ty)
    (Hi : Infer Γ t (TyProd A B)),
    Infer Γ (outr t) B

with Check : Ctx -> Tm -> Ty -> Prop :=
| Check_Infer :
  forall (Γ : Ctx) (t : Tm) (A : Ty)
    (Hi : Infer Γ t A),
    Check Γ t A
| Check_abs :
  forall (Γ : Ctx) (t : Tm) (A B : Ty) (l : list Atom)
    (Hc : forall x : Atom, x # l -> Check ((x, A) :: Γ) (t {{0 ~> x}}) B),
    Check Γ (abs t) (TyFun A B)
| Check_elimUnit' :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty)
    (Hc1 : Check Γ t1 TyUnit)
    (Hc2 : Check Γ t2 (TyFun TyUnit A)),
    Check Γ (elimUnit' t1 t2) A
| Check_elimUnit'' :
  forall (Γ : Ctx) (A : Ty),
    Check Γ elimUnit'' (TyFun (TyFun TyUnit A) (TyFun TyUnit A))
| Check_abort :
  forall (Γ : Ctx) (t' : Tm) (A : Ty)
    (Hc : Check Γ t' TyEmpty),
    Check Γ (abort t') A
| Check_pair :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty)
    (Hc1 : Check Γ t1 A)
    (Hc2 : Check Γ t2 B),
    Check Γ (pair t1 t2) (TyProd A B)
| Check_inl :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Hc : Check Γ t' A),
    Check Γ (inl t') (TySum A B)
| Check_inr :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Hc : Check Γ t' B),
    Check Γ (inr t') (TySum A B)
| Check_case :
  forall (Γ : Ctx) (A B C : Ty),
    Check Γ case (TyFun (TyFun A C) (TyFun (TyFun B C) (TyFun (TySum A B) C))).

#[export] Hint Constructors Infer Check : core.

Lemma Typing_Infer :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> Infer Γ t A -> Typing Γ t A

with Typing_Check :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> Check Γ t A -> Typing Γ t A.
Proof.
  - intros ? t A Hwf; destruct 1.
    + now constructor.
    + apply Typing_app with A.
      * now apply Typing_Infer.
      * now apply Typing_Check.
    + now constructor.
    + apply Typing_elimUnit with (l ++ map fst Γ).
      * now apply Typing_Check.
      * intros x Hx.
        apply Typing_Infer.
        -- now constructor; solve_fresh.
        -- now apply Hi2; solve_fresh.
    + now constructor; apply Typing_Infer.
    + now apply Typing_outl with B, Typing_Infer.
    + now apply Typing_outr with A, Typing_Infer.
  - intros Γ t A Hwf; destruct 1.
    + now apply Typing_Infer.
    + apply Typing_abs with (l ++ map fst Γ); intros x Hx.
      red in Hx; rewrite in_app_iff in Hx.
      apply Typing_Check.
      * now firstorder.
      * now apply Hc; firstorder.
    + constructor.
      * now apply Typing_Check.
      * now apply Typing_Check.
    + now constructor.
    + now constructor; apply Typing_Check.
    + constructor.
      * now apply Typing_Check.
      * now apply Typing_Check.
    + now constructor; apply Typing_Check.
    + now constructor; apply Typing_Check.
    + now constructor.
Qed.
