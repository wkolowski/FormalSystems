Require Import Bool.

From FormalSystems Require Export LocallyNameless.LocallyNameless.

(** * Types *)

Inductive Ty : Type :=
| TyFun   : Ty -> Ty -> Ty
| TyUnit  : Ty
| TyEmpty : Ty
| TyProd  : Ty -> Ty -> Ty
| TySum   : Ty -> Ty -> Ty
| TyNat   : Ty.

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
| annot      : Tm -> Ty -> Tm
| unit       : Tm
| elimUnit   : Tm -> Tm -> Tm
| abort      : Tm -> Tm
| pair       : Tm -> Tm -> Tm
| outl       : Tm -> Tm
| outr       : Tm -> Tm
| elimProd   : Tm -> Tm -> Tm
| inl        : Tm -> Tm
| inr        : Tm -> Tm
| case       : Tm -> Tm -> Tm -> Tm
| zero       : Tm
| succ       : Tm -> Tm
| rec        : Tm -> Tm -> Tm -> Tm.

Coercion fvar : Atom >-> Tm.
Coercion bvar : nat >-> Tm.

Fixpoint eq_dec_Tm (t u : Tm) : {t = u} + {t <> u}.
Proof.
  decide equality.
  - exact (eq_dec_Atom a a0).
  - exact (PeanoNat.Nat.eq_dec n n0).
  - exact (eq_dec_Ty t1 t3).
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

#[export] Hint Extern 1 (~ @eq Atom ?x ?y) =>
  try generalize dependent x;
  try generalize dependent y;
  clear; intros;
  solve_var x; solve_var y;
  firstorder congruence : core.

(** ** Opening and closing *)

#[export] Instance Open_Tm : Open nat Atom Tm :=
  fix open (t : Tm) (i : nat) (a : Atom) : Tm :=
    match t with
    | fvar a          => fvar a
    | bvar j          => if decide (i = j) then a else bvar j
    | abs t'          => abs (open t' (S i) a)
    | app t1 t2       => app (open t1 i a) (open t2 i a)
    | annot t' A      => annot (open t' i a) A
    | unit            => unit
    | elimUnit t1 t2  => elimUnit (open t1 i a) (open t2 i a)
    | abort t'        => abort (open t' i a)
    | pair t1 t2      => pair (open t1 i a) (open t2 i a)
    | outl t'         => outl (open t' i a)
    | outr t'         => outr (open t' i a)
    | elimProd t1 t2  => elimProd (open t1 i a) (open t2 i a)
    | inl t'          => inl (open t' i a)
    | inr t'          => inr (open t' i a)
    | case t1 t2 t3   => case (open t1 i a) (open t2 i a) (open t3 i a)
    | zero            => zero
    | succ t'         => succ (open t' i a)
    | rec t1 t2 t3    => rec (open t1 i a) (open t2 i a) (open t3 i a)
    end.

#[export] Instance Close_Tm : Close nat Atom Tm :=
  fix close (t : Tm) (i : nat) (a : Atom) : Tm :=
    match t with
    | fvar x          => if decide (a = x) then bvar i else fvar x
    | bvar n          => bvar n
    | abs t'          => abs (close t' (S i) a)
    | app t1 t2       => app (close t1 i a) (close t2 i a)
    | annot t' A      => annot (close t' i a) A
    | unit            => unit
    | elimUnit t1 t2  => elimUnit (close t1 i a) (close t2 i a)
    | abort t'        => abort (close t' i a)
    | pair t1 t2      => pair (close t1 i a) (close t2 i a)
    | outl t'         => outl (close t' i a)
    | outr t'         => outr (close t' i a)
    | elimProd t1 t2  => elimProd (close t1 i a) (close t2 i a)
    | inl t'          => inl (close t' i a)
    | inr t'          => inr (close t' i a)
    | case t1 t2 t3   => case (close t1 i a) (close t2 i a) (close t3 i a)
    | zero            => zero
    | succ t'         => succ (close t' i a)
    | rec t1 t2 t3    => rec (close t1 i a) (close t2 i a) (close t3 i a)
    end.

#[export, refine] Instance OC_Tm :
  OC nat Atom Tm Open_Tm Close_Tm := {}.
Proof.
  all: now induction t; cbn; intros;
    rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3; auto.
Qed.

Lemma open_open :
  forall (t : Tm) (i j : nat) (a b : Atom),
    i <> j ->
    t {{ i ~> a }} {{ j ~> b }} = t {{ i ~> a }} ->
      t {{ j ~> b }} = t.
Proof.
  now induction t; cbn; intros i j u1 u2 Hij [=]; f_equal; eauto.
Qed.

(** ** Locally nameless *)

Fixpoint fv (t : Tm) : list Atom :=
match t with
| fvar x          => [x]
| bvar _          => []
| abs t'          => fv t'
| app t1 t2       => fv t1 ++ fv t2
| annot t' A      => fv t'
| unit            => []
| elimUnit t1 t2  => fv t1 ++ fv t2
| abort t'        => fv t'
| pair t1 t2      => fv t1 ++ fv t2
| outl t'         => fv t'
| outr t'         => fv t'
| elimProd t1 t2  => fv t1 ++ fv t2
| inl t'          => fv t'
| inr t'          => fv t'
| case t1 t2 t3   => fv t1 ++ fv t2 ++ fv t3
| zero            => []
| succ t'         => fv t'
| rec t1 t2 t3    => fv t1 ++ fv t2 ++ fv t3
end.

#[export, refine] Instance LocallyNameless_Tm :
  LocallyNameless Atom Tm Open_Tm Close_Tm OC_Tm :=
{
  fv := fv;
}.
Proof.
  - unfold supports, Fresh'.
    induction t; cbn; only 1: rename a into b; intros a Ha;
      [| now f_equal; rewrite 1?(close_invariant _ _ 0), 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3 by auto..].
    now firstorder decide_all.
  - intros t.
    setoid_rewrite LocallyClosed_forall.
    induction t; cbn;
      try (now exists 0);
      try (now destruct IHt as [i IH];
        exists i; intros j a Hij; rewrite IH; [| lia]);
      try (now destruct IHt1 as [i1 IH1], IHt2 as [i2 IH2];
        exists (max i1 i2); intros j a Hle; rewrite IH1, IH2; [| lia..]);
      try (now destruct IHt1 as [i1 IH1], IHt2 as [i2 IH2], IHt3 as [i3 IH3];
        exists (max i1 (max i2 i3)); intros j a Hle; rewrite IH1, IH2, IH3; [| lia..]).
    exists (S n); intros j a Hij.
    now decide_all; lia.
Defined.

(** ** Characterization of equality *)

Lemma close_fv :
  forall (t : Tm) (i : nat) (x : Atom),
    x # fv t ->
    t {{ i <~ x }} = t.
Proof.
  induction t; cbn; intros i x Hx;
    [| now rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3; auto..].
  now firstorder decide_all.
Qed.

Lemma fv_close :
  forall (t : Tm) (i : nat) (x : Atom),
    x # fv (t {{ i <~ x }}).
Proof.
  now induction t; cbn; intros;
    try decide_all;
    rewrite ?Fresh_nil, ?Fresh_cons, ?Fresh_app; auto.
Qed.

Lemma open_close_fv :
  forall (t : Tm) (i : nat) (x : Atom),
    x # fv t ->
    t {{ i ~> x }} {{ i <~ x }} = t.
Proof.
  induction t; cbn; intros i x Hx;
    [| now rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3; auto..].
  now firstorder decide_all.
Qed.

Lemma abs_eq :
  forall (t1 t2 : Tm) (x : Atom),
    x # fv t1 ++ fv t2 ->
    t1 {{ 0 ~> x }} = t2 {{ 0 ~> x }} ->
      abs t1 = abs t2.
Proof.
  intros t1 t2 x Hx Heq.
  now rewrite <- (open_close_fv t1 0 x), Heq, open_close_fv by auto.
Qed.

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
| LocallyClosed'_annot :
  forall (i : nat) (t' : Tm) (A : Ty),
    LocallyClosed' i t' -> LocallyClosed' i (annot t' A)
| LocallyClosed'_unit :
  forall i : nat,
    LocallyClosed' i unit
| LocallyClosed'_elimUnit :
  forall (i : nat) (t1 t2 : Tm),
    LocallyClosed' i t1 ->
    LocallyClosed' i t2 ->
    LocallyClosed' i (elimUnit t1 t2)
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
| LocallyClosed'_elimProd :
  forall (i : nat) (t1 t2 : Tm),
    LocallyClosed' i t1 ->
    LocallyClosed' i t2 ->
    LocallyClosed' i (elimProd t1 t2)
| LocallyClosed'_inl :
  forall (i : nat) (t' : Tm),
    LocallyClosed' i t' -> LocallyClosed' i (inl t')
| LocallyClosed'_inr :
  forall (i : nat) (t' : Tm),
    LocallyClosed' i t' -> LocallyClosed' i (inr t')
| LocallyClosed'_case :
  forall (i : nat) (t1 t2 t3 : Tm),
    LocallyClosed' i t1 ->
    LocallyClosed' i t2 ->
    LocallyClosed' i t3 ->
    LocallyClosed' i (case t1 t2 t3)
| LocallyClosed'_zero :
  forall (i : nat),
    LocallyClosed' i zero
| LocallyClosed'_succ :
  forall (i : nat) (t' : Tm),
    LocallyClosed' i t' -> LocallyClosed' i (succ t')
| LocallyClosed'_rec :
  forall (i : nat) (t1 t2 t3 : Tm),
    LocallyClosed' i t1 ->
    LocallyClosed' i t2 ->
    LocallyClosed' i t3 ->
    LocallyClosed' i (rec t1 t2 t3).

#[export] Hint Constructors LocallyClosed' : core.

Lemma LocallyClosed'_spec :
  forall (i : nat) (t : Tm),
    LocallyClosed' i t <-> LocallyClosed i t.
Proof.
  setoid_rewrite LocallyClosed_forall.
  split.
  - intros Hlc; induction Hlc; intros j a Hij; cbn;
      [easy | | now rewrite 1?IHHlc, 1?IHHlc1, 1?IHHlc2, 1?IHHlc3; try lia..].
    now decide_all; lia.
  - revert i.
    induction t; cbn; intros i Hlc; constructor; try easy;
    try match goal with
    | IH : forall _, _ -> LocallyClosed' _ ?t  |- LocallyClosed' _ ?t =>
      now apply IH; intros j a Hij; injection (Hlc j a Hij)
    | IH : forall _, _ -> LocallyClosed' _ ?t  |- LocallyClosed' _ ?t =>
      now apply IH; intros [| j'] a Hle; [now lia |]; injection (Hlc j' a ltac:(lia))
    | IH : forall _, _ -> LocallyClosed' _ ?t  |- LocallyClosed' _ ?t =>
      now apply IH; intros [| [| j']] a Hle; [now lia.. |]; injection (Hlc j' a ltac:(lia))
    end.
    destruct (PeanoNat.Nat.lt_ge_cases n i); [easy |].
    specialize (Hlc n (fresh []) H).
    now decide_all.
Qed.

Lemma open_LocallyClosed' :
  forall (t : Tm) (i j : nat) (a : Atom),
    i <= j -> LocallyClosed' i t -> t {{ j ~> a }} = t.
Proof.
  intros t i j a Hij Hlc.
  apply open_LocallyClosed with j; [| now lia].
  now eapply LocallyClosed_le, LocallyClosed'_spec; eauto.
Qed.

Fixpoint dec_LC_aux (i : nat) (t : Tm) : bool :=
match t with
| fvar x          => true
| bvar n          => decide (n < i)
| abs t'          => dec_LC_aux (S i) t'
| app t1 t2       => dec_LC_aux i t1 && dec_LC_aux i t2
| annot t' A      => dec_LC_aux i t'
| unit            => true
| elimUnit t1 t2  => dec_LC_aux i t1 && dec_LC_aux i t2
| abort t'        => dec_LC_aux i t'
| pair t1 t2      => dec_LC_aux i t1 && dec_LC_aux i t2
| outl t'         => dec_LC_aux i t'
| outr t'         => dec_LC_aux i t'
| elimProd t1 t2  => dec_LC_aux i t1 && dec_LC_aux i t2
| inl t'          => dec_LC_aux i t'
| inr t'          => dec_LC_aux i t'
| case t1 t2 t3   => dec_LC_aux i t1 && dec_LC_aux i t2 && dec_LC_aux i t3
| zero            => true
| succ t'         => dec_LC_aux i t'
| rec t1 t2 t3    => dec_LC_aux i t1 && dec_LC_aux i t2 && dec_LC_aux i t3
end.

#[export, refine] Instance Decidable_LocallyClosed' :
  forall (i : nat) (t : Tm), Decidable (LocallyClosed' i t) :=
{
  Decidable_witness :=
    dec_LC_aux i t;
}.
Proof.
  split.
  - revert i; induction t; cbn; intros i H; [easy | |
      now repeat match goal with
      | H : _ && _ = true |- _ => apply andb_prop in H as []
      end; auto..].
    now constructor; decide (n < i); lia.
  - induction 1; cbn; rewrite ?andb_true_iff; [easy | | now auto..].
    now decide (n < i); auto.
Defined.

(** ** Characterization of freshness *)

Lemma Fresh'_spec :
  forall (x : Atom) (t : Tm),
    Fresh' x t <-> x # fv t.
Proof.
  split; [| now rapply supports_fv].
  unfold Fresh'.
  induction t; cbn; intros [=]; rewrite_fresh;
    rewrite ?(close_invariant _ _ 0) in *; [| now auto..].
  now decide_all.
Qed.

(** ** Substitution *)

Fixpoint subst (t : Tm) (x : Atom) (u : Tm) : Tm :=
match t with
| fvar y          => if decide (x = y) then u else fvar y
| bvar n          => bvar n
| abs t'          => abs (subst t' x u)
| app t1 t2       => app (subst t1 x u) (subst t2 x u)
| annot t' A      => annot (subst t' x u) A
| unit            => unit
| elimUnit t1 t2  => elimUnit (subst t1 x u) (subst t2 x u)
| abort t'        => abort (subst t' x u)
| pair t1 t2      => pair (subst t1 x u) (subst t2 x u)
| outl t'         => outl (subst t' x u)
| outr t'         => outr (subst t' x u)
| elimProd t1 t2  => elimProd (subst t1 x u) (subst t2 x u)
| inl t'          => inl (subst t' x u)
| inr t'          => inr (subst t' x u)
| case t1 t2 t3   => case (subst t1 x u) (subst t2 x u) (subst t3 x u)
| zero            => zero
| succ t'         => succ (subst t' x u)
| rec t1 t2 t3    => rec (subst t1 x u) (subst t2 x u) (subst t3 x u)
end.

Notation "t [[ x := u ]]" := (subst t x u) (at level 69, left associativity).

Lemma subst_fv :
  forall (t : Tm) (x : Atom) (u : Tm),
    x # fv t -> t [[ x := u ]] = t.
Proof.
  induction t; cbn; intros;
    [| now rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3 by auto..].
  now firstorder decide_all.
Qed.

Lemma subst_subst :
  forall (t : Tm) (x y : Atom) (u1 u2 : Tm),
    x <> y -> x # fv u2 -> y # fv u1 ->
    t [[ x := u1 ]] [[ y := u2 ]]
      =
    t [[ y := u2 ]] [[ x := u1 ]].
Proof.
  induction t; cbn; intros;
    [| now rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3..].
  now decide_all; rewrite subst_fv by auto.
Qed.

(** ** Opening with a term *)

Fixpoint open' (t : Tm) (i : nat) (u : Tm) : Tm :=
match t with
| fvar a          => fvar a
| bvar j          => if decide (i = j) then u else bvar j
| abs t'          => abs (open' t' (S i) u)
| app t1 t2       => app (open' t1 i u) (open' t2 i u)
| annot t' A      => annot (open' t' i u) A
| unit            => unit
| elimUnit t1 t2  => elimUnit (open' t1 i u) (open' t2 i u)
| abort t'        => abort (open' t' i u)
| pair t1 t2      => pair (open' t1 i u) (open' t2 i u)
| outl t'         => outl (open' t' i u)
| outr t'         => outr (open' t' i u)
| elimProd t1 t2  => elimProd (open' t1 i u) (open' t2 i u)
| inl t'          => inl (open' t' i u)
| inr t'          => inr (open' t' i u)
| case t1 t2 t3   => case (open' t1 i u) (open' t2 i u) (open' t3 i u)
| zero            => zero
| succ t'         => succ (open' t' i u)
| rec t1 t2 t3    => rec (open' t1 i u) (open' t2 i u) (open' t3 i u)
end.

Notation "t {[ i ~> u ]}" := (open' t i u) (at level 69, left associativity).

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
    [| now auto | now rewrite <- 1?IHt, 1?(IHt1 _ x), 1?(IHt2 _ x), 1?(IHt3 _ x) by auto..].
  now firstorder decide_all.
Qed.

Lemma open'_spec' :
  forall (t : Tm) (i : nat) (u : Tm),
    t {[ i ~> u ]} = t {{ i ~> fresh (fv t) }} [[ fresh (fv t) := u ]].
Proof.
  now intros; apply open'_spec; auto.
Qed.

Lemma open'_open' :
  forall (t : Tm) (i j : nat) (u1 u2 : Tm),
    i <> j ->
    t {[ i ~> u1 ]} {[ j ~> u2 ]} = t {[ i ~> u1 ]} ->
      t {[ j ~> u2 ]} = t.
Proof.
  now induction t; cbn; intros i j u1 u2 Hij [=]; f_equal; eauto.
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
| lc_annot :
  forall (t' : Tm) (A : Ty)
    (Hlc' : lc t'),
    lc (annot t' A)
| lc_unit : lc unit
| lc_elimUnit :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    lc (elimUnit t1 t2)
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
| lc_elimProd :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    lc (elimProd t1 t2)
| lc_inl :
  forall (t' : Tm)
    (Hlc' : lc t'),
    lc (inl t')
| lc_inr :
  forall (t' : Tm)
    (Hlc' : lc t'),
    lc (inr t')
| lc_case :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    lc (case t1 t2 t3)
| lc_zero : lc zero
| lc_succ :
  forall (t' : Tm)
    (Hlc' : lc t'),
    lc (succ t')
| lc_rec :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    lc (rec t1 t2 t3).

#[export] Hint Constructors lc : core.

Lemma LocallyClosed_lc :
  forall t : Tm,
    lc t -> LocallyClosed 0 t.
Proof.
  setoid_rewrite LocallyClosed_forall.
  intros t Hlc; induction Hlc; cbn; intros j a Hle;
    rewrite 1?IHHlc, 1?IHHlc1, 1?IHHlc2, 1?IHHlc3; f_equal;
    try now auto;
    try now eapply (open_open _ 0 (S j)); auto.
Qed.

Lemma open_lc :
  forall (t : Tm) (i : nat) (a : Atom),
    lc t -> t {{ i ~> a }} = t.
Proof.
  intros.
  apply open_LocallyClosed with i; [| now lia].
  now eapply LocallyClosed_le, LocallyClosed_lc; [lia |].
Qed.

Fixpoint abstract (i : nat) (t : Tm) : Tm :=
match i with
| 0 => t
| S i' => abs (abstract i' t)
end.

Lemma open_abstract :
  forall (i : nat) (t : Tm) (j : nat) (x : Atom),
    lc t ->
    abstract i t {{ j ~> x }} = abstract i (t {{ j ~> x }})

with lc_abstract :
  forall (i : nat) (t : Tm),
    lc t -> lc (abstract i t).
Proof.
  - induction i; cbn; intros; [easy |].
    rewrite !open_lc; [easy.. |].
    now apply lc_abstract.
  - induction i; cbn; intros; [easy |].
    apply lc_abs with []; intros x _.
    rewrite open_abstract by easy.
    rewrite open_lc by easy.
    now apply IHi.
Qed.

Lemma lc_open :
  forall (t : Tm) (i : nat) (a : Atom),
    lc t -> lc (t {{ i ~> a }}).
Proof.
  now intros; rewrite open_lc.
Qed.

Definition lcify (i : nat) (t : Tm) : Tm :=
match t with
| bvar n => if decide (n < i) then abstract i t else t
| _ => t
end.

Lemma lc_LocallyClosed :
  forall (i : nat) (t : Tm),
    LocallyClosed' i t -> lc (lcify i t).
Proof.
  induction 1; cbn; eauto.
  - decide (n < i); [| easy].
    apply lc_abstract.
    admit.
  - apply lc_abs with []; intros x _.
    apply lc_open.
    admit.
  - admit.
  - 
Abort.

Lemma open_subst :
  forall (t : Tm) (i : nat) (a b x : Atom),
    t {{ i ~> a }} [[ x := b ]]
      =
    t [[ x := b ]] {{ i ~> if decide (a = x) then b else a }}.
Proof.
  now induction t; cbn; intros;
    rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3; auto.
Qed.

Lemma subst_open :
  forall (t : Tm) (a b : Atom) (i : nat) (u : Tm),
    a <> b -> lc u ->
    t [[ a := u ]] {{ i ~> b }} = t {{ i ~> b }} [[ a := u ]].
Proof.
  induction t; cbn; intros; [| now auto | now rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3..].
  decide_all.
  now rewrite open_lc.
Qed.

Lemma lc_subst :
  forall (t : Tm) (x : Atom) (u : Tm),
    lc t -> lc u -> lc (t [[ x := u ]]).
Proof.
  intros t x u Ht Hu; revert x u Hu.
  induction Ht; cbn; intros; try now auto.
  apply lc_abs with (x :: l).
  now intros y Hy; rewrite subst_open; auto.
Qed.

Lemma lc_open' :
  forall (t u : Tm) (i : nat),
    (exists l : list Atom, forall x : Atom, x # l -> lc (t {{ i ~> x }})) ->
    lc u ->
      lc (t {[ i ~> u ]}).
Proof.
  intros t u i [l Hlct] Hlcu.
  rewrite (open'_spec _ _ (fresh (l ++ fv t))) by auto.
  now apply lc_subst; auto.
Qed.

Lemma lc_open'2 :
  forall (t u1 u2 : Tm) (i j : nat),
    (exists l : list Atom,
      forall (x y : Atom), x # l -> y # x :: l -> lc (t {{ i ~> x }} {{ j ~> y }})) ->
    lc u1 -> lc u2 ->
      lc (t {[ i ~> u1 ]} {[ j ~> u2 ]}).
Proof.
  intros t u1 u2 i j [l Hlct] Hlc1 Hlc2.
  pose (x := fresh (l ++ fv t)).
  pose (y := fresh ([x] ++ l ++ fv (t {[ i ~> u1 ]}))).
  rewrite (open'_spec _ _ y) by auto.
  apply lc_subst; [| now auto].
  rewrite (open'_spec _ _ x) by auto.
  rewrite subst_open by auto.
  now apply lc_subst; auto.
Qed.

#[export] Hint Resolve lc_subst lc_open : core.

#[export] Hint Extern 1 (lc (?t {[ _ ~> _ ]})) =>
  match t with
  | ?t' {[ _ ~> _ ]} => apply lc_open'2
  | _ => apply lc_open'
  end : core.

Lemma open'_lc :
  forall (t : Tm) (i : nat) (u : Tm),
    lc t -> t {[ i ~> u ]} = t.
Proof.
  intros t i u Hlc.
  rewrite open'_spec', (open_LocallyClosed t i); [.. | now lia].
  - now rewrite subst_fv by auto.
  - apply LocallyClosed_le with 0; [now lia |].
    now apply LocallyClosed_lc.
Qed.

Lemma open'_subst :
  forall (t : Tm) (i : nat) (u1 : Tm) (x : Atom) (u2 : Tm),
    lc u2 ->
    t {[ i ~> u1 ]} [[ x := u2 ]]
      =
    t [[ x := u2 ]] {[ i ~> u1 [[ x := u2 ]] ]}.
Proof.
  induction t; cbn; intros; [| now auto | now rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3..].
  decide_all.
  now rewrite open'_lc.
Qed.

Lemma lc_open_invariant :
  forall (t : Tm) (i : nat) (x y : Atom),
    lc (t {{ i ~> x }}) -> lc (t {{ i ~> y }}).
Proof.
  induction t; cbn; intros i x y Hlc;
    inversion Hlc; subst; try now eauto.
  - apply lc_abs with l; intros z Hz.
    admit.
Admitted.

Lemma lc_open_invariant' :
  forall (t : Tm) (i : nat) (x y : Atom),
    lc (t {{ i ~> x }}) <-> lc (t {{ i ~> y }}).
Proof.
  now split; apply lc_open_invariant.
Qed.

#[export] Hint Resolve lc_open_invariant : core.

Require Import Recdef.

Fixpoint size (t : Tm) : nat :=
match t with
| fvar x          => 1
| bvar n          => 1
| abs t'          => 1 + size t'
| app t1 t2       => 1 + size t1 + size t2
| annot t' A      => 1 + size t'
| unit            => 1
| elimUnit t1 t2  => 1 + size t1 + size t2
| abort t'        => 1 + size t'
| pair t1 t2      => 1 + size t1 + size t2
| outl t'         => 1 + size t'
| outr t'         => 1 + size t'
| elimProd t1 t2  => 1 + size t1 + size t2
| inl t'          => 1 + size t'
| inr t'          => 1 + size t'
| case t1 t2 t3   => 1 + size t1 + size t2 + size t3
| zero            => 1
| succ t'         => 1 + size t'
| rec t1 t2 t3    => 1 + size t1 + size t2 + size t3
end.

Lemma size_open :
  forall (t : Tm) (i : nat) (a : Atom),
    size (t {{ i ~> a }}) = size t.
Proof.
  now induction t; cbn; intros; auto.
Qed.

Unset Guard Checking.
Function decide_lc (a : Atom) (t : Tm) {struct t} : bool :=
match t with
| fvar x          => true
| bvar n          => false
| abs t'          => decide_lc a (t' {{ 0 ~> a }})
| app t1 t2       => decide_lc a t1 && decide_lc a t2
| annot t' A      => decide_lc a t'
| unit            => true
| elimUnit t1 t2  => decide_lc a t1 && decide_lc a t2
| abort t'        => decide_lc a t'
| pair t1 t2      => decide_lc a t1 && decide_lc a t2
| outl t'         => decide_lc a t'
| outr t'         => decide_lc a t'
| elimProd t1 t2  => decide_lc a t1 && decide_lc a t2
| inl t'          => decide_lc a t'
| inr t'          => decide_lc a t'
| case t1 t2 t3   => decide_lc a t1 && decide_lc a t2 && decide_lc a t3
| zero            => true
| succ t'         => decide_lc a t'
| rec t1 t2 t3    => decide_lc a t1 && decide_lc a t2 && decide_lc a t3
end.
(*
Proof.
  all: now cbn; intros; rewrite ?size_open; lia.
Defined.
*)
Set Guard Checking.

Lemma decide_lc_spec :
  forall (a : Atom) (t : Tm),
    reflect (lc t) (decide_lc a t).
Proof.
  intros a t.
  functional induction (decide_lc a t);
    try (now try destruct IHb; try destruct IHb0; try destruct IHb1;
      cbn; constructor; [auto | inversion 1..]).
  destruct IHb; constructor; [now apply lc_abs with [];  eauto |].
  inversion 1.
  now specialize (Hlc' (fresh l) (fresh_spec l)); eauto.
Qed.

#[export, refine] Instance Decidable_lc :
  forall t : Tm, Decidable (lc t) :=
{
  Decidable_witness :=
    decide_lc (fresh (fv t)) t;
}.
Proof.
  now destruct (decide_lc_spec (fresh (fv t)) t).
Defined.

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
  constructor; [| now auto].
  now apply IH in Hwf.
Qed.

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

Lemma Binds_inv' :
  forall (Γ1 Γ2 : Ctx) (x : Atom) (A B : Ty),
    Binds (Γ2 ++ (x, A) :: Γ1) x B -> WfCtx (Γ2 ++ (x, A) :: Γ1) -> A = B.
Proof.
  intros.
  eapply Binds_inv; [now eauto | | now eauto].
  red; rewrite in_app_iff; cbn.
  now firstorder.
Qed.

Lemma Binds_app_cons_inv :
  forall (Γ Δ : Ctx) (x y : Atom) (A B : Ty),
    Binds (Δ ++ (x, A) :: Γ) y B ->
      (x = y /\ A = B)
        \/
      Binds (Δ ++ Γ) y B.
Proof.
  induction Δ; cbn; [now firstorder congruence |].
  intros x y A B [ [= ->] | ]; [now auto |].
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
| Typing_annot :
  forall (Γ : Ctx) (t' : Tm) (A : Ty)
    (Ht' : Typing Γ t' A),
    Typing Γ (annot t' A) A
| Typing_unit :
  forall (Γ : Ctx)
    (Hwf : WfCtx Γ),
    Typing Γ unit TyUnit
| Typing_elimUnit :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty)
    (Ht1 : Typing Γ t1 (TyFun TyUnit A))
    (Ht2 : Typing Γ t2 TyUnit),
    Typing Γ (elimUnit t1 t2) A
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
| Typing_elimProd :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B C : Ty)
    (Ht1 : Typing Γ t1 (TyFun A (TyFun B C)))
    (Ht2 : Typing Γ t2 (TyProd A B)),
    Typing Γ (elimProd t1 t2) C
| Typing_inl :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Ht' : Typing Γ t' A),
    Typing Γ (inl t') (TySum A B)
| Typing_inr :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Ht' : Typing Γ t' B),
    Typing Γ (inr t') (TySum A B)
| Typing_case :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty)
    (Ht1 : Typing Γ t1 (TyFun A C))
    (Ht2 : Typing Γ t2 (TyFun B C))
    (Ht3 : Typing Γ t3 (TySum A B)),
    Typing Γ (case t1 t2 t3) C
| Typing_zero :
  forall (Γ : Ctx)
    (Hwf : WfCtx Γ),
    Typing Γ zero TyNat
| Typing_succ :
  forall (Γ : Ctx) (t' : Tm)
    (Ht' : Typing Γ t' TyNat),
    Typing Γ (succ t') TyNat
| Typing_rec :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A : Ty)
    (Ht1 : Typing Γ t1 A)
    (Ht2 : Typing Γ t2 (TyFun A A))
    (Ht3 : Typing Γ t3 TyNat),
    Typing Γ (rec t1 t2 t3) A.

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
  now apply (WfCtx_app_cons _ [] (fresh l) A), H; auto.
Qed.

#[export] Hint Immediate lc_Typing WfCtx_Typing : core.

#[export] Hint Resolve WfCtx_app_cons : core.

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
  induction Ht; intros; subst; try now eauto.
  - constructor; [easy |].
    unfold Binds in *.
    rewrite !in_app_iff; rewrite in_app_iff in HB.
    now firstorder.
  - apply Typing_abs with (l ++ map fst Γ1 ++ map fst Δ ++ map fst Γ2).
    now intros; rewrite !app_comm_cons; apply H; cbn; auto.
Qed.

Lemma weakening :
  forall (Γ Δ : Ctx) (t : Tm) (A : Ty),
    WfCtx (Δ ++ Γ) ->
    Typing Γ t A ->
    Typing (Δ ++ Γ) t A.
Proof.
  now intros; apply weakening_aux with (Γ1 := []); cbn.
Qed.

Lemma weakening_cons :
  forall (Γ : Ctx) (t : Tm) (x : Atom) (A B : Ty),
    WfCtx ((x, A) :: Γ) ->
    Typing Γ t B ->
    Typing ((x, A) :: Γ) t B.
Proof.
  now intros; apply weakening with (Δ := [(x, A)]).
Qed.

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
  induction Ht; cbn; intros; subst; try now eauto.
  - apply WfCtx_app_cons in Hwf as Hwf'.
    decide_all.
    + apply Binds_inv' in HB as ->; [| easy].
      now apply weakening.
    + now apply Binds_app_cons_inv in HB as [ [-> ->] |]; auto.
  - apply Typing_abs with (x :: l).
    intros y Hy; rewrite subst_open, !app_comm_cons by eauto.
    now eapply H; cbn; auto.
Qed.

Lemma Typing_subst :
  forall (Γ : Ctx) (x : Atom) (t u : Tm) (A B : Ty),
    Typing ((x, A) :: Γ) t B ->
    Typing Γ u A ->
    Typing Γ (t [[ x := u ]]) B.
Proof.
  now intros; eapply Typing_subst_aux with (Δ := []) (A := A).
Qed.

Lemma Typing_open' :
  forall (Γ : Ctx) (t u : Tm) (A B : Ty),
    (exists l : list Atom, forall x : Atom, x # l ->
      Typing ((x, A) :: Γ) (t {{ 0 ~> x }}) B) ->
    Typing Γ u A ->
    Typing Γ (t {[ 0 ~> u ]}) B.
Proof.
  intros Γ t u A B [l Ht] Hu.
  rewrite open'_spec with (x := fresh (l ++ fv t)) by auto.
  now apply Typing_subst with A; auto.
Qed.

Lemma Typing_open'2 :
  forall (Γ : Ctx) (t u1 u2 : Tm) (A B C : Ty),
    (exists l : list Atom, forall (x y : Atom), x # l -> y # x :: l ->
      Typing ((y, B) :: (x, A) :: Γ) (t {{ 0 ~> x }} {{ 1 ~> y }}) C) ->
    Typing Γ u1 A ->
    Typing Γ u2 B ->
    Typing Γ (t {[ 0 ~> u1 ]} {[ 1 ~> u2 ]}) C.
Proof.
  intros Γ t u1 u2 A B C [l Ht] Hu1 Hu2.
  pose (x := fresh (l ++ fv u2 ++ fv t ++ map fst Γ)).
  pose (y := fresh ([x] ++ l ++ fv u1 ++ fv (t {{ 0 ~> x }} [[ x := u1 ]]))).
  rewrite (open'_spec _ 0 x), (open'_spec _ 1 y), subst_open, subst_subst by eauto.
  apply Typing_subst with A; [| easy].
  apply Typing_subst with B; [now auto |].
  now apply weakening_cons; eauto.
Qed.

#[export] Hint Resolve Typing_open' Typing_open'2 : core.

(** * Computation *)

(** ** CBV *)

(** *** Values *)

Inductive CbvValue : Tm -> Prop :=
| CbvValue_abs  :
  forall (t' : Tm) (l : list Atom)
    (Hlc' : forall x : Atom, x # l -> lc (t' {{ 0 ~> x }})),
    CbvValue (abs t')
| CbvValue_unit : CbvValue unit
| CbvValue_abort :
  forall (t' : Tm)
    (Hlc' : lc t'),
    CbvValue (abort t')
| CbvValue_pair :
  forall t1 t2 : Tm,
    CbvValue t1 ->
    CbvValue t2 ->
    CbvValue (pair t1 t2)
| CbvValue_inl :
  forall v : Tm,
    CbvValue v ->
    CbvValue (inl v)
| CbvValue_inr :
  forall v : Tm,
    CbvValue v ->
    CbvValue (inr v)
| CbvValue_zero : CbvValue zero
| CbvValue_succ :
  forall (t' : Tm)
    (Hv' : CbvValue t'),
    CbvValue (succ t').

#[export] Hint Constructors CbvValue : core.

Lemma lc_CbvValue :
  forall t : Tm,
    CbvValue t -> lc t.
Proof.
  now induction 1; eauto.
Qed.

#[export] Hint Immediate lc_CbvValue : core.

Fixpoint cbvValue (t : Tm) : bool :=
match t with
| abs t'               => decide (lc (abs t'))
| unit                 => true
| abort t'             => decide (lc t')
| pair t1 t2           => cbvValue t1 && cbvValue t2
| inl t'               => cbvValue t'
| inr t'               => cbvValue t'
| zero                 => true
| succ t'              => cbvValue t'
| _                    => false
end.

#[export, refine] Instance Decidable_CbvValue :
  forall t : Tm, Decidable (CbvValue t) :=
{
  Decidable_witness := cbvValue t
}.
Proof.
  split.
  - induction t; cbn; subst; try now eauto.
    + intros H%Decidable_sound.
      now inversion H; subst; eauto.
    + intros H%Decidable_sound.
      now eauto.
    + now intros [Ht1 Ht2]%andb_prop; eauto.
  - induction 1; cbn in *; try now eauto using Decidable_complete.
    now rewrite IHCbvValue1, IHCbvValue2.
Defined.

(** *** Contraction *)

Inductive CbvContraction : Tm -> Tm -> Prop :=
| CbvContraction_app_abs :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : forall x : Atom, x # l -> lc (t1 {{ 0 ~> x }}))
    (Hv2 : CbvValue t2),
    CbvContraction (app (abs t1) t2) (t1 {[ 0 ~> t2 ]})
| CbvContraction_annot :
  forall (t : Tm) (A : Ty)
    (Hlc : lc t),
    CbvContraction (annot t A) t
| CbvContraction_elimUnit_unit :
  forall (t : Tm)
    (Hlc : lc t),
    CbvContraction (elimUnit t unit) (app t unit)
| CbvContraction_outl_pair :
  forall (v1 v2 : Tm)
    (Hv1 : CbvValue v1)
    (Hv2 : CbvValue v2),
    CbvContraction (outl (pair v1 v2)) v1
| CbvContraction_outr_pair :
  forall (v1 v2 : Tm)
    (Hv1 : CbvValue v1)
    (Hv2 : CbvValue v2),
    CbvContraction (outr (pair v1 v2)) v2
| CbvContraction_elimProd_pair :
  forall (v1 v2 t : Tm)
    (Hv1 : CbvValue v1)
    (Hv2 : CbvValue v2)
    (Hlc3 : lc t),
    CbvContraction (elimProd t (pair v1 v2)) (app (app t v1) v2)
| CbvContraction_case_inl :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv3 : CbvValue t3),
    CbvContraction (case t1 t2 (inl t3)) (app t1 t3)
| CbvContraction_case_inr :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv3 : CbvValue t3),
    CbvContraction (case t1 t2 (inr t3)) (app t2 t3)
| CbvContraction_rec_zero :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvContraction (rec t1 t2 zero) t1
| CbvContraction_rec_succ :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv3 : CbvValue t3),
    CbvContraction (rec t1 t2 (succ t3)) (app t2 (rec t1 t2 t3)).

#[export] Hint Constructors CbvContraction : core.

Lemma lc_CbvContraction_l :
  forall t t' : Tm,
    CbvContraction t t' -> lc t.
Proof.
  now inversion 1; eauto.
Qed.

Lemma lc_CbvContraction_r :
  forall t t' : Tm,
    CbvContraction t t' -> lc t'.
Proof.
  now inversion 1; eauto 6.
Qed.

#[export] Hint Immediate lc_CbvContraction_l lc_CbvContraction_r : core.

Lemma CbvContraction_det :
  forall t t1 t2 : Tm,
    CbvContraction t t1 -> CbvContraction t t2 -> t1 = t2.
Proof.
  now do 2 inversion 1.
Qed.

Lemma CbvContraction_not_CbvValue :
  forall t t' : Tm,
    CbvContraction t t' -> CbvValue t -> False.
Proof.
  now do 2 inversion 1.
Qed.

#[export] Hint Resolve CbvContraction_det CbvContraction_not_CbvValue : core.

Lemma preservation_CbvContraction :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    CbvContraction t1 t2 ->
    Typing Γ t1 A ->
    Typing Γ t2 A.
Proof.
  now inversion 1; subst; intros;
    repeat match goal with
    | H : Typing _ ?t _ |- _ => tryif is_var t then fail else (inversion H; subst; clear H)
    end; eauto.
Qed.

(*** *** Abortion *)

Inductive CbvAbortion : Tm -> Tm -> Prop :=
| CbvAbortion_app :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvAbortion (app (abort t1) t2) (abort t1)
| CbvAbortion_elimUnit :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvAbortion (elimUnit t1 (abort t2)) (abort t2)
| CbvAbortion_outl :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbvAbortion (outl (abort t)) (abort t)
| CbvAbortion_outr :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbvAbortion (outr (abort t)) (abort t)
| CbvAbortion_elimProd :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvAbortion (elimProd t1 (abort t2)) (abort t2)
| CbvAbortion_case :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbvAbortion (case t1 t2 (abort t3)) (abort t3)
| CbvAbortion_rec :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbvAbortion (rec t1 t2 (abort t3)) (abort t3).

#[export] Hint Constructors CbvAbortion : core.

Lemma lc_CbvAbortion_l :
  forall t t' : Tm,
    CbvAbortion t t' -> lc t.
Proof.
  now inversion 1; eauto.
Qed.

Lemma lc_CbvAbortion_r :
  forall t t' : Tm,
    CbvAbortion t t' -> lc t'.
Proof.
  now inversion 1; eauto.
Qed.

#[export] Hint Resolve lc_CbvAbortion_l lc_CbvAbortion_r : core.

Lemma CbvAbortion_det :
  forall t t1 t2 : Tm,
    CbvAbortion t t1 -> CbvAbortion t t2 -> t1 = t2.
Proof.
  now do 2 inversion 1.
Qed.

Lemma CbvAbortion_not_CbvValue :
  forall t t' : Tm,
    CbvAbortion t t' -> CbvValue t -> False.
Proof.
  now do 2 inversion 1.
Qed.

Lemma CbvAbortion_not_CbvContraction :
  forall t t1 t2 : Tm,
    CbvAbortion t t1 -> CbvContraction t t2 -> False.
Proof.
  now do 2 inversion 1.
Qed.

#[export] Hint Resolve
  CbvAbortion_det CbvAbortion_not_CbvValue CbvAbortion_not_CbvContraction : core.

Lemma preservation_CbvAbortion :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    CbvAbortion t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  now do 2 inversion 1; subst;
    match goal with
    | H : Typing _ (abort _) _ |- _ => inversion H
    end; auto.
Qed.

(** *** Reduction *)

Inductive CbvStep : Tm -> Tm -> Prop :=
| CbvStep_CbvContraction :
  forall t t' : Tm,
    CbvContraction t t' ->
    CbvStep t t'
| CbvStep_CbvAbortion :
  forall t t' : Tm,
    CbvAbortion t t' ->
    CbvStep t t'
| CbvStep_app_l :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    CbvStep t1 t1' ->
    CbvStep (app t1 t2) (app t1' t2)
| CbvStep_app_r :
  forall (t1 t2 t2' : Tm) (l : list Atom)
    (Hlc' : forall x : Atom, x # l -> lc (t1 {{ 0 ~> x }})),
    CbvStep t2 t2' ->
    CbvStep (app (abs t1) t2) (app (abs t1) t2')
| CbvStep_elimUnit :
  forall (t1 t2 t2' : Tm)
    (Hlc1 : lc t1),
    CbvStep t2 t2' ->
    CbvStep (elimUnit t1 t2) (elimUnit t1 t2')
| CbvStep_pair_l :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    CbvStep t1 t1' ->
    CbvStep (pair t1 t2) (pair t1' t2)
| CbvStep_pair_r :
  forall (t1 t2 t2' : Tm),
    CbvValue t1 ->
    CbvStep t2 t2' ->
    CbvStep (pair t1 t2) (pair t1 t2')
| CbvStep_outl :
  forall (t t' : Tm),
    CbvStep t t' ->
    CbvStep (outl t) (outl t')
| CbvStep_outr :
  forall (t t' : Tm),
    CbvStep t t' ->
    CbvStep (outr t) (outr t')
| CbvStep_elimProd :
  forall (t1 t2 t2' : Tm)
    (Hlc1 : lc t1)
    (Hs2 : CbvStep t2 t2'),
    CbvStep (elimProd t1 t2) (elimProd t1 t2')
| CbvStep_inl :
  forall t t' : Tm,
    CbvStep t t' ->
    CbvStep (inl t) (inl t')
| CbvStep_inr :
  forall t t' : Tm,
    CbvStep t t' ->
    CbvStep (inr t) (inr t')
| CbvStep_case :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : CbvStep t3 t3'),
    CbvStep (case t1 t2 t3) (case t1 t2 t3')
| CbvStep_succ :
  forall (t t' : Tm),
    CbvStep t t' ->
    CbvStep (succ t) (succ t')
| CbvStep_rec :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : CbvStep t3 t3'),
    CbvStep (rec t1 t2 t3) (rec t1 t2 t3').

#[export] Hint Constructors CbvStep : core.

Lemma lc_CbvStep_l :
  forall t t' : Tm,
    CbvStep t t' -> lc t.
Proof.
  now induction 1; eauto.
Qed.

Lemma lc_CbvStep_r :
  forall t t' : Tm,
    CbvStep t t' -> lc t'.
Proof.
  now induction 1; eauto.
Qed.

Lemma CbvStep_not_CbvValue :
  forall t t' : Tm,
    CbvStep t t' -> CbvValue t -> False.
Proof.
  induction 1; intros Hv; [| | | now inversion Hv..].
  - now eapply CbvContraction_not_CbvValue; eauto.
  - now eapply CbvAbortion_not_CbvValue; eauto.
  - now inversion Hv; subst; eauto.
Qed.

#[export] Hint Immediate lc_CbvStep_l lc_CbvStep_r CbvStep_not_CbvValue : core.

Lemma CbvContraction_CbvStep_det :
  forall t t1 t2 : Tm,
    CbvContraction t t1 -> CbvStep t t2 -> t1 = t2.
Proof.
  inversion 2; subst; intros; [| |
    match goal with
    | Hs : CbvStep _ _ |- _ =>
      now apply CbvStep_not_CbvValue in Hs; [| inversion H; subst; eauto]
    end..].
  - now eapply CbvContraction_det; eauto.
  - now eapply CbvAbortion_not_CbvContraction in H; [| eauto].
Qed.

Lemma CbvAbortion_CbvStep_det :
  forall t t1 t2 : Tm,
    CbvAbortion t t1 -> CbvStep t t2 -> t1 = t2.
Proof.
  inversion 2; subst; intros; [| |
    match goal with
    | Hs : CbvStep _ _ |- _ =>
      now apply CbvStep_not_CbvValue in Hs; [| inversion H; subst; eauto]
    end..].
  - now eapply CbvAbortion_not_CbvContraction in H; [| eauto].
  - now eapply CbvAbortion_det; eauto.
Qed.

#[export] Hint Resolve CbvContraction_CbvStep_det CbvAbortion_CbvStep_det : core.

Lemma CbvStep_det :
  forall t t1 t2 : Tm,
    CbvStep t t1 -> CbvStep t t2 -> t1 = t2.
Proof.
  intros t t1 t2 Hs1 Hs2; revert t2 Hs2.
  now induction Hs1; intros; inversion Hs2; subst; clear Hs2;
    repeat match goal with
    | H : CbvContraction _ _ |- _  => now eapply CbvContraction_CbvStep_det in H; eauto
    | H : CbvAbortion _ _ |- _     => now eapply CbvAbortion_CbvStep_det in H; eauto
    | H : CbvStep (app _ _) _ |- _ => now apply CbvStep_not_CbvValue in H; auto
    | H : CbvStep ?t _ |- _        =>
      tryif is_evar t
      then fail
      else now apply CbvStep_not_CbvValue in H; [| eauto]
    end;
    firstorder congruence.
Qed.

(** *** Progress and preservation *)

Lemma preservation_cbv :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    CbvStep t1 t2 ->
    Typing Γ t1 A ->
    Typing Γ t2 A.
Proof.
  intros Γ t1 t2 A Hstep; revert A.
  induction Hstep; intros A; [| | now inversion 1; subst; eauto..].
  - now eapply preservation_CbvContraction.
  - now eapply preservation_CbvAbortion.
Qed.

Lemma progress_cbv :
  forall (t : Tm) (A : Ty),
    Typing [] t A ->
      CbvValue t \/ exists t' : Tm, CbvStep t t'.
Proof.
  intros t A Ht.
  remember [] as Γ.
  induction Ht; subst; try now auto.
  - now left; eauto using lc_Typing.
  - destruct (IHHt1 eq_refl) as [ Hv | [t1' Hs1] ]; [| now eauto].
    inversion Hv; subst; inversion Ht1; subst; try now auto.
    + now destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; eauto.
    + now eauto 6.
  - now right; eauto.
  - right; destruct (IHHt2 eq_refl) as [ Hv | [t2' Hs2] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht2; subst; try (now inversion Ht0); eauto 6.
  - now left; eauto.
  - now destruct (IHHt1 eq_refl) as [| [] ], (IHHt2 eq_refl) as [| [] ]; eauto.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht; subst; try (now inversion Ht1); eauto 6.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht; subst; try (now inversion Ht1); eauto 6.
  - right; destruct (IHHt2 eq_refl) as [Hv | [t'' Hs] ]; [| now eauto 6].
    now inversion Hv; subst; inversion Ht2; subst; try (now inversion Ht0); eauto 6.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt3 eq_refl) as [Hv3 | [] ]; [| now eauto].
    now inversion Hv3; subst; inversion Ht3; subst; try (now inversion Ht0); eauto 6.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt3 eq_refl) as [Hv1 | [t1' Hs1] ]; [| now eauto 6].
    now inversion Hv1; subst; inversion Ht3; subst; try (now inversion Ht0); eauto 7.
Qed.

(** ** CBN *)

(** *** Values *)

Inductive CbnValue : Tm -> Prop :=
| CbnValue_abs  :
  forall (t' : Tm) (l : list Atom)
    (Hlc' : forall x : Atom, x # l -> lc (t' {{ 0 ~> x }})),
    CbnValue (abs t')
| CbnValue_unit : CbnValue unit
| CbnValue_abort :
  forall (t' : Tm)
    (Hlc' : lc t'),
    CbnValue (abort t')
| CbnValue_pair :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnValue (pair t1 t2)
| CbnValue_inl :
  forall (t' : Tm)
    (Hlc' : lc t'),
    CbnValue (inl t')
| CbnValue_inr :
  forall (t' : Tm)
    (Hlc' : lc t'),
    CbnValue (inr t')
| CbnValue_zero : CbnValue zero
| CbnValue_succ :
  forall (t' : Tm)
    (Hlc' : lc t'),
    CbnValue (succ t').

#[export] Hint Constructors CbnValue : core.

Lemma lc_CbnValue :
  forall t : Tm,
    CbnValue t -> lc t.
Proof.
  now induction 1; eauto.
Qed.

#[export] Hint Immediate lc_CbnValue : core.

Definition cbnValue (t : Tm) : bool :=
match t with
| fvar _     => false
| bvar _     => false
| abs t'     => true
| unit       => true
| annot _ _  => false
| abort t'   => true
| pair t1 t2 => true
| inl t'     => true
| inr t'     => true
| zero       => true
| succ t'    => true
| _          => false
end.

#[export, refine] Instance Decidable_CbnValue' :
  forall t : Tm, Decidable (CbnValue t) :=
{
  Decidable_witness := cbnValue t && decide (lc t)
}.
Proof.
  split.
  - now destruct t; cbn; try easy; intros H%Decidable_sound; inversion H; eauto.
  - now destruct 1; cbn; try easy; rewrite ?Decidable_spec; eauto.
Qed.

(** ** Contraction *)

Inductive CbnContraction : Tm -> Tm -> Prop :=
| CbnContraction_app_abs :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : forall x : Atom, x # l -> lc (t1 {{ 0 ~> x }}))
    (Hlc2 : lc t2),
    CbnContraction (app (abs t1) t2) (t1 {[ 0 ~> t2 ]})
| CbnContraction_annot :
  forall (t : Tm) (A : Ty)
    (Hlc : lc t),
    CbnContraction (annot t A) t
| CbnContraction_elimUnit :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction (elimUnit t1 t2) (app t1 unit)
| CbnContraction_outl_pair :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction (outl (pair t1 t2)) t1
| CbnContraction_outr_pair :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction (outr (pair t1 t2)) t2
| CbnContraction_elimProd_pair :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (elimProd t1 (pair t2 t3)) (app (app t1 t2) t3)
| CbnContraction_case_inl :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (case t1 t2 (inl t3)) (app t1 t3)
| CbnContraction_case_inr :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (case t1 t2 (inr t3)) (app t2 t3)
| CbnContraction_rec_zero :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction (rec t1 t2 zero) t1
| CbnContraction_rec_succ :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (rec t1 t2 (succ t3)) (app t2 (rec t1 t2 t3)).

#[export] Hint Constructors CbnContraction : core.

Lemma lc_CbnContraction_l :
  forall t t' : Tm,
    CbnContraction t t' -> lc t.
Proof.
  now inversion 1; eauto.
Qed.

Lemma lc_CbnContraction_r :
  forall t t' : Tm,
    CbnContraction t t' -> lc t'.
Proof.
  now inversion 1; eauto.
Qed.

#[export] Hint Immediate lc_CbnContraction_l lc_CbnContraction_r : core.

Lemma CbnContraction_det :
  forall t t1 t2 : Tm,
    CbnContraction t t1 -> CbnContraction t t2 -> t1 = t2.
Proof.
  now do 2 inversion 1.
Qed.

Lemma CbnContraction_not_CbnValue :
  forall t t' : Tm,
    CbnContraction t t' -> CbnValue t -> False.
Proof.
  now do 2 inversion 1.
Qed.

#[export] Hint Resolve CbnContraction_det CbnContraction_not_CbnValue : core.

Lemma preservation_CbnContraction :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    CbnContraction t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  now inversion 1; subst; intros;
    repeat match goal with
    | H : Typing _ ?t _ |- _ => tryif is_var t then fail else (inversion H; subst; clear H)
    end; eauto.
Qed.

(*** *** Abortion *)

Inductive CbnAbortion : Tm -> Tm -> Prop :=
| CbnAbortion_app :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnAbortion (app (abort t1) t2) (abort t1)
(*
| CbnAbortion_elimUnit :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnAbortion (elimUnit t1 (abort t2)) (abort t2)
*)
| CbnAbortion_outl :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbnAbortion (outl (abort t)) (abort t)
| CbnAbortion_outr :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbnAbortion (outr (abort t)) (abort t)
| CbnAbortion_elimProd :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnAbortion (elimProd t1 (abort t2)) (abort t2)
| CbnAbortion_case :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnAbortion (case t1 t2 (abort t3)) (abort t3)
| CbnAbortion_rec :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnAbortion (rec t1 t2 (abort t3)) (abort t3).

#[export] Hint Constructors CbnAbortion : core.

Lemma lc_CbnAbortion_l :
  forall t t' : Tm,
    CbnAbortion t t' -> lc t.
Proof.
  now inversion 1; eauto.
Qed.

Lemma lc_CbnAbortion_r :
  forall t t' : Tm,
    CbnAbortion t t' -> lc t'.
Proof.
  now inversion 1; eauto.
Qed.

#[export] Hint Resolve lc_CbnAbortion_l lc_CbnAbortion_r : core.

Lemma CbnAbortion_det :
  forall t t1 t2 : Tm,
    CbnAbortion t t1 -> CbnAbortion t t2 -> t1 = t2.
Proof.
  now do 2 inversion 1.
Qed.

Lemma CbnAbortion_not_CbnValue :
  forall t t' : Tm,
    CbnAbortion t t' -> CbnValue t -> False.
Proof.
  now do 2 inversion 1.
Qed.

Lemma CbnAbortion_not_CbnContraction :
  forall t t1 t2 : Tm,
    CbnAbortion t t1 -> CbnContraction t t2 -> False.
Proof.
  now do 2 inversion 1.
Qed.

#[export] Hint Resolve
  CbnAbortion_det CbnAbortion_not_CbnValue CbnAbortion_not_CbnContraction : core.

Lemma preservation_CbnAbortion :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    CbnAbortion t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  now do 2 inversion 1; subst;
    match goal with
    | H : Typing _ (abort _) _ |- _ => inversion H
    end; auto.
Qed.

(** ** Reduction *)

Inductive CbnStep : Tm -> Tm -> Prop :=
| CbnStep_CbnContraction :
  forall t t' : Tm,
    CbnContraction t t' ->
    CbnStep t t'
| CbnStep_CbnAbortion :
  forall t t' : Tm,
    CbnAbortion t t' ->
    CbnStep t t'
| CbnStep_app_l :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    CbnStep t1 t1' ->
    CbnStep (app t1 t2) (app t1' t2)
| CbnStep_outl :
  forall (t t' : Tm),
    CbnStep t t' ->
    CbnStep (outl t) (outl t')
| CbnStep_outr :
  forall (t t' : Tm),
    CbnStep t t' ->
    CbnStep (outr t) (outr t')
| CbnStep_elimProd :
  forall (t1 t2 t2' : Tm)
    (Hlc1 : lc t1)
    (Hs2 : CbnStep t2 t2'),
    CbnStep (elimProd t1 t2) (elimProd t1 t2')
| CbnStep_case :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : CbnStep t3 t3'),
    CbnStep (case t1 t2 t3) (case t1 t2 t3')
| CbnStep_rec :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : CbnStep t3 t3'),
    CbnStep (rec t1 t2 t3) (rec t1 t2 t3').

#[export] Hint Constructors CbnStep : core.

Lemma lc_CbnStep_l :
  forall t t' : Tm,
    CbnStep t t' -> lc t.
Proof.
  now induction 1; eauto.
Qed.

Lemma lc_CbnStep_r :
  forall t t' : Tm,
    CbnStep t t' -> lc t'.
Proof.
  now induction 1; eauto.
Qed.

Lemma CbnStep_not_CbnValue :
  forall t t' : Tm,
    CbnStep t t' -> CbnValue t -> False.
Proof.
  induction 1; intros Hv; [| | now inversion Hv; subst; auto..].
  - now eapply CbnContraction_not_CbnValue; eauto.
  - now eapply CbnAbortion_not_CbnValue; eauto.
Qed.

#[export] Hint Immediate lc_CbnStep_l lc_CbnStep_r CbnStep_not_CbnValue : core.

Lemma CbnContraction_CbnStep_det :
  forall t t1 t2 : Tm,
    CbnContraction t t1 -> CbnStep t t2 -> t1 = t2.
Proof.
  inversion 2; subst; intros; [| |
    match goal with
    | Hs : CbnStep _ _ |- _ =>
      now apply CbnStep_not_CbnValue in Hs; [| inversion H; subst; eauto]
    end..].
  - now eapply CbnContraction_det; eauto.
  - now eapply CbnAbortion_not_CbnContraction in H; [| eauto].
Qed.

Lemma CbnAbortion_CbnStep_det :
  forall t t1 t2 : Tm,
    CbnAbortion t t1 -> CbnStep t t2 -> t1 = t2.
Proof.
  inversion 2; subst; intros; [| |
    match goal with
    | Hs : CbnStep _ _ |- _ =>
      now apply CbnStep_not_CbnValue in Hs; [| inversion H; subst; eauto]
    end..].
  - now eapply CbnAbortion_not_CbnContraction in H; [| eauto].
  - now eapply CbnAbortion_det; eauto.
Qed.

#[export] Hint Resolve CbnContraction_CbnStep_det CbnAbortion_CbnStep_det : core.

Lemma CbnStep_det :
  forall t t1 t2 : Tm,
    CbnStep t t1 -> CbnStep t t2 -> t1 = t2.
Proof.
  intros t t1 t2 Hs1 Hs2; revert t2 Hs2.
  now induction Hs1; intros; inversion Hs2; subst; clear Hs2;
    repeat match goal with
    | H : CbnContraction _ _ |- _  => now eapply CbnContraction_CbnStep_det in H; eauto
    | H : CbnAbortion _ _ |- _     => now eapply CbnAbortion_CbnStep_det in H; eauto
    | H : CbnStep (app _ _) _ |- _ => now apply CbnStep_not_CbnValue in H; auto
    | H : CbnStep ?t _ |- _        =>
      tryif is_evar t
      then fail
      else now apply CbnStep_not_CbnValue in H; [| eauto]
    end;
    firstorder congruence.
Qed.

(** ** Progress and preservation *)

Lemma preservation_cbn :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    CbnStep t1 t2 ->
    Typing Γ t1 A ->
    Typing Γ t2 A.
Proof.
  intros Γ t1 t2 A Hstep; revert A.
  induction Hstep; intros A; [| | now inversion 1; subst; eauto..].
  - now eapply preservation_CbnContraction.
  - now eapply preservation_CbnAbortion.
Qed.

Lemma progress_cbn :
  forall (t : Tm) (A : Ty),
    Typing [] t A ->
      CbnValue t \/ exists t' : Tm, CbnStep t t'.
Proof.
  intros t A Ht.
  remember [] as Γ.
  induction Ht; subst; try now auto.
  - now left; eauto using lc_Typing.
  - destruct (IHHt1 eq_refl) as [ Hv | [t1' Hs1] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht1; subst; eauto 6.
  - now right; eauto.
  - right; destruct (IHHt1 eq_refl) as [ Hv | [t1' Hs1] ]; [| now eauto 6].
    now inversion Hv; subst; inversion Ht1; subst; try (now inversion Ht0); eauto 6.
  - now left; eauto.
  - now destruct (IHHt1 eq_refl) as [| [] ], (IHHt2 eq_refl) as [| [] ]; eauto.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht; subst; try (now inversion Ht1); eauto 6.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht; subst; try (now inversion Ht1); eauto 6.
  - right; destruct (IHHt2 eq_refl) as [Hv | [t'' Hs] ]; [| now eauto 6].
    now inversion Hv; subst; inversion Ht2; subst; try (now inversion Ht0); eauto 6.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt3 eq_refl) as [Hv3 | [] ]; [| now eauto].
    now inversion Hv3; subst; inversion Ht3; subst; try (now inversion Ht0); eauto 6.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt3 eq_refl) as [Hv1 | [t1' Hs1] ]; [| now eauto 6].
    now inversion Hv1; subst; inversion Ht3; subst; try (now inversion Ht0); eauto 7.
Qed.

Lemma Cbv_Cbn :
  forall (t1 t2 : Tm),
    CbvAbortion t1 t2 <-> CbnAbortion t1 t2.
Proof.
  split.
  - inversion 1; subst; eauto.
    admit.
  - inversion 1; eauto.
Admitted.

(** ** Deep CBV *)

(** *** Values *)

Inductive DeepCbvValue : Tm -> Prop :=
| DeepCbvValue_abs  :
  forall (t' : Tm) (l : list Atom)
    (Hv' : forall x : Atom, x # l -> DeepCbvValue (t' {{ 0 ~> x }})),
    DeepCbvValue (abs t')
| DeepCbvValue_unit : DeepCbvValue unit
| DeepCbvValue_abort :
  forall (t' : Tm)
    (Hlc' : lc t'),
    DeepCbvValue (abort t')
| DeepCbvValue_pair :
  forall t1 t2 : Tm,
    DeepCbvValue t1 ->
    DeepCbvValue t2 ->
    DeepCbvValue (pair t1 t2)
| DeepCbvValue_inl :
  forall v : Tm,
    DeepCbvValue v ->
    DeepCbvValue (inl v)
| DeepCbvValue_inr :
  forall v : Tm,
    DeepCbvValue v ->
    DeepCbvValue (inr v)
| DeepCbvValue_zero : DeepCbvValue zero
| DeepCbvValue_succ :
  forall (t' : Tm)
    (Hv' : DeepCbvValue t'),
    DeepCbvValue (succ t').

#[export] Hint Constructors DeepCbvValue : core.

Lemma lc_DeepCbvValue :
  forall t : Tm,
    DeepCbvValue t -> lc t.
Proof.
  induction 1; try now auto.
  now eapply lc_abs; eauto.
Qed.

#[export] Hint Resolve lc_DeepCbvValue : core.

Fixpoint deepCbvValue (t : Tm) : bool :=
match t with
| abs t'               => decide (lc (abs t'))
| unit                 => true
| abort t'             => decide (lc t')
| pair t1 t2           => deepCbvValue t1 && deepCbvValue t2
| inl t'               => deepCbvValue t'
| inr t'               => deepCbvValue t'
| zero                 => true
| succ t'              => deepCbvValue t'
| _                    => false
end.

(*
#[export, refine] Instance Decidable_DeepCbvValue :
  forall t : Tm, Decidable (DeepCbvValue t) :=
{
  Decidable_witness := deepCbvValue t
}.
Proof.
  split.
  - induction t; cbn; subst; try now eauto.
    + intros H%Decidable_sound.
      now inversion H; subst; eauto.
    + intros H%Decidable_sound.
      now eauto.
    + now intros [Ht1 Ht2]%andb_prop; eauto.
  - induction 1; cbn in *; try now eauto using Decidable_complete.
    now rewrite IHDeepCbvValue1, IHDeepCbvValue2.
Defined.
*)

(** *** Contraction *)

Inductive DeepCbvContraction : Tm -> Tm -> Prop :=
| DeepCbvContraction_app_abs :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hv1 : DeepCbvValue (abs t1))
    (Hv2 : DeepCbvValue t2),
    DeepCbvContraction (app (abs t1) t2) (t1 {[ 0 ~> t2 ]})
| DeepCbvContraction_annot :
  forall (t : Tm) (A : Ty)
    (Hlc : lc t),
    DeepCbvContraction (annot t A) t
| DeepCbvContraction_elimUnit_unit :
  forall (t : Tm)
    (Hlc : lc t),
    DeepCbvContraction (elimUnit t unit) (app t unit)
| DeepCbvContraction_outl_pair :
  forall (v1 v2 : Tm)
    (Hv1 : DeepCbvValue v1)
    (Hv2 : DeepCbvValue v2),
    DeepCbvContraction (outl (pair v1 v2)) v1
| DeepCbvContraction_outr_pair :
  forall (v1 v2 : Tm)
    (Hv1 : DeepCbvValue v1)
    (Hv2 : DeepCbvValue v2),
    DeepCbvContraction (outr (pair v1 v2)) v2
| DeepCbvContraction_elimProd_pair :
  forall (v1 v2 t : Tm)
    (Hv1 : DeepCbvValue v1)
    (Hv2 : DeepCbvValue v2)
    (Hlc3 : lc t),
    DeepCbvContraction (elimProd t (pair v1 v2)) (app (app t v1) v2)
| DeepCbvContraction_case_inl :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv3 : DeepCbvValue t3),
    DeepCbvContraction (case t1 t2 (inl t3)) (app t1 t3)
| DeepCbvContraction_case_inr :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv3 : DeepCbvValue t3),
    DeepCbvContraction (case t1 t2 (inr t3)) (app t2 t3)
| DeepCbvContraction_rec_zero :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    DeepCbvContraction (rec t1 t2 zero) t1
| DeepCbvContraction_rec_succ :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv3 : DeepCbvValue t3),
    DeepCbvContraction (rec t1 t2 (succ t3)) (app t2 (rec t1 t2 t3)).

#[export] Hint Constructors DeepCbvContraction : core.

Lemma lc_DeepCbvContraction_l :
  forall t t' : Tm,
    DeepCbvContraction t t' -> lc t.
Proof.
  now inversion 1; auto.
Qed.

Lemma lc_DeepCbvContraction_r :
  forall t t' : Tm,
    DeepCbvContraction t t' -> lc t'.
Proof.
  inversion 1; subst; try now auto.
  inversion Hv1; subst.
  now rewrite (open'_spec _ _ (fresh (l ++ l0 ++ fv t1))); auto.
Qed.

#[export] Hint Immediate lc_DeepCbvContraction_l lc_DeepCbvContraction_r : core.

Lemma DeepCbvContraction_det :
  forall t t1 t2 : Tm,
    DeepCbvContraction t t1 -> DeepCbvContraction t t2 -> t1 = t2.
Proof.
  now do 2 inversion 1.
Qed.

Lemma DeepCbvContraction_not_DeepCbvValue :
  forall t t' : Tm,
    DeepCbvContraction t t' -> DeepCbvValue t -> False.
Proof.
  now do 2 inversion 1.
Qed.

#[export] Hint Resolve DeepCbvContraction_det DeepCbvContraction_not_DeepCbvValue : core.

Lemma preservation_DeepCbvContraction :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    DeepCbvContraction t1 t2 ->
    Typing Γ t1 A ->
    Typing Γ t2 A.
Proof.
  now inversion 1; subst; intros;
    repeat match goal with
    | H : Typing _ ?t _ |- _ => tryif is_var t then fail else (inversion H; subst; clear H)
    end; eauto.
Qed.

(*** *** Abortion *)

Inductive DeepCbvAbortion : Tm -> Tm -> Prop :=
| DeepCbvAbortion_app :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    DeepCbvAbortion (app (abort t1) t2) (abort t1)
| DeepCbvAbortion_elimUnit :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    DeepCbvAbortion (elimUnit t1 (abort t2)) (abort t2)
| DeepCbvAbortion_outl :
  forall (t : Tm)
    (Hlc' : lc  t),
    DeepCbvAbortion (outl (abort t)) (abort t)
| DeepCbvAbortion_outr :
  forall (t : Tm)
    (Hlc' : lc  t),
    DeepCbvAbortion (outr (abort t)) (abort t)
| DeepCbvAbortion_elimProd :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    DeepCbvAbortion (elimProd t1 (abort t2)) (abort t2)
| DeepCbvAbortion_case :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    DeepCbvAbortion (case t1 t2 (abort t3)) (abort t3)
| DeepCbvAbortion_rec :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    DeepCbvAbortion (rec t1 t2 (abort t3)) (abort t3).

#[export] Hint Constructors DeepCbvAbortion : core.

Lemma lc_DeepCbvAbortion_l :
  forall t t' : Tm,
    DeepCbvAbortion t t' -> lc t.
Proof.
  now inversion 1; auto.
Qed.

Lemma lc_DeepCbvAbortion_r :
  forall t t' : Tm,
    DeepCbvAbortion t t' -> lc t'.
Proof.
  now inversion 1; auto.
Qed.

#[export] Hint Resolve lc_DeepCbvAbortion_l lc_DeepCbvAbortion_r : core.

Lemma DeepCbvAbortion_det :
  forall t t1 t2 : Tm,
    DeepCbvAbortion t t1 -> DeepCbvAbortion t t2 -> t1 = t2.
Proof.
  now do 2 inversion 1.
Qed.

Lemma DeepCbvAbortion_not_DeepCbvValue :
  forall t t' : Tm,
    DeepCbvAbortion t t' -> DeepCbvValue t -> False.
Proof.
  now do 2 inversion 1.
Qed.

Lemma DeepCbvAbortion_not_DeepCbvContraction :
  forall t t1 t2 : Tm,
    DeepCbvAbortion t t1 -> DeepCbvContraction t t2 -> False.
Proof.
  now do 2 inversion 1.
Qed.

#[export] Hint Resolve
  DeepCbvAbortion_det DeepCbvAbortion_not_DeepCbvValue DeepCbvAbortion_not_DeepCbvContraction : core.

Lemma preservation_DeepCbvAbortion :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    DeepCbvAbortion t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  now do 2 inversion 1; subst;
    match goal with
    | H : Typing _ (abort _) _ |- _ => inversion H
    end; auto.
Qed.

(** *** Reduction *)

Inductive DeepCbvStep : Tm -> Tm -> Prop :=
| DeepCbvStep_DeepCbvContraction :
  forall t t' : Tm,
    DeepCbvContraction t t' ->
    DeepCbvStep t t'
| DeepCbvStep_DeepCbvAbortion :
  forall t t' : Tm,
    DeepCbvAbortion t t' ->
    DeepCbvStep t t'
| DeepCbvStep_abs :
  forall (t1 t1' : Tm) (l : list Atom)
    (Hs1 : forall x : Atom, x # l -> DeepCbvStep (t1 {{ 0 ~> x }}) (t1' {{ 0 ~> x }})),
    DeepCbvStep (abs t1) (abs t1')
| DeepCbvStep_app_l :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    DeepCbvStep t1 t1' ->
    DeepCbvStep (app t1 t2) (app t1' t2)
| DeepCbvStep_app_r :
  forall (t1 t2 t2' : Tm) (l : list Atom)
    (Hv1 : DeepCbvValue (abs t1)),
    DeepCbvStep t2 t2' ->
    DeepCbvStep (app (abs t1) t2) (app (abs t1) t2')
| DeepCbvStep_elimUnit :
  forall (t1 t2 t2' : Tm)
    (Hlc1 : lc t1),
    DeepCbvStep t2 t2' ->
    DeepCbvStep (elimUnit t1 t2) (elimUnit t1 t2')
| DeepCbvStep_pair_l :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    DeepCbvStep t1 t1' ->
    DeepCbvStep (pair t1 t2) (pair t1' t2)
| DeepCbvStep_pair_r :
  forall (t1 t2 t2' : Tm),
    DeepCbvValue t1 ->
    DeepCbvStep t2 t2' ->
    DeepCbvStep (pair t1 t2) (pair t1 t2')
| DeepCbvStep_outl :
  forall (t t' : Tm),
    DeepCbvStep t t' ->
    DeepCbvStep (outl t) (outl t')
| DeepCbvStep_outr :
  forall (t t' : Tm),
    DeepCbvStep t t' ->
    DeepCbvStep (outr t) (outr t')
| DeepCbvStep_elimProd :
  forall (t1 t2 t2' : Tm)
    (Hlc1 : lc t1)
    (Hs2 : DeepCbvStep t2 t2'),
    DeepCbvStep (elimProd t1 t2) (elimProd t1 t2')
| DeepCbvStep_inl :
  forall t t' : Tm,
    DeepCbvStep t t' ->
    DeepCbvStep (inl t) (inl t')
| DeepCbvStep_inr :
  forall t t' : Tm,
    DeepCbvStep t t' ->
    DeepCbvStep (inr t) (inr t')
| DeepCbvStep_case :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : DeepCbvStep t3 t3'),
    DeepCbvStep (case t1 t2 t3) (case t1 t2 t3')
| DeepCbvStep_succ :
  forall (t t' : Tm),
    DeepCbvStep t t' ->
    DeepCbvStep (succ t) (succ t')
| DeepCbvStep_rec :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : DeepCbvStep t3 t3'),
    DeepCbvStep (rec t1 t2 t3) (rec t1 t2 t3').

#[export] Hint Constructors DeepCbvStep : core.

Lemma lc_DeepCbvStep_l :
  forall t t' : Tm,
    DeepCbvStep t t' -> lc t.
Proof.
  now induction 1; eauto.
Qed.

Lemma lc_DeepCbvStep_r :
  forall t t' : Tm,
    DeepCbvStep t t' -> lc t'.
Proof.
  now induction 1; eauto.
Qed.

Lemma DeepCbvStep_not_DeepCbvValue :
  forall t t' : Tm,
    DeepCbvStep t t' -> DeepCbvValue t -> False.
Proof.
  induction 1; intros Hv; [| | | now inversion Hv..].
  - now eapply DeepCbvContraction_not_DeepCbvValue; eauto.
  - now eapply DeepCbvAbortion_not_DeepCbvValue; eauto.
  - inversion Hv; subst.
    now apply (H (fresh (l ++ l0))); auto.
Qed.

#[export] Hint Immediate lc_DeepCbvStep_l lc_DeepCbvStep_r DeepCbvStep_not_DeepCbvValue : core.

Lemma DeepCbvContraction_DeepCbvStep_det :
  forall t t1 t2 : Tm,
    DeepCbvContraction t t1 -> DeepCbvStep t t2 -> t1 = t2.
Proof.
  inversion 2; subst; intros; [| |
    try match goal with
    | Hs : DeepCbvStep _ _ |- _ =>
      now apply DeepCbvStep_not_DeepCbvValue in Hs; [| inversion H; subst; eauto]
    end..].
  - now eapply DeepCbvContraction_det; eauto.
  - now eapply DeepCbvAbortion_not_DeepCbvContraction in H; [| eauto].
Qed.

Lemma DeepCbvAbortion_DeepCbvStep_det :
  forall t t1 t2 : Tm,
    DeepCbvAbortion t t1 -> DeepCbvStep t t2 -> t1 = t2.
Proof.
  inversion 2; subst; intros; [| |
    match goal with
    | Hs : DeepCbvStep _ _ |- _ =>
      now apply DeepCbvStep_not_DeepCbvValue in Hs; [| inversion H; subst; eauto]
    end..].
  - now eapply DeepCbvAbortion_not_DeepCbvContraction in H; [| eauto].
  - now eapply DeepCbvAbortion_det; eauto.
Qed.

#[export] Hint Resolve DeepCbvContraction_DeepCbvStep_det DeepCbvAbortion_DeepCbvStep_det : core.

Lemma DeepCbvStep_det :
  forall t t1 t2 : Tm,
    DeepCbvStep t t1 -> DeepCbvStep t t2 -> t1 = t2.
Proof.
  intros t t1 t2 Hs1 Hs2; revert t2 Hs2.
  induction Hs1; intros; inversion Hs2; subst; clear Hs2;
    repeat match goal with
    | H : DeepCbvContraction _ _ |- _  => now eapply DeepCbvContraction_DeepCbvStep_det in H; eauto
    | H : DeepCbvAbortion _ _ |- _     => now eapply DeepCbvAbortion_DeepCbvStep_det in H; eauto
    | H : DeepCbvStep (app _ _) _ |- _ => now apply DeepCbvStep_not_DeepCbvValue in H; auto
    | H : DeepCbvStep ?t _ |- _        =>
      tryif is_evar t
      then fail
      else now apply DeepCbvStep_not_DeepCbvValue in H; [| eauto]
    end; try now firstorder congruence.
  now apply abs_eq with (fresh (l ++ l0 ++ fv t1' ++ fv t1'0)); auto.
Qed.

(** *** Progress and preservation *)

Lemma preservation_deep_cbv :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    DeepCbvStep t1 t2 ->
    Typing Γ t1 A ->
    Typing Γ t2 A.
Proof.
  intros Γ t1 t2 A Hstep; revert Γ A.
  induction Hstep; intros Γ A; [| | | now inversion 1; subst; eauto..].
  - now eapply preservation_DeepCbvContraction.
  - now eapply preservation_DeepCbvAbortion.
  - inversion 1; subst.
    now apply Typing_abs with (l ++ l0); eauto.
Qed.

(*
Lemma progress_deep_cbv :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Typing Γ t A ->
      DeepCbvValue t \/ exists t' : Tm, DeepCbvStep t t'.
Proof.
  intros Γ t A Ht.
  induction Ht; subst; try now auto.
  - admit.
  - destruct IHHt1 as [ Hv | [t1' Hs1] ]; [| now eauto].
    inversion Hv; subst; inversion Ht1; subst; try now auto.
    + destruct IHHt2 as [ Hv2 | [t2' Hs2] ]; eauto.
    + now eauto 6.
  - now right; eauto.
  - right; destruct (IHHt2 eq_refl) as [ Hv | [t2' Hs2] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht2; subst; try (now inversion Ht0); eauto 6.
  - now left; eauto.
  - now destruct (IHHt1 eq_refl) as [| [] ], (IHHt2 eq_refl) as [| [] ]; eauto.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht; subst; try (now inversion Ht1); eauto 6.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht; subst; try (now inversion Ht1); eauto 6.
  - right; destruct (IHHt2 eq_refl) as [Hv | [t'' Hs] ]; [| now eauto 6].
    now inversion Hv; subst; inversion Ht2; subst; try (now inversion Ht0); eauto 6.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt3 eq_refl) as [Hv3 | [] ]; [| now eauto].
    now inversion Hv3; subst; inversion Ht3; subst; try (now inversion Ht0); eauto 6.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt3 eq_refl) as [Hv1 | [t1' Hs1] ]; [| now eauto 6].
    now inversion Hv1; subst; inversion Ht3; subst; try (now inversion Ht0); eauto 7.
Admitted.
*)
