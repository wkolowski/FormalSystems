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
| elimUnit'  : Tm -> Tm -> Tm
| elimUnit'' : Tm
| abort      : Tm -> Tm
| pair       : Tm -> Tm -> Tm
| outl       : Tm -> Tm
| outr       : Tm -> Tm
| elimProd   : Tm -> Tm -> Tm
| inl        : Tm -> Tm
| inr        : Tm -> Tm
| case       : Tm -> Tm -> Tm -> Tm
| case'      : Tm -> Tm -> Tm -> Tm
| case''     : Tm
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

(** ** Opening and closing *)

#[export] Instance Open_Tm : Open nat Atom Tm :=
  fix open (t : Tm) (i : nat) (a : Atom) : Tm :=
(*     let _ : Open nat Atom Tm := open in *)
    match t with
    | fvar a          => fvar a
    | bvar j          => if decide (i = j) then a else bvar j
(*     | abs t'          => abs (t' {{ S i ~> a }}) *)
    | abs t'          => abs (open t' (S i) a)
    | app t1 t2       => app (open t1 i a) (open t2 i a)
    | annot t' A      => annot (open t' i a) A
    | unit            => unit
    | elimUnit t1 t2  => elimUnit (open t1 i a) (open t2 (S i) a)
    | elimUnit' t1 t2 => elimUnit' (open t1 i a) (open t2 i a)
    | elimUnit''      => elimUnit''
    | abort t'        => abort (open t' i a)
    | pair t1 t2      => pair (open t1 i a) (open t2 i a)
    | outl t'         => outl (open t' i a)
    | outr t'         => outr (open t' i a)
    | elimProd t1 t2  => elimProd (open t1 i a) (open t2 (S (S i)) a)
    | inl t'          => inl (open t' i a)
    | inr t'          => inr (open t' i a)
    | case t1 t2 t3   => case (open t1 i a) (open t2 (S i) a) (open t3 (S i) a)
    | case' t1 t2 t3  => case' (open t1 i a) (open t2 i a) (open t3 i a)
    | case''          => case''
    | zero            => zero
    | succ t'         => succ (open t' i a)
    | rec t1 t2 t3    => rec (open t1 i a) (open t2 (S i) a) (open t3 i a)
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
    | elimUnit t1 t2  => elimUnit (close t1 i a) (close t2 (S i) a)
    | elimUnit' t1 t2 => elimUnit' (close t1 i a) (close t2 i a)
    | elimUnit''      => elimUnit''
    | abort t'        => abort (close t' i a)
    | pair t1 t2      => pair (close t1 i a) (close t2 i a)
    | outl t'         => outl (close t' i a)
    | outr t'         => outr (close t' i a)
    | elimProd t1 t2  => elimProd (close t1 i a) (close t2 (S (S i)) a)
    | inl t'          => inl (close t' i a)
    | inr t'          => inr (close t' i a)
    | case t1 t2 t3   => case (close t1 i a) (close t2 (S i) a) (close t3 (S i) a)
    | case' t1 t2 t3  => case' (close t1 i a) (close t2 i a) (close t3 i a)
    | case''          => case''
    | zero            => zero
    | succ t'         => succ (close t' i a)
    | rec t1 t2 t3    => rec (close t1 i a) (close t2 (S i) a) (close t3 i a)
    end.

#[export, refine] Instance OC_Tm :
  OC nat Atom Tm Open_Tm Close_Tm := {}.
Proof.
  all: induction t; cbn; intros;
    decide_all; rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3; congruence.
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
| fvar x          => [x]
| bvar _          => []
| abs t'          => fv t'
| app t1 t2       => fv t1 ++ fv t2
| annot t' A      => fv t'
| unit            => []
| elimUnit t1 t2  => fv t1 ++ fv t2
| elimUnit' t1 t2 => fv t1 ++ fv t2
| elimUnit''      => []
| abort t'        => fv t'
| pair t1 t2      => fv t1 ++ fv t2
| outl t'         => fv t'
| outr t'         => fv t'
| elimProd t1 t2  => fv t1 ++ fv t2
| inl t'          => fv t'
| inr t'          => fv t'
| case t1 t2 t3   => fv t1 ++ fv t2 ++ fv t3
| case' t1 t2 t3  => fv t1 ++ fv t2 ++ fv t3
| case''          => []
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
      try (now rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3 by solve_fresh').
    + now firstorder decide_all.
    + now f_equal; rewrite close_invariant, IHt.
    + rewrite IHt1 by solve_fresh'; f_equal.
      now rewrite close_invariant, IHt2 by solve_fresh'.
    + rewrite IHt1 by solve_fresh'; f_equal.
      now rewrite close_invariant, IHt2 by solve_fresh'.
    + rewrite IHt1 by solve_fresh'; f_equal.
      * now rewrite close_invariant, IHt2 by solve_fresh'.
      * now rewrite close_invariant, IHt3 by solve_fresh'.
    + rewrite IHt1, IHt3 by solve_fresh'; f_equal.
      now rewrite close_invariant, IHt2 by solve_fresh'.
  - intros t.
    setoid_rewrite LocallyClosed_forall.
    induction t; cbn;
      try (now exists 0);
      try (now destruct IHt as [i IH]; exists i; intros j a Hij; rewrite IH; [| lia]);
      try (now destruct IHt1 as [i1 IH1], IHt2 as [i2 IH2];
        exists (max i1 i2); intros j a Hle; rewrite IH1, IH2; [| lia..]).
    + exists (S n); intros j a Hij.
      now decide_all; lia.
    + destruct IHt1 as [i1 IH1], IHt2 as [i2 IH2], IHt3 as [i3 IH3].
      exists (max i1 (max i2 i3)); intros j a Hle.
      now rewrite IH1, IH2, IH3; [| lia..].
    + destruct IHt1 as [i1 IH1], IHt2 as [i2 IH2], IHt3 as [i3 IH3].
      exists (max i1 (max i2 i3)); intros j a Hle.
      now rewrite IH1, IH2, IH3; [| lia..].
    + destruct IHt1 as [i1 IH1], IHt2 as [i2 IH2], IHt3 as [i3 IH3].
      exists (max i1 (max i2 i3)); intros j a Hle.
      now rewrite IH1, IH2, IH3; [| lia..].
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
| LocallyClosed'_annot :
  forall (i : nat) (t' : Tm) (A : Ty),
    LocallyClosed' i t' -> LocallyClosed' i (annot t' A)
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
| LocallyClosed'_elimProd :
  forall (i : nat) (t1 t2 : Tm),
    LocallyClosed' i t1 ->
    LocallyClosed' (S (S i)) t2 ->
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
    LocallyClosed' (S i) t2 ->
    LocallyClosed' (S i) t3 ->
    LocallyClosed' i (case t1 t2 t3)
| LocallyClosed'_case' :
  forall (i : nat) (t1 t2 t3 : Tm),
    LocallyClosed' i t1 ->
    LocallyClosed' i t2 ->
    LocallyClosed' i t3 ->
    LocallyClosed' i (case' t1 t2 t3)
| LocallyClosed'_case'' :
  forall (i : nat),
    LocallyClosed' i case''
| LocallyClosed'_zero :
  forall (i : nat),
    LocallyClosed' i zero
| LocallyClosed'_succ :
  forall (i : nat) (t' : Tm),
    LocallyClosed' i t' -> LocallyClosed' i (succ t')
| LocallyClosed'_rec :
  forall (i : nat) (t1 t2 t3 : Tm),
    LocallyClosed' i t1 ->
    LocallyClosed' (S i) t2 ->
    LocallyClosed' i t3 ->
    LocallyClosed' i (rec t1 t2 t3).

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
    + now rewrite IHLocallyClosed'1, IHLocallyClosed'2; [| lia..].
    + now rewrite IHLocallyClosed'1, IHLocallyClosed'2, IHLocallyClosed'3; [| lia..].
    + now rewrite IHLocallyClosed'1, IHLocallyClosed'2, IHLocallyClosed'3; [| lia..].
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
| elimUnit t1 t2  => dec_LC_aux i t1 && dec_LC_aux (S i) t2
| elimUnit' t1 t2 => dec_LC_aux i t1 && dec_LC_aux i t2
| elimUnit''      => true
| abort t'        => dec_LC_aux i t'
| pair t1 t2      => dec_LC_aux i t1 && dec_LC_aux i t2
| outl t'         => dec_LC_aux i t'
| outr t'         => dec_LC_aux i t'
| elimProd t1 t2  => dec_LC_aux i t1 && dec_LC_aux (S (S i)) t2
| inl t'          => dec_LC_aux i t'
| inr t'          => dec_LC_aux i t'
| case t1 t2 t3   => dec_LC_aux i t1 && dec_LC_aux (S i) t2 && dec_LC_aux (S i) t3
| case' t1 t2 t3  => dec_LC_aux i t1 && dec_LC_aux i t2 && dec_LC_aux i t3
| case''          => true
| zero            => true
| succ t'         => dec_LC_aux i t'
| rec t1 t2 t3    => dec_LC_aux i t1 && dec_LC_aux (S i) t2 && dec_LC_aux i t3
end.

#[export, refine] Instance Decidable_LocallyClosed' :
  forall (i : nat) (t : Tm), Decidable (LocallyClosed' i t) :=
{
  Decidable_witness :=
    dec_LC_aux i t;
}.
Proof.
  split.
  - revert i; induction t; cbn; intros i H;
      repeat match goal with
      | H : _ && _ = true |- _ => apply andb_prop in H as []
      end;
      try now auto.
    now constructor; decide (n < i); lia.
  - induction 1; cbn; rewrite ?andb_true_iff; try now auto.
    now decide (n < i); auto.
Defined.

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
  - intros []; [now apply IHt1 |].
    apply IHt2; [| easy].
    now rewrite (close_invariant _ 0 1).
  - intros []; [now apply IHt1 |].
    apply IHt2; [| easy].
    now rewrite (close_invariant _ 0 2).
  - intros []; [now apply IHt1 |].
    destruct H.
    + apply IHt2; [| easy].
      now rewrite (close_invariant _ 0 1).
    + apply IHt3; [| easy].
      now rewrite (close_invariant _ 0 1).
  - intros [| []]; [now apply IHt1 | | now apply IHt3].
    apply IHt2; [| easy].
    now rewrite (close_invariant _ 0 1).
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
| elimUnit' t1 t2 => elimUnit' (subst t1 x u) (subst t2 x u)
| elimUnit''      => elimUnit''
| abort t'        => abort (subst t' x u)
| pair t1 t2      => pair (subst t1 x u) (subst t2 x u)
| outl t'         => outl (subst t' x u)
| outr t'         => outr (subst t' x u)
| elimProd t1 t2  => elimProd (subst t1 x u) (subst t2 x u)
| inl t'          => inl (subst t' x u)
| inr t'          => inr (subst t' x u)
| case t1 t2 t3   => case (subst t1 x u) (subst t2 x u) (subst t3 x u)
| case' t1 t2 t3  => case' (subst t1 x u) (subst t2 x u) (subst t3 x u)
| case''          => case''
| zero            => zero
| succ t'         => succ (subst t' x u)
| rec t1 t2 t3    => rec (subst t1 x u) (subst t2 x u) (subst t3 x u)
end.

Notation "t [[ x := u ]]" := (subst t x u) (at level 68).

Lemma subst_fv :
  forall (t : Tm) (x : Atom) (u : Tm),
    x # fv t -> t [[ x := u ]] = t.
Proof.
  now induction t; cbn; intros;
    [firstorder decide_all | rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3 by solve_fresh'..].
Qed.

Lemma subst_subst :
  forall (t : Tm) (x y : Atom) (u1 u2 : Tm),
    x <> y -> x # fv u2 -> y # fv u1 ->
    t [[ x := u1 ]] [[ y := u2 ]]
      =
    t [[ y := u2 ]] [[ x := u1 ]].
Proof.
  induction t; cbn; intros;
    try now rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3.
  now decide_all; rewrite subst_fv by solve_fresh'.
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
| elimUnit t1 t2  => elimUnit (open' t1 i u) (open' t2 (S i) u)
| elimUnit' t1 t2 => elimUnit' (open' t1 i u) (open' t2 i u)
| elimUnit''      => elimUnit''
| abort t'        => abort (open' t' i u)
| pair t1 t2      => pair (open' t1 i u) (open' t2 i u)
| outl t'         => outl (open' t' i u)
| outr t'         => outr (open' t' i u)
| elimProd t1 t2  => elimProd (open' t1 i u) (open' t2 (S (S i)) u)
| inl t'          => inl (open' t' i u)
| inr t'          => inr (open' t' i u)
| case t1 t2 t3   => case (open' t1 i u) (open' t2 (S i) u) (open' t3 (S i) u)
| case' t1 t2 t3  => case' (open' t1 i u) (open' t2 i u) (open' t3 i u)
| case''          => case''
| zero            => zero
| succ t'         => succ (open' t' i u)
| rec t1 t2 t3    => rec (open' t1 i u) (open' t2 (S i) u) (open' t3 i u)
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
    try now rewrite <- 1?IHt, 1?(IHt1 _ x), 1?(IHt2 _ x), 1?(IHt3 _ x) by solve_fresh'.
  - now firstorder decide_all.
  - now decide_all.
Qed.

Lemma open'_spec' :
  forall (t : Tm) (i : nat) (u : Tm),
    t {[ i ~> u ]} = t {{ i ~> fresh (fv t) }} [[ fresh (fv t) := u ]].
Proof.
  now intros; apply open'_spec; solve_fresh'.
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
| lc_annot :
  forall (t' : Tm) (A : Ty)
    (Hlc' : lc t'),
    lc (annot t' A)
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
| lc_elimProd :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x y : Atom, x # l -> y # x :: l -> lc (t2 {{ 0 ~> x }} {{ 1 ~> y }})),
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
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall y : Atom, y # l -> lc (t3 {{ 0 ~> y }})),
    lc (case t1 t2 t3)
| lc_case' :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    lc (case' t1 t2 t3)
| lc_case'' : lc case''
| lc_zero : lc zero
| lc_succ :
  forall (t' : Tm)
    (Hlc' : lc t'),
    lc (succ t')
| lc_rec :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : lc t3),
    lc (rec t1 t2 t3).

#[export] Hint Constructors lc : core.

Lemma LocallyClosed_lc :
  forall t : Tm,
    lc t -> LocallyClosed 0 t.
Proof.
  setoid_rewrite LocallyClosed_forall.
  induction 1; cbn; intros j a Hle; try now f_equal; unshelve eauto.
  - now f_equal; eapply open_open, (H _ (fresh_spec l)); lia.
  - f_equal; [now eauto |].
    now eapply open_open, (H0 _ (fresh_spec l)); lia.
  - f_equal; [now eauto |].
    now eapply open_open, open_open,
      (H0 _ _ (fresh_spec l) (fresh_spec ([fresh l] ++ l))); lia.
  - f_equal; [now eauto | |].
    + now eapply open_open, (H0 _ (fresh_spec l)); lia.
    + now eapply open_open, (H1 _ (fresh_spec l)); lia.
  - f_equal; [now eauto | | now eauto].
    now eapply open_open, (H0 _ (fresh_spec l)); lia.
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
    [decide_all | decide_all | rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3..].
Qed.

Lemma subst_open :
  forall (t : Tm) (a b : Atom) (i : nat) (u : Tm),
    a <> b -> lc u ->
    t [[ a := u ]] {{ i ~> b }} = t {{ i ~> b }} [[ a := u ]].
Proof.
  induction t; cbn; intros; [| | now rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3..].
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
    now intros y Hy; rewrite subst_open; firstorder.
  - apply lc_elimUnit with (x :: l); [now apply IHHt |].
    now intros y Hy; rewrite subst_open; firstorder.
  - now apply lc_elimProd with (x :: l); [now apply IHHt |];
     intros y z Hy Hz; rewrite !subst_open; firstorder.
  - now apply lc_case with (x :: l); [now apply IHHt | |];
      intros y Hy; rewrite subst_open; firstorder.
  - now apply lc_rec with (x :: l); [now apply IHHt1 | | now apply IHHt2];
      intros y Hy; rewrite subst_open; firstorder.
Qed.

Lemma lc_open' :
  forall (t u : Tm) (i : nat),
    (exists l : list Atom, forall x : Atom, x # l -> lc (t {{ i ~> x }})) ->
    lc u ->
      lc (t {[ i ~> u ]}).
Proof.
  intros t u i [l Hlct] Hlcu.
  rewrite (open'_spec _ _ (fresh (l ++ fv t))) by solve_fresh'.
  apply lc_subst; [| easy].
  apply Hlct.
  now solve_fresh'.
Qed.

#[export] Hint Resolve lc_open lc_open' : core.

Lemma open'_lc :
  forall (t : Tm) (i : nat) (u : Tm),
    lc t -> t {[ i ~> u ]} = t.
Proof.
  intros t i u Hlc.
  rewrite open'_spec'.
  rewrite (open_LocallyClosed t i); [.. | now lia].
  - now rewrite subst_fv by solve_fresh'.
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
  induction t; cbn; intros; [| | now rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3..].
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
  - now solve_fresh'.
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
| Typing_annot :
  forall (Γ : Ctx) (t' : Tm) (A : Ty)
    (Ht' : Typing Γ t' A),
    Typing Γ (annot t' A) A
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
| Typing_elimProd :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B C : Ty) (l : list Atom)
    (Ht1 : Typing Γ t1 (TyProd A B))
    (Ht2 : forall x y : Atom, x # l -> y # x :: l ->
      Typing ((y, B) :: (x, A) :: Γ) (t2 {{ 0 ~> x }} {{ 1 ~> y }}) C),
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
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty) (l : list Atom)
    (Ht1 : Typing Γ t1 (TySum A B))
    (Ht2 : forall x : Atom, x # l -> Typing ((x, A) :: Γ) (t2 {{ 0 ~> x }}) C)
    (Ht3 : forall y : Atom, y # l -> Typing ((y, B) :: Γ) (t3 {{ 0 ~> y }}) C),
    Typing Γ (case t1 t2 t3) C
| Typing_case' :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty)
    (Ht1 : Typing Γ t1 (TyFun A C))
    (Ht2 : Typing Γ t2 (TyFun B C))
    (Ht3 : Typing Γ t3 (TySum A B)),
    Typing Γ (case' t1 t2 t3) C
| Typing_case'' :
  forall (Γ : Ctx) (A B C : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ case'' (TyFun (TyFun A C) (TyFun (TyFun B C) (TyFun (TySum A B) C)))
| Typing_zero :
  forall (Γ : Ctx)
    (Hwf : WfCtx Γ),
    Typing Γ zero TyNat
| Typing_succ :
  forall (Γ : Ctx) (t' : Tm)
    (Ht' : Typing Γ t' TyNat),
    Typing Γ (succ t') TyNat
| Typing_rec :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A : Ty) (l : list Atom)
    (Ht1 : Typing Γ t1 A)
    (Ht2 : forall x : Atom, x # l -> Typing ((x, A) :: Γ) (t2 {{ 0 ~> x }}) A)
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
  apply (WfCtx_app_cons _ [] (fresh l) A), H.
  now solve_fresh'.
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
    apply H; [now solve_fresh' | easy |].
    now cbn; constructor; [| solve_fresh'].
  - apply Typing_elimUnit with (l ++ map fst Γ1 ++ map fst Δ ++ map fst Γ2);
      [now apply IHHt |].
    intros x Hx.
    rewrite app_comm_cons.
    apply H; [now solve_fresh' | easy |].
    now cbn; constructor; [| solve_fresh'].
  - apply Typing_elimProd with A B (l ++ map fst Γ1 ++ map fst Δ ++ map fst Γ2);
      [now apply IHHt |].
    intros x y Hx Hy.
    rewrite 2!app_comm_cons.
    apply H; cbn; [now solve_fresh' | now solve_fresh' | easy |].
    constructor; cbn; [| now solve_fresh'].
    now constructor; [| solve_fresh'].
  - apply Typing_case with A B (l ++ map fst Γ1 ++ map fst Δ ++ map fst Γ2);
      [now apply IHHt | |].
    + intros x Hx.
      rewrite app_comm_cons.
      apply H; [now solve_fresh' | easy |].
      now cbn; constructor; [| solve_fresh'].
    + intros x Hx.
      rewrite app_comm_cons.
      apply H0; [now solve_fresh' | easy |].
      now cbn; constructor; [| solve_fresh'].
  - apply Typing_rec with (l ++ map fst Γ1 ++ map fst Δ ++ map fst Γ2);
      [now apply IHHt1 | | now apply IHHt2].
    intros x Hx.
    rewrite app_comm_cons.
    apply H; [now solve_fresh' | easy |].
    now cbn; constructor; [| solve_fresh'].
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
    intros y [Hxy Hyl]%Fresh_cons.
    rewrite subst_open by eauto.
    now eapply (H y Hyl ((y, A) :: Δ)).
  - apply Typing_elimUnit with (x :: l); [now eapply IHHt |].
    intros y [Hxy Hyl]%Fresh_cons.
    rewrite subst_open; [| now firstorder | now eauto].
    now eapply (H y Hyl ((y, TyUnit) :: Δ)).
  - apply Typing_elimProd with A B (x :: l); [now eapply IHHt |].
    intros y z [Hxy Hyl]%Fresh_cons [Hzy Hzl]%Fresh_cons.
    rewrite subst_open by eauto.
    rewrite subst_open; [| now firstorder | now eauto].
    now eapply (H y z Hyl ltac:(solve_fresh') ((z, B) :: (y, A) :: Δ)).
  - apply Typing_case with A B (x :: l); [now eapply IHHt | |].
    + intros y [Hxy Hyl]%Fresh_cons.
      rewrite subst_open by eauto.
      now eapply (H y Hyl ((y, A) :: Δ)).
    + intros y [Hxy Hyl]%Fresh_cons.
      rewrite subst_open by eauto.
      now eapply (H0 y Hyl ((y, B) :: Δ)).
  - apply Typing_rec with (x :: l); [now eapply IHHt1 | | now eapply IHHt2].
    intros y [Hxy Hyl]%Fresh_cons.
    rewrite subst_open by eauto.
    now eapply (H y Hyl ((y, A) :: Δ)).
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

(** ** CBV *)

(** *** Values *)

Inductive CbvValue : Tm -> Prop :=
| CbvValue_abs  :
  forall (t' : Tm) (l : list Atom)
    (Hlc' : forall x : Atom, x # l -> lc (t' {{ 0 ~> x }})),
    CbvValue (abs t')
| CbvValue_unit : CbvValue unit
| CbvValue_elimUnit'' : CbvValue elimUnit''
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
| CbvValue_case'' : CbvValue case''
| CbvValue_case''1 :
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    CbvValue (app case'' t1)
| CbvValue_case''2 :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvValue (app (app case'' t1) t2)
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

#[export] Hint Resolve lc_CbvValue : core.

Fixpoint cbvValue (t : Tm) : bool :=
match t with
| abs t'               => true
| unit                 => true
| elimUnit''           => true
| abort t'             => true
| pair t1 t2           => cbvValue t1 && cbvValue t2
| inl t'               => cbvValue t'
| inr t'               => cbvValue t'
| case''               => true
| app case'' _         => true
| app (app case'' _) _ => true
| zero                 => true
| succ t'              => cbvValue t'
| _                    => false
end.

#[export, refine] Instance Decidable_CbvValue :
  forall t : Tm, Decidable (CbvValue t) :=
{
  Decidable_witness := cbvValue t;
}.
Proof.
  split.
  - induction t; inversion 1; auto.
    + admit.
    + destruct t1; try easy.
      * destruct t1_1; try easy.
        constructor; admit.
      * constructor; admit.
    + constructor. admit.
    + apply andb_prop in H1 as [H1 H2].
Abort.

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
| CbvContraction_elimUnit_nit :
  forall (t : Tm) (l : list Atom)
    (Hlc : forall x : Atom, x # l -> lc (t {{0 ~> x}})),
    CbvContraction (elimUnit unit t) (t {[ 0 ~> unit ]})
| CbvContraction_elimUnit'_unit :
  forall (t : Tm)
    (Hlc : lc t),
    CbvContraction (elimUnit' unit t) (app t unit)
| CbvContraction_app_elimUnit'' :
  forall (t : Tm)
    (Hlc : lc t),
    CbvContraction (app elimUnit'' t) t
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
  forall (v1 v2 t : Tm) (l : list Atom)
    (Hv1 : CbvValue v1)
    (Hv2 : CbvValue v2)
    (Hlc3 : forall x y : Atom, x # l -> y # x :: l -> lc (t {{ 0 ~> x }} {{ 1 ~> y }})),
    CbvContraction (elimProd (pair v1 v2) t) (t {[ 0 ~> v1 ]} {[ 1 ~> v2 ]})
| CbvContraction_case_inl :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hv1 : CbvValue t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{ 0 ~> x }})),
    CbvContraction (case (inl t1) t2 t3) (t2 {[ 0 ~> t1 ]})
| CbvContraction_case_inr :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hv1 : CbvValue t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{ 0 ~> x }})),
    CbvContraction (case (inr t1) t2 t3) (t3 {[ 0 ~> t1 ]})
| CbvContraction_case'_inl :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv3 : CbvValue t3),
    CbvContraction (case' t1 t2 (inl t3)) (app t1 t3)
| CbvContraction_case'_inr :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv3 : CbvValue t3),
    CbvContraction (case' t1 t2 (inr t3)) (app t2 t3)
| CbvContraction_case''_inl :
  forall (t1 t2 v : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv : CbvValue v),
    CbvContraction (app (app (app case'' t1) t2) (inl v)) (app t1 v)
| CbvContraction_case''_inr :
  forall (t1 t2 v : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv : CbvValue v),
    CbvContraction (app (app (app case'' t1) t2) (inr v)) (app t2 v)
| CbvContraction_rec_zero :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }})),
    CbvContraction (rec t1 t2 zero) t1
| CbvContraction_rec_succ :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hv1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hv3 : CbvValue t3),
    CbvContraction (rec t1 t2 (succ t3)) (t2 {[ 0 ~> rec t1 t2 t3 ]}).

#[export] Hint Constructors CbvContraction : core.

Lemma lc_CbvContraction_l :
  forall t t' : Tm,
    CbvContraction t t' -> lc t.
Proof.
  now inversion 1; subst; eauto 6.
Qed.

Lemma lc_CbvContraction_r :
  forall t t' : Tm,
    CbvContraction t t' -> lc t'.
Proof.
  inversion 1; subst; try now eauto 6.
  pose (x := fresh (l ++ fv t0)).
  pose (y := fresh ([x] ++ l ++ fv (t0 {[ 0 ~> v1 ]}))).
  rewrite (open'_spec _ _ y) by (subst y; solve_fresh').
  apply lc_subst; [| now eauto].
  rewrite (open'_spec _ _ x) by (subst x; solve_fresh').
  rewrite subst_open; [| | now eauto].
  - apply lc_subst; [| now eauto].
    apply Hlc3; subst x y; [now solve_fresh' |].
    now rewrite app_assoc; solve_fresh'.
  - pose (fresh_spec ([x] ++ l ++ fv (t0 {[ 0 ~> v1 ]}))).
    now firstorder.
Qed.

#[export] Hint Resolve lc_CbvContraction_l lc_CbvContraction_r : core.

Lemma CbvContraction_det :
  forall t t1 t2 : Tm,
    CbvContraction t t1 -> CbvContraction t t2 -> t1 = t2.
Proof.
  now induction 1;inversion 1; eauto.
Qed.

Lemma CbvContraction_not_CbvValue :
  forall t t' : Tm,
    CbvContraction t t' -> CbvValue t -> False.
Proof.
  now do 2 inversion 1.
Qed.

#[export] Hint Resolve CbvContraction_det CbvContraction_not_CbvValue : core.

Lemma preservation_CbvContraction :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    CbvContraction t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  induction 1; inversion 1; subst.
  - inversion Ht1; subst.
    rewrite open'_spec with (x := fresh (l0 ++ fv t1)) by solve_fresh'.
    apply Typing_subst with A0; [| easy].
    apply Ht'.
    now solve_fresh'.
  - easy.
  - rewrite open'_spec with (x := fresh (l0 ++ fv t)) by solve_fresh'.
    apply Typing_subst with TyUnit; [| easy].
    apply Ht2.
    now solve_fresh'.
  - now apply Typing_app with TyUnit.
  - now inversion Ht1; subst.
  - now inversion Ht'.
  - now inversion Ht'.
  - inversion Ht1; subst.
    pose (x := fresh (l0 ++ l ++ fv v2 ++ fv t ++ map fst Γ)).
    assert (Hx := fresh_spec (l0 ++ l ++ fv v2 ++ fv t ++ map fst Γ)).
    pose (y := fresh ([x] ++ l0 ++ l ++ fv v1 ++ fv (t {{ 0 ~> x }} [[ x := v1 ]]))).
    assert (Hy := fresh_spec ([x] ++ l0 ++ l ++ fv v1 ++ fv (t {{ 0 ~> x }} [[ x := v1 ]]))).
    assert (Hxy : x <> y) by firstorder.
    rewrite (open'_spec _ 0 x) by (subst x; solve_fresh').
    rewrite (open'_spec _ 1 y) by (subst y; solve_fresh').
    rewrite subst_open by eauto.
    rewrite subst_subst by (now subst x y; solve_fresh').
    apply Typing_subst with A0; [| easy].
    apply Typing_subst with B.
    + apply Ht2; [now subst x; solve_fresh' | now subst y; solve_fresh'].
    + apply (weakening _ [(x, A0)]); [| easy].
      constructor; [now eauto |].
      now subst x; solve_fresh'.
  - inversion Ht1; subst.
    rewrite open'_spec with (x := fresh (l0 ++ fv t2)) by solve_fresh'.
    apply Typing_subst with A0; [| easy].
    apply Ht2.
    now solve_fresh'.
  - inversion Ht1; subst.
    rewrite open'_spec with (x := fresh (l0 ++ fv t3)) by solve_fresh'.
    apply Typing_subst with B; [| easy].
    apply Ht3.
    now solve_fresh'.
  - now inversion Ht3; eauto.
  - now inversion Ht3; eauto.
  - now inversion Ht1; inversion Ht2; inversion Ht0; inversion Ht4; subst;
      inversion H15; subst; eauto.
  - now inversion Ht1; inversion Ht2; inversion Ht0; inversion Ht4; subst;
      inversion H15; subst; eauto.
  - easy.
  - inversion Ht3; subst.
    rewrite open'_spec with (x := fresh (l0 ++ fv t2)) by solve_fresh'.
    eapply Typing_subst with A; [| now eauto].
    apply Ht2.
    now solve_fresh'.
Qed.

(*** *** Abortion *)

Inductive CbvAbortion : Tm -> Tm -> Prop :=
| CbvAbortion_app :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvAbortion (app (abort t1) t2) (abort t1)
| CbvAbortion_elimUnit :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{0 ~> x}})),
    CbvAbortion (elimUnit (abort t1) t2) (abort t1)
| CbvAbortion_elimUnit' :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvAbortion (elimUnit' (abort t1) t2) (abort t1)
| CbvAbortion_outl :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbvAbortion (outl (abort t)) (abort t)
| CbvAbortion_outr :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbvAbortion (outr (abort t)) (abort t)
| CbvAbortion_elimProd :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x y : Atom, x # l -> y # x :: l -> lc (t2 {{ 0 ~> x }} {{ 1 ~> y }})),
    CbvAbortion (elimProd (abort t1) t2) (abort t1)
| CbvAbortion_case :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{0 ~> x}}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{0 ~> x}})),
    CbvAbortion (case (abort t1) t2 t3) (abort t1)
| CbvAbortion_case' :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbvAbortion (case' t1 t2 (abort t3)) (abort t3)
| CbvAbortion_case'' :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbvAbortion (app (app (app case'' t1) t2) (abort t3)) (abort t3)
| CbvAbortion_rec :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : lc t3),
    CbvAbortion (rec t1 t2 (abort t3)) (abort t3).

#[export] Hint Constructors CbvAbortion : core.

Lemma lc_CbvAbortion_l :
  forall t t' : Tm,
    CbvAbortion t t' -> lc t.
Proof.
  now inversion 1; subst; auto; eauto.
Qed.

Lemma lc_CbvAbortion_r :
  forall t t' : Tm,
    CbvAbortion t t' -> lc t'.
Proof.
  now inversion 1; subst; eauto.
Qed.

#[export] Hint Resolve lc_CbvAbortion_l lc_CbvAbortion_r : core.

Lemma CbvAbortion_det :
  forall t t1 t2 : Tm,
    CbvAbortion t t1 -> CbvAbortion t t2 -> t1 = t2.
Proof.
  now induction 1; inversion 1; subst; auto.
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
  now induction 1; inversion 1; subst; constructor;
    match goal with
    | H : Typing _ (abort _) _ |- _ => inversion H
    end.
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
  forall (t1 t1' t2 : Tm) (l : list Atom)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }})),
    CbvStep t1 t1' ->
    CbvStep (elimUnit t1 t2) (elimUnit t1' t2)
| CbvStep_elimUnit' :
  forall (t1 t1' t2 : Tm)
    (Hlc2 : lc t2),
    CbvStep t1 t1' ->
    CbvStep (elimUnit' t1 t2) (elimUnit' t1' t2)
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
  forall (t1 t1' t2 : Tm) (l : list Atom)
    (Hs1 : CbvStep t1 t1')
    (Hlc2 : forall x y : Atom, x # l -> y # x :: l -> lc (t2 {{ 0 ~> x }} {{ 1 ~> y }})),
    CbvStep (elimProd t1 t2) (elimProd t1' t2)
| CbvStep_inl :
  forall t t' : Tm,
    CbvStep t t' ->
    CbvStep (inl t) (inl t')
| CbvStep_inr :
  forall t t' : Tm,
    CbvStep t t' ->
    CbvStep (inr t) (inr t')
| CbvStep_case :
  forall (t1 t1' t2 t3 : Tm) (l : list Atom)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{ 0 ~> x }})),
    CbvStep t1 t1' ->
    CbvStep (case t1 t2 t3) (case t1' t2 t3)
| CbvStep_case' :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : CbvStep t3 t3'),
    CbvStep (case' t1 t2 t3) (case' t1 t2 t3')
| CbvStep_case'' :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : CbvStep t3 t3'),
    CbvStep (app (app (app case'' t1) t2) t3) (app (app (app case'' t1) t2) t3')
| CbvStep_succ :
  forall (t t' : Tm),
    CbvStep t t' ->
    CbvStep (succ t) (succ t')
| CbvStep_rec2 :
  forall (t1 t2 t3 t3' : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hs3 : CbvStep t3 t3'),
    CbvStep (rec t1 t2 t3) (rec t1 t2 t3').

#[export] Hint Constructors CbvStep : core.

Lemma lc_CbvStep_l :
  forall t t' : Tm,
    CbvStep t t' -> lc t.
Proof.
  now induction 1; auto; eauto.
Qed.

Lemma lc_CbvStep_r :
  forall t t' : Tm,
    CbvStep t t' -> lc t'.
Proof.
  now induction 1; auto; eauto.
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

#[export] Hint Resolve lc_CbvStep_l lc_CbvStep_r CbvStep_not_CbvValue : core.

Lemma CbvContraction_CbvStep_det :
  forall t t1 t2 : Tm,
    CbvContraction t t1 -> CbvStep t t2 -> t1 = t2.
Proof.
  inversion 2; subst; intros; [| |
    match goal with
    | Hs : CbvStep ?t ?t' |- _ =>
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
    | Hs : CbvStep ?t ?t' |- _ =>
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
  induction Hs1; intros; inversion Hs2; subst;
    try match goal with
    | H : CbvContraction _ _ |- _ =>
      now eapply CbvContraction_CbvStep_det in H; eauto
    | H : CbvAbortion _ _ |- _ =>
      now eapply CbvAbortion_CbvStep_det in H; eauto
    end; try firstorder congruence.
  - now inversion Hs1.
  - now apply CbvStep_not_CbvValue in Hs1; auto.
  - now inversion H3.
  - now apply CbvStep_not_CbvValue in Hs1.
  - now apply CbvStep_not_CbvValue in H4.
  - now apply CbvStep_not_CbvValue in H3; auto.
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
  - now right; eauto.
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
    inversion Hv; subst; inversion Ht; subst; [now eauto.. | |].
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    inversion Hv; subst; inversion Ht; subst; [now eauto.. | |].
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto 6].
    inversion Hv; subst; inversion Ht; subst; [now eauto 6.. | |].
    + now inversion Ht1.
    + now inversion Ht1.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto 7].
    inversion Hv; subst; inversion Ht; subst; [now eexists; do 2 econstructor; eauto.. | |].
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt3 eq_refl) as [Hv3 | [] ]; [| now eauto].
    inversion Hv3; subst; inversion Ht3; subst; [now eauto 6.. | |].
    + now inversion Ht0.
    + now inversion Ht0.
  - now left.
  - now left.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt2 eq_refl) as [Hv1 | [t1' Hs1] ]; [| now eauto 6].
    inversion Hv1; subst; inversion Ht3; subst; [now eauto 7 | | | now eauto 7..].
    + now inversion Ht0.
    + now inversion Ht0.
Qed.

(** ** CBN *)

(** *** Values *)

Inductive CbnValue : Tm -> Prop :=
| CbnValue_abs  :
  forall (t' : Tm) (l : list Atom)
    (Hlc' : forall x : Atom, x # l -> lc (t' {{ 0 ~> x }})),
    CbnValue (abs t')
| CbnValue_unit : CbnValue unit
| CbnValue_elimUnit'' : CbnValue elimUnit''
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
| CbnValue_case'' : CbnValue case''
| CbnValue_case''1 :
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    CbnValue (app case'' t1)
| CbnValue_case''2 :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnValue (app (app case'' t1) t2)
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

#[export] Hint Resolve lc_CbnValue : core.

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
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{0 ~> x}})),
    CbnContraction (elimUnit t1 t2) (t2 {[ 0 ~> unit ]})
| CbnContraction_elimUnit' :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction (elimUnit' t1 t2) (app t2 unit)
| CbnContraction_app_elimUnit'' :
  forall (t : Tm)
    (Hlc : lc t),
    CbnContraction (app elimUnit'' t) t
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
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : forall x y : Atom, x # l -> y # x :: l -> lc (t3 {{ 0 ~> x }} {{ 1 ~> y }})),
    CbnContraction (elimProd (pair t1 t2) t3) (t3 {[ 0 ~> t1 ]} {[ 1 ~> t2 ]})
| CbnContraction_case_inl :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{ 0 ~> x }})),
    CbnContraction (case (inl t1) t2 t3) (t2 {[ 0 ~> t1 ]})
| CbnContraction_case_inr :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{ 0 ~> x }})),
    CbnContraction (case (inr t1) t2 t3) (t3 {[ 0 ~> t1 ]})
| CbnContraction_case'_inl :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (case' t1 t2 (inl t3)) (app t1 t3)
| CbnContraction_case'_inr :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (case' t1 t2 (inr t3)) (app t2 t3)
| CbnContraction_case''_inl :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (app (app (app case'' t1) t2) (inl t3)) (app t1 t3)
| CbnContraction_case''_inr :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (app (app (app case'' t1) t2) (inr t3)) (app t2 t3)
| CbnContraction_rec_zero :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }})),
    CbnContraction (rec t1 t2 zero) t1
| CbnContraction_rec_succ :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : lc t3),
    CbnContraction (rec t1 t2 (succ t3)) (t2 {[ 0 ~> rec t1 t2 t3 ]}).

#[export] Hint Constructors CbnContraction : core.

Lemma lc_CbnContraction_l :
  forall t t' : Tm,
    CbnContraction t t' -> lc t.
Proof.
  now inversion 1; subst; econstructor; eauto.
Qed.

Lemma lc_CbnContraction_r :
  forall t t' : Tm,
    CbnContraction t t' -> lc t'.
Proof.
  inversion 1; subst; try (now auto); try (now apply lc_open'; eauto).
  pose (x := fresh (l ++ fv t3)).
  pose (y := fresh ([x] ++ l ++ fv (t3 {[ 0 ~> t1 ]}))).
  rewrite (open'_spec _ _ y) by (subst y; solve_fresh').
  apply lc_subst; [| now eauto].
  rewrite (open'_spec _ _ x) by (subst x; solve_fresh').
  rewrite subst_open; [| | now eauto].
  - apply lc_subst; [| now eauto].
    apply Hlc3; subst x y; [now solve_fresh' |].
    now rewrite app_assoc; solve_fresh'.
  - pose (fresh_spec ([x] ++ l ++ fv (t3 {[ 0 ~> t1 ]}))).
    now firstorder.
Qed.

#[export] Hint Resolve lc_CbnContraction_l lc_CbnContraction_r : core.

Lemma CbnContraction_det :
  forall t t1 t2 : Tm,
    CbnContraction t t1 -> CbnContraction t t2 -> t1 = t2.
Proof.
  now induction 1; inversion 1; eauto.
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
  induction 1; inversion 1; subst.
  - inversion Ht1; subst.
    rewrite open'_spec with (x := fresh (l0 ++ fv t1)) by solve_fresh'.
    apply Typing_subst with A0; [| easy].
    apply Ht'.
    now solve_fresh'.
  - easy.
  - rewrite open'_spec with (x := fresh (l0 ++ fv t2)) by solve_fresh'.
    apply Typing_subst with TyUnit; [| now eauto].
    apply Ht2.
    now solve_fresh'.
  - now apply Typing_app with TyUnit; eauto.
  - now inversion Ht1; subst.
  - now inversion Ht'.
  - now inversion Ht'.
  - inversion Ht1; subst.
    pose (x := fresh (l0 ++ l ++ fv t2 ++ fv t3 ++ map fst Γ)).
    assert (Hx := fresh_spec (l0 ++ l ++ fv t2 ++ fv t3 ++ map fst Γ)).
    pose (y := fresh ([x] ++ l0 ++ l ++ fv t1 ++ fv (t3 {{ 0 ~> x }} [[ x := t1 ]]))).
    assert (Hy := fresh_spec ([x] ++ l0 ++ l ++ fv t1 ++ fv (t3 {{ 0 ~> x }} [[ x := t1 ]]))).
    assert (Hxy : x <> y) by firstorder.
    rewrite (open'_spec _ 0 x) by (subst x; solve_fresh').
    rewrite (open'_spec _ 1 y) by (subst y; solve_fresh').
    rewrite subst_open by eauto.
    rewrite subst_subst by (now subst x y; solve_fresh').
    apply Typing_subst with A0; [| easy].
    apply Typing_subst with B.
    + apply Ht2; [now subst x; solve_fresh' | now subst y; solve_fresh'].
    + apply (weakening _ [(x, A0)]); [| easy].
      constructor; [now eauto |].
      now subst x; solve_fresh'.
  - inversion Ht1; subst.
    rewrite open'_spec with (x := fresh (l0 ++ fv t2)) by solve_fresh'.
    apply Typing_subst with A0; [| easy].
    apply Ht2.
    now solve_fresh'.
  - inversion Ht1; subst.
    rewrite open'_spec with (x := fresh (l0 ++ fv t3)) by solve_fresh'.
    apply Typing_subst with B; [| easy].
    apply Ht3.
    now solve_fresh'.
  - now inversion Ht3; eauto.
  - now inversion Ht3; eauto.
  - now inversion Ht1; inversion Ht2; inversion Ht0; inversion Ht4; subst;
      inversion H15; subst; eauto.
  - now inversion Ht1; inversion Ht2; inversion Ht0; inversion Ht4; subst;
      inversion H15; subst; eauto.
  - easy.
  - inversion Ht3; subst.
    rewrite open'_spec with (x := fresh (l0 ++ fv t2)) by solve_fresh'.
    eapply Typing_subst with A; [| now eauto].
    apply Ht2.
    now solve_fresh'.
Qed.

(*** *** Abortion *)

Inductive CbnAbortion : Tm -> Tm -> Prop :=
| CbnAbortion_app :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnAbortion (app (abort t1) t2) (abort t1)
| CbnAbortion_outl :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbnAbortion (outl (abort t)) (abort t)
| CbnAbortion_outr :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbnAbortion (outr (abort t)) (abort t)
| CbnAbortion_elimProd :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x y : Atom, x # l -> y # x :: l -> lc (t2 {{ 0 ~> x }} {{ 1 ~> y }})),
    CbnAbortion (elimProd (abort t1) t2) (abort t1)
| CbnAbortion_case :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{0 ~> x}}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{0 ~> x}})),
    CbnAbortion (case (abort t1) t2 t3) (abort t1)
| CbnAbortion_case' :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnAbortion (case' t1 t2 (abort t3)) (abort t3)
| CbnAbortion_case'' :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnAbortion (app (app (app case'' t1) t2) (abort t3)) (abort t3)
| CbnAbortion_rec :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : lc t3),
    CbnAbortion (rec t1 t2 (abort t3)) (abort t3).

#[export] Hint Constructors CbnAbortion : core.

Lemma lc_CbnAbortion_l :
  forall t t' : Tm,
    CbnAbortion t t' -> lc t.
Proof.
  now inversion 1; subst; auto; eauto.
Qed.

Lemma lc_CbnAbortion_r :
  forall t t' : Tm,
    CbnAbortion t t' -> lc t'.
Proof.
  now inversion 1; subst; eauto.
Qed.

#[export] Hint Resolve lc_CbnAbortion_l lc_CbnAbortion_r : core.

Lemma CbnAbortion_det :
  forall t t1 t2 : Tm,
    CbnAbortion t t1 -> CbnAbortion t t2 -> t1 = t2.
Proof.
  now induction 1; inversion 1; subst; auto.
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
  now induction 1; inversion 1; subst; constructor;
    match goal with
    | H : Typing _ (abort _) _ |- _ => inversion H
    end.
Qed.

(** ** Reduction *)

Inductive CbnStep : Tm -> Tm -> Prop :=
| CbnStep_CbnContraction :
  forall t t' : Tm,
    CbnContraction t t' ->
    CbnStep t t'
| CbnStep_CbvAbortion :
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
  forall (t1 t1' t2 : Tm) (l : list Atom)
    (Hs1 : CbnStep t1 t1')
    (Hlc2 : forall x y : Atom, x # l -> y # x :: l -> lc (t2 {{ 0 ~> x }} {{ 1 ~> y }})),
    CbnStep (elimProd t1 t2) (elimProd t1' t2)
| CbnStep_case :
  forall (t1 t1' t2 t3 : Tm) (l : list Atom)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{ 0 ~> x }})),
    CbnStep t1 t1' ->
    CbnStep (case t1 t2 t3) (case t1' t2 t3)
| CbnStep_case' :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : CbnStep t3 t3'),
    CbnStep (case' t1 t2 t3) (case' t1 t2 t3')
| CbnStep_case'' :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : CbnStep t3 t3'),
    CbnStep (app (app (app case'' t1) t2) t3) (app (app (app case'' t1) t2) t3')
| CbnStep_rec :
  forall (t1 t2 t3 t3' : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hs3 : CbnStep t3 t3'),
    CbnStep (rec t1 t2 t3) (rec t1 t2 t3').

#[export] Hint Constructors CbnStep : core.

Lemma lc_CbnStep_l :
  forall t t' : Tm,
    CbnStep t t' -> lc t.
Proof.
  now induction 1; auto; eauto.
Qed.

Lemma lc_CbnStep_r :
  forall t t' : Tm,
    CbnStep t t' -> lc t'.
Proof.
  now induction 1; auto; eauto.
Qed.

Lemma CbnStep_not_CbnValue :
  forall t t' : Tm,
    CbnStep t t' -> CbnValue t -> False.
Proof.
  induction 1; intros Hv; [| | inversion Hv; subst; auto..].
  - now eapply CbnContraction_not_CbnValue; eauto.
  - now eapply CbnAbortion_not_CbnValue; eauto.
Qed.

#[export] Hint Resolve lc_CbnStep_l lc_CbnStep_r CbnStep_not_CbnValue : core.

Lemma CbnContraction_CbnStep_det :
  forall t t1 t2 : Tm,
    CbnContraction t t1 -> CbnStep t t2 -> t1 = t2.
Proof.
  inversion 2; subst; intros; [| |
    match goal with
    | Hs : CbnStep ?t ?t' |- _ =>
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
    | Hs : CbnStep ?t ?t' |- _ =>
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
  induction Hs1; intros; inversion Hs2; subst;
    try match goal with
    | H : CbnContraction _ _ |- _ =>
      now eapply CbnContraction_CbnStep_det in H; eauto
    | H : CbnAbortion _ _ |- _ =>
      now eapply CbnAbortion_CbnStep_det in H; eauto
    end; try firstorder congruence.
  - now apply CbnStep_not_CbnValue in Hs1; auto.
  - now apply CbnStep_not_CbnValue in H3; auto.
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
  induction Ht; subst.
  - now inversion Hwf.
  - now left; eauto.
  - destruct (IHHt1 eq_refl) as [ Hv | [t1' Hs1] ]; [| now eauto].
    inversion Hv; subst; inversion Ht1; subst; try now eauto 6.
    destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; [| now eauto].
    inversion Ht0; inversion Ht4; subst.
    inversion Ht2; subst; inversion Hv2; subst; eauto.
    * inversion Ht2; subst; inversion Ht6.
    * inversion Ht2; subst; inversion Ht6; subst; inversion Ht10.
  - now right; eauto.
  - now left.
  - now right; eauto 7.
  - now right; eauto 7.
  - now left.
  - now left; eauto.
  - now destruct (IHHt1 eq_refl) as [| [] ], (IHHt2 eq_refl) as [| [] ]; eauto.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    inversion Hv; subst; inversion Ht; subst; [now eauto.. | |].
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    inversion Hv; subst; inversion Ht; subst; [now eauto.. | |].
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto 6].
    inversion Hv; subst; inversion Ht; subst; [now eauto 6.. | |].
    + now inversion Ht1.
    + now inversion Ht1.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ].
    + inversion Hv; subst; inversion Ht; subst; [now eexists; do 2 econstructor; eauto.. | |].
      * now inversion Ht1.
      * now inversion Ht1.
    + now eexists; eapply CbnStep_case; eauto.
  - right; destruct (IHHt3 eq_refl) as [Hv3 | [] ]; [| now eauto].
    inversion Hv3; subst; inversion Ht3; subst; [now eauto 6.. | |].
    + now inversion Ht0.
    + now inversion Ht0.
  - now left.
  - now left.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt2 eq_refl) as [Hv1 | [t1' Hs1] ].
    + inversion Hv1; subst; inversion Ht3; subst; [now eauto 7 | | | now eauto 7..].
      * now inversion Ht0.
      * now inversion Ht0.
    + eexists; eapply CbnStep_rec; eauto.
Qed.

(** ** Confluence *)

(** *** Contraction *)

Inductive FullContraction : Tm -> Tm -> Prop :=
| FullContraction_app_abs :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : forall x : Atom, x # l -> lc (t1 {{ 0 ~> x }}))
    (Hlc2 : lc t2),
    FullContraction (app (abs t1) t2) (t1 {[ 0 ~> t2 ]}).
(*
| FullContraction_annot :
  forall (t : Tm) (A : Ty)
    (Hlc : lc t),
    FullContraction (annot t A) t
| FullContraction_elimUnit :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{0 ~> x}})),
    FullContraction (elimUnit t1 t2) (t2 {[ 0 ~> unit ]})
| FullContraction_elimUnit' :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    FullContraction (elimUnit' t1 t2) (app t2 unit)
| FullContraction_app_elimUnit'' :
  forall (t : Tm)
    (Hlc : lc t),
    FullContraction (app elimUnit'' t) t
| FullContraction_outl_pair :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    FullContraction (outl (pair t1 t2)) t1
| FullContraction_outr_pair :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    FullContraction (outr (pair t1 t2)) t2
| FullContraction_elimProd_pair :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : forall x y : Atom, x # l -> y # x :: l -> lc (t3 {{ 0 ~> x }} {{ 1 ~> y }})),
    FullContraction (elimProd (pair t1 t2) t3) (t3 {[ 0 ~> t1 ]} {[ 1 ~> t2 ]})
| FullContraction_case_inl :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{ 0 ~> x }})),
    FullContraction (case (inl t1) t2 t3) (t2 {[ 0 ~> t1 ]})
| FullContraction_case_inr :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{ 0 ~> x }})),
    FullContraction (case (inr t1) t2 t3) (t3 {[ 0 ~> t1 ]})
| FullContraction_case'_inl :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    FullContraction (case' t1 t2 (inl t3)) (app t1 t3)
| FullContraction_case'_inr :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    FullContraction (case' t1 t2 (inr t3)) (app t2 t3)
| FullContraction_case''_inl :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    FullContraction (app (app (app case'' t1) t2) (inl t3)) (app t1 t3)
| FullContraction_case''_inr :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    FullContraction (app (app (app case'' t1) t2) (inr t3)) (app t2 t3)
| FullContraction_rec_zero :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }})),
    FullContraction (rec t1 t2 zero) t1
| FullContraction_rec_succ :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : lc t3),
    FullContraction (rec t1 t2 (succ t3)) (t2 {[ 0 ~> rec t1 t2 t3 ]}).
*)

#[export] Hint Constructors FullContraction : core.

Lemma lc_FullContraction_l :
  forall t t' : Tm,
    FullContraction t t' -> lc t.
Proof.
  now inversion 1; subst; econstructor; eauto.
Qed.

Lemma lc_FullContraction_r :
  forall t t' : Tm,
    FullContraction t t' -> lc t'.
Proof.
  inversion 1; subst; try (now auto); try (now apply lc_open'; eauto).
(*
  pose (x := fresh (l ++ fv t3)).
  pose (y := fresh ([x] ++ l ++ fv (t3 {[ 0 ~> t1 ]}))).
  rewrite (open'_spec _ _ y) by (subst y; solve_fresh').
  apply lc_subst; [| now eauto].
  rewrite (open'_spec _ _ x) by (subst x; solve_fresh').
  rewrite subst_open; [| | now eauto].
  - apply lc_subst; [| now eauto].
    apply Hlc3; subst x y; [now solve_fresh' |].
    now rewrite app_assoc; solve_fresh'.
  - pose (fresh_spec ([x] ++ l ++ fv (t3 {[ 0 ~> t1 ]}))).
    now firstorder.
*)
Qed.

#[export] Hint Resolve lc_FullContraction_l lc_FullContraction_r : core.

Lemma FullContraction_det :
  forall t t1 t2 : Tm,
    FullContraction t t1 -> FullContraction t t2 -> t1 = t2.
Proof.
  now induction 1; inversion 1; eauto.
Qed.

Inductive FullStep : Tm -> Tm -> Prop :=
| FullStep_FullContraction :
  forall t t' : Tm,
    FullContraction t t' ->
    FullStep t t'
(*| FullStep_Abortion :
  forall t t' : Tm,
    FullAbortion t t' ->
    FullStep t t'*)
| FullStep_abs :
  forall (t t' : Tm),
    FullStep t t' ->
    FullStep (abs t) (abs t')
| FullStep_app_l :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    FullStep t1 t1' ->
    FullStep (app t1 t2) (app t1' t2)
| FullStep_app_r :
  forall (t1 t1 t2 t2' : Tm),
    lc t1 ->
    FullStep t2 t2' ->
    FullStep (app t1 t2) (app t1 t2').
(*
| FullStep_outl :
  forall (t t' : Tm),
    FullStep t t' ->
    FullStep (outl t) (outl t')
| FullStep_outr :
  forall (t t' : Tm),
    FullStep t t' ->
    FullStep (outr t) (outr t')
| FullStep_elimProd :
  forall (t1 t1' t2 : Tm) (l : list Atom)
    (Hs1 : FullStep t1 t1')
    (Hlc2 : forall x y : Atom, x # l -> y # x :: l -> lc (t2 {{ 0 ~> x }} {{ 1 ~> y }})),
    FullStep (elimProd t1 t2) (elimProd t1' t2)
| FullStep_case :
  forall (t1 t1' t2 t3 : Tm) (l : list Atom)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{ 0 ~> x }})),
    FullStep t1 t1' ->
    FullStep (case t1 t2 t3) (case t1' t2 t3)
| FullStep_case' :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : FullStep t3 t3'),
    FullStep (case' t1 t2 t3) (case' t1 t2 t3')
| FullStep_case'' :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : FullStep t3 t3'),
    FullStep (app (app (app case'' t1) t2) t3) (app (app (app case'' t1) t2) t3')
| FullStep_rec :
  forall (t1 t2 t3 t3' : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hs3 : FullStep t3 t3'),
    FullStep (rec t1 t2 t3) (rec t1 t2 t3').
*)

#[export] Hint Constructors FullStep : core.

Lemma lc_FullStep_l :
  forall t t' : Tm,
    FullStep t t' -> lc t.
Proof.
  induction 1; only 1, 3-4: now eauto.
  apply lc_abs with []; intros x _.
  now rewrite open_lc.
Qed.

Lemma lc_FullStep_r :
  forall t t' : Tm,
    FullStep t t' -> lc t'.
Proof.
  induction 1; only 1, 3-4: now eauto.
  apply lc_abs with []; intros x _.
  now rewrite open_lc.
Qed.

#[export] Hint Resolve lc_FullStep_l lc_FullStep_r : core.

Require Import Coq.Relations.Relation_Operators.

Definition MultiStep : Tm -> Tm -> Prop :=
  clos_refl_trans _ FullStep.

#[export] Hint Unfold MultiStep : core.

Lemma lc_MultiStep_l :
  forall t t' : Tm,
    MultiStep t t' -> lc t.
Proof.
  induction 1. eauto. admit. eauto.
Admitted.

Lemma lc_MultiStep_r :
  forall t t' : Tm,
    MultiStep t t' -> lc t'.
Proof.
  induction 1. eauto. admit. eauto.
Admitted.

Lemma MultiStep_abs :
  forall t t' : Tm,
    MultiStep t t' -> MultiStep (abs t) (abs t').
Proof.
  induction 1.
  - now constructor; eauto.
  - now constructor 2.
  - now apply rt_trans with (abs y); eauto.
Qed.

Lemma MultiStep_app_l :
  forall t1 t1' t2 : Tm,
    lc t2 ->
    MultiStep t1 t1' ->
    MultiStep (app t1 t2) (app t1' t2).
Proof.
  induction 2.
  - now constructor; eauto.
  - now constructor 2.
  - now apply rt_trans with (app y t2); eauto.
Qed.

Lemma MultiStep_app_r :
  forall t1 t2 t2' : Tm,
    lc t1 ->
    MultiStep t2 t2' ->
    MultiStep (app t1 t2) (app t1 t2').
Proof.
  induction 2.
  - now constructor; eauto.
  - now constructor 2.
  - now apply rt_trans with (app t1 y); eauto.
Qed.

#[export] Hint Resolve MultiStep_abs MultiStep_app_l MultiStep_app_r : core.

Inductive ParallelStep : Tm -> Tm -> Prop :=
| ParallelStep_refl :
  forall (t : Tm)
    (Hlc' : lc t),
    ParallelStep t t
| ParallelStep_FullContraction :
  forall (t t' : Tm),
    FullContraction t t' ->
    ParallelStep t t'
(*| ParallelStep_Abortion :
  forall t t' : Tm,
    Abortion t t' ->
    ParallelStep t t'*)
| ParallelStep_abs :
  forall (t1 t2 : Tm),
    ParallelStep t1 t2 ->
    ParallelStep (abs t1) (abs t2)
| ParallelStep_app :
  forall (t1 t1' t2 t2' : Tm),
    ParallelStep t1 t1' ->
    ParallelStep t2 t2' ->
    ParallelStep (app t1 t2) (app t1' t2').
(*
| ParallelStep_elimUnit :
  forall (t1 t1' t2 : Tm) (l : list Atom)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }})),
    ParallelStep t1 t1' ->
    ParallelStep (elimUnit t1 t2) (elimUnit t1' t2)
| ParallelStep_elimUnit' :
  forall (t1 t1' t2 : Tm)
    (Hlc2 : lc t2),
    ParallelStep t1 t1' ->
    ParallelStep (elimUnit' t1 t2) (elimUnit' t1' t2)
| ParallelStep_pair :
  forall (t1 t1' t2 t2' : Tm),
    ParallelStep t1 t1' ->
    ParallelStep t2 t2' ->
    ParallelStep (pair t1 t2) (pair t1' t2')
| ParallelStep_outl :
  forall (t t' : Tm),
    ParallelStep t t' ->
    ParallelStep (outl t) (outl t')
| ParallelStep_outr :
  forall (t t' : Tm),
    ParallelStep t t' ->
    ParallelStep (outr t) (outr t')
| ParallelStep_elimProd :
  forall (t1 t1' t2 : Tm) (l : list Atom)
    (Hs1 : ParallelStep t1 t1')
    (Hlc2 : forall x y : Atom, x # l -> y # x :: l -> lc (t2 {{ 0 ~> x }} {{ 1 ~> y }})),
    ParallelStep (elimProd t1 t2) (elimProd t1' t2)
| ParallelStep_inl :
  forall t t' : Tm,
    ParallelStep t t' ->
    ParallelStep (inl t) (inl t')
| ParallelStep_inr :
  forall t t' : Tm,
    ParallelStep t t' ->
    ParallelStep (inr t) (inr t')
| ParallelStep_case :
  forall (t1 t1' t2 t3 : Tm) (l : list Atom)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{ 0 ~> x }})),
    ParallelStep t1 t1' ->
    ParallelStep (case t1 t2 t3) (case t1' t2 t3)
| ParallelStep_case' :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : ParallelStep t3 t3'),
    ParallelStep (case' t1 t2 t3) (case' t1 t2 t3')
| ParallelStep_succ :
  forall (t t' : Tm),
    ParallelStep t t' ->
    ParallelStep (succ t) (succ t')
| ParallelStep_rec :
  forall (t1 t1' t2 t3 t3' : Tm) (l : list Atom)
    (Hs1 : ParallelStep t1 t1')
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hs3 : ParallelStep t3 t3'),
    ParallelStep (rec t1 t2 t3) (rec t1' t2 t3').
*)

#[export] Hint Constructors ParallelStep : core.

Lemma lc_ParallelStep_l :
  forall t t' : Tm,
    ParallelStep t t' -> lc t.
Proof.
  induction 1; auto; [now eauto |].
  now apply lc_abs with []; auto.
Qed.

Lemma lc_ParallelStep_r :
  forall t t' : Tm,
    ParallelStep t t' -> lc t'.
Proof.
  induction 1; auto; [now eauto |].
  now apply lc_abs with []; auto.
Qed.

Lemma ParallelStep_open' :
  forall (t t' : Tm) (i : nat) (u u' : Tm),
    ParallelStep t t' ->
    ParallelStep u u' ->
    ParallelStep (t {[ i ~> u ]}) (t' {[ i ~> u' ]}).
Proof.
  intros t t' i u u' Ht Hu; revert i u u' Hu.
  induction Ht; cbn; intros; [| | now eauto..].
  - admit.
  - admit.
Admitted.

#[export] Hint Resolve lc_ParallelStep_l lc_ParallelStep_r : core.

Definition ParallelMultiStep : Tm -> Tm -> Prop :=
  clos_refl_trans _ ParallelStep.

#[export] Hint Unfold ParallelMultiStep : core.

#[export] Hint Constructors clos_refl_trans : core.

Lemma ParallelMultiStep_abs :
  forall t t' : Tm,
    ParallelMultiStep t t' -> ParallelMultiStep (abs t) (abs t').
Proof.
  induction 1; auto.
  now apply rt_trans with (abs y); auto.
Qed.

Lemma ParallelMultiStep_app :
  forall t1 t1' t2 t2' : Tm,
    ParallelMultiStep t1 t1' ->
    ParallelMultiStep t2 t2' ->
      ParallelMultiStep (app t1 t2) (app t1' t2').
Proof.
  intros t1 t1' t2 t2' H1 H2; revert t2 t2' H2.
  induction H1; intros.
  - apply rt_trans with (app y t2).
    + constructor. constructor 4. easy. apply ParallelStep_refl. auto.
Admitted.

Lemma ParallelMultiStep_open' :
  forall (t : Tm) (i : nat) (u u' : Tm),
    lc t ->
    ParallelMultiStep u u' ->
    ParallelMultiStep (t {[ i ~> u ]}) (t {[ i ~> u' ]}).
Proof.
  induction 2; [| now eauto..].
  now constructor; apply ParallelStep_open'; eauto.
Qed.

Lemma ParallelMultiStep_open'' :
  forall (t t' : Tm) (i : nat) (u u' : Tm),
    ParallelMultiStep t t' ->
    ParallelMultiStep u u' ->
    ParallelMultiStep (t {[ i ~> u ]}) (t' {[ i ~> u' ]}).
Proof.
Admitted.

#[export] Hint Resolve ParallelMultiStep_abs ParallelMultiStep_app : core.

Lemma ParallelStep_FullStep :
  forall t1 t2 : Tm,
    FullStep t1 t2 -> ParallelStep t1 t2.
Proof.
  now induction 1; eauto.
Qed.

Lemma MultiStep_ParallelStep :
  forall t1 t2 : Tm,
    ParallelStep t1 t2 -> MultiStep t1 t2.
Proof.
  induction 1; try now eauto.
  apply rt_trans with (app t1' t2).
  - now apply MultiStep_app_l.
  - now apply MultiStep_app_r.
Qed.

Lemma MultiStep_ParallelMultiStep :
  forall t1 t2 : Tm,
    MultiStep t1 t2 <-> ParallelMultiStep t1 t2.
Proof.
  split.
  - induction 1.
    + now constructor; apply ParallelStep_FullStep.
    + now constructor.
    + now apply rt_trans with y.
  - induction 1.
    + now apply MultiStep_ParallelStep.
    + now constructor.
    + now apply rt_trans with y.
Qed.

Lemma confluent_FullContraction_ParallelStep :
  forall t t1 t2 : Tm,
    FullContraction t t1 -> ParallelStep t t2 ->
      exists t3 : Tm, ParallelStep t1 t3 /\ ParallelStep t2 t3.
Proof.
  do 2 inversion 1; subst.
  - now exists (t0 {[ 0 ~> t3 ]}); eauto.
  - inversion H3; subst.
    now exists (t0 {[ 0 ~> t3 ]}); eauto 6.
  - inversion H5; subst.
    + admit.
    + now inversion H0.
    + exists (t0 {[ 0 ~> t2' ]}); split.
      * now apply ParallelStep_open'; eauto.
      * admit.
Abort.

Lemma confluent_ParallelStep_aux :
  forall t t1 t2 : Tm,
    ParallelStep t t1 -> ParallelStep t t2 ->
      exists t3 : Tm, ParallelMultiStep t1 t3 /\ ParallelMultiStep t2 t3.
Proof.
  intros t t1 t2 H1 H2; revert t2 H2.
  induction H1; intros.
  - now exists t2; eauto.
  - exists t2; split; [| now auto].
    
    admit.
(*     now eapply confluent_FullContraction_ParallelStep; eauto. *)
  - inversion H2; subst.
    + now exists (abs t2); auto.
    + now inversion H.
    + now destruct (IHParallelStep _ H0) as (t3 & IH1 & IH2); eauto.
  - inversion H2; subst.
    + now exists (app t1' t2'); eauto 6.
    + inversion H; subst.
      inversion H1_; subst.
      * exists (t3 {[ 0 ~> t2' ]}); split; [now eauto 6 |].
        now apply ParallelMultiStep_open'; auto.
      * now inversion H0.
      * exists (t0 {[ 0 ~> t2' ]}); split; [now constructor; eauto 6 |].
        now apply ParallelMultiStep_open''; auto.
    + destruct (IHParallelStep1 _ H1) as [t3 [IH11 IH12] ].
      destruct (IHParallelStep2 _ H4) as [t4 [IH21 IH22] ].
      now exists (app t3 t4); auto.
Admitted.

Lemma confluent_ParallelMultiStep :
  forall t t1 t2 : Tm,
    ParallelMultiStep t t1 -> ParallelMultiStep t t2 ->
      exists t3 : Tm, ParallelMultiStep t1 t3 /\ ParallelMultiStep t2 t3.
Proof.
  intros t t1 t2 H1 H2; revert t2 H2.
  induction H1; intros.
  - apply confluent_ParallelStep_aux with x. eauto. eauto.
  - now exists t2; split; [| constructor].
  - destruct (IHclos_refl_trans1 _ H2) as [t3 [Hyt3 Ht2t3] ].
    destruct (IHclos_refl_trans2 _ Hyt3) as [t4 [Hzt3 Ht3t4] ].
    exists t4; split; [easy |].
    now apply rt_trans with t3.
Qed.

Lemma confluent_Step_aux :
  forall t t1 t2 : Tm,
    CbvStep t t1 -> CbvStep t t2 ->
      exists t3 : Tm, MultiStep t1 t3 /\ MultiStep t2 t3.
Proof.
  intros t t1 t2 Hs1 Hs2.
  apply ParallelStep_Step in Hs1, Hs2.
  setoid_rewrite MultiStep_ParallelMultiStep.
  now apply confluent_ParallelMultiStep with t.
Qed.

Lemma confluent_Step :
  forall t t1 t2 : Tm,
    MultiStep t t1 -> MultiStep t t2 ->
      exists t3 : Tm, MultiStep t1 t3 /\ MultiStep t2 t3.
Proof.
  setoid_rewrite MultiStep_ParallelMultiStep.
  intros t t1 t2 Hs1 Hs2.
  now apply confluent_ParallelMultiStep with t.
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
| Infer_annot :
  forall (Γ : Ctx) (t : Tm) (A : Ty)
    (Hc' : Check Γ t A),
    Infer Γ (annot t A) A
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
| Infer_elimProd :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B C : Ty) (l : list Atom)
    (Hi1 : Infer Γ t1 (TyProd A B))
    (Hi2 : forall x y : Atom, x # l -> y # x :: l ->
      Infer ((y, B) :: (x, A) :: Γ) (t2 {{ 0 ~> x }} {{ 1 ~> y }}) C),
    Infer Γ (elimProd t1 t2) C
| Infer_case :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C1 C2 : Ty) (l : list Atom)
    (Hi1 : Infer Γ t1 (TySum A B))
    (Hi2 : forall x : Atom, x # l -> Infer ((x, A) :: Γ) (t2 {{ 0 ~> x }}) C1)
    (Hi3 : forall x : Atom, x # l -> Infer ((x, B) :: Γ) (t3 {{ 0 ~> x }}) C2)
    (Heq : C1 = C2),
    Infer Γ (case t1 t2 t3) C1
| Infer_case_asym :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty) (l : list Atom)
    (Hi1 : Infer Γ t1 (TySum A B))
    (Hi2 : forall x : Atom, x # l -> Infer ((x, A) :: Γ) (t2 {{ 0 ~> x }}) C)
    (Hc3 : forall x : Atom, x # l -> Check ((x, B) :: Γ) (t3 {{ 0 ~> x }}) C),
    Infer Γ (case t1 t2 t3) C
| Infer_zero :
  forall (Γ : Ctx),
    Infer Γ zero TyNat
| Infer_succ :
  forall (Γ : Ctx) (t : Tm)
    (Hc' : Check Γ t TyNat),
    Infer Γ (succ t) TyNat

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
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty) (l : list Atom)
    (Hi1 : Infer Γ t1 (TySum A B))
    (Hc2 : forall x : Atom, x # l -> Check ((x, A) :: Γ) (t2 {{ 0 ~> x }}) C)
    (Hc3 : forall x : Atom, x # l -> Check ((x, B) :: Γ) (t3 {{ 0 ~> x }}) C),
    Check Γ (case t1 t2 t3) C
| Check_case' :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty)
    (Hi3 : Infer Γ t3 (TySum A B))
    (Hc1 : Check Γ t1 (TyFun A C))
    (Hc2 : Check Γ t2 (TyFun B C)),
    Check Γ (case' t1 t2 t3) C
| Check_case'' :
  forall (Γ : Ctx) (A B C : Ty),
    Check Γ case'' (TyFun (TyFun A C) (TyFun (TyFun B C) (TyFun (TySum A B) C))).

#[export] Hint Constructors Infer Check : core.

Lemma Typing_Infer :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> Infer Γ t A -> Typing Γ t A

with Typing_Check :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> Check Γ t A -> Typing Γ t A.
Proof.
  - intros ? t A Hwf; destruct 1; try now constructor; auto.
    + now apply Typing_app with A; auto.
    + apply Typing_elimUnit with (l ++ map fst Γ); [now auto |].
      intros x Hx.
      apply Typing_Infer.
      * now constructor; [| solve_fresh'].
      * now apply Hi2; solve_fresh'.
    + now econstructor; eauto.
    + now econstructor; eauto.
    + apply Typing_elimProd with A B (l ++ map fst Γ); [now auto |].
      intros x y Hx Hy.
      apply Typing_Infer; [| now apply Hi2; solve_fresh'].
      constructor; cbn.
      * now constructor; [| solve_fresh'].
      * now solve_fresh'.
    + apply Typing_case with A B (l ++ map fst Γ); [now auto | |].
      * intros x Hx.
        apply Typing_Infer.
        -- now constructor; [| solve_fresh'].
        -- now apply Hi2; solve_fresh'.
      * intros x Hx.
        apply Typing_Infer.
        -- now constructor; [| solve_fresh'].
        -- now subst; apply Hi3; solve_fresh'.
    + apply Typing_case with A B (l ++ map fst Γ); [now auto | |].
      * intros x Hx.
        apply Typing_Infer.
        -- now constructor; [| solve_fresh'].
        -- now apply Hi2; solve_fresh'.
      * intros x Hx.
        apply Typing_Check.
        -- now constructor; [| solve_fresh'].
        -- now subst; apply Hc3; solve_fresh'.
  - intros Γ t A Hwf; destruct 1; try now constructor; auto.
    + now apply Typing_Infer.
    + apply Typing_abs with (l ++ map fst Γ); intros x Hx.
      apply Typing_Check, Hc; [| now solve_fresh'].
      now constructor; [| solve_fresh'].
    + apply Typing_case with A B  (l ++ map fst Γ); [now auto | |].
      * intros x Hx.
        apply Typing_Check.
        -- now constructor; [| solve_fresh'].
        -- now apply Hc2; solve_fresh'.
      * intros x Hx.
        apply Typing_Check.
        -- now constructor; [| solve_fresh'].
        -- now apply Hc3; solve_fresh'.
    + now apply Typing_case' with A B; auto.
Qed.

Lemma Infer_det :
  forall (Γ : Ctx) (t : Tm) (A1 A2 : Ty),
    WfCtx Γ ->
    Infer Γ t A1 ->
    Infer Γ t A2 ->
    A1 = A2.
Proof.
  intros * Hwf Hi1 Hi2; revert A2 Hi2.
  induction Hi1; inversion 1; subst; try easy.
  - now eapply Binds_inv; eauto.
  - now firstorder congruence.
  - apply (H (fresh (l ++ l0 ++ map fst Γ))).
    + now solve_fresh'.
    + now constructor; [| solve_fresh'].
    + now apply Hi1; solve_fresh'.
  - now firstorder congruence.
  - now firstorder congruence.
  - now firstorder congruence.
  - injection (IHHi1 Hwf _ Hi3) as [= <- <-].
    pose (x := fresh (l0 ++ l ++ fv t1 ++ map fst Γ)).
    pose (y := fresh ([x] ++ l0 ++ l ++ fv t1 ++ map fst Γ)).
    apply (H x y).
    + now subst x; solve_fresh'.
    + now subst y; solve_fresh'.
    + constructor.
      * now constructor; [| subst x; solve_fresh'].
      * now subst y; solve_fresh'.
    + apply Hi4; [now subst x; solve_fresh' |].
      now subst y; solve_fresh'.
  - injection (IHHi1 Hwf _ Hi4) as [= <- <-].
    apply (H (fresh (l ++ l0 ++ map fst Γ))).
    + now solve_fresh'.
    + now constructor; [| solve_fresh'].
    + now apply Hi5; solve_fresh'.
  - injection (IHHi1 Hwf _ Hi4) as [= <- <-].
    apply (H (fresh (l ++ l0 ++ map fst Γ))).
    + now solve_fresh'.
    + now constructor; [| solve_fresh'].
    + now apply Hi5; solve_fresh'.
  - injection (IHHi1 Hwf _ Hi3) as [= <- <-].
    apply (H (fresh (l ++ l0 ++ map fst Γ))).
    + now solve_fresh'.
    + now constructor; [| solve_fresh'].
    + now apply Hi4; solve_fresh'.
  - injection (IHHi1 Hwf _ Hi3) as [= <- <-].
    apply (H (fresh (l ++ l0 ++ map fst Γ))).
    + now solve_fresh'.
    + now constructor; [| solve_fresh'].
    + now apply Hi4; solve_fresh'.
Qed.

Inductive Mode : Type :=
| infer
| check (T : Ty).

Require Import Recdef Bool.

Definition typeRet (m : Mode) : Type :=
match m with
| infer => option Ty
| check _ => bool
end.

(*

Function type (m : Mode) (Γ : Ctx) (t : Tm) {measure size t} : typeRet m :=
match m, t with
| infer, fvar x          => None
| infer, bvar n          => None
| infer, abs t'          => None
| infer, app t1 t2       =>
  match type infer Γ t1 with
  | Some (TyFun A B) => if type (check A) Γ t2 then Some B else None
  | _ => None
  end
| infer, annot t' A      => if type (check A) Γ t' then Some A else None
| infer, unit            => Some TyUnit
| infer, elimUnit t1 t2  =>
  if type (check TyUnit) Γ t1
  then let x := fresh (fv t2) in type infer ((x, TyUnit) :: Γ) (t2 {{ 0 ~> x }})
  else None
| infer, elimUnit' t1 t2 => None
| infer, elimUnit''      => None
| infer, abort t'        => None
| infer, pair t1 t2      =>
  match type infer Γ t1, type infer Γ t2 with
  | Some A, Some B => Some (TyProd A B)
  | _, _ => None
  end
| infer, outl t'         =>
  match type infer Γ t' with
  | Some (TyProd A B) => Some A
  | _ => None
  end
| infer, outr t'         =>
  match type infer Γ t' with
  | Some (TyProd A B) => Some B
  | _ => None
  end
| infer, inl t'          => None
| infer, inr t'          => None
| infer, case t1 t2 t3   =>
  match type infer Γ t1 with
  | Some (TySum A B) =>
    let x := fresh (fv t1) in
    let y := fresh (fv t2) in
      match
        type infer ((x, A) :: Γ) (t2 {{ 0 ~> x }}),
        type infer ((y, B) :: Γ) (t3 {{ 0 ~> y }})
      with
      | Some C1, Some C2 => if decide (C1 = C2) then Some C1 else None
      | _, _ => None
      end
  | _ => None
  end
| infer, case' t1 t2 t3  => None
| infer, case''          => None
| infer, zero            => Some TyNat
| infer, succ t'         => if type (check TyNat) Γ t' then Some TyNat else None
| infer, rec t1 t2 t3    =>
  if type (check TyNat) Γ t3
  then
    match type infer Γ t1 with
    | Some A =>
      let
        x := fresh (fv t2)
      in
        if type (check A) ((x, A) :: Γ) (t2 {{ 0 ~> x }})
        then Some A
        else None
    | _ => None
    end
  else None
| check (TyFun A B), abs t' => let x := fresh (fv t') in type (check B) ((x, A) :: Γ) t'
| check A, elimUnit' t1 t2  => type (check TyUnit) Γ t1 && type (check (TyFun TyUnit A)) Γ t2
| check T, elimUnit'' =>
  match T with
  | TyFun (TyFun TyUnit A) (TyFun TyUnit B) => decide (A = B)
  | _ => false
  end
| check _, abort t'        => type (check TyEmpty) Γ t'
| check (TyProd A B), pair t1 t2 => type (check A) Γ t1 && type (check B) Γ t2
| check (TySum A B), inl t' => type (check A) Γ t'
| check (TySum A B), inr t' => type (check B) Γ t'
| check C, case' t1 t2 t3  =>
  match type infer Γ t1 with
  | Some (TySum A B) => type (check (TyFun A C)) Γ t2 && type (check (TyFun B C)) Γ t3
  | _ => false
  end
| check T, case''       =>
  match T with
  | TyFun (TyFun A1 C1) (TyFun (TyFun B2 C2) (TyFun (TySum A3 B3) C3)) =>
    decide (A1 = A3) && decide (B2 = B3) && decide (C1 = C2) && decide (C2 = C3)
  | _ => false
  end
| check T, _              =>
  match type infer Γ t with
  | Some T' => decide (T = T')
  | _ => false
  end
end.


Function infer (Γ : Ctx) (t : Tm) {measure size t} : option Ty :=
match t with
| fvar x          => None
| bvar n          => None
| abs t'          => None
| app t1 t2       =>
  match infer Γ t1 with
  | Some (TyFun A B) => if check Γ t2 A then Some B else None
  | _ => None
  end
| annot t' A      => if check Γ t' A then Some A else None
| unit            => Some TyUnit
| elimUnit t1 t2  =>
  if check Γ t1 TyUnit
  then let x := fresh (fv t2) in infer ((x, TyUnit) :: Γ) (t2 {{ 0 ~> x}})
  else None
| elimUnit' t1 t2 => None
| elimUnit''      => None
| abort t'        => None
| pair t1 t2      =>
  match infer Γ t1, infer Γ t2 with
  | Some A, Some B => Some (TyProd A B)
  | _, _ => None
  end
| outl t'         =>
  match infer Γ t' with
  | Some (TyProd A B) => Some A
  | _ => None
  end
| outr t'         =>
  match infer Γ t' with
  | Some (TyProd A B) => Some B
  | _ => None
  end
| inl t'          => None
| inr t'          => None
| case t1 t2 t3   =>
  match infer Γ t1 with
  | Some (TySum A B) =>
    let x := fresh (fv t1) in
    let y := fresh (fv t2) in
      match infer ((x, A) :: Γ) (t2 {{ 0 ~> x }}), infer ((y, B) :: Γ) (t3 {{ 0 ~> y }}) with
      | Some C1, Some C2 => if decide (C1 = C2) then Some C1 else None
      | _, _ => None
      end
  | _ => None
  end
| case' t1 t2 t3  => None
| case''          => None
| zero            => Some TyNat
| succ t'         => if check Γ t' TyNat then Some TyNat else None
| rec t1 t2 t3    =>
  if check Γ t3 TyNat
  then
    match infer Γ t1 with
    | Some A =>
      let
        x := fresh (fv t2)
      in
        if check ((x, A) :: Γ) (t2 {{ 0 ~> x }}) A
        then Some A
        else None
    | _ => None
    end
  else None
end

with check (Γ : Ctx) (t : Tm) (T : Ty) {struct t} : bool :=
match t, T with
| abs t', TyFun A B  => let x := fresh (fv t') in check ((x, A) :: Γ) t' B
| elimUnit' t1 t2, _ => andb (check Γ t1 TyUnit) (check Γ t2 (TyFun TyUnit T))
| elimUnit'', _      =>
  match T with
  | TyFun (TyFun TyUnit A) (TyFun TyUnit B) => decide (A = B)
  | _ => false
  end
| abort t', _        => check Γ t' TyEmpty
| pair t1 t2, TyProd A B => check Γ t1 A && check Γ t2 B
| inl t', TySum A B => check Γ t' A
| inr t', TySum A B => check Γ t' B
| case' t1 t2 t3, _  =>
  match infer Γ t1 with
  | Some (TySum A B) => check Γ t2 (TyFun A T) && check Γ t3 (TyFun B T)
  | _ => false
  end
| case'', _       =>
  match T with
  | TyFun (TyFun A1 C1) (TyFun (TyFun B2 C2) (TyFun (TySum A3 B3) C3)) =>
    decide (A1 = A3) && decide (B2 = B3) && decide (C1 = C2) && decide (C2 = C3)
  | _ => false
  end
| _, _              =>
  match infer Γ t with
  | Some T' => decide (T = T')
  | _ => false
  end
end.
*)
