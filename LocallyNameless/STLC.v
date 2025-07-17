Require Import
  List
  Coq.Classes.DecidableClass.

Import ListNotations.

Inductive Ty : Type :=
| TyUnit : Ty
| TyFun : Ty -> Ty -> Ty.

Parameters
  (Atom : Type)
  (Decidable_eq_Atom : forall x y : Atom, Decidable (x = y)).

Existing Instance Decidable_eq_Atom.

Inductive Tm : Type :=
| fvar : Atom -> Tm
| bvar : nat -> Tm
| abs  : Tm -> Tm
| app  : Tm -> Tm -> Tm.

Coercion fvar : Atom >-> Tm.
Coercion bvar : nat >-> Tm.

Example I : Tm :=
  abs 0.

Example K : Tm :=
  abs (abs 0).

Example S' : Tm :=
  abs (abs (abs (app 2 (app 1 0)))).

Example two : Tm :=
  abs (abs (app 1 (app 1 0))).

Fixpoint subst (x : Atom) (u t : Tm) : Tm :=
match t with
| fvar y    => if decide (x = y) then u else fvar y
| bvar n    => bvar n
| abs t'    => abs (subst x u t')
| app t1 t2 => app (subst x u t1) (subst x u t2)
end.

Notation "x |> f" := (f x) (at level 68, only parsing).

(* Notation "t [ x ~> u ]" := (subst x u t) (at level 68). *)

Notation "t [ x := u ]" := (subst x u t) (at level 68).

Lemma subst_demo :
  forall x y : Atom,
    abs (app 0 x) |> subst x y = abs (app 0 y).
Proof.
  intros x y; cbn.
  now decide (x = x).
Qed.

Fixpoint fv (t : Tm) : list Atom :=
match t with
| fvar x    => [x]
| bvar _    => []
| abs t'    => fv t'
| app t1 t2 => fv t1 ++ fv t2
end.

Lemma subst_fresh :
  forall (x : Atom) (u t : Tm),
    ~ In x (fv t) -> t |> subst x u = t.
Proof.
  induction t; cbn; intros.
  - decide (x = a); [| easy].
    now firstorder congruence.
  - easy.
  - now rewrite IHt.
  - rewrite in_app_iff in H.
    now firstorder congruence.
Qed.

Lemma subst_fresh' :
  forall (x : Atom) (u t : Tm),
    In x (fv t) \/ t |> subst x u = t.
Proof.
  induction t; cbn; intros.
  - now decide (x = a); firstorder.
  - now right.
  - now destruct IHt; firstorder congruence.
  - rewrite in_app_iff.
    now destruct IHt1, IHt2; firstorder congruence.
Qed.

Fixpoint open_aux (i : nat) (u t : Tm) : Tm :=
match t with
| fvar a    => fvar a
| bvar j    => if decide (i = j) then u else bvar j
| abs t'    => abs (open_aux (S i) u t')
| app t1 t2 => app (open_aux i u t1) (open_aux i u t2)
end.

(* Notation "{ n ~> t2 } t1" := (open_aux t1 n t2) (at level 68). *)
Notation "t { i ~> u }" := (open_aux i u t) (at level 68).

Definition open (u t : Tm) : Tm :=
  open_aux 0 u t.

Lemma open_demo :
  forall y : Atom,
    app (abs (app 1 0)) 0 |> open y = app (abs (app y 0)) y.
Proof.
  easy.
Qed.

Inductive lc : Tm -> Prop :=
| lc_fvar : forall x : Atom, lc x
| lc_abs  : forall (t : Tm) (x : Atom), lc (open x t)  -> lc (abs t)
| lc_app  : forall t1 t2 : Tm, lc t1 -> lc t2 -> lc (app t1 t2).

#[export] Hint Constructors lc : core.

Lemma open_aux_open_aux :
  forall (t : Tm) (n m : nat) (u1 u2 : Tm),
    n <> m ->
    t |> open_aux n u1 |> open_aux m u2 = t |> open_aux n u1 ->
      t |> open_aux m u2 = t.
Proof.
  induction t; cbn; intros * Hneq H.
  - easy.
  - destruct (PeanoNat.Nat.eqb_spec n0 n); [| easy].
    destruct (PeanoNat.Nat.eqb_spec m n); [| easy].
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

Lemma open_aux_open :
  forall (t : Tm) (n : nat) (x : Atom) (u : Tm),
    t |> open x |> open_aux (S n) u = t |> open x ->
      t |> open_aux (S n) u = t.
Proof.
  unfold open.
  intros.
  now apply open_aux_open_aux in H.
Qed.

Lemma open_aux_lc :
  forall (t : Tm) (n : nat) (u : Tm),
    lc t -> t |> open_aux n u = t.
Proof.
  intros t n u Hlc; revert n u.
  induction Hlc; cbn; intros; [easy | |].
  - f_equal.
    now eapply open_aux_open, IHHlc.
  - now f_equal.
Qed.

Lemma subst_open_aux :
  forall (t : Tm) (n : nat) (u1 : Tm) (x : Atom) (u2 : Tm),
    lc u2 ->
    t |> open_aux n u1 |> subst x u2
      =
    t |> subst x u2 |> open_aux n (u1 |> subst x u2).
Proof.
  induction t; cbn; intros.
  - rewrite open_aux_lc; [easy |].
    now decide (x = a).
  - now destruct (PeanoNat.Nat.eqb n0 n).
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Qed.

Lemma open_subst :
  forall (t : Tm) (x y : Atom) (u : Tm),
    x <> y -> lc u ->
      t |> subst x u |> open y = t |> open y |> subst x u.
Proof.
  unfold open.
  intros.
  rewrite subst_open_aux; cbn; [| easy].
  now decide (x = y).
Qed.

Lemma lc_subst :
  forall (t : Tm) (x : Atom) (u : Tm),
    lc t -> lc u -> lc (subst x u t).
Proof.
  intros t x u Ht Hu; revert x u Hu.
  induction Ht; cbn; intros.
  - now decide (x0 = x).
  - admit.
  - now constructor; firstorder.
Abort.
