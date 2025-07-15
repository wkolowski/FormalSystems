Require Import
  List
  Coq.Classes.DecidableClass.

Import ListNotations.

Inductive Ty : Type :=
| TyUnit : Ty
| TyFun : Ty -> Ty -> Ty.

Parameters
  (Fvar : Type)
  (Decidable_eq_Fvar : forall x y : Fvar, Decidable (x = y)).

Existing Instance Decidable_eq_Fvar.

Inductive Tm : Type :=
| fvar : Fvar -> Tm
| bvar : nat -> Tm
| abs  : Tm -> Tm
| app  : Tm -> Tm -> Tm.

Coercion fvar : Fvar >-> Tm.
Coercion bvar : nat >-> Tm.

Example I : Tm :=
  abs 0.

Example K : Tm :=
  abs (abs 0).

Example S' : Tm :=
  abs (abs (abs (app 2 (app 1 0)))).

Example two : Tm :=
  abs (abs (app 1 (app 1 0))).

Fixpoint subst (t1 : Tm) (x : Fvar) (t2 : Tm) : Tm :=
match t1 with
| fvar y      => if decide (x = y) then t2 else fvar y
| bvar n      => bvar n
| abs t1'     => abs (subst t1' x t2)
| app t11 t12 => app (subst t11 x t2) (subst t12 x t2)
end.

Notation "t1 [ x := t2 ]" := (subst t1 x t2) (at level 68).

Lemma subst_demo :
  forall x y : Fvar,
(*     (abs (app 0 x)) [x := y] = abs (app 0 y). *)
    subst (abs (app 0 x)) x y = abs (app 0 y).
Proof.
  intros x y; cbn.
  now decide (x = x).
Qed.

Fixpoint fv (t : Tm) : list Fvar :=
match t with
| fvar x => [x]
| bvar _ => []
| abs t' => fv t'
| app t1 t2 => fv t1 ++ fv t2
end.

Lemma subst_fresh :
  forall (x : Fvar) (t1 t2 : Tm),
    ~ In x (fv t1) -> subst t1 x t2 = t1.
Proof.
  induction t1 as [y | n | t1' | t11 IH1 t12 IH2]; cbn; intros.
  - decide (x = y); [| easy].
    firstorder congruence.
  - easy.
  - now f_equal; apply IHt1'.
  - rewrite in_app_iff in H.
    now f_equal; firstorder.
Qed.

Lemma subst_fresh' :
  forall (x : Fvar) (t1 t2 : Tm),
    In x (fv t1) \/ subst t1 x t2 = t1.
Proof.
  induction t1 as [y | n | t1' | t11 IH1 t12 IH2]; cbn; intros.
  - now decide (x = y); firstorder.
  - now right.
  - now destruct (IHt1' t2); firstorder congruence.
  - rewrite in_app_iff.
    now destruct (IH1 t2), (IH2 t2); firstorder congruence.
Qed.

Fixpoint open_aux (t1 : Tm) (n : nat) (t2 : Tm) : Tm :=
match t1 with
| fvar x      => fvar x
| bvar m      => if decide (n = m) then t2 else bvar m
| abs t1'     => abs (open_aux t1' (S n) t2)
| app t11 t12 => app (open_aux t11 n t2) (open_aux t12 n t2)
end.

Definition open (t1 t2 : Tm) : Tm :=
  open_aux t1 0 t2.

Lemma open_demo :
  forall y : Fvar,
    open (app (abs (app 1 0)) 0) y = app (abs (app y 0)) y.
Proof.
  easy.
Qed.

Inductive lc : Tm -> Prop :=
| lc_fvar : forall x : Fvar, lc x
| lc_abs  : forall (t : Tm) (x : Fvar), lc (open t x)  -> lc (abs t)
| lc_app  : forall t1 t2 : Tm, lc t1 -> lc t2 -> lc (app t1 t2).

#[export] Hint Constructors lc : core.

Lemma open_aux_open_aux :
  forall (t : Tm) (n m : nat) (t1 t2 : Tm),
    n <> m ->
    open_aux (open_aux t n t1) m t2 = open_aux t n t1 ->
      open_aux t m t2 = t.
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
  forall (t : Tm) (n : nat) (x : Fvar) (t' : Tm),
    open_aux (open t x) (S n) t' = open t x ->
      open_aux t (S n) t' = t.
Proof.
  intros.
  unfold open in H.
  now apply open_aux_open_aux in H.
Qed.

Lemma lc_open_aux :
  forall (t : Tm) (n : nat) (t' : Tm),
    lc t -> open_aux t n t' = t.
Proof.
  intros t n t' Hlc; revert n t'.
  induction Hlc; cbn; [easy | |].
  - intros n t'; f_equal.
    now eapply open_aux_open, IHHlc.
  - now intros n t'; f_equal.
Qed.

Lemma subst_open_aux :
  forall (t1 : Tm) (n : nat) (t2 : Tm) (x : Fvar) (t3 : Tm),
    lc t3 ->
    subst (open_aux t1 n t2) x t3
      =
    open_aux (subst t1 x t3) n (subst t2 x t3).
Proof.
  induction t1; cbn; intros.
  - rewrite lc_open_aux; [easy |].
    now decide (x = f).
  - now destruct (PeanoNat.Nat.eqb n0 n).
  - now rewrite IHt1.
  - now rewrite IHt1_1, IHt1_2.
Qed.
