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
| fvar (a : Atom) : Tm
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

Notation "t [[ x := u ]]" := (subst x u t) (at level 68).

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

Fixpoint open (i : nat) (u t : Tm) : Tm :=
match t with
| fvar a    => fvar a
| bvar j    => if decide (i = j) then u else bvar j
| abs t'    => abs (open (S i) u t')
| app t1 t2 => app (open i u t1) (open i u t2)
end.

(* Notation "{ n ~> t2 } t1" := (open t1 n t2) (at level 68). *)
Notation "t {{ i ~> u }}" := (open i u t) (at level 68).

Definition open' (u t : Tm) : Tm :=
  open 0 u t.

Lemma open_demo :
  forall y : Atom,
    app (abs (app 1 0)) 0 |> open' y = app (abs (app y 0)) y.
Proof.
  easy.
Qed.

Inductive lc : Tm -> Prop :=
| lc_fvar : forall x : Atom, lc x
| lc_abs  : forall (t : Tm) (x : Atom), lc (open' x t)  -> lc (abs t)
| lc_app  : forall t1 t2 : Tm, lc t1 -> lc t2 -> lc (app t1 t2).

#[export] Hint Constructors lc : core.

Lemma open_open :
  forall (t : Tm) (i j : nat) (u1 u2 : Tm),
    i <> j ->
    t {{ i ~> u1 }} {{ j ~> u2 }} = t {{ i ~> u1 }} ->
      t {{ j ~> u2 }} = t.
Proof.
  induction t; cbn; intros * Hneq H.
  - easy.
  - destruct (PeanoNat.Nat.eqb_spec i n); [| easy].
    destruct (PeanoNat.Nat.eqb_spec j n); [| easy].
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

Lemma open_open' :
  forall (t : Tm) (i : nat) (x : Atom) (u : Tm),
(*     t |> open' x |> open (S i) u = t |> open' x -> *)
    t {{ 0 ~> x }} {{ S i ~> u }} = t {{ 0 ~> x }} ->
      t {{ S i ~> u }} = t.
Proof.
  unfold open'.
  intros.
  now apply open_open in H.
Qed.

Lemma open_lc :
  forall (t : Tm) (i : nat) (u : Tm),
    lc t -> t {{ i ~> u }} = t.
Proof.
  intros t n u Hlc; revert n u.
  induction Hlc; cbn; intros; [easy | |].
  - f_equal.
    now eapply open_open', IHHlc.
  - now f_equal.
Qed.

Lemma subst_open :
  forall (t : Tm) (i : nat) (u1 : Tm) (x : Atom) (u2 : Tm),
    lc u2 ->
    t {{ i ~> u1 }} [[ x := u2 ]]
      =
    t [[ x := u2 ]] {{ i ~> u1 [[ x := u2 ]] }}.
Proof.
  induction t; cbn; intros.
  - rewrite open_lc; [easy |].
    now decide (x = a).
  - now destruct (PeanoNat.Nat.eqb i n).
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Qed.

Lemma open_subst :
  forall (t : Tm) (a b : Atom) (u : Tm),
    a <> b -> lc u ->
    t [[ a := u ]] {{ 0 ~> b }} = t {{ 0 ~> b }} [[ a := u ]].
Proof.
  intros.
  rewrite subst_open; cbn; [| easy].
  now decide (a = b).
Qed.

Lemma lc_subst :
  forall (t : Tm) (a : Atom) (u : Tm),
    lc t -> lc u -> lc (t [[ a := u ]]).
Proof.
  intros t x u Ht Hu; revert x u Hu.
  induction Ht; cbn; intros.
  - now decide (x0 = x).
  - admit.
  - now constructor; firstorder.
Abort.

Fixpoint succ (t : Tm) : Tm :=
match t with
| fvar x    => fvar x
| bvar i    => bvar (S i)
| abs t'    => abs t'
| app t1 t2 => app (succ t1) (succ t2)
end.

(*
Fixpoint close (a : Atom) (u t : Tm) : Tm :=
match t with
| fvar x    => if decide (a = x) then u else fvar x
| bvar i    => bvar i
| abs t'    => abs (close a (succ u) t')
| app t1 t2 => app (close a u t1) (close a u t2)
end.

Notation "t {{ u <~ a }}" := (close a u t) (at level 68).
*)

Fixpoint close (a : Atom) (i : nat) (t : Tm) : Tm :=
match t with
| fvar x    => if decide (a = x) then bvar i else fvar x
| bvar n    => bvar n
| abs t'    => abs (close a (S i) t')
| app t1 t2 => app (close a i t1) (close a i t2)
end.

Notation "t {{ i <~ a }}" := (close a i t) (at level 68).

(* OC 1 *)
Lemma open_open_eq :
  forall (t : Tm) (i : nat) (a b : Atom),
    t {{ i ~> a }} {{ i ~> b }} = t {{ i ~> a }}.
Proof.
  induction t; cbn; intros; [easy | | |].
  - destruct (PeanoNat.Nat.eqb_spec i n); cbn; [easy |].
    now destruct (PeanoNat.Nat.eqb_spec i n).
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Qed.

(* OC 2 *)
Lemma close_close_eq :
  forall (t : Tm) (a : Atom) (i j : nat),
    t {{ i <~ a }} {{ j <~ a }} = t {{ i <~ a }}.
Proof.
  induction t; cbn; intros; [| easy | |].
  - decide (a0 = a); cbn; [easy |].
    now decide (a0 = a).
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Qed.

(* OC 3 *)
Lemma open_close_eq :
  forall (t : Tm) (i : nat) (a : Atom),
    t {{ i ~> a }} {{ i <~ a }} = t {{ i <~ a }}.
Proof.
  induction t; cbn; intros; [easy | ..].
  - destruct (PeanoNat.Nat.eqb_spec i n); subst; cbn; [| easy].
    now decide (a = a).
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Qed.

(* OC 4 *)
Lemma close_open_eq :
  forall (t : Tm) (i : nat) (a : Atom),
    t {{ i <~ a }} {{ i ~> a }} = t {{ i ~> a }}.
Proof.
  induction t; cbn; intros; [| easy | ..].
  - decide (a0 = a); subst; cbn; [| easy].
    now destruct (PeanoNat.Nat.eqb_spec i i).
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Qed.

(* OC 5 *)
Lemma open_open_neq :
  forall (t : Tm) (i j : nat) (a b : Atom),
    i <> j ->
      t {{ i ~> a }} {{ j ~> b }} = t {{ j ~> b }} {{ i ~> a }}.
Proof.
  induction t; cbn; intros; [easy | ..].
  - destruct (PeanoNat.Nat.eqb_spec j n); cbn;
      destruct (PeanoNat.Nat.eqb_spec i n); subst; cbn; [easy | | easy |].
    + now destruct (PeanoNat.Nat.eqb_spec n n).
    + now destruct (PeanoNat.Nat.eqb_spec j n).
  - now rewrite IHt; [| congruence].
  - now rewrite IHt1, IHt2.
Qed.

(* OC 6 *)
Lemma close_close_neq :
  forall (t : Tm) (i j : nat) (a b : Atom),
    a <> b ->
      t {{ i <~ a }} {{ j <~ b }} = t {{ j <~ b }} {{ i <~ a }}.
Proof.
  induction t; cbn; intros; [| easy | ..].
  - decide (a0 = a); subst; cbn;
      decide (b = a); subst; cbn; only 1, 3: easy.
    + now decide (a = a).
    + now decide (a0 = a).
  - now rewrite IHt; [| congruence].
  - now rewrite IHt1, IHt2.
Qed.

(* OC 7 *)
Lemma open_close_neq :
  forall (t : Tm) (i j : nat) (a b : Atom),
    i <> j -> a <> b ->
      t {{ i ~> a }} {{ j <~ b }} = t {{ j <~ b }} {{ i ~> a }}.
Proof.
  induction t; cbn; intros.
  - decide (b = a); subst; cbn; [| easy].
    now destruct (PeanoNat.Nat.eqb_spec i j).
  - destruct (PeanoNat.Nat.eqb_spec i n); cbn; [| easy].
    now decide (b = a); subst.
  - now rewrite IHt; congruence.
  - now rewrite IHt1, IHt2.
Qed.

(* OC 8 *)
Lemma open_close_open :
  forall (t : Tm) (i j : nat) (a b : Atom),
    t {{ i ~> a }} {{ j <~ a }} {{ j ~> b }}
      =
    t {{ j ~> b }} {{ i <~ a }} {{ i ~> b }}.
Proof.
  induction t; cbn; intros.
  - decide (a0 = a); cbn; [| easy].
    now destruct (PeanoNat.Nat.eqb_spec j j), (PeanoNat.Nat.eqb_spec i i).
  - destruct (PeanoNat.Nat.eqb_spec i n); subst; cbn;
      destruct (PeanoNat.Nat.eqb_spec j n); subst; cbn.
    + rewrite Decidable_complete by easy.
      now decide (a = b); cbn; destruct (PeanoNat.Nat.eqb_spec n n).
    + rewrite Decidable_complete by easy; cbn.
      now destruct (PeanoNat.Nat.eqb_spec j j), (PeanoNat.Nat.eqb_spec n n).
    + decide (a = b); cbn; [| easy].
      now destruct (PeanoNat.Nat.eqb_spec i i).
    + now destruct (PeanoNat.Nat.eqb_spec i n).
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Qed.

(* OC 9 *)
Lemma close_open_close :
  forall (t : Tm) (i j : nat) (a b : Atom),
    t {{ i <~ a }} {{ i ~> b }} {{ j <~ b }}
      =
    t {{ j <~ b }} {{ i ~> a }} {{ j <~ a }}.
Proof.
  induction t; cbn; intros.
  - decide (b = a); subst; cbn; decide (a0 = a); subst; cbn.
    + now destruct (PeanoNat.Nat.eqb_spec i j), (PeanoNat.Nat.eqb_spec i i); cbn;
        rewrite ?Decidable_complete by easy.
    + rewrite Decidable_complete by easy.
      destruct (PeanoNat.Nat.eqb_spec i j); cbn; [| easy].
      now rewrite Decidable_complete.
    + destruct (PeanoNat.Nat.eqb_spec i i); cbn; [| easy].
      now rewrite Decidable_complete.
    + now decide (b = a).
  - destruct (PeanoNat.Nat.eqb_spec i n); subst; cbn; [| easy].
    now rewrite !Decidable_complete.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
Qed.

