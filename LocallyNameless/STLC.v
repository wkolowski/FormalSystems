Require Import
  List
  Coq.Classes.DecidableClass.

Import ListNotations.

Inductive Ty : Type :=
| TyUnit : Ty
| TyFun : Ty -> Ty -> Ty.

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

Parameters
  (Atom : Type)
  (Decidable_eq_Atom : forall x y : Atom, Decidable (x = y))
  (fresh : list Atom -> Atom)
  (fresh_spec : forall l : list Atom, ~ In (fresh l) l).

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

Lemma open_from_subst :
  forall (t : Tm) (i : nat) (a : Atom) (u : Tm),
    ~ In a (fv t) ->
      t {{ i ~> u }} = t {{ i ~> a }} [[ a := u ]].
Proof.
  induction t; cbn; intros.
  - now decide (a0 = a); subst; firstorder.
  - destruct (PeanoNat.Nat.eqb_spec i n); cbn; [| easy].
    now decide (a = a).
  - now rewrite <- IHt.
  - rewrite in_app_iff in H.
    now rewrite <- IHt1, <- IHt2; firstorder.
Qed.

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
    t {{ 0 ~> x }} {{ S i ~> u }} = t {{ 0 ~> x }} ->
      t {{ S i ~> u }} = t.
Proof.
  intros.
  now apply open_open in H.
Qed.

Module first_try.

Inductive lc : Tm -> Prop :=
| lc_fvar : forall x : Atom, lc x
| lc_abs  : forall (t : Tm) (x : Atom), lc (open' x t)  -> lc (abs t)
| lc_app  : forall t1 t2 : Tm, lc t1 -> lc t2 -> lc (app t1 t2).

#[export] Hint Constructors lc : core.

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
  forall (t : Tm) (x : Atom) (u : Tm),
    lc t -> lc u -> lc (t [[ x := u ]]).
Proof.
  intros t x u Ht Hu; revert x u Hu.
  induction Ht; cbn; intros.
  - now decide (x0 = x).
  - eapply lc_abs. rewrite open_subst; [| | easy]. unfold open' in Ht. admit. admit.
  - now constructor; firstorder.
Abort.

End first_try.

Inductive lc : Tm -> Prop :=
| lc_fvar : forall x : Atom, lc x
| lc_abs  : forall (t : Tm) (l : list Atom), (forall x, ~ In x l -> lc (open' x t)) -> lc (abs t)
| lc_app  : forall t1 t2 : Tm, lc t1 -> lc t2 -> lc (app t1 t2).

#[export] Hint Constructors lc : core.

Lemma open_lc :
  forall (t : Tm) (i : nat) (u : Tm),
    lc t -> t {{ i ~> u }} = t.
Proof.
  intros t n u Hlc; revert n u.
  induction Hlc; cbn; intros; [easy | |].
  - f_equal.
    apply open_open' with (fresh l), H0.
    now apply fresh_spec.
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
  forall (t : Tm) (x : Atom) (u : Tm),
    lc t -> lc u -> lc (t [[ x := u ]]).
Proof.
  intros t x u Ht Hu; revert x u Hu.
  induction Ht; cbn; intros.
  - now decide (x0 = x).
  - apply lc_abs with (x :: l).
    intros y Hin.
    rewrite open_subst; [| now firstorder | easy].
    apply H0; [| easy].
    now firstorder.
  - now constructor; [apply IHHt1 | apply IHHt2].
Qed.

Definition Ctx : Type := list (Atom * Ty).

Inductive WfCtx : Ctx -> Prop :=
| WfCtx_nil  : WfCtx []
| WfCtx_cons :
    forall (x : Atom) (A : Ty) (G : Ctx),
      WfCtx G -> ~ In x (map fst G) -> WfCtx ((x, A) :: G).

Inductive Binds : Ctx -> Atom -> Ty -> Prop :=
| Binds_head :
  forall (G : Ctx) (x : Atom) (A : Ty),
    Binds ((x, A) :: G) x A
| Binds_tail :
  forall (G : Ctx) (x y : Atom) (A B : Ty),
    x <> y ->
    Binds G x A ->
    Binds ((y, B) :: G) x A.

#[export] Hint Constructors Binds : core.

Lemma Binds_app_l :
  forall (G1 G2 : Ctx) (x : Atom) (A : Ty),
    Binds G1 x A -> Binds (G1 ++ G2) x A.
Proof.
  now induction 1; cbn; constructor.
Qed.

Lemma Binds_app_r :
  forall (G1 G2 : Ctx) (x : Atom) (A : Ty),
    (forall B : Ty, ~ Binds G1 x B) -> Binds G2 x A -> Binds (G1 ++ G2) x A.
Proof.
  induction G1 as [| [y B] G1' IH]; cbn; intros; [easy |].
  decide (x = y); subst.
  - contradiction (H B).
    now constructor.
  - constructor; [easy |].
    apply IH; [| easy].
    intros C HC.
    apply (H C).
    now constructor.
Qed.

Lemma Binds_app_inv :
  forall (G1 G2 : Ctx) (x : Atom) (A : Ty),
    Binds (G1 ++ G2) x A ->
    Binds G1 x A
      \/
    ((forall B : Ty, ~ Binds G1 x B) /\ Binds G2 x A).
Proof.
  induction G1 as [| [y B] G1' IH]; cbn; intros; [now right |].
  inversion H; subst; [now left |].
  destruct (IH _ _ _ H6).
  - now left; constructor.
  - right; split; [| easy].
    intros C HC.
    destruct H0 as [H0 _].
    apply (H0 C).
    now inversion HC; subst.
Qed.

Inductive Typing : Ctx -> Tm -> Ty -> Prop :=
| Typing_fvar :
  forall (G : Ctx) (x : Atom) (A : Ty),
    Binds G x A -> Typing G x A
| Typing_abs :
  forall (G : Ctx) (t : Tm) (A B : Ty) (l : list Atom),
    (forall x : Atom, ~ In x l -> Typing ((x, A) :: G) (t {{ 0 ~> x }}) B) ->
    Typing G (abs t) (TyFun A B)
| Typing_app :
  forall (G : Ctx) (t1 t2 : Tm) (A B : Ty),
    Typing G t1 (TyFun A B) ->
    Typing G t2 A ->
    Typing G (app t1 t2) B.

#[export] Hint Constructors Typing : Core.

Lemma weakening :
  forall (G1 G2 D : Ctx) (t : Tm) (A : Ty),
    Typing (G1 ++ G2) t A ->
    WfCtx (G1 ++ D ++ G2) ->
    Typing (G1 ++ D ++ G2) t A.
Proof.
  intros * Ht.
  remember (G1 ++ G2) as G.
  revert G1 G2 D HeqG.
  induction Ht; only 2-3: intros; subst.
  - intros; subst.
    constructor.
    apply Binds_app_inv in H as [].
    + now apply Binds_app_l.
    + apply Binds_app_r; [easy |].
      apply Binds_app_r; [| easy].
      intros B HB.
  - apply Typing_abs with l.
    intros.
    rewrite app_comm_cons.
    now apply H0.
  - apply Typing_app with A.
    + now apply IHHt1.
    + now apply IHHt2.
Admitted.

Lemma weakening :
  forall (G1 G2 D : Ctx) (t : Tm) (A : Ty),
    Typing (G1 ++ G2) t A ->
    Typing (G1 ++ D ++ G2) t A.
Proof.
  intros * Ht.
  remember (G1 ++ G2) as G.
  revert G1 G2 D HeqG.
  induction Ht; only 2-3: intros; subst.
  - intros; subst.
    constructor.
    apply Binds_app_inv in H as [].
    + now apply Binds_app_l.
    + apply Binds_app_r; [easy |].
      apply Binds_app_r; [| easy].
      admit.
  - apply Typing_abs with l.
    intros.
    rewrite app_comm_cons.
    now apply H0.
  - apply Typing_app with A.
    + now apply IHHt1.
    + now apply IHHt2.
Admitted.

Lemma weakening' :
  forall (G D : Ctx) (t : Tm) (A : Ty),
    Typing G t A ->
    Typing (G ++ D) t A.
Proof.
  intros * Ht.
  revert D.
  induction Ht; intros; subst.
  - constructor.
    now apply Binds_app_l.
  - apply Typing_abs with l.
    intros.
    rewrite app_comm_cons.
    now apply H0.
  - apply Typing_app with A.
    + now apply IHHt1.
    + now apply IHHt2.
Qed.

Lemma weakening'' :
  forall (G D : Ctx) (t : Tm) (A : Ty),
    Typing G t A ->
    Typing (D ++ G) t A.
Proof.
  intros * Ht.
  revert D.
  induction Ht; intros; subst.
  - constructor.
    apply Binds_app_r; [| easy].
    admit.
  - apply Typing_abs with l.
    intros.
    rewrite app_comm_cons.
    admit.
  - apply Typing_app with A.
    + now apply IHHt1.
    + now apply IHHt2.
Admitted.

