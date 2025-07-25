Require Import
  List
  Coq.Classes.DecidableClass.

Import ListNotations.

(*
Parameters
  (Atom : Type)
  (Decidable_eq_Atom : forall x y : Atom, Decidable (x = y))
  (fresh : list Atom -> Atom)
  (fresh_spec : forall l : list Atom, ~ In (fresh l) l).

Existing Instance Decidable_eq_Atom.
*)

Inductive Atom : Type :=
| fresh : list Atom -> Atom.

Fixpoint size (x : Atom) : nat :=
match x with
| fresh l => 1 + fold_right (fun h t => size h + t) 0 l
end.

Definition sizes l := 1 + fold_right (fun h t => size h + t) 0 l.

Require Import Lia.

Lemma In_size :
  forall (x : Atom) (l : list Atom),
    In x l -> size x < sizes l.
Proof.
  induction l as [| h t IH]; intros Hin; [easy |].
  destruct Hin as [-> | Hin]; cbn; [now lia |].
  unfold sizes in IH.
  specialize (IH Hin).
  now lia.
Qed.

Lemma fresh_spec :
  forall l : list Atom,
    ~ In (fresh l) l.
Proof.
  intros l Hin.
  apply In_size in Hin. cbn in Hin.
  now lia.
Qed.

Fixpoint eq_dec_Atom (x y : Atom) : {x = y} + {x <> y}.
Proof.
  refine
  (
    match x, y with
    | fresh lx, fresh ly =>
      match list_eq_dec eq_dec_Atom lx ly with
      | left eq => _
      | right neq => _
      end
    end
  ).
  - now left; f_equal.
  - now right; intros [=].
Defined.

#[export, refine] Instance Decidable_eq_Atom :
  forall x y : Atom, Decidable (x = y) :=
{
  Decidable_witness :=
    match eq_dec_Atom x y with
    | left _ => true
    | right _ => false
    end;
}.
Proof.
  now destruct (eq_dec_Atom x y).
Qed.

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

Lemma WfCtx_app_cons :
  forall (G1 G2 : Ctx) (x : Atom) (A : Ty),
    WfCtx (G2 ++ (x, A) :: G1) -> WfCtx (G2 ++ G1).
Proof.
  induction G2 as [| [y B] G2' IH]; cbn; intros.
  - now inversion H.
  - inversion H; subst.
    constructor.
    + now apply IH in H2.
    + rewrite map_app, !in_app_iff in *; cbn in *.
      now firstorder.
Qed.

Definition Binds (G : Ctx) (x : Atom) (A : Ty) : Prop :=
  In (x, A) G.

Inductive Typing : Ctx -> Tm -> Ty -> Prop :=
| Typing_fvar :
  forall (G : Ctx) (x : Atom) (A : Ty),
    WfCtx G ->
    Binds G x A ->
    Typing G x A
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

Lemma weakening_aux :
  forall (G1 G2 D : Ctx) (t : Tm) (A : Ty),
    Typing (G1 ++ G2) t A ->
    WfCtx (G1 ++ D ++ G2) ->
    Typing (G1 ++ D ++ G2) t A.
Proof.
  intros * Ht.
  remember (G1 ++ G2) as G.
  revert G1 G2 D HeqG.
  induction Ht; intros; subst.
  - constructor; [easy |].
    unfold Binds in *.
    rewrite !in_app_iff; rewrite in_app_iff in H0.
    now firstorder.
  - apply Typing_abs with (l ++ map fst G1 ++ map fst D ++ map fst G2).
    intros.
    rewrite !in_app_iff in H2.
    rewrite app_comm_cons.
    apply H0; [now firstorder | easy |].
    cbn; constructor; [easy |].
    rewrite !map_app, !in_app_iff.
    now firstorder.
  - apply Typing_app with A.
    + now apply IHHt1.
    + now apply IHHt2.
Qed.

Lemma weakening :
  forall (Γ Δ : Ctx) (t : Tm) (A : Ty),
    WfCtx (Δ ++ Γ) -> Typing Γ t A -> Typing (Δ ++ Γ) t A.
Proof.
  now intros; apply weakening_aux with (G1 := []); cbn.
Qed.

Lemma lc_Typing :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Typing Γ t A -> lc t.
Proof.
  induction 1; only 1, 3: now constructor.
  apply lc_abs with l.
  unfold open'.
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
  induction Δ.
  - now cbn; firstorder congruence.
  - inversion 1; subst.
    + now firstorder.
    + apply IHΔ in H0.
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
    assert (x <> y /\ ~ In y l) as [Hxy Hyl] by firstorder.
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

Inductive Step : Tm -> Tm -> Prop :=
| Step_FunComp :
  forall (t1 t2 : Tm),
    lc (abs t1) ->
    Value t2 ->
    Step (app (abs t1) t2) (t1 {{ 0 ~> t2 }})
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

Lemma open_subst' :
  forall (t : Tm) (i : nat) (x : Atom) (u : Tm),
    ~ In x (fv t) ->
      t {{ i ~> u }} = t {{ i ~> x }} [[ x := u ]].
Proof.
  induction t; cbn; intros i x u Hfresh.
  - now decide (x = a); firstorder congruence.
  - destruct (PeanoNat.Nat.eqb_spec i n); cbn; [| easy].
    now decide (x = x).
  - now erewrite IHt.
  - rewrite in_app_iff in Hfresh.
    now erewrite IHt1, IHt2; firstorder.
Qed.

Lemma preservation :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    Step t1 t2 ->
    Typing Γ t1 A ->
    Typing Γ t2 A.
Proof.
  intros * Hs.
  revert Γ A.
  induction Hs; intros Γ A Ht.
  - inversion Ht; subst.
    inversion H4; subst.
    replace (t1 {{ 0 ~> t2 }}) with
      (t1 {{ 0 ~> fresh (l ++ fv t1) }} [[ fresh (l ++ fv t1) := t2 ]]).
    + apply Typing_subst with A0; [| easy].
      apply H5.
      intro Hin.
      apply (fresh_spec (l ++ fv t1)).
      rewrite in_app_iff.
      now left.
    + rewrite <- open_subst'; [easy |].
      intro Hin.
      apply (fresh_spec (l ++ fv t1)).
      rewrite in_app_iff.
      now right.
  - inversion Ht; subst.
    econstructor; [| now apply H5].
    now apply IHHs.
  - inversion Ht; subst.
    econstructor; [now apply H3 |].
    now apply IHHs.
Restart.
  intros * Hs Ht.
  revert t2 Hs.
  induction Ht; intros; inversion Hs; subst.
  - inversion Ht1; subst.
    rewrite open_subst' with (x := fresh (l ++ fv t3)).
    + apply Typing_subst with A; [| easy].
      apply H4.
      intro Hin.
      apply (fresh_spec (l ++ fv t3)).
      rewrite in_app_iff.
      now left.
    + intro Hin.
      apply (fresh_spec (l ++ fv t3)).
      rewrite in_app_iff.
      now right.
  - econstructor; [| now apply Ht2].
    now apply IHHt1.
  - econstructor; [now apply Ht1 |].
    now apply IHHt2.
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
    + destruct (IHHt2 eq_refl) as [ [t2' Hlc2] | [t2' Hs2] ].
      * right; eexists.
        now constructor 1.
      * right; eexists.
        now constructor 3; eauto.
    + right; eexists.
      constructor 2; eauto.
      now apply lc_Typing in Ht2.
Qed.

Lemma lc_open :
  forall (t u : Tm),
    lc (abs t) -> lc u ->
      lc (t {{ 0 ~> u }}).
Proof.
  inversion 1; intros Hu.
  rewrite (open_subst' _ _ (fresh (l ++ fv t))).
  - apply lc_subst; [| easy].
    apply H1; intros Hin.
    apply fresh_spec with (l ++ fv t).
    rewrite in_app_iff.
    now left.
  - intros Hin.
    apply fresh_spec with (l ++ fv t).
    rewrite in_app_iff.
    now right.
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

