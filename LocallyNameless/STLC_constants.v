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

Inductive Const : Type :=
| unit       : Const
| elimUnit   : Const
| abort      : Const
| pair       : Const
| outl       : Const
| outr       : Const
| elimProd   : Const
| inl        : Const
| inr        : Const
| case       : Const
| zero       : Const
| succ       : Const
| rec        : Const.

Inductive Tm : Type :=
| fvar       : Atom -> Tm
| bvar       : nat -> Tm
| abs        : Tm -> Tm
| app        : Tm -> Tm -> Tm
| annot      : Tm -> Ty -> Tm
| const      : Const -> Tm.

Coercion fvar  : Atom >-> Tm.
Coercion bvar  : nat >-> Tm.
Coercion const : Const >-> Tm.

Fixpoint eq_dec_Tm (t u : Tm) : {t = u} + {t <> u}.
Proof.
  decide equality.
  - exact (eq_dec_Atom a a0).
  - exact (PeanoNat.Nat.eq_dec n n0).
  - exact (eq_dec_Ty t1 t3).
  - decide equality.
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
    | fvar a     => fvar a
    | bvar j     => if decide (i = j) then a else bvar j
    | abs t'     => abs (open t' (S i) a)
    | app t1 t2  => app (open t1 i a) (open t2 i a)
    | annot t' A => annot (open t' i a) A
    | const c    => const c
    end.

#[export] Instance Close_Tm : Close nat Atom Tm :=
  fix close (t : Tm) (i : nat) (a : Atom) : Tm :=
    match t with
    | fvar x     => if decide (a = x) then bvar i else fvar x
    | bvar n     => bvar n
    | abs t'     => abs (close t' (S i) a)
    | app t1 t2  => app (close t1 i a) (close t2 i a)
    | annot t' A => annot (close t' i a) A
    | const c    => const c
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
| fvar x     => [x]
| bvar _     => []
| abs t'     => fv t'
| app t1 t2  => fv t1 ++ fv t2
| annot t' A => fv t'
| const _    => []
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
| LocallyClosed'_const :
  forall (i : nat) (c : Const),
    LocallyClosed' i (const c).

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
| const _         => true
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
| const c         => const c
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
| const c         => const c
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
| lc_const :
  forall c : Const,
    lc (const c).

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
  - apply lc_abs with (x :: l).
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

Require Import Recdef.

Fixpoint size (t : Tm) : nat :=
match t with
| fvar x          => 1
| bvar n          => 1
| abs t'          => 1 + size t'
| app t1 t2       => 1 + size t1 + size t2
| annot t' A      => 1 + size t'
| const _         => 1
end.

Lemma size_open :
  forall (t : Tm) (i : nat) (a : Atom),
    size (t {{ i ~> a }}) = size t.
Proof.
  now induction t; cbn; intros; auto.
Qed.

Unset Guard Checking.
Function decide_lc' (a : Atom) (t : Tm) {struct t} : bool :=
match t with
| fvar x          => true
| bvar n          => false
| abs t'          => decide_lc' a (t' {{ 0 ~> a }})
| app t1 t2       => decide_lc' a t1 && decide_lc' a t2
| annot t' A      => decide_lc' a t'
| const _         => true
end.
(*
Proof.
  all: now cbn; intros; rewrite ?size_open; lia.
Defined.
*)
Set Guard Checking.

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

Lemma decide_lc'_spec :
  forall (a : Atom) (t : Tm),
    reflect (lc t) (decide_lc' a t).
Proof.
  intros a t.
  functional induction (decide_lc' a t);
    try (now try destruct IHb; try destruct IHb0; try destruct IHb1;
      cbn; constructor; [auto | inversion 1..]).
  - destruct IHb; constructor.
    + now unshelve eauto; exact [].
    + now inversion 1; subst; eauto.
Qed.

#[export, refine] Instance Decidable_lc :
  forall t : Tm, Decidable (lc t) :=
{
  Decidable_witness :=
    decide_lc' (fresh (fv t)) t;
}.
Proof.
  split.
  - induction t; cbn; try easy.
Abort.

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
  forall (Γ : Ctx) (A : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ elimUnit (TyFun (TyFun TyUnit A) (TyFun TyUnit A))
| Typing_abort :
  forall (Γ : Ctx) (A : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ abort (TyFun TyEmpty A)
| Typing_pair :
  forall (Γ : Ctx) (A B : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ pair (TyFun A (TyFun B (TyProd A B)))
| Typing_outl :
  forall (Γ : Ctx) (A B : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ outl (TyFun (TyProd A B) A)
| Typing_outr :
  forall (Γ : Ctx) (A B : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ outr (TyFun (TyProd A B) B)
| Typing_elimProd :
  forall (Γ : Ctx) (A B C : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ elimProd (TyFun (TyFun A (TyFun B C)) (TyFun (TyProd A B) C))
| Typing_inl :
  forall (Γ : Ctx) (A B : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ inl (TyFun A (TySum A B))
| Typing_inr :
  forall (Γ : Ctx) (A B : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ inr (TyFun B (TySum A B))
| Typing_case :
  forall (Γ : Ctx) (A B C : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ case (TyFun (TyFun A C) (TyFun (TyFun B C) (TyFun (TySum A B) C)))
| Typing_zero :
  forall (Γ : Ctx)
    (Hwf : WfCtx Γ),
    Typing Γ zero TyNat
| Typing_succ :
  forall (Γ : Ctx)
    (Hwf : WfCtx Γ),
    Typing Γ succ (TyFun TyNat TyNat)
| Typing_rec :
  forall (Γ : Ctx) (A : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ rec (TyFun A (TyFun (TyFun A A) (TyFun TyNat A))).

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

#[export] Hint Resolve lc_Typing : core.

(*
#[export] Hint Extern 1 (WfCtx (?Δ ++ ?Γ)) =>
  match goal with
  | H : WfCtx (Δ ++ _ :: Γ) |- _ => now apply WfCtx_app_cons in H
  end : core.
*)

#[export] Hint Resolve WfCtx_app_cons WfCtx_Typing : core.

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
  Time induction Ht; intros; subst; try now eauto.
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
  Time induction Ht; cbn; intros; subst; try now unshelve eauto.
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
| CbvValue_elimUnit : CbvValue elimUnit
| CbvValue_abort : CbvValue abort
| CbvValue_abort1 :
  forall (t' : Tm)
    (Hv1 : CbvValue t'),
    CbvValue (app abort t')
| CbvValue_pair : CbvValue pair
| CbvValue_pair1 :
  forall t1 : Tm,
    CbvValue t1 ->
    CbvValue (app pair t1)
| CbvValue_pair2 :
  forall t1 t2 : Tm,
    CbvValue t1 ->
    CbvValue t2 ->
    CbvValue (app (app pair t1) t2)
| CbvValue_outl : CbvValue outl
| CbvValue_outr : CbvValue outr
| CbvValue_elimProd : CbvValue elimProd
| CbvValue_elimProd1 :
  forall (t1 : Tm)
    (Hv1 : CbvValue t1),
    CbvValue (app elimProd t1)
| CbvValue_inl : CbvValue inl
| CbvValue_inl1 :
  forall v : Tm,
    CbvValue v ->
    CbvValue (app inl v)
| CbvValue_inr : CbvValue inr
| CbvValue_inr1 :
  forall v : Tm,
    CbvValue v ->
    CbvValue (app inr v)
| CbvValue_case : CbvValue case
| CbvValue_case1 :
  forall (t1 : Tm)
    (Hv1 : CbvValue t1),
    CbvValue (app case t1)
| CbvValue_case2 :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvValue (app (app case t1) t2)
| CbvValue_zero : CbvValue zero
| CbvValue_succ : CbvValue succ
| CbvValue_succ1 :
  forall (t' : Tm)
    (Hv' : CbvValue t'),
    CbvValue (app succ t')
| CbvValue_rec : CbvValue rec
| CbvValue_rec1 :
  forall (t1 : Tm)
    (Hv1 : CbvValue t1),
    CbvValue (app rec t1)
| CbvValue_rec2 :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvValue (app (app rec t1) t2).

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
| fvar _               => false
| bvar _               => false
| abs t'               => true
| app _ _              => false
| annot _ _            => false
| const _              => true
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
| CbvContraction_app_elimUnit'' :
  forall (t : Tm)
    (Hlc : lc t),
    CbvContraction (app elimUnit t) t
| CbvContraction_outl_pair :
  forall (v1 v2 : Tm)
    (Hv1 : CbvValue v1)
    (Hv2 : CbvValue v2),
    CbvContraction (app outl (app (app pair v1) v2)) v1
| CbvContraction_outr_pair :
  forall (v1 v2 : Tm)
    (Hv1 : CbvValue v1)
    (Hv2 : CbvValue v2),
    CbvContraction (app outr (app (app pair v1) v2)) v2
| CbvContraction_elimProd_pair :
  forall (v1 v2 t : Tm)
    (Hv1 : CbvValue v1)
    (Hv2 : CbvValue v2)
    (Hlc3 : lc t),
    CbvContraction (app (app elimProd t) (app (app pair v1) v2)) (app (app t v1) v2)
| CbvContraction_case_inl :
  forall (t1 t2 v : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv : CbvValue v),
    CbvContraction (app (app (app case t1) t2) (app inl v)) (app t1 v)
| CbvContraction_case_inr :
  forall (t1 t2 v : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv : CbvValue v),
    CbvContraction (app (app (app case t1) t2) (app inr v)) (app t2 v)
| CbvContraction_rec_zero :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvContraction (app (app (app rec t1) t2) zero) t1
| CbvContraction_rec_succ :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv3 : CbvValue t3),
    CbvContraction
      (app (app (app rec t1) t2) (app succ t3))
      (app t2 (app (app (app rec t1) t2) t3)).

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
  now inversion 1; subst; eauto 6.
Qed.

#[export] Hint Resolve lc_CbvContraction_l lc_CbvContraction_r : core.

Lemma CbvContraction_det :
  forall t t1 t2 : Tm,
    CbvContraction t t1 -> CbvContraction t t2 -> t1 = t2.
Proof.
  now induction 1; inversion 1; auto.
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
  - now inversion Ht1; subst; eauto.
  - easy.
  - now inversion Ht1; subst.
  - now inversion Ht1; inversion Ht2; inversion Ht0; subst; inversion Ht4; subst.
  - now inversion Ht1; inversion Ht2; inversion Ht0; subst; inversion Ht4; subst.
  - now inversion Ht1; inversion Ht2; inversion Ht0; subst; inversion Ht4;
      inversion Ht6; subst; eauto.
  - now inversion Ht1; inversion Ht2; subst; inversion Ht0; subst; inversion Ht4; subst;
      inversion Ht6; subst; eauto.
  - now inversion Ht1; inversion Ht2; subst; inversion Ht0; subst; inversion Ht4; subst;
      inversion Ht6; subst; eauto.
  - now inversion Ht1; inversion Ht2; subst; inversion Ht0; subst; inversion Ht4; subst.
  - now inversion Ht1; inversion Ht2; subst; inversion Ht0; subst; inversion Ht4; subst;
      inversion Ht6; subst; eauto.
Qed.

(*** *** Abortion *)

Inductive CbvAbortion : Tm -> Tm -> Prop :=
| CbvAbortion_app :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvAbortion (app (app abort t1) t2) (app abort t1)
| CbvAbortion_elimUnit'' :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvAbortion (app (app elimUnit t1) (app abort t2)) (app abort t2)
| CbvAbortion_outl :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbvAbortion (app outl (app abort t)) (app abort t)
| CbvAbortion_outr :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbvAbortion (app outr (app abort t)) (app abort t)
| CbvAbortion_elimProd :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvAbortion (app (app elimProd t1) (app abort t2)) (app abort t2)
| CbvAbortion_case :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbvAbortion (app (app (app case t1) t2) (app abort t3)) (app abort t3)
| CbvAbortion_rec :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbvAbortion (app (app (app rec t1) t2) (app abort t3)) (app abort t3).

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
  now inversion 1; subst; auto.
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
  now induction 1; inversion 1; subst; (econstructor; [now eauto |]);
    do 2 match goal with
    | H : Typing _ (const abort) _ |- _ => inversion H; subst
    | H : Typing _ (app (const abort) _) _ |- _ => inversion H; subst
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
    (Hv1 : CbvValue t1)
    (Hs2 : CbvStep t2 t2'),
    CbvStep (app t1 t2) (app t1 t2').

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
  induction 1; intros Hv; [| | now inversion Hv; subst; eauto..].
  - now eapply CbvContraction_not_CbvValue; eauto.
  - now eapply CbvAbortion_not_CbvValue; eauto.
Qed.

#[export] Hint Immediate lc_CbvStep_l lc_CbvStep_r CbvStep_not_CbvValue : core.

Lemma CbvContraction_CbvStep_det :
  forall t t1 t2 : Tm,
    CbvContraction t t1 -> CbvStep t t2 -> t1 = t2.
Proof.
  inversion 2; subst; intros.
  - now eapply CbvContraction_det; eauto.
  - now eapply CbvAbortion_not_CbvContraction in H; [| eauto].
  - inversion H; subst.
    + now apply CbvStep_not_CbvValue in H2; [| eauto].
    + now apply CbvStep_not_CbvValue in H2; [| eauto].
    + now apply CbvStep_not_CbvValue in H2; [| eauto].
    + now apply CbvStep_not_CbvValue in H2; [| eauto].
    + apply CbvStep_not_CbvValue in H2; [easy |]. admit.
    + inversion H2; subst; [easy.. | |].
    + admit.
    + now apply CbvStep_not_CbvValue in H2; [| eauto].
    + now apply CbvStep_not_CbvValue in H2; [| eauto].
  - 
    match goal with
    | Hs : CbvStep ?t ?t' |- _ =>
      apply CbvStep_not_CbvValue in Hs
    end. easy. inversion H; subst; eauto. eauto. inversion H2; 
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
  - now apply CbvStep_not_CbvValue in Hs1; auto.
  - now apply CbvStep_not_CbvValue in Hs1; auto.
  - now apply CbvStep_not_CbvValue in Hs1; auto.
  - now inversion H3.
  - now apply CbvStep_not_CbvValue in Hs1.
  - now apply CbvStep_not_CbvValue in H4.
  - now apply CbvStep_not_CbvValue in H3; auto.
  - now apply CbvStep_not_CbvValue in H3; auto.
  - now apply CbvStep_not_CbvValue in H3; auto.
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
    inversion Hv; subst; inversion Ht1; subst; only 2-4, 6-7, 11: now eauto 6.
    + now destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; eauto.
    + destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; [| now eauto].
      inversion Ht0; subst.
      inversion Ht2; subst; inversion Hv2; subst; try now eauto.
      * now inversion Ht4; inversion Ht6.
      * now inversion Ht4; inversion Ht6.
    + destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; [| now eauto].
      inversion Ht0; inversion Ht4; subst.
      inversion Ht2; subst; inversion Hv2; subst; try now eauto.
      * now inversion Ht2; subst; inversion Ht6; subst; inversion Ht10.
      * now inversion Ht2; subst; inversion Ht6; subst; inversion Ht10.
    + now destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; eauto.
    + easy.
    + destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; [| now eauto].
      now inversion Ht0; inversion Ht4; subst.
  - now right; eauto.
  - now left.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    inversion Hv; subst; inversion Ht; subst; [now eauto 6 | now eauto 6 | easy | easy | | | |].
    + now inversion Ht1.
    + now inversion Ht1.
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt1 eq_refl) as [ Hv | [t1' Hs1] ]; [| now eauto].
    inversion Hv; subst; inversion Ht1; subst; [now eauto.. | | | easy |].
    + now inversion Ht0.
    + now inversion Ht0.
    + now inversion Ht0.
  - now left.
  - now left; eauto.
  - now destruct (IHHt1 eq_refl) as [| [] ], (IHHt2 eq_refl) as [| [] ]; eauto.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    inversion Hv; subst; inversion Ht; subst; [now eauto.. | | | easy |].
    + now inversion Ht1.
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    inversion Hv; subst; inversion Ht; subst; [now eauto.. | | | easy |].
    + now inversion Ht1.
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto 6].
    inversion Hv; subst; inversion Ht; subst; [now eauto 6.. | | | easy |].
    + now inversion Ht1.
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt2 eq_refl) as [Hv | [t'' Hs] ]; [| now eauto 6].
    inversion Hv; subst; inversion Ht2; subst; [now eauto 6.. | | | easy |].
    + now inversion Ht0.
    + now inversion Ht0.
    + now inversion Ht0.
  - now left.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ].
    + inversion Hv; subst; inversion Ht; subst; try easy;
        [now eexists; do 2 econstructor; eauto.. | |].
      * now inversion Ht1.
      * now inversion Ht1.
    + now eexists; econstructor; eauto.
  - right; destruct (IHHt3 eq_refl) as [Hv3 | [] ]; [| now eauto].
    inversion Hv3; subst; inversion Ht3; subst; [now eauto 6.. | | | easy |].
    + now inversion Ht0.
    + now inversion Ht0.
    + now inversion Ht0.
  - now left.
  - now left.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - now left.
  - right; destruct (IHHt2 eq_refl) as [Hv1 | [t1' Hs1] ]; [| now eauto 6].
    inversion Hv1; subst; inversion Ht3; subst;
      [now eauto 7 | easy | easy | | now eauto 7.. | | easy |].
    + now inversion Ht0.
    + admit.
    + now inversion Ht0.
  - right; destruct (IHHt3 eq_refl) as [Hv1 | [t1' Hs1] ]; [| now eauto 6].
    inversion Hv1; subst; inversion Ht3; subst;
      [now eauto 7 | easy | easy | | now eauto 7.. | | easy |].
    + now inversion Ht0.
    + admit.
    + now inversion Ht0.
Admitted.

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
| CbnValue_elimProd'' : CbnValue elimProd''
| CbnValue_elimProd''1 :
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    CbnValue (app elimProd'' t1)
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
    CbnValue (succ t')
| CbnValue_rec'' : CbnValue rec''
| CbnValue_rec''1 :
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    CbnValue (app rec'' t1)
| CbnValue_rec''2 :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnValue (app (app rec'' t1) t2).

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
| CbnContraction_elimProd'_pair :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (elimProd' t1 (pair t2 t3)) (app (app t1 t2) t3)
| CbnContraction_elimProd''_pair :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (app (app elimProd'' t1) (pair t2 t3)) (app (app t1 t2) t3)
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
    CbnContraction (rec t1 t2 (succ t3)) (t2 {[ 0 ~> rec t1 t2 t3 ]})
| CbnContraction_rec'_zero :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction (rec' t1 t2 zero) t1
| CbnContraction_rec'_succ :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (rec' t1 t2 (succ t3)) (app t2 (rec' t1 t2 t3))
| CbnContraction_rec''_zero :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction (app (app (app rec'' t1) t2) zero) t1
| CbnContraction_rec''_succ :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (app (app (app rec'' t1) t2) (succ t3)) (app t2 (app (app (app rec'' t1) t2) t3)).

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
  now inversion 1; auto; eauto.
Qed.

#[export] Hint Resolve lc_CbnContraction_l lc_CbnContraction_r : core.

Lemma CbnContraction_det :
  forall t t1 t2 : Tm,
    CbnContraction t t1 -> CbnContraction t t2 -> t1 = t2.
Proof.
  now induction 1; inversion 1; auto.
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
  - now inversion Ht1; subst; eauto.
  - easy.
  - now eauto.
  - now eauto.
  - now inversion Ht1; subst.
  - now inversion Ht'.
  - now inversion Ht'.
  - now inversion Ht1; subst; eauto.
  - now inversion Ht2; subst; eauto.
  - now inversion Ht1; inversion Ht2; subst; inversion Ht0; subst; eauto.
  - now inversion Ht1; subst; eauto.
  - now inversion Ht1; subst; eauto.
  - now inversion Ht3; eauto.
  - now inversion Ht3; eauto.
  - now inversion Ht1; inversion Ht2; inversion Ht0; inversion Ht4; subst;
      inversion H15; subst; eauto.
  - now inversion Ht1; inversion Ht2; inversion Ht0; inversion Ht4; subst;
      inversion H15; subst; eauto.
  - easy.
  - now inversion Ht3; subst; eauto.
  - easy.
  - now inversion Ht3; subst; eauto.
  - now inversion Ht1; inversion Ht0; inversion Ht4.
  - now inversion Ht1; inversion Ht0; inversion Ht4.
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
| CbnAbortion_elimProd' :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnAbortion (elimProd' t1 (abort t2)) (abort t2)
| CbnAbortion_elimProd'' :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnAbortion (app (app elimProd'' t1) (abort t2)) (abort t2)
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
    CbnAbortion (rec t1 t2 (abort t3)) (abort t3)
| CbnAbortion_rec' :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnAbortion (rec' t1 t2 (abort t3)) (abort t3)
| CbnAbortion_rec'' :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnAbortion (app (app (app rec'' t1) t2) (abort t3)) (abort t3).

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
  now inversion 1; subst; auto.
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
| CbnStep_elimProd' :
  forall (t1 t2 t2' : Tm)
    (Hlc1 : lc t1)
    (Hs2 : CbnStep t2 t2'),
    CbnStep (elimProd' t1 t2) (elimProd' t1 t2')
| CbnStep_elimProd'' :
  forall (t1 t2 t2' : Tm)
    (Hlc1 : lc t1)
    (Hs2 : CbnStep t2 t2'),
    CbnStep (app (app elimProd'' t1) t2) (app (app elimProd'' t1) t2')
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
    CbnStep (rec t1 t2 t3) (rec t1 t2 t3')
| CbnStep_rec' :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : CbnStep t3 t3'),
    CbnStep (rec' t1 t2 t3) (rec' t1 t2 t3')
| CbnStep_rec'' :
  forall (t1 t2 t3 t3' : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hs3 : CbnStep t3 t3'),
    CbnStep (app (app (app rec'' t1) t2) t3) (app (app (app rec'' t1) t2) t3').

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
  induction 1; intros Hv; [| | now inversion Hv; subst; auto..].
  - now eapply CbnContraction_not_CbnValue; eauto.
  - now eapply CbnAbortion_not_CbnValue; eauto.
Qed.

#[export] Hint Resolve lc_CbnStep_l lc_CbnStep_r CbnStep_not_CbnValue : core.

Lemma CbnContraction_CbnStep_det :
  forall t t1 t2 : Tm,
    CbnContraction t t1 -> CbnStep t t2 -> t1 = t2.
Proof.
  inversion 2; subst; intros; [| |
    try match goal with
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
  - now apply CbnStep_not_CbnValue in Hs1; auto.
  - now apply CbnStep_not_CbnValue in Hs1; auto.
  - now apply CbnStep_not_CbnValue in H3; auto.
  - now apply CbnStep_not_CbnValue in H3; auto.
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
    inversion Hv; subst; inversion Ht1; subst; only 1-4, 6-7, 9: now eauto 6.
    + destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; [| now eauto].
      inversion Ht0; subst.
      inversion Ht2; subst; inversion Hv2; subst; try now eauto.
      * now inversion Ht4; inversion Ht6.
      * now inversion Ht4; inversion Ht6.
    + destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; [| now eauto].
      inversion Ht0; inversion Ht4; subst.
      inversion Ht2; subst; inversion Hv2; subst; try now eauto.
      * inversion Ht2; subst; inversion Ht6; subst; inversion Ht10.
      * inversion Ht2; subst; inversion Ht6; subst; inversion Ht10.
    + destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; [| now eauto].
      now inversion Ht0; inversion Ht4; subst.
  - now right; eauto.
  - now left.
  - now right; eauto 7.
  - now right; eauto 7.
  - now left.
  - now left; eauto.
  - now destruct (IHHt1 eq_refl) as [| [] ], (IHHt2 eq_refl) as [| [] ]; eauto.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    inversion Hv; subst; inversion Ht; subst; [now eauto.. | | easy |].
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    inversion Hv; subst; inversion Ht; subst; [now eauto.. | | easy |].
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto 6].
    inversion Hv; subst; inversion Ht; subst; [now eauto 6.. | | easy |].
    + now inversion Ht1.
    + now inversion Ht1.
  - right; destruct (IHHt2 eq_refl) as [Hv | [t'' Hs] ]; [| now eauto 6].
    inversion Hv; subst; inversion Ht2; subst; [now eauto 6.. | | easy |].
    + now inversion Ht0.
    + now inversion Ht0.
  - now left.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ].
    + inversion Hv; subst; inversion Ht; subst; try easy;
        [now eexists; do 2 econstructor; intros; try eapply lc_Typing; eauto.. | |].
      * now inversion Ht1.
      * now inversion Ht1.
    + now eexists; econstructor; intros; try eapply lc_Typing; eauto.
  - right; destruct (IHHt3 eq_refl) as [Hv3 | [] ]; [| now eauto].
    inversion Hv3; subst; inversion Ht3; subst; [now eauto 6.. | | easy |].
    + now inversion Ht0.
    + now inversion Ht0.
  - now left.
  - now left.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt2 eq_refl) as [Hv1 | [t1' Hs1] ].
    + inversion Hv1; subst; inversion Ht3; subst;
        [now eauto 7 | easy | easy | | now eauto 7.. | easy |].
      * now inversion Ht0.
      * now inversion Ht0.
    + now eexists; econstructor; eauto.
  - right; destruct (IHHt3 eq_refl) as [Hv1 | [t1' Hs1] ].
    + inversion Hv1; subst; inversion Ht3; subst;
        [now eauto 7 | easy | easy | | now eauto 7.. | easy |].
      * now inversion Ht0.
      * now inversion Ht0.
    + now eexists; econstructor; eauto.
Qed.
