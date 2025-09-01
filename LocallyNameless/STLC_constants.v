Require Import Bool.

From FormalSystems Require Export LocallyNameless.LocallyNameless.

(** * Types *)

Inductive Ty : Type :=
| TyFun   : Ty -> Ty -> Ty
| TyUnit  : Ty
| TyEmpty : Ty
| TyProd  : Ty -> Ty -> Ty
| TySum   : Ty -> Ty -> Ty
| TyNat   : Ty
| TyBool  : Ty
| TyList  : Ty -> Ty.

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

(*
Inductive Const0 : Type :=
| unit       : Const0
| zero       : Const0
| tt         : Const0
| ff         : Const0.

Inductive Const1 : Type :=
| abort      : Const1
| outl       : Const1
| outr       : Const1
| inl        : Const1
| inr        : Const1
| succ       : Const1.

Inductive Const2 : Type :=
| elimUnit   : Const2
| pair       : Const2
| elimProd   : Const2.

Inductive Const3 : Type :=
| case       : Const3
| rec        : Const3
| elimBool   : Const3.

Inductive Const : Type :=
| const0 : Const0 -> Const
| const1 : Const1 -> Const
| const2 : Const2 -> Const
| const3 : Const3 -> Const.

Coercion const0 : Const0 >-> Const.
Coercion const1 : Const1 >-> Const.
Coercion const2 : Const2 >-> Const.
Coercion const3 : Const3 >-> Const.
*)

Inductive Const : Type :=
| unit
| elimUnit
| abort
| pair
| outl
| outr
| elimProd
| inl
| inr
| case
| zero
| succ
| rec
| tt
| ff
| elimBool
| cnil
| ccons
| elimList.

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
    rewrite 1?IHHlc, 1?IHHlc1, 1?IHHlc2, 1?IHHlc3; f_equal; [| now lia..].
  now eapply (open_open _ 0 (S j)); auto.
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
  induction t; cbn; intros;
    [| now auto | now rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3..].
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
  induction t; cbn; intros;
    [| now auto | now rewrite 1?IHt, 1?IHt1, 1?IHt2, 1?IHt3..].
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
  destruct IHb; constructor.
  - now unshelve eauto; exact [].
  - now inversion 1; subst; eauto.
Qed.

#[export, refine] Instance Decidable_lc :
  forall t : Tm, Decidable (lc t) :=
{
  Decidable_witness :=
    decide_lc' (fresh (fv t)) t;
}.
Proof.
  now destruct (decide_lc'_spec (fresh (fv t)) t).
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
    Typing Γ rec (TyFun A (TyFun (TyFun A A) (TyFun TyNat A)))
| Typing_tt :
  forall (Γ : Ctx)
    (Hwf : WfCtx Γ),
    Typing Γ tt TyBool
| Typing_ff :
  forall (Γ : Ctx)
    (Hwf : WfCtx Γ),
    Typing Γ ff TyBool
| Typing_elimBool :
  forall (Γ : Ctx) (A : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ elimBool (TyFun A (TyFun A (TyFun TyBool A)))
| Typing_cnil :
  forall (Γ : Ctx) (A : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ cnil (TyList A)
| Typing_ccons :
  forall (Γ : Ctx) (A : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ ccons (TyFun A (TyFun (TyList A) (TyList A)))
| Typing_elimList :
  forall (Γ : Ctx) (A B : Ty)
    (Hwf : WfCtx Γ),
    Typing Γ elimList (TyFun B (TyFun (TyFun A (TyFun B B)) (TyFun (TyList A) B))).

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
| CbvValue_const :
  forall (c : Const),
    CbvValue c
| CbvValue_elimUnit1 :
  forall (t' : Tm)
    (Hv' : CbvValue t'),
    CbvValue (app elimUnit t')
| CbvValue_abort1 :
  forall (t' : Tm)
    (Hv1 : CbvValue t'),
    CbvValue (app abort t')
| CbvValue_pair1 :
  forall t1 : Tm,
    CbvValue t1 ->
    CbvValue (app pair t1)
| CbvValue_pair2 :
  forall t1 t2 : Tm,
    CbvValue t1 ->
    CbvValue t2 ->
    CbvValue (app (app pair t1) t2)
| CbvValue_elimProd1 :
  forall (t1 : Tm)
    (Hv1 : CbvValue t1),
    CbvValue (app elimProd t1)
| CbvValue_inl1 :
  forall v : Tm,
    CbvValue v ->
    CbvValue (app inl v)
| CbvValue_inr1 :
  forall v : Tm,
    CbvValue v ->
    CbvValue (app inr v)
| CbvValue_case1 :
  forall (t1 : Tm)
    (Hv1 : CbvValue t1),
    CbvValue (app case t1)
| CbvValue_case2 :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvValue (app (app case t1) t2)
| CbvValue_succ1 :
  forall (t' : Tm)
    (Hv' : CbvValue t'),
    CbvValue (app succ t')
| CbvValue_rec1 :
  forall (t1 : Tm)
    (Hv1 : CbvValue t1),
    CbvValue (app rec t1)
| CbvValue_rec2 :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvValue (app (app rec t1) t2)
| CbvValue_elimBool1 :
  forall (t1 : Tm)
    (Hv1 : CbvValue t1),
    CbvValue (app elimBool t1)
| CbvValue_elimBool2 :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvValue (app (app elimBool t1) t2)
| CbvValue_ccons1 :
  forall (t1 : Tm)
    (Hv1 : CbvValue t1),
    CbvValue (app ccons t1)
| CbvValue_ccons2 :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvValue (app (app ccons t1) t2)
| CbvValue_elimList1 :
  forall (t1 : Tm)
    (Hv1 : CbvValue t1),
    CbvValue (app elimList t1)
| CbvValue_elimList2 :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvValue (app (app elimList t1) t2).

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
| fvar _                   => false
| bvar _                   => false
| abs t'                   => decide_lc' (fresh (fv t)) t
| annot _ _                => false
| const _                  => true
| app elimUnit t'          => cbvValue t'
| app abort t'             => cbvValue t'
| app pair t1              => cbvValue t1
| app (app pair t1) t2     => cbvValue t1 && cbvValue t2
| app elimProd t1          => cbvValue t1
| app inl t'               => cbvValue t'
| app inr t'               => cbvValue t'
| app case t1              => cbvValue t1
| app (app case t1) t2     => cbvValue t1 && cbvValue t2
| app succ t'              => cbvValue t'
| app rec t1               => cbvValue t1
| app (app rec t1) t2      => cbvValue t1 && cbvValue t2
| app elimBool t1          => cbvValue t1
| app (app elimBool t1) t2 => cbvValue t1 && cbvValue t2
| app ccons t1             => cbvValue t1
| app (app ccons t1) t2    => cbvValue t1 && cbvValue t2
| app elimList t1          => cbvValue t1
| app (app elimList t1) t2 => cbvValue t1 && cbvValue t2
| app _ _                  => false
end.

#[export, refine] Instance Decidable_CbvValue :
  forall t : Tm, Decidable (CbvValue t) :=
{
  Decidable_witness := cbvValue t;
}.
Proof.
  split.
  - induction t; inversion 1; auto.
    + destruct (decide_lc'_spec (fresh (fv t)) (t {{ 0 ~> fresh (fv t) }})); [| easy].
      now unshelve eauto; exact [].
    + destruct t1; try easy; [| now destruct c; eauto].
      destruct t1_1; try easy.
      destruct c; try easy;
        apply andb_prop in H1 as []; cbn in *;
        specialize (IHt1 H0); inversion IHt1; eauto.
  - induction 1; cbn; auto; [| now rewrite andb_true_iff..].
    now destruct (decide_lc'_spec (fresh (fv t')) (t' {{ 0 ~> fresh (fv t') }})); [| eauto].
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
| CbvContraction_elimUnit''_unit :
  forall (t : Tm)
    (Hv : CbvValue t),
    CbvContraction (app (app elimUnit t) unit) (app t unit)
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
    (Hv3 : CbvValue t),
    CbvContraction (app (app elimProd t) (app (app pair v1) v2)) (app (app t v1) v2)
| CbvContraction_case_inl :
  forall (t1 t2 t3 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2)
    (Hv3 : CbvValue t3),
    CbvContraction (app (app (app case t1) t2) (app inl t3)) (app t1 t3)
| CbvContraction_case_inr :
  forall (t1 t2 t3 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2)
    (Hv3 : CbvValue t3),
    CbvContraction (app (app (app case t1) t2) (app inr t3)) (app t2 t3)
| CbvContraction_rec_zero :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvContraction (app (app (app rec t1) t2) zero) t1
| CbvContraction_rec_succ :
  forall (t1 t2 t3 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2)
    (Hv3 : CbvValue t3),
    CbvContraction
      (app (app (app rec t1) t2) (app succ t3))
      (app t2 (app (app (app rec t1) t2) t3))
| CbvContraction_elimBool_tt :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvContraction
      (app (app (app elimBool t1) t2) tt) t1
| CbvContraction_elimBool_ff :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvContraction
      (app (app (app elimBool t1) t2) ff) t2
| CbvContraction_elimList_cnil :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvContraction (app (app (app elimList t1) t2) cnil) t1
| CbvContraction_elimList_ccons :
  forall (t1 t2 t3 t4 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2)
    (Hv3 : CbvValue t3)
    (Hv4 : CbvValue t4),
    CbvContraction
      (app (app (app elimList t1) t2) (app (app ccons t3) t4))
      (app (app t2 t3) (app (app (app elimList t1) t2) t4)).

#[export] Hint Constructors CbvContraction : core.

Lemma lc_CbvContraction_l :
  forall t t' : Tm,
    CbvContraction t t' -> lc t.
Proof.
  now inversion 1; eauto 6.
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

Lemma preservation_CbvContraction :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    CbvContraction t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  now inversion 1; subst; intros;
    repeat match goal with
    | H : Typing _ ?t _ |- _ => tryif is_var t then fail else (inversion H; subst; clear H)
    end; eauto 7.
Qed.

(*** *** Abortion *)

Inductive CbvAbortion : Tm -> Tm -> Prop :=
| CbvAbortion_app :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvAbortion (app (app abort t1) t2) (app abort t1)
| CbvAbortion_elimUnit :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvAbortion (app (app elimUnit t1) (app abort t2)) (app abort t2)
| CbvAbortion_outl :
  forall (t : Tm)
    (Hv' : CbvValue  t),
    CbvAbortion (app outl (app abort t)) (app abort t)
| CbvAbortion_outr :
  forall (t : Tm)
    (Hv' : CbvValue  t),
    CbvAbortion (app outr (app abort t)) (app abort t)
| CbvAbortion_elimProd :
  forall (t1 t2 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2),
    CbvAbortion (app (app elimProd t1) (app abort t2)) (app abort t2)
| CbvAbortion_case :
  forall (t1 t2 t3 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2)
    (Hv3 : CbvValue t3),
    CbvAbortion (app (app (app case t1) t2) (app abort t3)) (app abort t3)
| CbvAbortion_rec :
  forall (t1 t2 t3 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2)
    (Hv3 : CbvValue t3),
    CbvAbortion (app (app (app rec t1) t2) (app abort t3)) (app abort t3)
| CbvAbortion_elimBool :
  forall (t1 t2 t3 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2)
    (Hv3 : CbvValue t3),
    CbvAbortion (app (app (app elimBool t1) t2) (app abort t3)) (app abort t3)
| CbvAbortion_elimList :
  forall (t1 t2 t3 : Tm)
    (Hv1 : CbvValue t1)
    (Hv2 : CbvValue t2)
    (Hv3 : CbvValue t3),
    CbvAbortion (app (app (app elimList t1) t2) (app abort t3)) (app abort t3).

#[export] Hint Constructors CbvAbortion : core.

Lemma lc_CbvAbortion_l :
  forall t t' : Tm,
    CbvAbortion t t' -> lc t.
Proof.
  now inversion 1; auto.
Qed.

Lemma lc_CbvAbortion_r :
  forall t t' : Tm,
    CbvAbortion t t' -> lc t'.
Proof.
  now inversion 1; auto.
Qed.

#[export] Hint Immediate lc_CbvAbortion_l lc_CbvAbortion_r : core.

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

Lemma preservation_CbvAbortion :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    CbvAbortion t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  now do 2 inversion 1; subst;
    do 2 match goal with
    | H : Typing _ (const abort) _ |- _ => inversion H; subst
    | H : Typing _ (app (const abort) _) _ |- _ => inversion H; subst
    end; eauto.
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
  forall (t1 t2 t2' : Tm)
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

#[export] Hint Immediate lc_CbvStep_l lc_CbvStep_r : core.

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

Lemma CbvStep_det :
  forall t t1 t2 : Tm,
    CbvStep t t1 -> CbvStep t t2 -> t1 = t2.
Proof.
  intros t t1 t2 Hs1 Hs2; revert t2 Hs2.
  induction Hs1; intros; inversion Hs2; subst; clear Hs2;
    try match goal with
    | H : CbvContraction _ _ |- _ =>
      now eapply CbvContraction_CbvStep_det in H; eauto
    | H : CbvAbortion _ _ |- _ =>
      now eapply CbvAbortion_CbvStep_det in H; eauto
    end; try firstorder congruence.
  - now apply CbvStep_not_CbvValue in Hs1; auto.
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
  induction Ht; subst; try now eauto 6 using lc_Typing.
  destruct (IHHt1 eq_refl) as [ Hv1 | [t1' Hs1] ]; [| now eauto].
  destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; [| now eauto].
  Time now inversion Hv1; subst;
    repeat (auto; match goal with
    | H : Typing _ (const _) _ |- _ => inversion H; subst; clear H
    | H : Typing _ (app _ _) _ |- _ => inversion H; subst; clear H
    end); eauto;
  match goal with
  | |- context [CbvValue (app _ ?t)] =>
    repeat match goal with
    | Hv : CbvValue t, Ht : Typing [] t _ |- _ =>
      inversion Hv; subst; inversion Ht; subst
    | H : Typing _ (const _) _ |- _ => inversion H; subst; clear H
    | H : Typing _ (app _ _) _ |- _ => inversion H; subst; clear H
    end
  end; eauto.
Qed.

(** ** CBN *)

(** *** Values *)

Inductive CbnValue : Tm -> Prop :=
| CbnValue_abs  :
  forall (t' : Tm) (l : list Atom)
    (Hlc' : forall x : Atom, x # l -> lc (t' {{ 0 ~> x }})),
    CbnValue (abs t')
| CbnValue_const :
  forall (c : Const),
    CbnValue c
| CbnValue_elimUnit1 :
  forall (t' : Tm)
    (Hlc' : lc t'),
    CbnValue (app elimUnit t')
| CbnValue_abort1 :
  forall (t' : Tm)
    (Hlc1 : lc t'),
    CbnValue (app abort t')
| CbnValue_pair1 :
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    CbnValue (app pair t1)
| CbnValue_pair2 :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnValue (app (app pair t1) t2)
| CbnValue_elimProd1 :
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    CbnValue (app elimProd t1)
| CbnValue_inl1 :
  forall (t' : Tm)
    (Hlc' : lc t'),
    CbnValue (app inl t')
| CbnValue_inr1 :
  forall (t' : Tm)
    (Hlc' : lc t'),
    CbnValue (app inr t')
| CbnValue_case1 :
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    CbnValue (app case t1)
| CbnValue_case2 :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnValue (app (app case t1) t2)
| CbnValue_succ1 :
  forall (t' : Tm)
    (Hlc' : lc t'),
    CbnValue (app succ t')
| CbnValue_rec1 :
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    CbnValue (app rec t1)
| CbnValue_rec2 :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnValue (app (app rec t1) t2)
| CbnValue_elimBool1 :
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    CbnValue (app elimBool t1)
| CbnValue_elimBool2 :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnValue (app (app elimBool t1) t2)
| CbnValue_ccons1 :
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    CbnValue (app ccons t1)
| CbnValue_ccons2 :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnValue (app (app ccons t1) t2)
| CbnValue_elimList1 :
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    CbnValue (app elimList t1)
| CbnValue_elimList2 :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnValue (app (app elimList t1) t2).

#[export] Hint Constructors CbnValue : core.

Lemma lc_CbnValue :
  forall t : Tm,
    CbnValue t -> lc t.
Proof.
  now induction 1; eauto.
Qed.

#[export] Hint Immediate lc_CbnValue : core.

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
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    CbnContraction (app (app elimUnit t1) unit) (app t1 unit)
| CbnContraction_outl_pair :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction (app outl (app (app pair t1) t2)) t1
| CbnContraction_outr_pair :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction (app outr (app (app pair t1) t2)) t2
| CbnContraction_elimProd_pair :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (app (app elimProd t1) (app (app pair t2) t3)) (app (app t1 t2) t3)
| CbnContraction_case_inl :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (app (app (app case t1) t2) (app inl t3)) (app t1 t3)
| CbnContraction_case_inr :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction (app (app (app case t1) t2) (app inr t3)) (app t2 t3)
| CbnContraction_rec_zero :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction (app (app (app rec t1) t2) zero) t1
| CbnContraction_rec_succ :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnContraction
      (app (app (app rec t1) t2) (app succ t3))
      (app t2 (app (app (app rec t1) t2) t3))
| CbnContraction_elimBool_tt :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction
      (app (app (app elimBool t1) t2) tt) t1
| CbnContraction_elimBool_ff :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction
      (app (app (app elimBool t1) t2) ff) t2
| CbnContraction_elimList_cnil :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnContraction (app (app (app elimList t1) t2) cnil) t1
| CbnContraction_elimList_ccons :
  forall (t1 t2 t3 t4 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3)
    (Hlc4 : lc t4),
    CbnContraction
      (app (app (app elimList t1) t2) (app (app ccons t3) t4))
      (app (app t2 t3) (app (app (app elimList t1) t2) t4)).

#[export] Hint Constructors CbnContraction : core.

Lemma lc_CbnContraction_l :
  forall t t' : Tm,
    CbnContraction t t' -> lc t.
Proof.
  now inversion 1; eauto 6.
Qed.

Lemma lc_CbnContraction_r :
  forall t t' : Tm,
    CbnContraction t t' -> lc t'.
Proof.
  now inversion 1; eauto 6.
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

Lemma preservation_CbnContraction :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    CbnContraction t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  now inversion 1; subst; intros;
    repeat match goal with
    | H : Typing _ ?t _ |- _ => tryif is_var t then fail else (inversion H; subst; clear H)
    end; eauto 7.
Qed.

(*** *** Abortion *)

Inductive CbnAbortion : Tm -> Tm -> Prop :=
| CbnAbortion_app :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnAbortion (app (app abort t1) t2) (app abort t1)
| CbnAbortion_elimUnit :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnAbortion (app (app elimUnit t1) (app abort t2)) (app abort t2)
| CbnAbortion_outl :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbnAbortion (app outl (app abort t)) (app abort t)
| CbnAbortion_outr :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbnAbortion (app outr (app abort t)) (app abort t)
| CbnAbortion_elimProd :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbnAbortion (app (app elimProd t1) (app abort t2)) (app abort t2)
| CbnAbortion_case :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnAbortion (app (app (app case t1) t2) (app abort t3)) (app abort t3)
| CbnAbortion_rec :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnAbortion (app (app (app rec t1) t2) (app abort t3)) (app abort t3)
| CbnAbortion_elimBool :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnAbortion (app (app (app elimBool t1) t2) (app abort t3)) (app abort t3)
| CbnAbortion_elimList :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbnAbortion (app (app (app elimList t1) t2) (app abort t3)) (app abort t3).

#[export] Hint Constructors CbnAbortion : core.

Lemma lc_CbnAbortion_l :
  forall t t' : Tm,
    CbnAbortion t t' -> lc t.
Proof.
  now inversion 1; auto.
Qed.

Lemma lc_CbnAbortion_r :
  forall t t' : Tm,
    CbnAbortion t t' -> lc t'.
Proof.
  now inversion 1; auto.
Qed.

#[export] Hint Immediate lc_CbnAbortion_l lc_CbnAbortion_r : core.

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

Lemma preservation_CbnAbortion :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    CbnAbortion t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  now do 2 inversion 1; subst;
    do 2 match goal with
    | H : Typing _ (const abort) _ |- _ => inversion H; subst
    | H : Typing _ (app (const abort) _) _ |- _ => inversion H; subst
    end; eauto.
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
    CbnStep (app t1 t2) (app t1' t2).

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

#[export] Hint Immediate lc_CbnStep_l lc_CbnStep_r : core.

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

Lemma CbnStep_det :
  forall t t1 t2 : Tm,
    CbnStep t t1 -> CbnStep t t2 -> t1 = t2.
Proof.
  intros t t1 t2 Hs1 Hs2; revert t2 Hs2.
  now induction Hs1; intros; inversion Hs2; subst; clear Hs2;
    repeat match goal with
    | H : CbnContraction _ _ |- _  => now eapply CbnContraction_CbnStep_det in H; eauto
    | H : CbnAbortion _ _ |- _     => now eapply CbnAbortion_CbnStep_det in H; eauto
    | H : CbnStep (const _) _ |- _ => now apply CbnStep_not_CbnValue in H
    | H : CbnStep (app _ _) _ |- _ => now apply CbnStep_not_CbnValue in H; auto
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
  induction Ht; subst; try now eauto 6 using lc_Typing.
  destruct (IHHt1 eq_refl) as [ Hv1 | [t1' Hs1] ]; [| now eauto].
  inversion Hv1; subst;
    repeat (auto; match goal with
    | H : Typing _ (const _) _ |- _ => inversion H; subst; clear H
    | H : Typing _ (app _ _) _ |- _ => inversion H; subst; clear H
    end); eauto;
  match goal with
  | |- context [CbnValue (app _ ?t)] =>
    repeat match goal with
    | Hv : CbnValue t, Ht : Typing [] t _ |- _ =>
      inversion Hv; subst; inversion Ht; subst
    | H : Typing _ (const _) _ |- _ => inversion H; subst; clear H
    | H : Typing _ (app _ _) _ |- _ => inversion H; subst; clear H
    end
  end; eauto 7.
  - destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ].
    inversion Hv2; subst; inversion Ht2; subst; inversion Ht1; subst; eauto.
    + inversion Ht3.
    + inversion Ht3.
    + inversion Ht3.
    + right. eexists.
    admit.
Admitted.

Lemma Cbv_Cbn :
  forall (t1 t2 : Tm),
    CbvAbortion t1 t2 <-> CbnAbortion t1 t2.
Proof.
  split.
  - inversion 1; eauto.
  - inversion 1; eauto.
    + constructor.
Admitted.

(** ** Full reduction *)

(** Normal and neutral forms *)

Inductive Nf : Tm -> Prop :=
| Nf_Ne :
  forall (t' : Tm),
    Ne t' -> Nf t'
| Nf_abs  :
  forall (t' : Tm) (l : list Atom)
    (Hnf' : forall x : Atom, x # l -> Nf (t' {{ 0 ~> x }})),
    Nf (abs t')
| Nf_const :
  forall (c : Const),
    Nf c
| Nf_elimUnit1 :
  forall (t' : Tm)
    (Hnf' : Nf t'),
    Nf (app elimUnit t')
| Nf_abort1 :
  forall (t' : Tm)
    (Hnf1 : Nf t'),
    Nf (app abort t')
| Nf_pair1 :
  forall t1 : Tm,
    Nf t1 ->
    Nf (app pair t1)
| Nf_pair2 :
  forall (t1 t2 : Tm)
    (Hnf1 : Nf t1)
    (Hnf2 : Nf t2),
    Nf (app (app pair t1) t2)
| Nf_elimProd1 :
  forall (t1 : Tm)
    (Hnf1 : Nf t1),
    Nf (app elimProd t1)
| Nf_inl1 :
  forall (t1 : Tm)
    (Hnf1 : Nf t1),
    Nf (app inl t1)
| Nf_inr1 :
  forall (t1 : Tm)
    (Hnf1 : Nf t1),
    Nf (app inr t1)
| Nf_case1 :
  forall (t1 : Tm)
    (Hnf1 : Nf t1),
    Nf (app case t1)
| Nf_case2 :
  forall (t1 t2 : Tm)
    (Hnf1 : Nf t1)
    (Hnf2 : Nf t2),
    Nf (app (app case t1) t2)
| Nf_succ1 :
  forall (t' : Tm)
    (Hnf' : Nf t'),
    Nf (app succ t')
| Nf_rec1 :
  forall (t1 : Tm)
    (Hnf1 : Nf t1),
    Nf (app rec t1)
| Nf_rec2 :
  forall (t1 t2 : Tm)
    (Hnf1 : Nf t1)
    (Hnf2 : Nf t2),
    Nf (app (app rec t1) t2)
| Nf_elimBool1 :
  forall (t1 : Tm)
    (Hnf1 : Nf t1),
    Nf (app elimBool t1)
| Nf_elimBool2 :
  forall (t1 t2 : Tm)
    (Hnf1 : Nf t1)
    (Hnf2 : Nf t2),
    Nf (app (app elimBool t1) t2)
| Nf_ccons1 :
  forall (t1 : Tm)
    (Hnf1 : Nf t1),
    Nf (app ccons t1)
| Nf_ccons2 :
  forall (t1 t2 : Tm)
    (Hnf1 : Nf t1)
    (Hnf2 : Nf t2),
    Nf (app (app ccons t1) t2)
| Nf_elimList1 :
  forall (t1 : Tm)
    (Hnf1 : Nf t1),
    Nf (app elimList t1)
| Nf_elimList2 :
  forall (t1 t2 : Tm)
    (Hnf1 : Nf t1)
    (Hnf2 : Nf t2),
    Nf (app (app elimList t1) t2)

with Ne : Tm -> Prop :=
| Ne_fvar :
  forall (x : Atom),
    Ne x
| Ne_app  :
  forall (t1 t2 : Tm)
    (Hne1 : Ne t1)
    (Hnf2 : Nf t2),
    Ne (app t1 t2)
| Ne_elimUnit :
  forall (t1 t2 : Tm)
    (Hnf1 : Nf t1)
    (Hne2 : Ne t2),
    Ne (app (app elimUnit t1) t2)
| Ne_abort :
  forall (t1 : Tm)
    (Hne1 : Ne t1),
    Ne (app abort t1)
| Ne_elimProd :
  forall (t1 t2 : Tm)
    (Hnf1 : Nf t1)
    (Hne2 : Ne t2),
    Ne (app (app elimProd t1) t2)
| Ne_case :
  forall (t1 t2 t3 : Tm)
    (Hnf1 : Nf t1)
    (Hnf2 : Nf t2)
    (Hne3 : Ne t3),
    Ne (app (app (app case t1) t2) t3)
| Ne_rec :
  forall (t1 t2 t3 : Tm)
    (Hnf1 : Nf t1)
    (Hnf2 : Nf t2)
    (Hne3 : Ne t3),
    Ne (app (app (app rec t1) t2) t3)
| Ne_elimBool :
  forall (t1 t2 t3 : Tm)
    (Hnf1 : Nf t1)
    (Hnf2 : Nf t2)
    (Hne3 : Ne t3),
    Ne (app (app (app elimBool t1) t2) t3)
| Ne_elimList :
  forall (t1 t2 t3 : Tm)
    (Hnf1 : Nf t1)
    (Hnf2 : Nf t2)
    (Hne3 : Ne t3),
    Ne (app (app (app elimList t1) t2) t3).

#[export] Hint Constructors Nf Ne : core.

Lemma lc_Nf :
  forall t : Tm,
    Nf t -> lc t

with lc_Ne :
  forall t : Tm,
    Ne t -> lc t.
Proof.
  - destruct 1; [| | now repeat constructor; auto..].
    + now apply lc_Ne.
    + apply lc_abs with l; intros x Hx.
      now apply lc_Nf, Hnf'.
  - destruct 1; repeat constructor; (try now apply lc_Ne); auto.
Qed.

#[export] Hint Resolve lc_Nf : core.

(** ** Contraction *)

Inductive Contraction : Tm -> Tm -> Prop :=
| Contraction_app_abs :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : forall x : Atom, x # l -> lc (t1 {{ 0 ~> x }}))
    (Hlc2 : lc t2),
    Contraction (app (abs t1) t2) (t1 {[ 0 ~> t2 ]})
| Contraction_annot :
  forall (t : Tm) (A : Ty)
    (Hlc : lc t),
    Contraction (annot t A) t
| Contraction_elimUnit :
  forall (t1 : Tm)
    (Hlc1 : lc t1),
    Contraction (app (app elimUnit t1) unit) (app t1 unit)
| Contraction_outl_pair :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    Contraction (app outl (app (app pair t1) t2)) t1
| Contraction_outr_pair :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    Contraction (app outr (app (app pair t1) t2)) t2
| Contraction_elimProd_pair :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    Contraction (app (app elimProd t1) (app (app pair t2) t3)) (app (app t1 t2) t3)
| Contraction_case_inl :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    Contraction (app (app (app case t1) t2) (app inl t3)) (app t1 t3)
| Contraction_case_inr :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    Contraction (app (app (app case t1) t2) (app inr t3)) (app t2 t3)
| Contraction_rec_zero :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    Contraction (app (app (app rec t1) t2) zero) t1
| Contraction_rec_succ :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    Contraction
      (app (app (app rec t1) t2) (app succ t3))
      (app t2 (app (app (app rec t1) t2) t3))
| Contraction_elimBool_tt :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    Contraction
      (app (app (app elimBool t1) t2) tt) t1
| Contraction_elimBool_ff :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    Contraction
      (app (app (app elimBool t1) t2) ff) t2
| Contraction_elimList_cnil :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    Contraction (app (app (app elimList t1) t2) cnil) t1
| Contraction_elimList_ccons :
  forall (t1 t2 t3 t4 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3)
    (Hlc4 : lc t4),
    Contraction
      (app (app (app elimList t1) t2) (app (app ccons t3) t4))
      (app (app t2 t3) (app (app (app elimList t1) t2) t4)).

#[export] Hint Constructors Contraction : core.

Lemma lc_Contraction_l :
  forall t t' : Tm,
    Contraction t t' -> lc t.
Proof.
  now inversion 1; eauto 6.
Qed.

Lemma lc_Contraction_r :
  forall t t' : Tm,
    Contraction t t' -> lc t'.
Proof.
  now inversion 1; eauto 6.
Qed.

#[export] Hint Immediate lc_Contraction_l lc_Contraction_r : core.

Lemma Contraction_det :
  forall t t1 t2 : Tm,
    Contraction t t1 -> Contraction t t2 -> t1 = t2.
Proof.
  now do 2 inversion 1.
Qed.

Lemma Contraction_not_Nf :
  forall t t' : Tm,
    Contraction t t' -> Nf t -> False.
Proof.
  inversion 1; subst; intros;
  repeat match goal with
  | Hnf : Nf ?t |- _ => tryif is_var t then fail else inversion Hnf; subst; clear Hnf
  | Hne : Ne ?t |- _ => tryif is_var t then fail else inversion Hne; subst; clear Hne
  end.
Qed.

Lemma preservation_Contraction :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    Contraction t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  now inversion 1; subst; intros;
    repeat match goal with
    | H : Typing _ ?t _ |- _ => tryif is_var t then fail else (inversion H; subst; clear H)
    end; eauto 7.
Qed.

(** ** Reduction *)

Inductive Step : Tm -> Tm -> Prop :=
| Step_Contraction :
  forall t t' : Tm,
    Contraction t t' ->
    Step t t'
| Step_abs :
  forall (t t' : Tm) (l : list Atom)
    (Hs : forall x : Atom, x # l -> Step (t {{ 0 ~> x }}) (t' {{ 0 ~> x }})),
    Step (abs t) (abs t')
| Step_app_l :
  forall (t1 t1' t2 : Tm),
    lc t2 ->
    Step t1 t1' ->
    Step (app t1 t2) (app t1' t2)
| Step_app_r :
  forall (t1 t2 t2' : Tm),
    lc t1 ->
    Step t2 t2' ->
    Step (app t1 t2) (app t1 t2').

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

Lemma Step_not_Nf :
  forall t t' : Tm,
    Step t t' -> Nf t -> False

with Step_not_Ne :
  forall t t' : Tm,
    Step t t' -> Ne t -> False.
Proof.
  - destruct 1; intros Hnf.
    + now eapply Contraction_not_Nf; eauto.
    + inversion Hnf; subst; [now inversion H |].
      pose (x := fresh (l ++ l0)).
      now apply (Step_not_Nf (t {{ 0 ~> x }}) (t' {{ 0 ~> x }})); auto.
    + apply Step_not_Nf in H0; [easy |]; clear Step_not_Nf Step_not_Ne.
      inversion Hnf; subst; try now eauto.
      now inversion H1; subst; auto.
    + apply Step_not_Nf in H0; [easy |]; clear Step_not_Nf Step_not_Ne.
      inversion Hnf; subst; try now eauto.
      now inversion H1; subst; auto.
  - destruct 1; intros Hnf.
    + now eapply Contraction_not_Nf; eauto.
    + now inversion Hnf.
    + now inversion Hnf; subst; eauto.
    + now inversion Hnf; subst; eauto.
Qed.

#[export] Hint Immediate lc_Step_l lc_Step_r : core.

(** ** Progress and preservation *)

Lemma preservation_ :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    Step t1 t2 ->
    Typing Γ t1 A ->
    Typing Γ t2 A.
Proof.
  intros Γ t1 t2 A Hstep; revert Γ A.
  induction Hstep; intros Γ A; [| | now inversion 1; subst; eauto..].
  - now eapply preservation_Contraction.
  - inversion 1; subst.
    now apply Typing_abs with (l ++ l0); intros x Hx; auto.
Qed.

Lemma progress_ :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Typing Γ t A ->
      Nf t \/ exists t' : Tm, Step t t'.
Proof.
  intros Γ t A Ht.
  induction Ht; subst; try now eauto 6.
  - destruct (H (fresh (l ++ fv t')) ltac:(auto)) as [| [t'' IH] ].
    + left; apply Nf_abs with (l ++ fv (t')); intros x Hx.
      destruct (H x ltac:(auto)) as [| [t'' IH] ]; [easy |].
      apply Step_not_Nf in IH; [easy |].
      admit.
    + right; exists (abs t'').
      apply Step_abs with l; intros x Hx.
      admit.
  - destruct IHHt1 as [| [t1' IH1] ]; [| now eauto].
    destruct IHHt2 as [| [t2' IH2] ]; [| now eauto].
(*
    inversion H; subst; [now destruct IHHt2 as [| [t'' IH] ]; eauto.. | |].
    + right; exists (t' {[ 0 ~> t2 ]}); constructor.
      constructor 1 with l; [| now eauto].
      intros x Hx.
      apply lc_Typing in Ht1.
      now inversion Ht1; eauto.
    + inversion H; subst. Focus 2.
  - right. eauto. destruct IHHt as [| [t1' IH1] ].
    inversion H; subst; [now destruct IHHt2 as [| [t'' IH] ]; eauto |].
    right; exists (t' {[ 0 ~> t2 ]}); constructor.
    constructor 1 with l; [| now eauto].
    intros x Hx.
    apply lc_Typing in Ht1.
    now inversion Ht1; eauto.
*)

  inversion H; subst; clear H;
    repeat (auto; match goal with
    | H : Typing _ (const _) _ |- _ => inversion H; subst; clear H
    | H : Typing _ (app _ _) _ |- _ => inversion H; subst; clear H
    end); eauto 7.
  match goal with
  | |- context [Nf (app _ ?t)] =>
    repeat match goal with
    | Hv : Nf t, Ht : Typing _ t _ |- _ =>
      inversion Hv; subst; inversion Ht; subst
    | H : Typing _ (const _) _ |- _ => inversion H; subst; clear H
    | H : Typing _ (app _ _) _ |- _ => inversion H; subst; clear H
    end
  end; eauto.
Admitted.
