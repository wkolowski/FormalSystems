From FormalSystems Require Export LocallyNameless.LocallyNameless.

(** * Types *)

Inductive Ty : Type :=
| TyFun  : Ty -> Ty -> Ty
| TyUnit : Ty
| TyEmpty : Ty
| TyProd : Ty -> Ty -> Ty.

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
| fvar (a : Atom) : Tm
| bvar  : nat -> Tm
| abs   : Tm -> Tm
| app   : Tm -> Tm -> Tm
| unit  : Tm
| elimUnit : Tm -> Tm -> Tm
| elimUnit' : Tm -> Tm -> Tm
| abort : Tm -> Tm
| pair  : Tm -> Tm -> Tm
| outl  : Tm -> Tm
| outr  : Tm -> Tm.

Coercion fvar : Atom >-> Tm.
Coercion bvar : nat >-> Tm.

Fixpoint eq_dec_Tm (t u : Tm) : {t = u} + {t <> u}.
Proof.
  decide equality.
  - apply (eq_dec_Atom a a0).
  - apply PeanoNat.Nat.eq_dec.
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
    | fvar a     => fvar a
    | bvar j     => if decide (i = j) then a else bvar j
    | abs t'     => abs (open t' (S i) a)
    | app t1 t2  => app (open t1 i a) (open t2 i a)
    | unit       => unit
    | elimUnit t1 t2 => elimUnit (open t1 i a) (open t2 (S i) a)
    | elimUnit' t1 t2 => elimUnit' (open t1 i a) (open t2 i a)
    | abort t'   => abort (open t' i a)
    | pair t1 t2 => pair (open t1 i a) (open t2 i a)
    | outl t'    => outl (open t' i a)
    | outr t'    => outr (open t' i a)
    end.

#[export] Instance Close_Tm : Close nat Atom Tm :=
  fix close (t : Tm) (i : nat) (a : Atom) : Tm :=
    match t with
    | fvar x     => if decide (a = x) then bvar i else fvar x
    | bvar n     => bvar n
    | abs t'     => abs (close t' (S i) a)
    | app t1 t2  => app (close t1 i a) (close t2 i a)
    | unit       => unit
    | elimUnit t1 t2 => elimUnit (close t1 i a) (close t2 (S i) a)
    | elimUnit' t1 t2 => elimUnit' (close t1 i a) (close t2 i a)
    | abort t'   => abort (close t' i a)
    | pair t1 t2 => pair (close t1 i a) (close t2 i a)
    | outl t'    => outl (close t' i a)
    | outr t'    => outr (close t' i a)
    end.

#[export, refine] Instance OC_Tm :
  OC nat Atom Tm Open_Tm Close_Tm := {}.
Proof.
  all: induction t; cbn; intros;
  [
    now decide_all                     |
    now decide_all                     |
    now rewrite IHt; congruence        |
    now rewrite IHt1, IHt2             |
    easy                               |
    now rewrite IHt1, IHt2; congruence |
    now rewrite IHt1, IHt2             |
    now rewrite IHt                    |
    now rewrite IHt1, IHt2             |
    now rewrite IHt                    |
    now rewrite IHt
  ].
Qed.

Lemma open_open :
  forall (t : Tm) (i j : nat) (a b : Atom),
    i <> j ->
    t {{ i ~> a }} {{ j ~> b }} = t {{ i ~> a }} ->
      t {{ j ~> b }} = t.
Proof.
  induction t; cbn; intros * Hneq H.
  - easy.
  - now decide_all.
  - inversion H.
    f_equal.
    now apply IHt in H1; [| lia].
  - inversion H.
    f_equal.
    + now apply IHt1 in H1.
    + now apply IHt2 in H2.
  - easy.
  - inversion H.
    f_equal.
    + now apply IHt1 in H1.
    + now apply IHt2 in H2; [| lia].
  - inversion H.
    f_equal.
    + now apply IHt1 in H1.
    + now apply IHt2 in H2; [| lia].
  - inversion H.
    f_equal.
    now apply IHt in H1.
  - inversion H.
    f_equal.
    + now apply IHt1 in H1.
    + now apply IHt2 in H2.
  - inversion H.
    f_equal.
    now apply IHt in H1; [| lia].
  - inversion H.
    f_equal.
    now apply IHt in H1; [| lia].
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
| abort t'   => fv t'
| pair t1 t2 => fv t1 ++ fv t2
| outl t'    => fv t'
| outr t'    => fv t'
end.

#[export, refine] Instance LocallyNameless_Tm :
  LocallyNameless Atom Tm Open_Tm Close_Tm OC_Tm :=
{
  fv := fv;
}.
Proof.
  - unfold supports, Fresh'.
    induction t; cbn.
    + now firstorder decide_all.
    + easy.
    + intros a Hfresh.
      f_equal.
      now apply Fresh'_invariant, IHt.
    + intros a Hfresh.
      now rewrite IHt1, IHt2; only 2-3: solve_fresh.
    + easy.
    + intros a Hfresh.
      f_equal.
      * now rewrite IHt1 by solve_fresh.
      * now rewrite close_invariant, IHt2 by solve_fresh.
    + intros a Hfresh.
      now rewrite IHt1, IHt2; only 2-3: solve_fresh.
    + intros a Hfresh.
      f_equal.
      now apply Fresh'_invariant, IHt.
    + intros a Hfresh.
      now rewrite IHt1, IHt2; only 2-3: solve_fresh.
    + intros a Hfresh.
      f_equal.
      now apply Fresh'_invariant, IHt.
    + intros a Hfresh.
      f_equal.
      now apply Fresh'_invariant, IHt.
  - unfold LocallyClosed.
    induction t; cbn.
    + exists 0.
      intros _ _.
      now exists (fresh []).
    + exists (S n).
      intros j Hij.
      exists (fresh []).
      now decide_all; lia.
    + destruct IHt as [i IH].
      exists i.
      intros j Hij.
      destruct (IH (S j) ltac:(lia)) as [a Ha].
      exists a.
      now rewrite Ha.
    + destruct IHt1 as [i1 IH1], IHt2 as [i2 IH2].
      exists (max i1 i2).
      intros j Hle.
      destruct
        (IH1 (max i1 i2) ltac:(lia)) as [a1 Ha1],
        (IH2 (max i1 i2) ltac:(lia)) as [a2 Ha2].
      exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
      f_equal.
      * rewrite (open_LocallyClosed _ i1); [easy | | now lia].
        now rapply IH1.
      * rewrite (open_LocallyClosed _ i2); [easy | | now lia].
        now rapply IH2.
    + now exists 0; intros _ _; exists (fresh []).
    + destruct IHt1 as [i1 IH1], IHt2 as [i2 IH2].
      exists (max i1 i2).
      intros j Hle.
      destruct
        (IH1 (max i1 i2) ltac:(lia)) as [a1 Ha1],
        (IH2 (max i1 i2) ltac:(lia)) as [a2 Ha2].
      exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
      f_equal.
      * rewrite (open_LocallyClosed _ i1); [easy | | now lia].
        now rapply IH1.
      * rewrite (open_LocallyClosed _ i2); [easy | | now lia].
        now rapply IH2.
    + destruct IHt1 as [i1 IH1], IHt2 as [i2 IH2].
      exists (max i1 i2).
      intros j Hle.
      destruct
        (IH1 (max i1 i2) ltac:(lia)) as [a1 Ha1],
        (IH2 (max i1 i2) ltac:(lia)) as [a2 Ha2].
      exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
      f_equal.
      * rewrite (open_LocallyClosed _ i1); [easy | | now lia].
        now rapply IH1.
      * rewrite (open_LocallyClosed _ i2); [easy | | now lia].
        now rapply IH2.
    + destruct IHt as [i IH].
      exists i; intros j Hij.
      destruct (IH j Hij) as [a Ha].
      exists a.
      now rewrite Ha.
    + destruct IHt1 as [i1 IH1], IHt2 as [i2 IH2].
      exists (max i1 i2).
      intros j Hle.
      destruct
        (IH1 (max i1 i2) ltac:(lia)) as [a1 Ha1],
        (IH2 (max i1 i2) ltac:(lia)) as [a2 Ha2].
      exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
      f_equal.
      * rewrite (open_LocallyClosed _ i1); [easy | | now lia].
        now rapply IH1.
      * rewrite (open_LocallyClosed _ i2); [easy | | now lia].
        now rapply IH2.
    + destruct IHt as [i IH].
      exists i.
      intros j Hij.
      destruct (IH j Hij) as [a Ha].
      exists a.
      now rewrite Ha.
    + destruct IHt as [i IH].
      exists i.
      intros j Hij.
      destruct (IH j Hij) as [a Ha].
      exists a.
      now rewrite Ha.
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
    LocallyClosed' i t' -> LocallyClosed' i (outr t').

#[export] Hint Constructors LocallyClosed' : core.

Lemma LocallyClosed'_spec :
  forall (i : nat) (t : Tm),
    LocallyClosed' i t <-> LocallyClosed i t.
Proof.
  unfold LocallyClosed.
  split.
  - induction 1; intros j Hij; cbn.
    + now exists (fresh []).
    + exists (fresh []).
      now decide_all; lia.
    + destruct (IHLocallyClosed' (S j) ltac:(lia)) as [a Ha].
      now exists a; f_equal.
    + destruct
        (IHLocallyClosed'1 j Hij) as [a1 IH1],
        (IHLocallyClosed'2 j Hij) as [a2 IH2].
      exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
      f_equal.
      * now rewrite open_invariant, IH1.
      * now rewrite open_invariant, IH2.
    + now exists (fresh []).
    + destruct
        (IHLocallyClosed'1 j Hij) as [a1 IH1],
        (IHLocallyClosed'2 (S j) ltac:(lia)) as [a2 IH2].
      exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
      f_equal.
      * now rewrite open_invariant, IH1.
      * now rewrite open_invariant, IH2.
    + destruct
        (IHLocallyClosed'1 j Hij) as [a1 IH1],
        (IHLocallyClosed'2 j Hij) as [a2 IH2].
      exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
      f_equal.
      * now rewrite open_invariant, IH1.
      * now rewrite open_invariant, IH2.
    + destruct (IHLocallyClosed' j Hij) as [a Ha].
      now exists a; f_equal.
    + destruct
        (IHLocallyClosed'1 j Hij) as [a1 IH1],
        (IHLocallyClosed'2 j Hij) as [a2 IH2].
      exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
      f_equal.
      * now rewrite open_invariant, IH1.
      * now rewrite open_invariant, IH2.
    + destruct (IHLocallyClosed' j Hij) as [a Ha].
      now exists a; f_equal.
    + destruct (IHLocallyClosed' j Hij) as [a Ha].
      now exists a; f_equal.
  - revert i.
    induction t; cbn; intros i Hlc.
    + now constructor.
    + constructor.
      destruct (PeanoNat.Nat.lt_ge_cases n i); [easy |].
      destruct (Hlc _ H) as [a Ha].
      now decide_all.
    + constructor.
      apply IHt; intros j Hle.
      destruct j as [| j']; [now lia |].
      destruct (Hlc j' ltac:(lia)) as [a [=] ].
      now exists a.
    + constructor.
      * apply IHt1; intros j Hij.
        destruct (Hlc j Hij) as [a Ha].
        now exists a; congruence.
      * apply IHt2; intros j Hij.
        destruct (Hlc j Hij) as [a Ha].
        now exists a; congruence.
    + now constructor.
    + constructor.
      * apply IHt1; intros j Hij.
        destruct (Hlc j Hij) as [a Ha].
        now exists a; congruence.
      * apply IHt2; intros j Hle.
        destruct j as [| j']; [now lia |].
        destruct (Hlc j' ltac:(lia)) as [a [=] ].
        now exists a.
    + constructor.
      * apply IHt1; intros j Hij.
        destruct (Hlc j Hij) as [a Ha].
        now exists a; congruence.
      * apply IHt2; intros j Hij.
        destruct (Hlc j Hij) as [a Ha].
        now exists a; congruence.
    + constructor.
      apply IHt; intros j Hij.
      destruct (Hlc j Hij) as [a [=] ].
      now exists a.
    + constructor.
      * apply IHt1; intros j Hij.
        destruct (Hlc j Hij) as [a Ha].
        now exists a; congruence.
      * apply IHt2; intros j Hij.
        destruct (Hlc j Hij) as [a Ha].
        now exists a; congruence.
    + constructor.
      apply IHt; intros j Hij.
      destruct (Hlc j Hij) as [a [=] ].
      now exists a.
    + constructor.
      apply IHt; intros j Hij.
      destruct (Hlc j Hij) as [a [=] ].
      now exists a.
Qed.

Lemma open_LocallyClosed' :
  forall (t : Tm) (i j : nat) (a : Atom),
    i <= j -> LocallyClosed' i t -> t {{ j ~> a }} = t.
Proof.
  intros.
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
  intros H.
  induction t; cbn; intros.
  - intros [-> |]; [| easy].
    cbn in H.
    now decide (x = x).
  - easy.
  - apply IHt.
    cbn in H; inversion H; subst.
    now rewrite close_close_eq.
  - cbn in H; inversion H; subst.
    rewrite H1, H2, in_app_iff.
    now firstorder.
  - easy.
  - cbn in H; inversion H; subst.
    rewrite H1, H2, in_app_iff.
    intros []; firstorder.
    apply IHt2; [| easy].
    now rewrite <- H2, close_close_eq.
  - cbn in H; inversion H; subst.
    rewrite H1, H2, in_app_iff.
    now firstorder.
  - apply IHt.
    cbn in H; inversion H; subst.
    now rewrite close_close_eq.
  - cbn in H; inversion H; subst.
    rewrite H1, H2, in_app_iff.
    now firstorder.
  - apply IHt.
    cbn in H; inversion H; subst.
    now rewrite close_close_eq.
  - apply IHt.
    cbn in H; inversion H; subst.
    now rewrite close_close_eq.
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
| abort t'   => abort (subst t' x u)
| pair t1 t2 => pair (subst t1 x u) (subst t2 x u)
| outl t'    => outl (subst t' x u)
| outr t'    => outr (subst t' x u)
end.

Notation "t [[ x := u ]]" := (subst t x u) (at level 68).

Lemma subst_fv :
  forall (t : Tm) (x : Atom) (u : Tm),
    x # fv t -> t [[ x := u ]] = t.
Proof.
  induction t; cbn; intros.
  - decide_all.
    now firstorder.
  - easy.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2; solve_fresh.
  - easy.
  - now rewrite IHt1, IHt2; solve_fresh.
  - now rewrite IHt1, IHt2; solve_fresh.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2; solve_fresh.
  - now rewrite IHt.
  - now rewrite IHt.
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
| abort t'   => abort (open' t' i u)
| pair t1 t2 => pair (open' t1 i u) (open' t2 i u)
| outl t'    => outl (open' t' i u)
| outr t'    => outr (open' t' i u)
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
  induction t; cbn; intros.
  - now decide (x = a); subst; firstorder.
  - now decide_all.
  - now rewrite <- IHt.
  - now rewrite (IHt1 _ x), (IHt2 _ x); solve_fresh.
  - easy.
  - now rewrite (IHt1 _ x), (IHt2 _ x); solve_fresh.
  - now rewrite (IHt1 _ x), (IHt2 _ x); solve_fresh.
  - now rewrite <- IHt.
  - now rewrite (IHt1 _ x), (IHt2 _ x); solve_fresh.
  - now rewrite <- IHt.
  - now rewrite <- IHt.
Qed.

Lemma open'_open' :
  forall (t : Tm) (i j : nat) (u1 u2 : Tm),
    i <> j ->
    t {[ i ~> u1 ]} {[ j ~> u2 ]} = t {[ i ~> u1 ]} ->
      t {[ j ~> u2 ]} = t.
Proof.
  induction t; cbn; intros * Hneq H.
  - easy.
  - now decide_all.
  - inversion H.
    f_equal.
    eapply IHt, H1.
    now congruence.
  - inversion H.
    f_equal.
    + now eapply IHt1, H1.
    + now eapply IHt2, H2.
  - easy.
  - inversion H.
    f_equal.
    + now eapply IHt1, H1.
    + now eapply IHt2, H2; lia.
  - inversion H.
    f_equal.
    + now eapply IHt1, H1.
    + now eapply IHt2, H2.
  - inversion H.
    f_equal.
    eapply IHt, H1.
    now congruence.
  - inversion H.
    f_equal.
    + now eapply IHt1, H1.
    + now eapply IHt2, H2.
  - inversion H.
    f_equal.
    eapply IHt, H1.
    now congruence.
  - inversion H.
    f_equal.
    eapply IHt, H1.
    now congruence.
Qed.

(** ** Local closure *)

Inductive lc : Tm -> Prop :=
| lc_fvar :
  forall x : Atom,
    lc x
| lc_abs :
  forall (t : Tm) (l : list Atom)
    (Hcof : forall x : Atom, x # l -> lc (t {{ 0 ~> x }})),
    lc (abs t)
| lc_app :
  forall t1 t2 : Tm,
    lc t1 ->
    lc t2 ->
    lc (app t1 t2)
| lc_unit : lc unit
| lc_elimUnit :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hcof : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }})),
    lc (elimUnit t1 t2)
| lc_elimUnit' :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    lc (elimUnit' t1 t2)
| lc_abort :
  forall t' : Tm,
    lc t' ->
    lc (abort t')
| lc_pair :
  forall t1 t2 : Tm,
    lc t1 ->
    lc t2 ->
    lc (pair t1 t2)
| lc_outl :
  forall t' : Tm,
    lc t' ->
    lc (outl t')
| lc_outr :
  forall t' : Tm,
    lc t' ->
    lc (outr t').

#[export] Hint Constructors lc : core.

Lemma LocallyClosed_lc :
  forall t : Tm,
    lc t -> LocallyClosed 0 t.
Proof.
  unfold LocallyClosed.
  induction 1; cbn; intros j Hle.
  - now exists x.
  - destruct (H (fresh l) (fresh_spec l) (S j) ltac:(lia)) as [a Heq].
    exists a.
    f_equal.
    now apply open_open in Heq.
  - destruct (IHlc1 j Hle) as [a1 IH1].
    destruct (IHlc2 j Hle) as [a2 IH2].
    exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
    f_equal.
    + now rewrite open_invariant, IH1.
    + now rewrite open_invariant, IH2.
  - now exists (fresh []).
  - destruct (IHlc j Hle) as [a1 Ha1].
    destruct (H0 (fresh l) (fresh_spec l) (S j) ltac:(lia)) as [a2 Ha2].
    exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
    f_equal.
    + now rewrite open_invariant, Ha1.
    + apply open_open in Ha2; [| lia].
      now rewrite open_invariant, Ha2.
  - destruct (IHlc1 j Hle) as [a1 IH1].
    destruct (IHlc2 j Hle) as [a2 IH2].
    exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
    f_equal.
    + now rewrite open_invariant, IH1.
    + now rewrite open_invariant, IH2.
  - destruct (IHlc j Hle) as [a Ha].
    exists a.
    now rewrite Ha.
  - destruct (IHlc1 j Hle) as [a1 IH1].
    destruct (IHlc2 j Hle) as [a2 IH2].
    exists (fresh (fv t1 ++ fv t2 ++ [a1; a2])).
    f_equal.
    + now rewrite open_invariant, IH1.
    + now rewrite open_invariant, IH2.
  - destruct (IHlc j Hle) as [a Ha].
    exists a.
    now rewrite Ha.
  - destruct (IHlc j Hle) as [a Ha].
    exists a.
    now rewrite Ha.
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
  induction t; cbn; intros.
  - now decide_all.
  - now decide_all.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - easy.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt.
  - now rewrite IHt.
Qed.

Lemma subst_open :
  forall (t : Tm) (a b : Atom) (i : nat) (u : Tm),
    a <> b -> lc u ->
    t [[ a := u ]] {{ i ~> b }} = t {{ i ~> b }} [[ a := u ]].
Proof.
  induction t; cbn; intros.
  - decide_all.
    now rewrite open_lc.
  - now decide_all.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - easy.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt.
  - now rewrite IHt.
Qed.

Lemma lc_subst :
  forall (t : Tm) (x : Atom) (u : Tm),
    lc t -> lc u -> lc (t [[ x := u ]]).
Proof.
  intros t x u Ht Hu; revert x u Hu.
  induction Ht; cbn; intros.
  - now decide_all.
  - apply lc_abs with (x :: l).
    intros y Hin.
    rewrite subst_open; [| now firstorder | easy].
    apply H; [| easy].
    now firstorder.
  - now constructor; [apply IHHt1 | apply IHHt2].
  - now constructor.
  - apply lc_elimUnit with (x :: l).
    + now apply IHHt.
    + intros y Hy.
    rewrite subst_open; [| now firstorder | easy].
    apply H; [| easy].
    now firstorder.
  - now constructor; [apply IHHt1 | apply IHHt2].
  - now constructor; apply IHHt.
  - now constructor; [apply IHHt1 | apply IHHt2].
  - now constructor; apply IHHt.
  - now constructor; apply IHHt.
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
  apply Hcof.
  now solve_fresh.
Qed.

Lemma lc_open'' :
  forall (t : Tm) (i : nat) (u : Tm),
    lc t -> lc (t {[ i ~> u ]}).
Proof.
  intros.
  now rewrite open'_lc.
Qed.

Lemma open'_subst :
  forall (t : Tm) (i : nat) (u1 : Tm) (x : Atom) (u2 : Tm),
    lc u2 ->
    t {[ i ~> u1 ]} [[ x := u2 ]]
      =
    t [[ x := u2 ]] {[ i ~> u1 [[ x := u2 ]] ]}.
Proof.
  induction t; cbn; intros.
  - decide_all.
    now rewrite open'_lc.
  - now decide_all.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - easy.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt.
  - now rewrite IHt.
Qed.

(** * Contexts *)

Definition Ctx : Type := list (Atom * Ty).

Inductive WfCtx : Ctx -> Prop :=
| WfCtx_nil  :
  WfCtx []
| WfCtx_cons :
    forall (Γ : Ctx) (x : Atom) (A : Ty),
      WfCtx Γ -> x # map fst Γ -> WfCtx ((x, A) :: Γ).

#[export] Hint Constructors WfCtx : core.

Lemma WfCtx_app_cons :
  forall (Γ1 Γ2 : Ctx) (x : Atom) (A : Ty),
    WfCtx (Γ2 ++ (x, A) :: Γ1) -> WfCtx (Γ2 ++ Γ1).
Proof.
  induction Γ2 as [| [y B] Γ2' IH]; cbn; inversion 1; [easy |].
  constructor.
  - now apply IH in H2.
  - unfold Fresh in *; rewrite map_app, !in_app_iff in *; cbn in *.
    now firstorder.
Qed.

(** * Binding variables in context *)

Definition Binds (Γ : Ctx) (x : Atom) (A : Ty) : Prop :=
  In (x, A) Γ.

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
  induction Δ; cbn.
  - now firstorder congruence.
  - inversion 1; subst; [now firstorder |].
    apply IHΔ in H0.
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
  forall (Γ : Ctx) (t : Tm) (A B : Ty) (l : list Atom)
    (Hcof : forall x : Atom, x # l -> Typing ((x, A) :: Γ) (t {{ 0 ~> x }}) B),
    Typing Γ (abs t) (TyFun A B)
| Typing_app :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty),
    Typing Γ t1 (TyFun A B) ->
    Typing Γ t2 A ->
    Typing Γ (app t1 t2) B
| Typing_unit :
  forall (Γ : Ctx),
    WfCtx Γ ->
    Typing Γ unit TyUnit
| Typing_elimUnit :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty) (l : list Atom),
    Typing Γ t1 TyUnit ->
    forall (Hcof : forall x : Atom, x # l -> Typing ((x, TyUnit) :: Γ) (t2 {{ 0 ~> x }}) A),
    Typing Γ (elimUnit t1 t2) A
| Typing_elimUnit' :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    Typing Γ t1 TyUnit ->
    Typing Γ t2 (TyFun TyUnit A) ->
    Typing Γ (elimUnit' t1 t2) A
| Typing_abort :
  forall (Γ : Ctx) (t' : Tm) (A : Ty),
    Typing Γ t' TyEmpty ->
    Typing Γ (abort t') A
| Typing_pair :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty),
    Typing Γ t1 A ->
    Typing Γ t2 B ->
    Typing Γ (pair t1 t2) (TyProd A B)
| Typing_outl :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty),
    Typing Γ t' (TyProd A B) ->
    Typing Γ (outl t') A
| Typing_outr :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty),
    Typing Γ t' (TyProd A B) ->
    Typing Γ (outr t') B.

#[export] Hint Constructors Typing : Core.

Lemma lc_Typing :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Typing Γ t A -> lc t.
Proof.
  induction 1.
  - now constructor.
  - apply lc_abs with l; intros x Hx.
    now apply H.
  - now constructor.
  - now constructor.
  - apply lc_elimUnit with l; [easy |].
    intros x Hx.
    now apply H0.
  - now constructor.
  - now constructor.
  - now constructor.
  - now constructor.
  - now constructor.
Qed.

Lemma WfCtx_Typing :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Typing Γ t A -> WfCtx Γ.
Proof.
  induction 1; try easy.
  apply (WfCtx_app_cons _ [] (fresh l) A), H.
  now solve_fresh.
Qed.

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
  induction Ht; intros; subst.
  - constructor; [easy |].
    unfold Binds in *.
    rewrite !in_app_iff; rewrite in_app_iff in HB.
    now firstorder.
  - apply Typing_abs with (l ++ map fst Γ1 ++ map fst Δ ++ map fst Γ2).
    intros x Hx.
    red in Hx; rewrite !in_app_iff in Hx.
    rewrite app_comm_cons.
    apply H; [now firstorder | easy |].
    cbn; constructor; [easy |].
    red; rewrite !map_app, !in_app_iff.
    now firstorder.
  - apply Typing_app with A.
    + now apply IHHt1.
    + now apply IHHt2.
  - now constructor.
  - apply Typing_elimUnit with (l ++ map fst Γ1 ++ map fst Δ ++ map fst Γ2).
    + now apply IHHt.
    + intros x Hx.
      red in Hx; rewrite !in_app_iff in Hx.
      rewrite app_comm_cons.
      apply H; [now firstorder | easy |].
      cbn; constructor; [easy |].
      red; rewrite !map_app, !in_app_iff.
      now firstorder.
  - constructor.
    + now apply IHHt1.
    + now apply IHHt2.
  - now constructor; apply IHHt.
  - constructor.
    + now apply IHHt1.
    + now apply IHHt2.
  - apply Typing_outl with B.
    now apply IHHt.
  - apply Typing_outr with A.
    now apply IHHt.
Qed.

Lemma weakening :
  forall (Γ Δ : Ctx) (t : Tm) (A : Ty),
    WfCtx (Δ ++ Γ) ->
    Typing Γ t A ->
    Typing (Δ ++ Γ) t A.
Proof.
  now intros; apply weakening_aux with (Γ1 := []); cbn.
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
  induction Ht; cbn; intros; subst.
  - apply WfCtx_app_cons in Hwf as Hwf'.
    decide (x0 = x); subst.
    + replace A with A0.
      * now apply weakening.
      * symmetry.
        eapply (Binds_inv _ _ _ _ Hwf HB).
        red; rewrite in_app_iff; cbn.
        now firstorder.
    + apply Binds_app_cons_inv in HB as [ [-> ->] |]; [easy |].
      now constructor.
  - apply Typing_abs with (x :: l).
    intros y Hy.
    assert (x <> y /\ y # l) as [Hxy Hyl] by firstorder.
    rewrite subst_open; [| now firstorder | now apply lc_Typing in Hu].
    now eapply (H y Hyl ((y, A) :: Δ)).
  - econstructor.
    + now eapply IHHt1.
    + now eapply IHHt2.
  - constructor.
    now apply WfCtx_app_cons in H.
  - apply Typing_elimUnit with (x :: l).
    + now eapply IHHt.
    + intros y Hy.
      assert (x <> y /\ y # l) as [Hxy Hyl] by firstorder.
      rewrite subst_open; [| now firstorder | now apply lc_Typing in Hu].
      now eapply (H y Hyl ((y, TyUnit) :: Δ)).
  - econstructor.
    + now eapply IHHt1.
    + now eapply IHHt2.
  - now constructor; eapply IHHt.
  - constructor.
    + now eapply IHHt1.
    + now eapply IHHt2.
  - apply Typing_outl with B.
    now eapply IHHt.
  - apply Typing_outr with A.
    now eapply IHHt.
Qed.

Lemma Typing_subst :
  forall (Γ : Ctx) (x : Atom) (t u : Tm) (A B : Ty),
    Typing ((x, A) :: Γ) t B ->
    Typing Γ u A ->
    Typing Γ (t [[ x := u ]]) B.
Proof.
  now intros; eapply Typing_subst_aux with (Δ := []) (A := A).
Qed.

(** * Computation *)

(** ** Values *)

Inductive Value : Tm -> Prop :=
| Value_abs  :
  forall t : Tm,
    lc (abs t) ->
    Value (abs t)
| Value_unit : Value unit
| Value_abort :
  forall t' : Tm,
    lc t' ->
    Value (abort t')
| Value_pair :
  forall t1 t2 : Tm,
    Value t1 ->
    Value t2 ->
    Value (pair t1 t2).

#[export] Hint Constructors Value : core.

Lemma lc_Value :
  forall t : Tm,
    Value t -> lc t.
Proof.
  now induction 1; eauto.
Qed.

(** *** Computation *)

(** ** Contraction *)

Inductive Contraction : Tm -> Tm -> Prop :=
| Contraction_Fun :
  forall (t1 t2 : Tm),
    lc (abs t1) ->
    Value t2 ->
    Contraction (app (abs t1) t2) (t1 {[ 0 ~> t2 ]})
| Contraction_Unit :
  forall (t : Tm) (l : list Atom)
    (Hcof : forall x : Atom, x # l -> lc (t {{0 ~> x}})),
    Contraction (elimUnit unit t) (t {[ 0 ~> unit ]})
| Contraction_Unit' :
  forall (t : Tm),
    lc t ->
    Contraction (elimUnit' unit t) (app t unit)
| Contraction_OutlPair :
  forall v1 v2 : Tm,
    Value v1 ->
    Value v2 ->
    Contraction (outl (pair v1 v2)) v1
| Contraction_OutrPair :
  forall v1 v2 : Tm,
    Value v1 ->
    Value v2 ->
    Contraction (outr (pair v1 v2)) v2.

#[export] Hint Constructors Contraction : core.

#[export] Hint Resolve lc_Value : core.

Lemma lc_Contraction_l :
  forall t t' : Tm,
    Contraction t t' -> lc t.
Proof.
  now inversion 1; subst; eauto.
Qed.

Lemma lc_Contraction_r :
  forall t t' : Tm,
    Contraction t t' -> lc t'.
Proof.
  inversion 1; subst; only 3-5: now eauto.
  - now apply lc_open'; eauto.
  - rewrite (open'_spec _ _ (fresh (l ++ fv t0))) by solve_fresh.
    apply lc_subst; [| easy].
    apply Hcof.
    now solve_fresh.
Qed.

Lemma preservation_Contraction :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    Contraction t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  induction 1; inversion 1; subst.
  - inversion H5; subst.
    rewrite open'_spec with (x := fresh (l ++ fv t1)) by solve_fresh.
    apply Typing_subst with A0; [| easy].
    apply Hcof.
    now solve_fresh.
  - rewrite open'_spec with (x := fresh (l0 ++ fv t)) by solve_fresh.
    apply Typing_subst with TyUnit; [| easy].
    apply Hcof0.
    now solve_fresh.
  - now apply Typing_app with TyUnit.
  - now inversion H4.
  - now inversion H4.
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
    Abortion (outr (abort t)) (abort t).

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

Lemma preservation_Abortion :
  forall (Γ : Ctx) (t t' : Tm) (A : Ty),
    Abortion t t' ->
    Typing Γ t A ->
    Typing Γ t' A.
Proof.
  induction 1; inversion 1; subst; constructor.
  - now inversion H5.
  - now inversion H4.
  - now inversion H3.
  - now inversion H3.
  - now inversion H3.
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
    Step (outr t) (outr t').

#[export] Hint Constructors Step : core.

Lemma lc_Step_l :
  forall t t' : Tm,
    Step t t' -> lc t.
Proof.
  induction 1; try eauto.
  - now apply lc_Contraction_l in H.
  - now apply lc_Abortion_l in H.
Qed.

Lemma lc_Step_r :
  forall t t' : Tm,
    Step t t' -> lc t'.
Proof.
  induction 1; try eauto.
  - now apply lc_Contraction_r in H.
  - now apply lc_Abortion_r in H.
Qed.

(** ** Progress and preservation *)

Lemma preservation :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    Step t1 t2 ->
    Typing Γ t1 A ->
    Typing Γ t2 A.
Proof.
  intros Γ t1 t2 A Hstep; revert A.
  induction Hstep; intros A; [| | now inversion 1; subst; econstructor; eauto..].
  - now eapply preservation_Contraction.
  - now eapply preservation_Abortion; eauto.
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
  - left; constructor.
    apply lc_abs with l.
    intros x Hx.
    now eapply lc_Typing, Hcof.
  - destruct (IHHt1 eq_refl) as [ Hv | [t1' Hs1] ].
    + inversion Hv; subst; inversion Ht1; subst.
      * now destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; eauto.
      * now apply lc_Typing in H2, Ht2; eauto.
    + right.
      destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ].
      * now apply lc_Value in Hv2; eauto.
      * now apply lc_Step_l in Hs2; eauto.
  - now left.
  - destruct (IHHt eq_refl) as [Hv | [t'' Hs] ].
    + inversion Hv; subst; inversion Ht; subst.
      inversion Hv; subst; inversion Ht; subst.
      * right; exists (t2 {[ 0 ~> unit ]}).
        constructor.
        apply Contraction_Unit with l; intros x Hx.
        now eapply lc_Typing, Hcof.
      * right; exists (abort t').
        constructor 2.
        apply Abortion_Unit with l; [easy |].
        intros x Hx.
        specialize (Hcof x Hx).
        eapply lc_Typing, Hcof.
    + right; exists (elimUnit t'' t2).
      apply Step_ElimUnitCongr with l ; [| easy].
      intros x Hx.
      now eapply lc_Typing, Hcof.
  - destruct (IHHt1 eq_refl) as [ Hv | [t1' Hs1] ].
    + inversion Hv; subst; inversion Ht1; subst.
      * now apply lc_Typing in Ht2; eauto.
      * now apply lc_Typing in H2, Ht2; eauto.
    + right.
      destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ].
      * now apply lc_Value in Hv2; eauto.
      * now apply lc_Step_l in Hs2; eauto.
  - destruct (IHHt eq_refl) as [Hv | [t'' Hs] ].
    + now apply lc_Value in Hv; eauto.
    + now apply lc_Step_l in Hs; eauto.
  - destruct (IHHt1 eq_refl) as [Hv1 | [t1' Hs1] ].
    + now destruct (IHHt2 eq_refl) as [Hv2 | [t2' Hs1] ]; eauto.
    + destruct (IHHt2 eq_refl) as [Hv2 | [t2' Hs2] ].
      * now apply lc_Value in Hv2; eauto.
      * now apply lc_Step_l in Hs2; eauto.
  - destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht; subst; eauto.
  - destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    now inversion Hv; subst; inversion Ht; subst; eauto.
Qed.

(** * Bidirectional typing *)

Inductive Infer : Ctx -> Tm -> Ty -> Prop :=
| Infer_fvar :
  forall (Γ : Ctx) (x : Atom) (A : Ty),
    Binds Γ x A -> Infer Γ x A
| Infer_app  :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty),
    Infer Γ t1 (TyFun A B) ->
    Check Γ t2 A ->
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
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty),
    Infer Γ t1 A ->
    Infer Γ t2 B ->
    Infer Γ (pair t1 t2) (TyProd A B)
| Infer_outl :
  forall (Γ : Ctx) (t : Tm) (A B : Ty),
    Infer Γ t (TyProd A B) ->
    Infer Γ (outl t) A
| Infer_outr :
  forall (Γ : Ctx) (t : Tm) (A B : Ty),
    Infer Γ t (TyProd A B) ->
    Infer Γ (outr t) B

with Check : Ctx -> Tm -> Ty -> Prop :=
| Check_Infer :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Infer Γ t A ->
    Check Γ t A
| Check_abs :
  forall (Γ : Ctx) (t : Tm) (A B : Ty) (l : list Atom)
    (Hcof : forall x : Atom, x # l -> Check ((x, A) :: Γ) (t {{0 ~> x}}) B),
    Check Γ (abs t) (TyFun A B)
| Check_elimUnit' :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty)
    (Hc1 : Check Γ t1 TyUnit)
    (Hc2 : Check Γ t2 (TyFun TyUnit A)),
    Check Γ (elimUnit' t1 t2) A
| Check_abort :
  forall (Γ : Ctx) (t' : Tm) (A : Ty),
    Check Γ t' TyEmpty ->
    Check Γ (abort t') A
| Check_pair :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty),
    Check Γ t1 A ->
    Check Γ t2 B ->
    Check Γ (pair t1 t2) (TyProd A B).

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
      * now apply Hcof; firstorder.
    + constructor.
      * now apply Typing_Check.
      * now apply Typing_Check.
    + now constructor; apply Typing_Check.
    + constructor.
      * now apply Typing_Check.
      * now apply Typing_Check.
Qed.
