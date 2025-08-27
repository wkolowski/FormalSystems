From FormalSystems Require Export LocallyNameless.STLC.

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

(** *** Reduction *)

Inductive CbvStep : Tm -> Tm -> Prop :=
| CbvStep_Contraction_app_abs :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : forall x : Atom, x # l -> lc (t1 {{ 0 ~> x }}))
    (Hv2 : CbvValue t2),
    CbvStep (app (abs t1) t2) (t1 {[ 0 ~> t2 ]})
| CbvStep_Contraction_annot :
  forall (t : Tm) (A : Ty)
    (Hlc : lc t),
    CbvStep (annot t A) t
| CbvStep_Contraction_elimUnit_unit :
  forall (t : Tm) (l : list Atom)
    (Hlc : forall x : Atom, x # l -> lc (t {{0 ~> x}})),
    CbvStep (elimUnit unit t) (t {[ 0 ~> unit ]})
| CbvStep_Contraction_elimUnit'_unit :
  forall (t : Tm)
    (Hlc : lc t),
    CbvStep (elimUnit' unit t) (app t unit)
| CbvStep_Contraction_app_elimUnit'' :
  forall (t : Tm)
    (Hlc : lc t),
    CbvStep (app elimUnit'' t) t
| CbvStep_Contraction_outl_pair :
  forall (v1 v2 : Tm)
    (Hv1 : CbvValue v1)
    (Hv2 : CbvValue v2),
    CbvStep (outl (pair v1 v2)) v1
| CbvStep_Contraction_outr_pair :
  forall (v1 v2 : Tm)
    (Hv1 : CbvValue v1)
    (Hv2 : CbvValue v2),
    CbvStep (outr (pair v1 v2)) v2
| CbvStep_Contraction_elimProd_pair :
  forall (v1 v2 t : Tm) (l : list Atom)
    (Hv1 : CbvValue v1)
    (Hv2 : CbvValue v2)
    (Hlc3 : forall x y : Atom, x # l -> y # x :: l -> lc (t {{ 0 ~> x }} {{ 1 ~> y }})),
    CbvStep (elimProd (pair v1 v2) t) (t {[ 0 ~> v1 ]} {[ 1 ~> v2 ]})
| CbvStep_Contraction_case_inl :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hv1 : CbvValue t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{ 0 ~> x }})),
    CbvStep (case (inl t1) t2 t3) (t2 {[ 0 ~> t1 ]})
| CbvStep_Contraction_case_inr :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hv1 : CbvValue t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{ 0 ~> x }})),
    CbvStep (case (inr t1) t2 t3) (t3 {[ 0 ~> t1 ]})
| CbvStep_Contraction_case'_inl :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv3 : CbvValue t3),
    CbvStep (case' t1 t2 (inl t3)) (app t1 t3)
| CbvStep_Contraction_case'_inr :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv3 : CbvValue t3),
    CbvStep (case' t1 t2 (inr t3)) (app t2 t3)
| CbvStep_Contraction_case''_inl :
  forall (t1 t2 v : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv : CbvValue v),
    CbvStep (app (app (app case'' t1) t2) (inl v)) (app t1 v)
| CbvStep_Contraction_case''_inr :
  forall (t1 t2 v : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hv : CbvValue v),
    CbvStep (app (app (app case'' t1) t2) (inr v)) (app t2 v)
| CbvStep_Contraction_rec_zero :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }})),
    CbvStep (rec t1 t2 zero) t1
| CbvStep_Contraction_rec_succ :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hv1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hv3 : CbvValue t3),
    CbvStep (rec t1 t2 (succ t3)) (t2 {[ 0 ~> rec t1 t2 t3 ]})
| CbvStep_Abortion_app :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvStep (app (abort t1) t2) (abort t1)
| CbvStep_Abortion_elimUnit :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{0 ~> x}})),
    CbvStep (elimUnit (abort t1) t2) (abort t1)
| CbvStep_Abortion_elimUnit' :
  forall (t1 t2 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2),
    CbvStep (elimUnit' (abort t1) t2) (abort t1)
| CbvStep_Abortion_outl :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbvStep (outl (abort t)) (abort t)
| CbvStep_Abortion_outr :
  forall (t : Tm)
    (Hlc' : lc  t),
    CbvStep (outr (abort t)) (abort t)
| CbvStep_Abortion_elimProd :
  forall (t1 t2 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x y : Atom, x # l -> y # x :: l -> lc (t2 {{ 0 ~> x }} {{ 1 ~> y }})),
    CbvStep (elimProd (abort t1) t2) (abort t1)
| CbvStep_Abortion_case :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{0 ~> x}}))
    (Hlc3 : forall x : Atom, x # l -> lc (t3 {{0 ~> x}})),
    CbvStep (case (abort t1) t2 t3) (abort t1)
| CbvStep_Abortion_case' :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbvStep (case' t1 t2 (abort t3)) (abort t3)
| CbvStep_Abortion_case'' :
  forall (t1 t2 t3 : Tm)
    (Hlc1 : lc t1)
    (Hlc2 : lc t2)
    (Hlc3 : lc t3),
    CbvStep (app (app (app case'' t1) t2) (abort t3)) (abort t3)
| CbvStep_Abortion_rec :
  forall (t1 t2 t3 : Tm) (l : list Atom)
    (Hlc1 : lc t1)
    (Hlc2 : forall x : Atom, x # l -> lc (t2 {{ 0 ~> x }}))
    (Hlc3 : lc t3),
    CbvStep (rec t1 t2 (abort t3)) (abort t3)
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
  now induction 1; econstructor; eauto.
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
  now induction 1; intros Hvt; inversion Hvt; subst; auto.
Qed.

#[export] Hint Resolve lc_CbvStep_l lc_CbvStep_r CbvStep_not_CbvValue : core.

(* #[export] Hint Extern 0 =>
  match goal with
  | Hv : CbvValue ?t, Hs : CbvStep ?t _ |- _ =>
    now apply CbvStep_not_CbvValue in Hs
  end : core. *)

Lemma CbvStep_det :
  forall t t1 t2 : Tm,
    CbvStep t t1 -> CbvStep t t2 -> t1 = t2.
Proof.
  intros t t1 t2 Hs1 Hs2; revert t2 Hs2.
  now induction Hs1; intros; inversion Hs2; subst; try now f_equal; auto;
    try match goal with
    | H : CbvStep ?t1 _ |- _ => now apply CbvStep_not_CbvValue in H; auto
    end.
Qed.

(** *** Progress and preservation *)

#[export] Hint Extern 1 (Typing ?Γ (?t {[ 0 ~> ?u ]}) _) =>
  match goal with
  | Ht : forall _ : Atom, _ # _ -> Typing ((_, _) :: Γ) (t {{ 0 ~> _ }}) _,
    Hu : Typing Γ u ?B |- _ =>
      apply Typing_open' with B
(*   | Ht : forall _ : Atom, _ # _ -> Typing ((_, _) :: Γ) (t {{ 0 ~> _ }}) _ |- _ =>
      eapply Typing_open' *)
  end : core.


(*
#[export] Hint Extern 1 (Typing ?Γ (?t {[ 0 ~> ?u ]}) _) =>
  match goal with
  | Ht : forall _ : Atom, _ # _ -> Typing ((_, _) :: Γ) (t {{ 0 ~> _ }}) _ |- _ =>
      eapply Typing_open'
  end : core.
*)

Lemma preservation_cbv :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty),
    CbvStep t1 t2 ->
    Typing Γ t1 A ->
    Typing Γ t2 A.
Proof.
  intros Γ t1 t2 A Hstep; revert A.
  induction Hstep; inversion 1; subst;
    try match goal with
    | H : Typing _ (abort _) _ |- _ => now inversion H; auto
    end; auto.
  - now inversion Ht1; subst; eauto.
  - now eauto.
  - now eauto.
  - now inversion Ht1; subst.
  - now inversion Ht'.
  - now inversion Ht'.
  - now inversion Ht1; subst; eauto.
  - now inversion Ht1; subst; eauto.
  - now inversion Ht1; subst; eauto.
  - now inversion Ht3; subst; eauto.
  - now inversion Ht3; subst; eauto.
  - now inversion Ht1; inversion Ht2; inversion Ht0; inversion Ht4; subst;
      inversion H15; subst; eauto.
  - now inversion Ht1; inversion Ht2; inversion Ht0; inversion Ht4; subst;
      inversion H15; subst; eauto.
  - now inversion Ht3; subst; eauto.
  - now eauto.
  - now eauto.
  - now eauto.
  - now eauto.
  - now eauto.
  - now eauto.
  - now eauto.
  - now eauto.
  - now eauto.
  - now eauto.
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
    inversion Hv; subst; inversion Ht1; subst; [| now eauto 6.. |].
    + destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; [| now eauto].
      now right; eexists; econstructor 1; eauto.
    + destruct (IHHt2 eq_refl) as [ Hv2 | [t2' Hs2] ]; [| now eauto].
      inversion Ht0; inversion Ht4; subst.
      inversion Ht2; subst; inversion Hv2; subst; eauto.
      * inversion Ht2; subst; inversion Ht6.
      * inversion Ht2; subst; inversion Ht6; subst; inversion Ht10.
  - now right; eauto.
  - now left.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; [| now eauto].
    inversion Hv; subst; inversion Ht; subst; [| | now inversion Ht1..].
    + now eauto.
    + now eexists; econstructor; eauto.
  - right; destruct (IHHt1 eq_refl) as [ Hv | [t1' Hs1] ]; [| now eauto].
    inversion Hv; subst; inversion Ht1; subst; [now eauto.. | |].
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
    Time inversion Hv; subst; inversion Ht; subst; [now eexists; econstructor; eauto.. | |].
    + now inversion Ht1.
    + now inversion Ht1.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt eq_refl) as [Hv | [t'' Hs] ].
    + inversion Hv; subst; inversion Ht; subst; [now eexists; econstructor; eauto.. | |].
      * now inversion Ht1.
      * now inversion Ht1.
    + exists (case t'' t2 t3).
      now apply CbvStep_case with l; eauto.
  - right; destruct (IHHt3 eq_refl) as [Hv3 | [] ]; [| now eauto].
    inversion Hv3; subst; inversion Ht3; subst; [now eauto 6.. | |].
    + now inversion Ht0.
    + now inversion Ht0.
  - now left.
  - now left.
  - now destruct (IHHt eq_refl) as [Hv | [t'' Hs] ]; eauto.
  - right; destruct (IHHt2 eq_refl) as [Hv1 | [t1' Hs1] ]; [| now eauto 6].
    inversion Hv1; subst; inversion Ht3; subst;
      [now eexists; econstructor; eauto | | | now eexists; econstructor; eauto..].
    + now inversion Ht0.
    + now inversion Ht0.
Qed.
