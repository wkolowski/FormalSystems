From FormalSystems Require Export LocallyNameless.STLC.Funs.

(** * Bidirectional typing *)

Definition checkable (t : Tm) : bool :=
match t with
| abs _        => true
| elimUnit _ _ => true
| abort _      => true
| pair _ _     => true
| inl _        => true
| inr _        => true
| case _ _ _   => true
| rec _ _ _    => true
| _            => false
end.

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
    (Hc : Check Γ t A),
    Infer Γ (annot t A) A
| Infer_unit :
  forall (Γ : Ctx),
    Infer Γ unit TyUnit
| Infer_elimUnit :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty)
    (Hi1 : Infer Γ t1 (TyFun TyUnit A))
    (Hc2 : Check Γ t2 TyUnit),
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
  forall (Γ : Ctx) (t1 t2 : Tm) (A B C : Ty)
    (Hi1 : Infer Γ t1 (TyFun A (TyFun B C)))
    (Hc2 : Check Γ t2 (TyProd A B)),
      Infer Γ (elimProd t1 t2) C
| Infer_case :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty)
    (Hi1 : Infer Γ t1 (TyFun A C))
    (Hi2 : Infer Γ t2 (TyFun B C))
    (Hc3 : Check Γ t3 (TySum A B)),
      Infer Γ (case t1 t2 t3) C
| Infer_zero :
  forall (Γ : Ctx),
    Infer Γ zero TyNat
| Infer_succ :
  forall (Γ : Ctx) (t : Tm)
    (Hc' : Check Γ t TyNat),
    Infer Γ (succ t) TyNat
| Infer_rec :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A : Ty)
    (Hi1 : Infer Γ t1 A)
    (Hi2 : Check Γ t2 (TyFun A A))
    (Hc3 : Check Γ t3 TyNat),
      Infer Γ (rec t1 t2 t3) A

with Check : Ctx -> Tm -> Ty -> Prop :=
| Check_Infer :
  forall (Γ : Ctx) (t : Tm) (A : Ty)
    (Hnc : checkable t = false)
    (Hi : Infer Γ t A),
    Check Γ t A
| Check_abs :
  forall (Γ : Ctx) (t : Tm) (A B : Ty)
    (Hc' : forall x : Atom, x # (map fst Γ ++ fv t) -> Check ((x, A) :: Γ) (t {{0 ~> x}}) B),
    Check Γ (abs t) (TyFun A B)
| Check_elimUnit :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty)
    (Hc1 : Check Γ t1 (TyFun TyUnit A))
    (Hc2 : Check Γ t2 TyUnit),
    Check Γ (elimUnit t1 t2) A
| Check_abort :
  forall (Γ : Ctx) (t' : Tm) (A : Ty)
    (Hc' : Check Γ t' TyEmpty),
    Check Γ (abort t') A
| Check_pair :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty)
    (Hc1 : Check Γ t1 A)
    (Hc2 : Check Γ t2 B),
    Check Γ (pair t1 t2) (TyProd A B)
| Check_inl :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Hc' : Check Γ t' A),
    Check Γ (inl t') (TySum A B)
| Check_inr :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Hc' : Check Γ t' B),
    Check Γ (inr t') (TySum A B)
| Check_case :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty)
    (Hi3 : Infer Γ t3 (TySum A B))
    (Hc1 : Check Γ t1 (TyFun A C))
    (Hc2 : Check Γ t2 (TyFun B C)),
    Check Γ (case t1 t2 t3) C
| Check_rec :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A : Ty)
    (Hi1 : Check Γ t1 A)
    (Hi2 : Check Γ t2 (TyFun A A))
    (Hc3 : Check Γ t3 TyNat),
    Check Γ (rec t1 t2 t3) A.

#[export] Hint Constructors Infer Check : core.

Lemma Typing_Infer :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> Infer Γ t A -> Typing Γ t A

with Typing_Check :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> Check Γ t A -> Typing Γ t A.
Proof.
  - now intros ? t A Hwf; destruct 1; econstructor; eauto.
  - intros Γ t A Hwf; destruct 1; only 3-9: now econstructor; eauto.
    + now apply Typing_Infer.
    + now apply Typing_abs with (map fst Γ ++ fv t); auto.
Qed.

Lemma Infer_det :
  forall (Γ : Ctx) (t : Tm) (A1 A2 : Ty),
    WfCtx Γ ->
    Infer Γ t A1 ->
    Infer Γ t A2 ->
    A1 = A2.
Proof.
  intros * Hwf Hi1 Hi2; revert A2 Hi2.
  induction Hi1; inversion 1; subst; [| firstorder congruence..].
  now eapply Binds_inv; eauto.
Qed.

Definition lookup_fvar (Γ : Ctx) (x : Atom) : option Ty :=
match find (fun '(a, _) => decide (x = a)) Γ with
| Some (_, A) => Some A
| _ => None
end.

Definition lookup_bvar (Γ : Ctx) (i : nat) : option Ty :=
match nth_error Γ i with
| Some (_, A) => Some A
| _ => None
end.



#[export, refine] Instance Decidable_eq_option :
  forall {A : Type} (eq_dec_A : forall x y : A, Decidable (x = y)),
    forall x y : option A, Decidable (x = y) :=
{
  Decidable_witness :=
    match x, y with
    | None, None => true
    | Some x', Some y' => decide (x' = y')
    | _, _ => false
    end;
}.
Proof.
  destruct x as [x' |], y as [y' |]; [| easy..].
  rewrite Decidable_spec.
  now split; intros [= ->].
Defined.

Require Import Bool.

Unset Guard Checking.
Fixpoint infer (Γ : Ctx) (t : Tm) {struct t} : option Ty :=
match t with
| fvar x         => lookup_fvar Γ x
| bvar n         => None
| annot t' A     => if check Γ t' A then Some A else None
| abs t'         => None
| app t1 t2      =>
  match infer Γ t1 with
  | Some (TyFun A B) => if check Γ t2 A then Some B else None
  | _ => None
  end
| unit           => Some TyUnit
| elimUnit t1 t2 =>
  match infer Γ t1 with
  | Some (TyFun TyUnit A) => if check Γ t2 TyUnit then Some A else None
  | _ => None
  end
| abort t'       => None
| pair t1 t2     =>
  match infer Γ t1, infer Γ t2 with
  | Some A, Some B => Some (TyProd A B)
  | _, _ => None
  end
| outl t'        =>
  match infer Γ t' with
  | Some (TyProd A _) => Some A
  | _ => None
  end
| outr t'        =>
  match infer Γ t' with
  | Some (TyProd _ B) => Some B
  | _ => None
  end
| elimProd t1 t2 =>
  match infer Γ t1 with
  | Some (TyFun A (TyFun B C)) =>
    if check Γ t2 (TyProd A B)
    then Some C
    else None
  | _ => None
  end
| inl t'         => None
| inr t'         => None
| case t1 t2 t3  =>
  match infer Γ t1, infer Γ t2 with
  | Some (TyFun A C1), Some (TyFun B C2) =>
    if check Γ t3 (TySum A B) && decide (C1 = C2)
    then Some C1
    else None
  | _, _ => None
  end
| zero           => Some TyNat
| succ t'        => if check Γ t' TyNat then Some TyNat else None
| rec t1 t2 t3   =>
  match infer Γ t1 with
  | Some A =>
    if check Γ t2 (TyFun A A) && check Γ t3 TyNat
    then Some A
    else None
  | _ => None
  end
end

with check (Γ : Ctx) (t : Tm) (A : Ty) {struct t} : bool :=
match t with
| bvar i         => false
| abs t'         =>
  match A with
  | TyFun B C =>
    let x := fresh (map fst Γ ++ fv t') in
      check ((x, B) :: Γ) (t' {{ 0 ~> x }}) C
  | _ => false
  end
| elimUnit t1 t2 => check Γ t1 (TyFun TyUnit A) && check Γ t2 TyUnit
| abort t'       => check Γ t' TyEmpty
| pair t1 t2     =>
  match A with
  | TyProd A1 A2 => check Γ t1 A1 && check Γ t2 A2
  | _ => false
  end
| inl t'         =>
  match A with
  | TySum B _ => check Γ t' B
  | _ => false
  end
| inr t'         =>
  match A with
  | TySum _ C => check Γ t' C
  | _ => false
  end
| case t1 t2 t3  =>
  match infer Γ t3 with
  | Some (TySum B1 B2) => check Γ t1 (TyFun B1 A) && check Γ t2 (TyFun B2 A)
  | _ => false
  end
| rec t1 t2 t3   => check Γ t1 A && check Γ t2 (TyFun A A) && check Γ t3 TyNat
| fvar x         => decide (infer Γ t = Some A)
| annot _ _      => decide (infer Γ t = Some A)
| app t1 t2      => decide (infer Γ t = Some A)
| unit           => decide (infer Γ t = Some A)
| outl t'        => decide (infer Γ t = Some A)
| outr t'        => decide (infer Γ t = Some A)
| elimProd t1 t2 => decide (infer Γ t = Some A)
| zero           => decide (infer Γ t = Some A)
| succ t'        => decide (infer Γ t = Some A)
end.
Set Guard Checking.

Lemma lookup_fvar_spec :
  forall (Γ : Ctx) (x : Atom) (A : Ty),
    Binds Γ x A <-> lookup_fvar Γ x = Some A.
Proof.
  unfold Binds, lookup_fvar; split.
  - induction Γ; cbn; [easy |].
    intros [-> |]; [now decide (x = x) |].
    destruct a as [a A'].
    decide (x = a); subst.
Admitted. (* TODO: change [Binds] to only "bind" the last occurrence *)

Lemma infer_Infer :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Infer Γ t A -> infer Γ t = Some A

with check_Check :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    Check Γ t A -> check Γ t A = true.
Proof.
  - intros Γ t A; destruct 1; cbn;
      erewrite ?infer_Infer by eauto; cbn;
      rewrite ?check_Check by easy; try easy.
    + now apply lookup_fvar_spec.
    + now decide (C = C).
  - intros Γ t A; destruct 1; cbn;
      erewrite ?infer_Infer by eauto; cbn;
      rewrite ?check_Check by easy; try easy.
    + now destruct t; try easy;
      match goal with
      | |- check Γ ?t A = true =>
        change (decide (infer Γ t = Some A) = true);
        erewrite infer_Infer by eauto; decide_all
      end.
    + now apply check_Check, Hc'; auto.
Qed.

Fixpoint rename_ctx (Γ : Ctx) (x y : Atom) : Ctx :=
match Γ with
| [] => []
| (z, A) :: Γ' =>
  if decide (x = z)
  then (y, A) :: rename_ctx Γ' x y
  else (z, A) :: rename_ctx Γ' x y
end.

Lemma Infer_rename :
  forall (Γ : Ctx) (t : Tm) (A : Ty) (x y : Atom),
    y # map fst Γ ++ fv t ->
    Infer Γ t A -> Infer (rename_ctx Γ x y) (t [[ x := y ]]) A

with Check_rename :
  forall (Γ : Ctx) (t : Tm) (A : Ty) (x y : Atom),
    y # map fst Γ ++ fv t ->
    Check Γ t A -> Check (rename_ctx Γ x y) (t [[ x := y ]]) A.
Proof.
  - intros Γ t A x y Hy Hi; revert x y Hy; destruct Hi; cbn; intros;
      [| now econstructor; eauto..].
    decide_all.
    + admit.
    + admit.
  - intros Γ t A x y Hy Hc; revert x y Hy; destruct Hc; cbn; intros;
      try now constructor; auto.
    + apply Check_Infer.
      * admit.
      * now apply Infer_rename.
    + apply Check_abs; intros z Hz.
      admit.
    + now eapply Check_case; eauto.
Admitted.

Fixpoint Infer_infer (Γ : Ctx) (t : Tm) {struct t} :
  forall (A : Ty), WfCtx Γ -> infer Γ t = Some A -> Infer Γ t A

with Check_check (Γ : Ctx) (t : Tm) {struct t} :
  forall (A : Ty), WfCtx Γ -> check Γ t A = true -> Check Γ t A.
Proof.
  - destruct t; cbn; intros A Hwf Hi; try easy;
      repeat match goal with
      | Hi : context [match infer ?Γ ?t with _ => _ end] |- _ =>
        let H := fresh "Hi" t in destruct (infer Γ t) eqn: H; [| easy..]
      | Hc : context [match check ?Γ ?t ?A with _ => _ end] |- _ =>
        let H := fresh "Hc" t in destruct (check Γ t A) eqn: H; [| easy..]
      | Hc : context [match check ?Γ ?t ?A && _ with _ => _ end] |- _ =>
        let H := fresh "Hc" t in destruct (check Γ t A) eqn: H; [| easy..]; cbn in Hc
      | H : context [if decide _ then _ else _] |- _ => decide_all
      | H : context [match ?t with _ => _ end] |- _ => destruct t; try easy
      | H : Some _ = Some _ |- _ => injection H as [= ->]
      | H : Some _ = Some _ |- _ => injection H as [= <-]
      end;
      try now econstructor; eauto.
    constructor.
    now apply lookup_fvar_spec.
  - destruct t; intros A Hwf Hc; try easy;
      (try now apply Check_Infer, Infer_infer; [easy.. |]; apply Decidable_sound in Hc);
      cbn in Hc;
      repeat match goal with
      | H : context [match infer ?Γ ?t with _ => _ end] |- _ =>
        let H' := fresh H in destruct (infer Γ t) eqn: H'; try easy
      | H : context [match ?A with _ => _ end] |- _ => destruct A; try easy
      | H : _ && _ = true |- _ =>
        let H1 := fresh H in
        let H2 := fresh H in
          apply andb_prop in H as [H1 H2]
      end;
      try now constructor; auto.
    + apply Check_abs; intros x Hx.
      apply Check_check; [now auto |].
      admit.
    + now eapply Check_case; eauto.
Admitted. (* Termination. Because check calls infer on t. *)

Lemma infer_spec :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> infer Γ t = Some A -> Typing Γ t A.
Proof.
  now intros; apply Typing_Infer, Infer_infer.
Qed.

Lemma check_spec :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> check Γ t A = true -> Typing Γ t A.
Proof.
  now intros; apply Typing_Check, Check_check.
Qed.
