From FormalSystems Require Export LocallyNameless.STLC.Funs.

(** * Bidirectional typing *)

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
  - intros ? t A Hwf; destruct 1; try now constructor; auto.
    + now apply Typing_app with A; auto.
    + now apply Typing_outl with B; auto.
    + now apply Typing_outr with A; auto.
    + now apply Typing_elimProd with A B; auto.
    + now apply Typing_case with A B; auto.
  - intros Γ t A Hwf; destruct 1; try now constructor; auto.
    + now apply Typing_Infer.
    + now apply Typing_abs with (map fst Γ ++ fv t); auto.
    + now apply Typing_case with A B; auto.
Restart.
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
  induction Hi1; inversion 1; subst; try firstorder congruence.
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
| fvar x => lookup_fvar Γ x
| bvar n => None (* lookup_bvar Γ n *)
| annot t' A => if check Γ t' A then Some A else None
| abs t' => None
| app t1 t2 =>
  match infer Γ t1 with
  | Some (TyFun A B) => if check Γ t2 A then Some B else None
  | _ => None
  end
| unit => Some TyUnit
| elimUnit t1 t2 =>
  match infer Γ t1 with
  | Some (TyFun TyUnit A) => if check Γ t2 TyUnit then Some A else None
  | _ => None
  end
| abort t'        => None
| pair t1 t2      =>
  match infer Γ t1, infer Γ t2 with
  | Some A, Some B => Some (TyProd A B)
  | _, _ => None
  end
| outl t'         =>
  match infer Γ t' with
  | Some (TyProd A _) => Some A
  | _ => None
  end
| outr t'         =>
  match infer Γ t' with
  | Some (TyProd _ B) => Some B
  | _ => None
  end
| elimProd t1 t2  =>
  match infer Γ t1 with
  | Some (TyFun A (TyFun B C)) =>
    if check Γ t2 (TyProd A B)
    then Some C
    else None
  | _ => None
  end
| inl t'          => None
| inr t'          => None
| case t1 t2 t3  =>
  match infer Γ t1, infer Γ t2 with
  | Some (TyFun A C1), Some (TyFun B C2) =>
    if check Γ t3 (TySum A B) && decide (C1 = C2)
    then Some C1
    else None
  | _, _ => None
  end
| zero            => Some TyNat
| succ t'         => if check Γ t' TyNat then Some TyNat else None
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
| fvar x          => decide (infer Γ t = Some A)
| bvar i          => decide (infer Γ t = Some A)
| annot _ _       => decide (infer Γ t = Some A)
| abs t'          =>
  match A with
  | TyFun B C =>
    let x := fresh (map fst Γ ++ fv t') in
      check ((x, B) :: Γ) (t' {{ 0 ~> x }}) C
  | _ => false
  end
| app t1 t2       => decide (infer Γ t = Some A)
(*
  match infer Γ t2 with
  | Some B => check Γ t1 (TyFun B A)
  | _ => false
  end
*)
| unit            => decide (A = TyUnit)
| elimUnit t1 t2  => check Γ t1 (TyFun TyUnit A) && check Γ t2 TyUnit
| abort t'        => check Γ t' TyEmpty
| pair t1 t2      =>
  match A with
  | TyProd A1 A2 => check Γ t1 A1 && check Γ t2 A2
  | _ => false
  end
| outl t'         => decide (infer Γ t = Some A)
| outr t'         => decide (infer Γ t = Some A)
| elimProd t1 t2  => decide (infer Γ t = Some A)
| inl t'          =>
  match A with
  | TySum B _ => check Γ t' B
  | _ => false
  end
| inr t'          =>
  match A with
  | TySum _ C => check Γ t' C
  | _ => false
  end
| case t1 t2 t3  =>
  match infer Γ t3 with
  | Some (TySum B1 B2) => check Γ t1 (TyFun B1 A) && check Γ t2 (TyFun B2 A)
  | _ => false
  end
| zero            => decide (A = TyNat)
| succ t'         => decide (A = TyNat) && check Γ t' TyNat
| rec t1 t2 t3   => check Γ t1 A && check Γ t2 (TyFun A A) && check Γ t3 TyNat
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
  - intros Γ t A; destruct 1; cbn.
    + now apply lookup_fvar_spec.
    + erewrite infer_Infer by eauto; cbn.
      now rewrite check_Check.
    + now rewrite check_Check.
    + easy.
    + erewrite infer_Infer by eauto; cbn.
      now erewrite check_Check.
    + erewrite infer_Infer by eauto.
      now erewrite infer_Infer by eauto.
    + now erewrite infer_Infer by eauto; cbn.
    + now erewrite infer_Infer by eauto; cbn.
    + erewrite infer_Infer by eauto; cbn.
      now erewrite check_Check by eauto.
    + erewrite infer_Infer by eauto; cbn.
      erewrite infer_Infer by eauto; cbn.
      rewrite check_Check by easy.
      now decide (C = C).
    + easy.
    + now erewrite check_Check by eauto.
    + erewrite infer_Infer by eauto; cbn.
      rewrite check_Check by easy.
      erewrite check_Check by easy.
      now cbn.
  - intros Γ t A; destruct 1.
    + apply check_Check.
      now constructor.
    + now cbn; apply check_Check, Hc'; auto.
    + now cbn; rewrite 2!check_Check.
    + now cbn; rewrite check_Check.
    + now cbn; rewrite 2!check_Check.
    + now cbn; rewrite check_Check.
    + now cbn; rewrite check_Check.
    + cbn; erewrite infer_Infer by eauto; cbn.
      now rewrite 2!check_Check.
Restart.
  - intros Γ t A; destruct 1; cbn;
      erewrite ?infer_Infer by eauto; cbn;
      rewrite ?check_Check by easy; try easy.
    + now apply lookup_fvar_spec.
    + now decide (C = C).
  - intros Γ t A; destruct 1; cbn;
      erewrite ?infer_Infer by eauto; cbn;
      rewrite ?check_Check by easy; try easy.
    + apply check_Check.
      now constructor.
    + now apply check_Check, Hc'; auto.
Admitted. (* termination *)

Lemma Infer_infer :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> infer Γ t = Some A -> Infer Γ t A

with Check_check :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> check Γ t A = true -> Check Γ t A.
Proof.
  - destruct t; cbn; intros A Hwf Hi.
    + constructor.
      now apply lookup_fvar_spec.
    + easy.
    + easy.
    + destruct (infer Γ t1) as [ [B A' | | | | |] |] eqn: Hi1; [| easy..].
      destruct (check Γ t2 B) eqn: Hc2; [| easy].
      injection Hi as [= ->].
      apply Infer_app with B.
      * now apply Infer_infer.
      * now apply Check_check.
    + destruct (check Γ t t0) eqn: Hc; [| easy].
      injection Hi as [= ->].
      constructor.
      now apply Check_check.
    + injection Hi as [= <-].
      now constructor.
    + destruct (infer Γ t1) as [ [ [] | | | | |] |] eqn: Hi2; try easy.
      destruct (check Γ t2 TyUnit) eqn: Hc1; [| easy].
      injection Hi as [= ->].
      apply Infer_elimUnit.
      * now apply Infer_infer.
      * now apply Check_check.
    + easy.
    + destruct (infer Γ t1) eqn: Hi1; [| easy].
      destruct (infer Γ t2) eqn: Hi2; [| easy].
      injection Hi as [= <-].
      now constructor; apply Infer_infer.
    + destruct (infer Γ t) as [ [] |] eqn: Hi'; try easy.
      injection Hi as [= ->].
      apply Infer_outl with t1.
      now apply Infer_infer.
    + destruct (infer Γ t) as [ [] |] eqn: Hi'; try easy.
      injection Hi as [= ->].
      apply Infer_outr with t0.
      now apply Infer_infer.
    + destruct (infer Γ t1) as [ [] |] eqn: Hi1; try easy.
      destruct t0; try easy.
      destruct (check Γ t2 (TyProd t t0_1)) eqn: Hc2; [| easy].
      injection Hi as [= ->].
      econstructor.
      * now apply Infer_infer; eauto.
      * now apply Check_check; eauto.
    + easy.
    + easy.
    + destruct (infer Γ t1) as [ [] |] eqn: Hi1; try easy.
      destruct (infer Γ t2) as [ [] |] eqn: Hi2; try easy.
      destruct (check Γ t3 _) eqn: Hc3; [| easy].
      decide (t0 = t5); subst; [| easy].
      cbn in Hi; injection Hi as [= ->].
      econstructor.
      * now apply Infer_infer; eauto.
      * now apply Infer_infer; eauto.
      * now apply Check_check; eauto.
    + injection Hi as [= <-].
      now constructor.
    + destruct (check Γ t TyNat) eqn: Hc; [| easy].
      injection Hi as [= <-].
      constructor.
      now apply Check_check.
    + destruct (infer Γ t1) eqn: Hi1; try easy.
      destruct (check Γ t2 _) eqn: Hc2; [| easy].
      destruct (check Γ t3 _) eqn: Hc3; [| easy].
      cbn in Hi; injection Hi as [= ->].
      constructor.
      * now apply Infer_infer.
      * now apply Check_check.
      * now apply Check_check.
  - destruct t; intros A Hwf Hc.
    + constructor.
      apply Infer_infer; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + now cbn in Hc; apply Decidable_sound in Hc.
    + cbn in Hc.
      destruct A as [B C | | | | |]; try easy.
      apply Check_abs; intros x Hx.
      apply Check_check; [now auto |].
      admit.
    + constructor.
      apply Infer_infer; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
      (* cbn in Hc.
      destruct (infer Γ t2) eqn: Hi2; [| easy].
      apply Check_app with t.
      * now apply Check_check.
      * now apply Infer_infer.
      *)
    + constructor.
      apply Infer_infer; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + constructor.
      apply Infer_infer; [easy |].
      cbn in Hc |- *; apply Decidable_sound in Hc.
      now congruence.
    + cbn in Hc; apply andb_prop in Hc as [Hc1 Hc2].
      now apply Check_elimUnit; apply Check_check. 
    + cbn in Hc.
      now constructor; apply Check_check.
    + destruct A; cbn in Hc; try easy.
      cbn in Hc; apply andb_prop in Hc as [Hc1 Hc2].
      now apply Check_pair; apply Check_check.
    + constructor.
      apply Infer_infer; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + constructor.
      apply Infer_infer; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + constructor.
      apply Infer_infer; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + destruct A; cbn in Hc; try easy.
      now constructor; apply Check_check.
    + destruct A; cbn in Hc; try easy.
      now constructor; apply Check_check.
    + cbn in Hc.
      destruct (infer Γ t3) as [ [] |] eqn: Hi3; try easy.
      apply andb_prop in Hc as [Hc1 Hc2].
      eapply Check_case.
      * now eapply Infer_infer; eauto.
      * now apply Check_check; eauto.
      * now apply Check_check; eauto.
    + cbn in Hc; apply Decidable_sound in Hc as ->.
      now constructor.
    + constructor.
      apply Infer_infer; [easy |].
      now cbn in Hc |- *; apply andb_prop in Hc as [->%Decidable_sound ->].
    + cbn in Hc.
      
      apply andb_prop in Hc as [ [Hc1 Hc2]%andb_prop Hc3].
      now apply Check_rec; apply Check_check.
Admitted. (* Termination. Because check calls infer on t. *)

Lemma infer_spec :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> infer Γ t = Some A -> Typing Γ t A.
Proof.
  intros.
  now apply Typing_Infer, Infer_infer.
Qed.

Lemma check_spec :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> check Γ t A = true -> Typing Γ t A.
Proof.
  intros.
  now apply Typing_Check, Check_check.
Qed.

Lemma size_open :
  forall (t : Tm) (i : nat) (x : Atom),
    size (t {{ i ~> x }}) = size t.
Proof.
  now induction t; cbn; intros; rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; auto.
Qed.

Function type (Γ : Ctx) (t : Tm) (Hint : option Ty) {measure size t} : option Ty :=
match t with
| fvar x         => lookup_fvar Γ x
| bvar n         => None
| annot t' A     => type Γ t' (Some A)
| abs t'         =>
  match Hint with
  | Some (TyFun A B) =>
    let x := fresh (map fst Γ ++ fv t') in
      type ((x, A) :: Γ) (t' {{ 0 ~> x }}) (Some B)
  | _ => None
  end
| app t1 t2      =>
  match type Γ t1 Hint with
  | Some (TyFun A B) =>
    if decide (type Γ t2 (Some A) = Some A)
    then Some B
    else None
  | _ => None
  end
| unit => Some TyUnit
| elimUnit t1 t2 =>
  if decide (type Γ t2 (Some TyUnit) = Some TyUnit)
  then
    match Hint with
    | Some A =>
      if decide (type Γ t1 (Some (TyFun TyUnit A)) = Some (TyFun TyUnit A))
      then Some A
      else None
    | None =>
      match type Γ t1 None with
      | Some (TyFun TyUnit A) => Some A
      | _ => None
      end
    end
  else
    None
| abort t'       =>
  match Hint with
  | Some A =>
    if decide (type Γ t' (Some TyEmpty) = Some TyEmpty)
    then Some A
    else None
  | None => None
  end
| pair t1 t2     =>
  match Hint with
  | Some (TyProd A B) =>
    if decide (type Γ t1 (Some A) = Some A) && decide (type Γ t2 (Some B) = Some B)
    then Some (TyProd A B)
    else None
  | _ =>
    match type Γ t1 None, type Γ t2 None with
    | Some A, Some B => Some (TyProd A B)
    | _, _ => None
    end
  end
| outl t'        =>
  match type Γ t' None with
  | Some (TyProd A _) => Some A
  | _ => None
  end
| outr t'        =>
  match type Γ t' None with
  | Some (TyProd _ B) => Some B
  | _ => None
  end
| elimProd t1 t2 =>
  match type Γ t2 None with
  | Some (TyProd A B) =>
    match Hint with
    | Some C =>
      if decide (type Γ t1 (Some (TyFun A (TyFun B C))) = Some (TyFun A (TyFun B C)))
      then Some C
      else None
    | _ =>
      match type Γ t1 None with
      | Some (TyFun A' (TyFun B' C)) =>
        if decide (A = A') && decide (B = B')
        then Some C
        else None
      | _ => None
      end
    end
  | _ =>
    match type Γ t1 None with
    | Some (TyFun A (TyFun B C)) =>
      if decide (type Γ t2 (Some (TyProd A B)) = Some (TyProd A B))
      then Some C
      else None
    | _ => None
    end
  end
| inl t'         =>
  match Hint with
  | Some (TySum A B) =>
    if decide (type Γ t' (Some A) = Some A)
    then Some (TySum A B)
    else None
  | _ => None
  end
| inr t'         =>
  match Hint with
  | Some (TySum A B) =>
    if decide (type Γ t' (Some B) = Some B)
    then Some (TySum A B)
    else None
  | _ => None
  end
| case t1 t2 t3  =>
  match type Γ t3 None with
  | Some (TySum A B) =>
    match Hint with
    | Some C =>
      if
        decide (type Γ t1 (Some (TyFun A C)) = Some (TyFun A C))
          &&
        decide (type Γ t2 (Some (TyFun B C)) = Some (TyFun B C))
      then
        Some C
      else None
    | None =>
      match type Γ t1 None, type Γ t2 None with
      | Some (TyFun A' C1), Some (TyFun B' C2) =>
        if decide (A = A') && decide (B = B') && decide (C1 = C2)
        then Some C1
        else None
      | _, _ => None
      end
    end
  | _ =>
    match type Γ t1 None, type Γ t2 None with
    | Some (TyFun A C1), Some (TyFun B C2) =>
      if
        decide (type Γ t1 (Some A) = Some A)
          &&
        decide (type Γ t2 (Some B) = Some B)
          &&
        decide (C1 = C2)
      then if decide (type Γ t3 (Some (TySum A B)) = Some (TySum A B)) then Some C1 else None
      else None
    | _, _ => None
    end
  end
| zero           => Some TyNat
| succ t'        =>
  if decide (type Γ t' (Some TyNat) = Some TyNat)
  then Some TyNat
  else None
| rec t1 t2 t3   =>
  if decide (type Γ t3 (Some TyNat) = Some TyNat)
  then
    match Hint with
    | Some A =>
      if
        decide (type Γ t1 (Some A) = Some A)
          &&
        decide (type Γ t2 (Some (TyFun A A)) = Some (TyFun A A))
      then
        Some A
      else
        None
    | _ =>
      match type Γ t1 None with
      | Some A =>
        if decide (type Γ t2 (Some (TyFun A A)) = Some (TyFun A A))
        then Some A
        else None
      | _ => None
      end
    end
  else
    None
end.
Proof.
  all: intros; subst; cbn; rewrite ?size_open; lia.
Abort. (* Cannot create equation lemma. This may be because the function is nested-recursive. *)

(*
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
    (Hc' : Check Γ t A),
    Infer Γ (annot t A) A
| Infer_unit :
  forall (Γ : Ctx),
    Infer Γ unit TyUnit
| Infer_elimUnit :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty) (l : list Atom)
    (Hc1 : Check Γ t1 TyUnit)
    (Hi2 : forall x : Atom, x # l -> Infer ((x, TyUnit) :: Γ) (t2 {{ 0 ~> x }}) A),
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
  forall (Γ : Ctx) (t1 t2 : Tm) (A B C : Ty) (l : list Atom)
    (Hi1 : Infer Γ t1 (TyProd A B))
    (Hi2 : forall x y : Atom, x # l -> y # x :: l ->
      Infer ((y, B) :: (x, A) :: Γ) (t2 {{ 0 ~> x }} {{ 1 ~> y }}) C),
    Infer Γ (elimProd t1 t2) C
| Infer_case :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C1 C2 : Ty) (l : list Atom)
    (Hi1 : Infer Γ t1 (TySum A B))
    (Hi2 : forall x : Atom, x # l -> Infer ((x, A) :: Γ) (t2 {{ 0 ~> x }}) C1)
    (Hi3 : forall x : Atom, x # l -> Infer ((x, B) :: Γ) (t3 {{ 0 ~> x }}) C2)
    (Heq : C1 = C2),
    Infer Γ (case t1 t2 t3) C1
| Infer_case_asym :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty) (l : list Atom)
    (Hi1 : Infer Γ t1 (TySum A B))
    (Hi2 : forall x : Atom, x # l -> Infer ((x, A) :: Γ) (t2 {{ 0 ~> x }}) C)
    (Hc3 : forall x : Atom, x # l -> Check ((x, B) :: Γ) (t3 {{ 0 ~> x }}) C),
    Infer Γ (case t1 t2 t3) C
| Infer_zero :
  forall (Γ : Ctx),
    Infer Γ zero TyNat
| Infer_succ :
  forall (Γ : Ctx) (t : Tm)
    (Hc' : Check Γ t TyNat),
    Infer Γ (succ t) TyNat

with Check : Ctx -> Tm -> Ty -> Prop :=
| Check_Infer :
  forall (Γ : Ctx) (t : Tm) (A : Ty)
    (Hi : Infer Γ t A),
    Check Γ t A
| Check_abs :
  forall (Γ : Ctx) (t : Tm) (A B : Ty) (l : list Atom)
    (Hc : forall x : Atom, x # l -> Check ((x, A) :: Γ) (t {{0 ~> x}}) B),
    Check Γ (abs t) (TyFun A B)
| Check_elimUnit' :
  forall (Γ : Ctx) (t1 t2 : Tm) (A : Ty)
    (Hc1 : Check Γ t1 TyUnit)
    (Hc2 : Check Γ t2 (TyFun TyUnit A)),
    Check Γ (elimUnit' t1 t2) A
| Check_elimUnit'' :
  forall (Γ : Ctx) (A : Ty),
    Check Γ elimUnit'' (TyFun (TyFun TyUnit A) (TyFun TyUnit A))
| Check_abort :
  forall (Γ : Ctx) (t' : Tm) (A : Ty)
    (Hc : Check Γ t' TyEmpty),
    Check Γ (abort t') A
| Check_pair :
  forall (Γ : Ctx) (t1 t2 : Tm) (A B : Ty)
    (Hc1 : Check Γ t1 A)
    (Hc2 : Check Γ t2 B),
    Check Γ (pair t1 t2) (TyProd A B)
| Check_inl :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Hc : Check Γ t' A),
    Check Γ (inl t') (TySum A B)
| Check_inr :
  forall (Γ : Ctx) (t' : Tm) (A B : Ty)
    (Hc : Check Γ t' B),
    Check Γ (inr t') (TySum A B)
| Check_case :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty) (l : list Atom)
    (Hi1 : Infer Γ t1 (TySum A B))
    (Hc2 : forall x : Atom, x # l -> Check ((x, A) :: Γ) (t2 {{ 0 ~> x }}) C)
    (Hc3 : forall x : Atom, x # l -> Check ((x, B) :: Γ) (t3 {{ 0 ~> x }}) C),
    Check Γ (case t1 t2 t3) C
| Check_case' :
  forall (Γ : Ctx) (t1 t2 t3 : Tm) (A B C : Ty)
    (Hi3 : Infer Γ t3 (TySum A B))
    (Hc1 : Check Γ t1 (TyFun A C))
    (Hc2 : Check Γ t2 (TyFun B C)),
    Check Γ (case' t1 t2 t3) C
| Check_case'' :
  forall (Γ : Ctx) (A B C : Ty),
    Check Γ case'' (TyFun (TyFun A C) (TyFun (TyFun B C) (TyFun (TySum A B) C))).
*)
