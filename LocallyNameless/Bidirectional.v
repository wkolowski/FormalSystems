From FormalSystems Require Export LocallyNameless.STLC.

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
    + now apply Typing_elimUnit with (l ++ map fst Γ); auto.
    + now apply Typing_outl with B; auto.
    + now apply Typing_outr with A; auto.
    + now apply Typing_elimProd with A B (l ++ map fst Γ); auto.
    + now apply Typing_case with A B (l ++ map fst Γ); subst; auto.
    + now apply Typing_case with A B (l ++ map fst Γ); auto.
  - intros Γ t A Hwf; destruct 1; try now constructor; auto.
    + now apply Typing_Infer.
    + now apply Typing_abs with (l ++ map fst Γ); auto.
    + now apply Typing_case with A B (l ++ map fst Γ); auto.
    + now apply Typing_case' with A B; auto.
Qed.

Lemma Infer_det :
  forall (Γ : Ctx) (t : Tm) (A1 A2 : Ty),
    WfCtx Γ ->
    Infer Γ t A1 ->
    Infer Γ t A2 ->
    A1 = A2.
Proof.
  intros * Hwf Hi1 Hi2; revert A2 Hi2.
  induction Hi1; inversion 1; subst; try easy.
  - now eapply Binds_inv; eauto.
  - now firstorder congruence.
  - now apply (H (fresh (l ++ l0 ++ map fst Γ))); auto.
  - now firstorder congruence.
  - now firstorder congruence.
  - now firstorder congruence.
  - injection (IHHi1 Hwf _ ltac:(eauto)) as [= <- <-].
    pose (x := fresh (l ++ l0 ++ fv t1 ++ map fst Γ)).
    pose (y := fresh ([x] ++ l ++ l0 ++ fv t1 ++ map fst Γ)).
    now apply (H x y); auto.
  - injection (IHHi1 Hwf _ ltac:(eauto)) as [= <- <-].
    now apply (H (fresh (l ++ l0 ++ map fst Γ))); auto.
  - injection (IHHi1 Hwf _ ltac:(eauto)) as [= <- <-].
    now apply (H (fresh (l ++ l0 ++ map fst Γ))); auto.
  - injection (IHHi1 Hwf _ ltac:(eauto)) as [= <- <-].
    now apply (H (fresh (l ++ l0 ++ map fst Γ))); auto.
  - injection (IHHi1 Hwf _ ltac:(eauto)) as [= <- <-].
    now apply (H (fresh (l ++ l0 ++ map fst Γ))); auto.
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
| elimUnit t1 t2  => None
| elimUnit' t1 t2 => None
| elimUnit''      => None
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
| elimProd t1 t2  => None
| inl t'          => None
| inr t'          => None
| case t1 t2 t3   => None
| case' t1 t2 t3  => None
| case''          => None
| zero            => Some TyNat
| succ t'         => if check Γ t' TyNat then Some TyNat else None
| rec t1 t2 t3    => None
end

with check (Γ : Ctx) (t : Tm) (A : Ty) {struct t} : bool :=
match t with
| fvar x => decide (infer Γ t = Some A)
| bvar i => decide (infer Γ t = Some A)
| annot _ _ => decide (infer Γ t = Some A)
| abs t' => false
(*  match A with
  | TyFun B C => check ((fresh (fv t'), B) :: Γ) t' C
  | _ => false
  end*)
| app t1 t2       =>
  match infer Γ t2 with
  | Some B => check Γ t1 (TyFun B A)
  | _ => false
  end
| unit            => decide (A = TyUnit)
| elimUnit t1 t2  => decide (infer Γ t = Some A)
| elimUnit' t1 t2 => decide (infer Γ t = Some A)
| elimUnit''      => decide (infer Γ t = Some A)
| abort t'        => check Γ t' TyEmpty
| pair t1 t2      => decide (infer Γ t = Some A)
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
| case t1 t2 t3   => decide (infer Γ t = Some A)
| case' t1 t2 t3  => decide (infer Γ t = Some A)
| case''          => decide (infer Γ t = Some A)
| zero            => decide (A = TyNat)
| succ t'         => decide (infer Γ t = Some A)
| rec t1 t2 t3    => decide (infer Γ t = Some A)
(* | _ => decide (infer Γ t = Some A) *)
end.
Set Guard Checking.

Lemma infer_spec :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> infer Γ t = Some A -> Typing Γ t A

with check_spec :
  forall (Γ : Ctx) (t : Tm) (A : Ty),
    WfCtx Γ -> check Γ t A = true -> Typing Γ t A.
Proof.
  - destruct t; cbn; intros A Hwf Hi.
    + constructor; [easy |].
      unfold Binds; unfold lookup_fvar in Hi.
      destruct (find _ Γ) as [ [b B] |] eqn: Hfind; [| easy].
      apply find_some in Hfind as [Hin Heq].
      apply Decidable_sound in Heq as <-.
      now injection Hi as [= ->].
    + easy.
    + easy.
    + destruct (infer Γ t1) as [ [B A' | | | | |] |] eqn: Hi1; [| easy..].
      destruct (check Γ t2 B) eqn: Hc2; [| easy].
      injection Hi as [= ->].
      apply Typing_app with B.
      * now apply infer_spec.
      * now apply check_spec.
    + destruct (check Γ t t0) eqn: Hc; [| easy].
      injection Hi as [= ->].
      constructor.
      now apply check_spec.
    + injection Hi as [= <-].
      now constructor.
    + easy.
    + easy.
    + easy.
    + easy.
    + destruct (infer Γ t1) eqn: Hi1; [| easy].
      destruct (infer Γ t2) eqn: Hi2; [| easy].
      injection Hi as [= <-].
      now constructor; apply infer_spec.
    + destruct (infer Γ t) as [ [] |] eqn: Hi'; try easy.
      injection Hi as [= ->].
      apply Typing_outl with t1.
      now apply infer_spec.
    + destruct (infer Γ t) as [ [] |] eqn: Hi'; try easy.
      injection Hi as [= ->].
      apply Typing_outr with t0.
      now apply infer_spec.
    + easy.
    + easy.
    + easy.
    + easy.
    + easy.
    + easy.
    + injection Hi as [= <-].
      now constructor.
    + destruct (check Γ t TyNat) eqn: Hc; [| easy].
      injection Hi as [= <-].
      constructor.
      now apply check_spec.
    + easy.
  - destruct t; intros A Hwf Hc.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + now cbn in Hc; apply Decidable_sound in Hc.
    + (*cbn in Hc.
      destruct A as [B C | | | | |]; try easy.
      apply Typing_abs with (fv t ++ map fst Γ); intros x Hx.
      apply check_spec; [now auto |].*)
      easy.
    + cbn in Hc.
      destruct (infer Γ t2) eqn: Hi2; [| easy].
      apply Typing_app with t.
      * now apply check_spec.
      * now apply infer_spec.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + cbn in Hc; apply Decidable_sound in Hc as ->.
      now constructor.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + cbn in Hc.
      now constructor; apply check_spec.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + destruct A as [ | | | | | ]; cbn in Hc; try easy.
      now constructor; apply check_spec.
    + destruct A as [ | | | | | ]; cbn in Hc; try easy.
      now constructor; apply check_spec.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + cbn in Hc; apply Decidable_sound in Hc as ->.
      now constructor.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
    + apply infer_spec; [easy |].
      now cbn in Hc |- *; apply Decidable_sound in Hc.
Admitted.

(*

Inductive Mode : Type :=
| infer
| check (T : Ty).

Require Import Recdef Bool.

Definition typeRet (m : Mode) : Type :=
match m with
| infer => option Ty
| check _ => bool
end.

Function type (m : Mode) (Γ : Ctx) (t : Tm) {measure size t} : typeRet m :=
match m, t with
| infer, fvar x          => None
| infer, bvar n          => None
| infer, abs t'          => None
| infer, app t1 t2       =>
  match type infer Γ t1 with
  | Some (TyFun A B) => if type (check A) Γ t2 then Some B else None
  | _ => None
  end
| infer, annot t' A      => if type (check A) Γ t' then Some A else None
| infer, unit            => Some TyUnit
| infer, elimUnit t1 t2  =>
  if type (check TyUnit) Γ t1
  then let x := fresh (fv t2) in type infer ((x, TyUnit) :: Γ) (t2 {{ 0 ~> x }})
  else None
| infer, elimUnit' t1 t2 => None
| infer, elimUnit''      => None
| infer, abort t'        => None
| infer, pair t1 t2      =>
  match type infer Γ t1, type infer Γ t2 with
  | Some A, Some B => Some (TyProd A B)
  | _, _ => None
  end
| infer, outl t'         =>
  match type infer Γ t' with
  | Some (TyProd A B) => Some A
  | _ => None
  end
| infer, outr t'         =>
  match type infer Γ t' with
  | Some (TyProd A B) => Some B
  | _ => None
  end
| infer, inl t'          => None
| infer, inr t'          => None
| infer, case t1 t2 t3   =>
  match type infer Γ t1 with
  | Some (TySum A B) =>
    let x := fresh (fv t1) in
    let y := fresh (fv t2) in
      match
        type infer ((x, A) :: Γ) (t2 {{ 0 ~> x }}),
        type infer ((y, B) :: Γ) (t3 {{ 0 ~> y }})
      with
      | Some C1, Some C2 => if decide (C1 = C2) then Some C1 else None
      | _, _ => None
      end
  | _ => None
  end
| infer, case' t1 t2 t3  => None
| infer, case''          => None
| infer, zero            => Some TyNat
| infer, succ t'         => if type (check TyNat) Γ t' then Some TyNat else None
| infer, rec t1 t2 t3    =>
  if type (check TyNat) Γ t3
  then
    match type infer Γ t1 with
    | Some A =>
      let
        x := fresh (fv t2)
      in
        if type (check A) ((x, A) :: Γ) (t2 {{ 0 ~> x }})
        then Some A
        else None
    | _ => None
    end
  else None
| check (TyFun A B), abs t' => let x := fresh (fv t') in type (check B) ((x, A) :: Γ) t'
| check A, elimUnit' t1 t2  => type (check TyUnit) Γ t1 && type (check (TyFun TyUnit A)) Γ t2
| check T, elimUnit'' =>
  match T with
  | TyFun (TyFun TyUnit A) (TyFun TyUnit B) => decide (A = B)
  | _ => false
  end
| check _, abort t'        => type (check TyEmpty) Γ t'
| check (TyProd A B), pair t1 t2 => type (check A) Γ t1 && type (check B) Γ t2
| check (TySum A B), inl t' => type (check A) Γ t'
| check (TySum A B), inr t' => type (check B) Γ t'
| check C, case' t1 t2 t3  =>
  match type infer Γ t1 with
  | Some (TySum A B) => type (check (TyFun A C)) Γ t2 && type (check (TyFun B C)) Γ t3
  | _ => false
  end
| check T, case''       =>
  match T with
  | TyFun (TyFun A1 C1) (TyFun (TyFun B2 C2) (TyFun (TySum A3 B3) C3)) =>
    decide (A1 = A3) && decide (B2 = B3) && decide (C1 = C2) && decide (C2 = C3)
  | _ => false
  end
| check T, _              =>
  match type infer Γ t with
  | Some T' => decide (T = T')
  | _ => false
  end
end.


Function infer (Γ : Ctx) (t : Tm) {measure size t} : option Ty :=
match t with
| fvar x          => None
| bvar n          => None
| abs t'          => None
| app t1 t2       =>
  match infer Γ t1 with
  | Some (TyFun A B) => if check Γ t2 A then Some B else None
  | _ => None
  end
| annot t' A      => if check Γ t' A then Some A else None
| unit            => Some TyUnit
| elimUnit t1 t2  =>
  if check Γ t1 TyUnit
  then let x := fresh (fv t2) in infer ((x, TyUnit) :: Γ) (t2 {{ 0 ~> x}})
  else None
| elimUnit' t1 t2 => None
| elimUnit''      => None
| abort t'        => None
| pair t1 t2      =>
  match infer Γ t1, infer Γ t2 with
  | Some A, Some B => Some (TyProd A B)
  | _, _ => None
  end
| outl t'         =>
  match infer Γ t' with
  | Some (TyProd A B) => Some A
  | _ => None
  end
| outr t'         =>
  match infer Γ t' with
  | Some (TyProd A B) => Some B
  | _ => None
  end
| inl t'          => None
| inr t'          => None
| case t1 t2 t3   =>
  match infer Γ t1 with
  | Some (TySum A B) =>
    let x := fresh (fv t1) in
    let y := fresh (fv t2) in
      match infer ((x, A) :: Γ) (t2 {{ 0 ~> x }}), infer ((y, B) :: Γ) (t3 {{ 0 ~> y }}) with
      | Some C1, Some C2 => if decide (C1 = C2) then Some C1 else None
      | _, _ => None
      end
  | _ => None
  end
| case' t1 t2 t3  => None
| case''          => None
| zero            => Some TyNat
| succ t'         => if check Γ t' TyNat then Some TyNat else None
| rec t1 t2 t3    =>
  if check Γ t3 TyNat
  then
    match infer Γ t1 with
    | Some A =>
      let
        x := fresh (fv t2)
      in
        if check ((x, A) :: Γ) (t2 {{ 0 ~> x }}) A
        then Some A
        else None
    | _ => None
    end
  else None
end

with check (Γ : Ctx) (t : Tm) (T : Ty) {struct t} : bool :=
match t, T with
| abs t', TyFun A B  => let x := fresh (fv t') in check ((x, A) :: Γ) t' B
| elimUnit' t1 t2, _ => andb (check Γ t1 TyUnit) (check Γ t2 (TyFun TyUnit T))
| elimUnit'', _      =>
  match T with
  | TyFun (TyFun TyUnit A) (TyFun TyUnit B) => decide (A = B)
  | _ => false
  end
| abort t', _        => check Γ t' TyEmpty
| pair t1 t2, TyProd A B => check Γ t1 A && check Γ t2 B
| inl t', TySum A B => check Γ t' A
| inr t', TySum A B => check Γ t' B
| case' t1 t2 t3, _  =>
  match infer Γ t1 with
  | Some (TySum A B) => check Γ t2 (TyFun A T) && check Γ t3 (TyFun B T)
  | _ => false
  end
| case'', _       =>
  match T with
  | TyFun (TyFun A1 C1) (TyFun (TyFun B2 C2) (TyFun (TySum A3 B3) C3)) =>
    decide (A1 = A3) && decide (B2 = B3) && decide (C1 = C2) && decide (C2 = C3)
  | _ => false
  end
| _, _              =>
  match infer Γ t with
  | Some T' => decide (T = T')
  | _ => false
  end
end.
*)
