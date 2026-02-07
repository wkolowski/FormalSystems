From FormalSystems Require Export Base.

(** 1.1 STLC with Booleans *)

Module STLC_with_Booleans.

Inductive type : Type :=
| TBool : type
| TArr : type -> type -> type.

Inductive tm : Type :=
| TVar : Atom -> tm
| TApp : tm -> tm -> tm
| TLam : Atom -> tm -> tm
| TTrue : tm
| TFalse : tm
| TIf : tm -> tm -> tm -> tm.

Definition Ctx : Type := Atom -> option type.

Inductive has_type : Ctx -> tm -> type -> Prop :=
| ht_Var :
    forall (G : Ctx) (x : Atom) (A : type),
      G x = Some A -> has_type G (TVar x) A
| ht_App :
    forall (G : Ctx) (t1 t2 : tm) (A B : type),
      has_type G t1 (TArr A B) -> has_type G t2 A ->
        has_type G (TApp t1 t2) B
| ht_Abs :
    forall (G : Ctx) (x : Atom) (t : tm) (A B : type),
      has_type (fun v : Atom => if decide (x = v) then Some A else G v) t B ->
        has_type G (TLam x t) (TArr A B)
| ht_True :
    forall G : Ctx, has_type G TTrue TBool
| ht_False :
    forall G : Ctx, has_type G TFalse TBool
| ht_If :
    forall (G : Ctx) (t1 t2 t3 : tm) (A : type),
      has_type G t1 TBool -> has_type G t2 A -> has_type G t3 A ->
        has_type G (TIf t1 t2 t3) A.

Fixpoint eq_dec_type (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.

#[global]
#[refine]
Instance Decidable_eq_type :
  forall (t1 t2 : type), Decidable (t1 = t2) :=
{
  Decidable_witness :=
    match eq_dec_type t1 t2 with
    | left _ => true
    | right _ => false
    end;
}.
Proof.
  now destruct (eq_dec_type t1 t2).
Defined.

Fixpoint infer (G : Ctx) (t : tm) : option type :=
match t with
| TVar x => G x
| TApp t1 t2 =>
  match infer G t1, infer G t2 with
  | Some (TArr A B), Some A' => if decide (A = A') then Some B else None
  | _, _ => None
  end
| TLam x t' => None
| TTrue => Some TBool
| TFalse => Some TBool
| TIf t1 t2 t3 =>
  match infer G t1, infer G t2, infer G t3 with
  | Some TBool, Some A, Some A' => if decide (A = A') then Some A else None
  | _, _, _ => None
  end
end.

Lemma has_type_infer :
  forall (G : Ctx) (x : tm) (A : type),
    has_type G x A -> infer G x = Some A.
Proof.
  induction 1; cbn; only 1, 4-5: easy.
  - now rewrite IHhas_type1, IHhas_type2, Decidable_complete.
  - admit.
  - now rewrite IHhas_type1, IHhas_type2, IHhas_type3, Decidable_complete.
Admitted.

End STLC_with_Booleans.

(** 1.2 Bidirectional STLC with Booleans *)

Module Bidirectional_STLC_with_Booleans.

Inductive type : Type :=
| TBool : type
| TArr : type -> type -> type.

Inductive tm : Type :=
| TVar : Atom -> tm
| TApp : tm -> tm -> tm
| TLam : Atom -> tm -> tm
| TTrue : tm
| TFalse : tm
| TIf : tm -> tm -> tm -> tm
| TAnn : tm -> type -> tm.

Definition Ctx : Type := Atom -> option type.

Inductive infer_type : Ctx -> tm -> type -> Prop :=
| infer_Var :
    forall (G : Ctx) (x : Atom) (A : type),
      G x = Some A -> infer_type G (TVar x) A
| infer_App :
    forall (G : Ctx) (t1 t2 : tm) (A B : type),
      infer_type G t1 (TArr A B) -> check_type G t2 A ->
        infer_type G (TApp t1 t2) B
| infer_True :
    forall G : Ctx, infer_type G TTrue TBool
| infer_False :
    forall G : Ctx, infer_type G TFalse TBool
| infer_Ann :
    forall (G : Ctx) (t : tm) (A : type),
      check_type G t A -> infer_type G (TAnn t A) A

with check_type : Ctx -> tm -> type -> Prop :=
| check_Lam :
    forall (G : Ctx) (x : Atom) (t : tm) (A B : type),
      check_type (fun v : Atom => if decide (x = v) then Some A else G v) t B ->
        check_type G (TLam x t) (TArr A B)
| check_If :
    forall (G : Ctx) (t1 t2 t3 : tm) (A : type),
      check_type G t1 TBool -> check_type G t2 A -> check_type G t3 A ->
        check_type G (TIf t1 t2 t3) A
| check_infer :
    forall (G : Ctx) (t : tm) (A : type),
      infer_type G t A -> check_type G t A.

#[global] Hint Constructors infer_type : core.
#[global] Hint Constructors check_type : core.

Fixpoint eq_dec_type (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.

#[global]
#[refine]
Instance Decidable_eq_type :
  forall (t1 t2 : type), Decidable (t1 = t2) :=
{
  Decidable_witness :=
    match eq_dec_type t1 t2 with
    | left _ => true
    | right _ => false
    end;
}.
Proof.
  now destruct (eq_dec_type t1 t2).
Defined.

Fixpoint infer (G : Ctx) (t : tm) : option type :=
match t with
| TVar x => G x
| TApp t1 t2 =>
  match infer G t1 with
  | Some (TArr A B) => if check G t2 A then Some B else None
  | _ => None
  end
| TTrue => Some TBool
| TFalse => Some TBool
| TAnn t A => if check G t A then Some A else None
| _ => None
end

with check (G : Ctx) (t : tm) (A : type) : bool :=
match t with
| TLam x t =>
  match A with
  | TArr X Y => check (fun v : Atom => if decide (x = v) then Some X else G v) t Y
  | _ => false
  end
| TIf t1 t2 t3 => check G t1 TBool && check G t2 A && check G t3 A
| TVar x =>
  match G x with
  | Some B => decide (A = B)
  | _ => false
  end
| TApp t1 t2 =>
  match infer G t1 with
  | Some (TArr X Y) => check G t2 X && decide (Y = A)
  | _ => false
  end
| TTrue => decide (TBool = A)
| TFalse => decide (TBool = A)
| TAnn t' A' => check G t' A' && decide (A = A')
end.

Lemma infer_check :
  forall (G : Ctx) (t : tm) (A : type),
    infer G t = Some A -> check G t A = true.
Proof.
  intros G [] A Hi; cbn in *; only 3-6: now inversion Hi.
  - now rewrite Hi, Decidable_complete.
  - destruct (infer G t) as [[] |]; [easy | | easy].
    destruct (check G t0 t1); cbn; [| easy].
    injection Hi as [= ->].
    now apply Decidable_complete.
  - destruct (check G t t0); cbn; [| easy].
    injection Hi as [= ->].
    now apply Decidable_complete.
Qed.

Lemma infer_correct :
  forall (G : Ctx) (t : tm) (A : type),
    infer G t = Some A -> infer_type G t A

with check_correct :
  forall (G : Ctx) (t : tm) (A : type),
    check G t A = true -> check_type G t A.
Proof.
  - destruct t; cbn; intros.
    + now constructor.
    + destruct (infer G t1) eqn: Ht1; [| easy].
      destruct t; [easy |].
      destruct (check G t2 t3) eqn: Ht23; [| easy].
      injection H as [= ->].
      apply infer_App with t3.
      * now apply infer_correct.
      * now apply check_correct.
    + easy.
    + now injection H as [= <-]; constructor.
    + now injection H as [= <-]; constructor.
    + easy.
    + destruct (check G t t0) eqn: Ht; [| easy].
      injection H as [= ->].
      now constructor; apply check_correct.
  - destruct t; cbn; intros.
    + destruct (G a) eqn: HGa; [| easy].
      apply Decidable_sound in H; subst.
      now do 2 constructor.
    + destruct (infer G t1) eqn: Ht1; [| now congruence].
      destruct t; [easy |].
      apply andb_prop in H as [H1 [= ->]%Decidable_sound].
      constructor.
      apply infer_App with t3.
      * now apply infer_correct.
      * now apply check_correct.
    + destruct A; [easy |].
      now constructor; apply check_correct.
    + destruct A; [| easy].
      now constructor.
    + destruct A; [| easy].
      now constructor.
    + apply andb_prop in H as [[H1 H2]%andb_prop H3].
      now constructor; apply check_correct.
    + apply andb_prop in H as [H1 [= ->]%Decidable_sound].
      now do 2 constructor; apply check_correct.
Qed.

Lemma infer_complete :
  forall (G : Ctx) (t : tm) (A : type),
    infer_type G t A -> infer G t = Some A

with check_complete :
  forall (G : Ctx) (t : tm) (A : type),
    check_type G t A -> check G t A = true.
Proof.
  - intros G t A []; cbn; only 1, 3-4: easy.
    + apply infer_complete in H as ->.
      now apply check_complete in H0 as ->.
    + now apply check_complete in H as ->.
  - intros G t A []; cbn.
    + now apply check_complete.
    + now rewrite !check_complete; cbn.
    + now apply infer_check, infer_complete.
Qed.

End Bidirectional_STLC_with_Booleans.

(** 1.3 Bidirectional STLC with Booleans using mutual induction *)

Module Bidirectional_STLC_with_Booleans_using_mutual_induction.

Inductive type : Type :=
| TBool : type
| TArr : type -> type -> type.

Inductive tmEx : Type :=
| TVar : Atom -> tmEx
| TApp : tmEx -> tmIn -> tmEx
| TTrue : tmEx
| TFalse : tmEx
| TAnn : tmIn -> type -> tmEx

with tmIn : Type :=
| TLam : Atom -> tmIn -> tmIn
| TIf : tmIn -> tmIn -> tmIn -> tmIn
| TEx : tmEx -> tmIn.

Definition Ctx : Type := Atom -> option type.

Inductive infer_type : Ctx -> tmEx -> type -> Prop :=
| infer_Var :
    forall (G : Ctx) (x : Atom) (A : type),
      G x = Some A -> infer_type G (TVar x) A
| infer_App :
    forall (G : Ctx) (t1 : tmEx) (t2 : tmIn) (A B : type),
      infer_type G t1 (TArr A B) -> check_type G t2 A ->
        infer_type G (TApp t1 t2) B
| infer_True :
    forall G : Ctx, infer_type G TTrue TBool
| infer_False :
    forall G : Ctx, infer_type G TFalse TBool
| infer_Ann :
    forall (G : Ctx) (t : tmIn) (A : type),
      check_type G t A -> infer_type G (TAnn t A) A

with check_type : Ctx -> tmIn -> type -> Prop :=
| check_Lam :
    forall (G : Ctx) (x : Atom) (t : tmIn) (A B : type),
      check_type (fun v : Atom => if decide (x = v) then Some A else G v) t B ->
        check_type G (TLam x t) (TArr A B)
| check_If :
    forall (G : Ctx) (t1 t2 t3 : tmIn) (A : type),
      check_type G t1 TBool -> check_type G t2 A -> check_type G t3 A ->
        check_type G (TIf t1 t2 t3) A
| check_Ex :
    forall (G : Ctx) (t : tmEx) (A : type),
      infer_type G t A -> check_type G (TEx t) A.

#[global] Hint Constructors infer_type : core.
#[global] Hint Constructors check_type : core.

Fixpoint eq_dec_type (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.

#[global]
#[refine]
Instance Decidable_eq_type :
  forall (t1 t2 : type), Decidable (t1 = t2) :=
{
  Decidable_witness :=
    match eq_dec_type t1 t2 with
    | left _ => true
    | right _ => false
    end;
}.
Proof.
  now destruct (eq_dec_type t1 t2).
Defined.

Fixpoint infer (G : Ctx) (t : tmEx) : option type :=
match t with
| TVar x => G x
| TApp t1 t2 =>
  match infer G t1 with
  | Some (TArr A B) => if check G t2 A then Some B else None
  | _ => None
  end
| TTrue => Some TBool
| TFalse => Some TBool
| TAnn t A => if check G t A then Some A else None
end

with check (G : Ctx) (t : tmIn) (A : type) : bool :=
match t with
| TLam x t =>
  match A with
  | TArr X Y => check (fun v : Atom => if decide (x = v) then Some X else G v) t Y
  | _ => false
  end
| TIf t1 t2 t3 => check G t1 TBool && check G t2 A && check G t3 A
| TEx t' =>
  match infer G t' with
  | Some B => decide (A = B)
  | _ => false
  end
end.

Lemma infer_correct :
  forall (G : Ctx) (t : tmEx) (A : type),
    infer G t = Some A -> infer_type G t A

with check_correct :
  forall (G : Ctx) (t : tmIn) (A : type),
    check G t A = true -> check_type G t A.
Proof.
  - destruct t; cbn; intros.
    + now constructor.
    + destruct (infer G t) eqn: Ht; [| easy].
      destruct t1; [easy |].
      destruct (check G t0 t1_1) eqn: Ht'; [| easy].
      injection H as [= ->].
      apply infer_App with t1_1.
      * now apply infer_correct.
      * now apply check_correct.
    + now injection H as [= <-]; constructor.
    + now injection H as [= <-]; constructor.
    + destruct (check G t t0) eqn: Hc; [| easy].
      injection H as [= ->].
      now constructor; apply check_correct.
  - destruct t; cbn; intros.
    + destruct A; [easy |].
      now constructor; apply check_correct.
    + apply andb_prop in H as [[H1 H2]%andb_prop H3].
      now constructor; apply check_correct.
    + constructor; apply infer_correct.
      destruct (infer G t); [| easy].
      now apply Decidable_sound in H as <-.
Qed.

Lemma infer_complete :
  forall (G : Ctx) (t : tmEx) (A : type),
    infer_type G t A -> infer G t = Some A

with check_complete :
  forall (G : Ctx) (t : tmIn) (A : type),
    check_type G t A -> check G t A = true.
Proof.
  - destruct 1; cbn; intros; only 1, 3-4: easy.
    + now rewrite (infer_complete _ _ _ H), (check_complete _ _ _ H0).
    + now rewrite (check_complete _ _ _ H).
  - destruct 1; cbn; intros.
    + now apply check_complete.
    + now rewrite !check_complete; cbn.
    + now rewrite (infer_complete _ _ _ H), Decidable_complete.
Qed.

End Bidirectional_STLC_with_Booleans_using_mutual_induction.

(** 1.4 Bidirectional STLC with lots of other stuff *)

Module Bidirectional_STLC_with_stuff.

Inductive type : Type :=
| TArr   : type -> type -> type
| TEmpty : type
| TUnit  : type
| TBool  : type
| TProd  : type -> type -> type
| TSum   : type -> type -> type.

Inductive tmEx : Type :=
| TVar : Atom -> tmEx
| TAnn : tmIn -> type -> tmEx

| TApp : tmEx -> tmIn -> tmEx

| TStar : tmEx

| TTrue : tmEx
| TFalse : tmEx
| TIf : tmIn -> tmEx -> tmEx -> tmEx

| TPair : tmEx -> tmEx -> tmEx
| TOutl : tmEx -> tmEx
| TOutr : tmEx -> tmEx

| TCase : tmEx -> tmEx -> tmEx -> tmEx

with tmIn : Type :=
| TEx : tmEx -> tmIn
| TLam : Atom -> tmIn -> tmIn
| TExfalso : tmIn -> tmIn

| TInl : tmIn -> tmIn
| TInr : tmIn -> tmIn.

Definition Ctx : Type := Atom -> option type.

Inductive infer_type : Ctx -> tmEx -> type -> Prop :=
| infer_Var :
    forall (G : Ctx) (x : Atom) (A : type),
      G x = Some A -> infer_type G (TVar x) A
| infer_Ann :
    forall (G : Ctx) (t : tmIn) (A : type),
      check_type G t A -> infer_type G (TAnn t A) A
| infer_App :
    forall (G : Ctx) (t1 : tmEx) (t2 : tmIn) (A B : type),
      infer_type G t1 (TArr A B) -> check_type G t2 A ->
        infer_type G (TApp t1 t2) B
| infer_Star :
    forall G : Ctx, infer_type G TStar TUnit
| infer_True :
    forall G : Ctx, infer_type G TTrue TBool
| infer_False :
    forall G : Ctx, infer_type G TFalse TBool
| infer_If :
    forall (G : Ctx) (t1 : tmIn) (t2 t3 : tmEx) (A : type),
      check_type G t1 TBool ->
      infer_type G t2 A -> infer_type G t3 A ->
        infer_type G (TIf t1 t2 t3) A
| infer_Pair :
    forall (G : Ctx) (t1 t2 : tmEx) (A B : type),
      infer_type G t1 A -> infer_type G t2 B ->
        infer_type G (TPair t1 t2) (TProd A B)
| infer_Outl :
    forall (G : Ctx) (t : tmEx) (A B : type),
      infer_type G t (TProd A B) -> infer_type G (TOutl t) A
| infer_Outr :
    forall (G : Ctx) (t : tmEx) (A B : type),
      infer_type G t (TProd A B) -> infer_type G (TOutr t) B
| infer_Case :
    forall (G : Ctx) (t1 t2 t3 : tmEx) (A B C : type),
      infer_type G t1 (TSum A B) ->
      infer_type G t2 (TArr A C) ->
      infer_type G t3 (TArr B C) ->
        infer_type G (TCase t1 t2 t3) C

with check_type : Ctx -> tmIn -> type -> Prop :=
| check_Ex :
    forall (G : Ctx) (t : tmEx) (A : type),
      infer_type G t A -> check_type G (TEx t) A
| check_Lam :
    forall (G : Ctx) (x : Atom) (t : tmIn) (A B : type),
      check_type (fun v : Atom => if decide (x = v) then Some A else G v) t B ->
        check_type G (TLam x t) (TArr A B)
| check_Exfalso :
    forall (G : Ctx) (t : tmIn) (A : type),
      check_type G t TEmpty -> check_type G (TExfalso t) A
| check_Inl :
    forall (G : Ctx) (t : tmIn) (A B : type),
      check_type G t A -> check_type G (TInl t) (TSum A B)
| check_Inr :
    forall (G : Ctx) (t : tmIn) (A B : type),
      check_type G t B -> check_type G (TInr t) (TSum A B).

#[global] Hint Constructors infer_type : core.
#[global] Hint Constructors check_type : core.

Fixpoint eq_dec_type (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.

#[global]
#[refine]
Instance Decidable_eq_type :
  forall (t1 t2 : type), Decidable (t1 = t2) :=
{
  Decidable_witness :=
    match eq_dec_type t1 t2 with
    | left _ => true
    | right _ => false
    end;
}.
Proof.
  now destruct (eq_dec_type t1 t2).
Defined.

Fixpoint infer (G : Ctx) (t : tmEx) : option type :=
match t with
| TVar x => G x
| TAnn t A => if check G t A then Some A else None
| TApp t1 t2 =>
  match infer G t1 with
  | Some (TArr A B) => if check G t2 A then Some B else None
  | _ => None
  end
| TStar => Some TUnit
| TTrue => Some TBool
| TFalse => Some TBool
| TIf t1 t2 t3 =>
  match infer G t2, infer G t3 with
  | Some A, Some B => if check G t1 TBool && decide (A = B) then Some A else None
  | _, _ => None
  end
| TPair t1 t2 =>
  match infer G t1, infer G t2 with
  | Some A, Some B => Some (TProd A B)
  | _, _ => None
  end
| TOutl t' =>
  match infer G t' with
  | Some (TProd A B) => Some A
  | _ => None
  end
| TOutr t' =>
  match infer G t' with
  | Some (TProd A B) => Some B
  | _ => None
  end
| TCase t1 t2 t3 =>
  match infer G t1, infer G t2, infer G t3 with
  | Some (TSum A B), Some (TArr A' C), Some (TArr B' C') =>
      if decide (A = A') && decide (B = B') && decide (C = C')
      then Some C
      else None
  | _, _, _ => None
  end
end

with check (G : Ctx) (t : tmIn) (A : type) : bool :=
match t with
| TEx t' =>
  match infer G t' with
  | Some B => decide (A = B)
  | _ => false
  end
| TLam x t =>
  match A with
  | TArr X Y => check (fun v : Atom => if decide (x = v) then Some X else G v) t Y
  | _ => false
  end
| TExfalso t' => check G t' TEmpty
| TInl t' =>
  match A with
  | TSum B C => check G t' B
  | _ => false
  end
| TInr t' =>
  match A with
  | TSum B C => check G t' C
  | _ => false
  end
end.

Lemma infer_correct :
  forall (G : Ctx) (t : tmEx) (A : type),
    infer G t = Some A -> infer_type G t A

with check_correct :
  forall (G : Ctx) (t : tmIn) (A : type),
    check G t A = true -> check_type G t A.
Proof.
  - destruct t; cbn; intros.
    + now constructor.
    + destruct (check G t t0) eqn: Hc; [| easy].
      injection H as [= ->].
      now constructor; apply check_correct.
    + destruct (infer G t) eqn: Hi; [| easy].
      destruct t1; [| easy..].
      destruct (check G t0 t1_1) eqn: Hc; [| easy].
      injection H as [= ->].
      apply infer_App with t1_1.
      * now apply infer_correct.
      * now apply check_correct.
    + now injection H as [= <-]; constructor.
    + now injection H as [= <-]; constructor.
    + now injection H as [= <-]; constructor.
    + destruct (infer G t2) eqn: Hi2; [| easy].
      destruct (infer G t3) eqn: Hi3; [| easy].
      destruct (check G t1 TBool) eqn: Hc1; [| easy].
      decide (t = t0); subst; [| easy].
      cbn in H; injection H as [= <-].
      now constructor; auto.
    + destruct (infer G t1) eqn: Hi1; [| easy].
      destruct (infer G t2) eqn: Hi2; [| easy].
      injection H as [= <-].
      now constructor; apply infer_correct.
    + destruct (infer G t) eqn: Hi; [| easy].
      destruct t0; try easy.
      injection H as [= <-].
      now econstructor; apply infer_correct; eauto.
    + destruct (infer G t) eqn: Hi; [| easy].
      destruct t0; try easy.
      injection H as [= <-].
      now econstructor; apply infer_correct; eauto.
    + destruct (infer G t1) eqn: Hi1; [| easy].
      destruct t; inversion H; subst; clear H1.
      destruct (infer G t2) eqn: Hi2; [| easy].
      destruct t; inversion H; subst; clear H1.
      destruct (infer G t3) eqn: Hi3; [| easy].
      destruct t; try easy.
      decide (t4 = t6); decide (t5 = t8); decide (t7 = t9);
        inversion H; subst.
      now econstructor; apply infer_correct; eauto.
  - destruct t; cbn; intros.
    + constructor; apply infer_correct.
      destruct (infer G t); [| easy].
      now apply Decidable_sound in H as <-.
    + destruct A; try easy.
      now constructor; apply check_correct.
    + now constructor; apply check_correct.
    + destruct A; try easy.
      now constructor; apply check_correct.
    + destruct A; try easy.
      now constructor; apply check_correct.
Qed.

Lemma infer_correct' :
  forall (G : Ctx) (t : tmEx) (A : type),
    infer G t = Some A <-> infer_type G t A

with check_correct' :
  forall (G : Ctx) (t : tmIn) (A : type),
    reflect (check_type G t A) (check G t A).
Proof.
  - split.
    + destruct t; cbn; intros.
      * now constructor.
      * destruct (check_correct' G t t0); [| easy].
        now injection H as [= ->]; constructor.
      * destruct (infer G t) eqn: Hi; [| easy].
        destruct t1; try easy.
        destruct (check G t0 t1_1) eqn: Hc; [| easy].
        injection H as [= ->].
        apply infer_App with t1_1.
        -- now apply infer_correct'.
        -- now destruct (check_correct' G t0 t1_1).
      * now injection H as [= <-]; constructor.
      * now injection H as [= <-]; constructor.
      * now injection H as [= <-]; constructor.
      * destruct (infer G t2) eqn: Hi2; [| easy].
        destruct (infer G t3) eqn: Hi3; [| easy].
        destruct (check_correct' G t1 TBool); [| easy].
        decide (t = t0); subst; [| easy].
        cbn in H; injection H as [= ->].
        now constructor; [| apply infer_correct'..].
      * destruct (infer G t1) eqn: Hi1; [| easy].
        destruct (infer G t2) eqn: Hi2; [| easy].
        injection H as [= <-].
        now constructor; rewrite <- infer_correct'.
      * destruct (infer G t) eqn: Hi; [| easy].
        destruct t0; try easy.
        injection H as [= ->].
        now econstructor; apply infer_correct'; eauto.
      * destruct (infer G t) eqn: Hi; [| easy].
        destruct t0; try easy.
        injection H as [= ->].
        now econstructor; apply infer_correct'; eauto.
      * destruct (infer G t1) eqn: Hi1; [| easy].
        destruct t; try easy.
        destruct (infer G t2) eqn: Hi2; [| easy].
        destruct t; try easy.
        destruct (infer G t3) eqn: Hi3; [| easy].
        destruct t; try easy.
        decide (t4 = t6); decide (t5 = t8); decide (t7 = t9);
          cbn in *; subst; inversion H; subst.
        now econstructor; apply infer_correct'; eauto.
    + destruct t; cbn; inversion 1; subst.
      * easy.
      * now destruct (check_correct' G t A).
      * destruct (infer_correct' G t (TArr A0 A)) as [_ ->]; [| easy].
        now destruct (check_correct' G t0 A0).
      * easy.
      * easy.
      * easy.
      * destruct (infer_correct' G t2 A) as [_ ->]; [| easy].
        destruct (infer_correct' G t3 A) as [_ ->]; [| easy].
        destruct (check_correct' G t1 TBool); cbn; [| easy].
        now rewrite Decidable_complete.
      * destruct (infer_correct' G t1 A0) as [_ ->]; [| easy].
        now destruct (infer_correct' G t2 B) as [_ ->].
      * now destruct (infer_correct' G t (TProd A B)) as [_ ->].
      * now destruct (infer_correct' G t (TProd A0 A)) as [_ ->].
      * destruct (infer_correct' G t1 (TSum A0 B)) as [_ ->]; [| easy].
        destruct (infer_correct' G t2 (TArr A0 A)) as [_ ->]; [| easy].
        destruct (infer_correct' G t3 (TArr B A)) as [_ ->]; [| easy].
        now rewrite !Decidable_complete.
  - destruct t; cbn; intros.
    + destruct (infer G t) eqn: Hi.
      * decide (A = t0); constructor; subst;
          [now constructor; apply infer_correct' |].
        inversion 1; subst.
        now firstorder congruence.
      * constructor; inversion 1; subst.
        now firstorder congruence.
    + destruct A; try (now constructor; inversion 1).
      destruct (check_correct' (fun v : Atom => if decide (a = v) then Some A1 else G v) t A2);
        constructor; [now constructor | now inversion 1].
    + destruct (check_correct' G t TEmpty); subst;
        constructor; [now constructor | now inversion 1].
    + destruct A; try (now constructor; inversion 1).
      destruct (check_correct' G t A1);
        constructor; [now constructor | now inversion 1].
    + destruct A; try (now constructor; inversion 1).
      destruct (check_correct' G t A2);
        constructor; [now constructor | now inversion 1].
Qed.

Inductive reflect_option {A : Type} (P : A -> Prop) : option A -> Type :=
| reflect_None  : (forall x : A, ~ P x) -> reflect_option P None
| reflect_Some  : forall x : A, P x -> reflect_option P (Some x).

(* Pretty hard *)
Lemma infer_correct'' :
  forall (G : Ctx) (t : tmEx),
    reflect_option (infer_type G t) (infer G t)

with check_correct'' :
  forall (G : Ctx) (t : tmIn) (A : type),
    reflect (check_type G t A) (check G t A).
Proof.
  - intros G t.
    destruct (infer G t) eqn: H; cycle 1.
    + constructor.
      intros t'; inversion 1; subst; cbn in *; try now congruence.
      * now destruct (check_correct'' G t0 t').
      * destruct (infer_correct'' G t1) as [| []].
Abort.

End Bidirectional_STLC_with_stuff.
