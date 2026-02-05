From Stdlib Require Import Bool Arith List.
Import ListNotations.

(** 1.1 STLC with Booleans *)

Module STLC_with_Booleans.

Parameter V : Type.
Parameter dec : V -> V -> bool.
Parameter dec_spec :
  forall x y : V, reflect (x = y) (dec x y).

Notation "x =? y" := (dec x y) (at level 70).

Inductive type : Type :=
| TBool : type
| TArr : type -> type -> type.

Inductive tm : Type :=
| TVar : V -> tm
| TApp : tm -> tm -> tm
| TLam : V -> tm -> tm
| TTrue : tm
| TFalse : tm
| TIf : tm -> tm -> tm -> tm.

Definition Ctx : Type := V -> option type.

Inductive has_type : Ctx -> tm -> type -> Prop :=
| ht_Var :
    forall (G : Ctx) (x : V) (A : type),
      G x = Some A -> has_type G (TVar x) A
| ht_App :
    forall (G : Ctx) (t1 t2 : tm) (A B : type),
      has_type G t1 (TArr A B) -> has_type G t2 A ->
        has_type G (TApp t1 t2) B
| ht_Abs :
    forall (G : Ctx) (x : V) (t : tm) (A B : type),
      has_type (fun v : V => if x =? v then Some A else G v) t B ->
        has_type G (TLam x t) (TArr A B)
| ht_True :
    forall G : Ctx, has_type G TTrue TBool
| ht_False :
    forall G : Ctx, has_type G TFalse TBool
| ht_If :
    forall (G : Ctx) (t1 t2 t3 : tm) (A : type),
      has_type G t1 TBool -> has_type G t2 A -> has_type G t3 A ->
        has_type G (TIf t1 t2 t3) A.

Fixpoint type_eq_dec (t1 t2 : type) : bool :=
match t1, t2 with
| TBool, TBool => true
| TArr t11 t12, TArr t21 t22 => type_eq_dec t11 t21 && type_eq_dec t12 t22
| _, _ => false
end.

Fixpoint infer (G : Ctx) (t : tm) : option type :=
match t with
| TVar x => G x
| TApp t1 t2 =>
  match infer G t1, infer G t2 with
  | Some (TArr A B), Some A' => if type_eq_dec A A' then Some B else None
  | _, _ => None
  end
| TLam x t' => None
| TTrue => Some TBool
| TFalse => Some TBool
| TIf t1 t2 t3 =>
  match infer G t1, infer G t2, infer G t3 with
  | Some TBool, Some A, Some A' => if type_eq_dec A A' then Some A else None
  | _, _, _ => None
  end
end.

Lemma type_eq_dec_refl :
  forall A : type, type_eq_dec A A = true.
Proof.
  induction A; cbn; [easy |].
  now rewrite IHA1, IHA2; cbn.
Qed.

Lemma has_type_infer :
  forall (G : Ctx) (x : tm) (A : type),
    has_type G x A -> infer G x = Some A.
Proof.
  induction 1; cbn; only 1, 4-5: easy.
  - now rewrite IHhas_type1, IHhas_type2, type_eq_dec_refl.
  - admit. (* lambda *)
  - now rewrite IHhas_type1, IHhas_type2, IHhas_type3, type_eq_dec_refl.
Admitted.

End STLC_with_Booleans.

(** 1.2 Bidirectional STLC with Booleans *)

Module Bidirectional_STLC_with_Booleans.

Parameter V : Type.
Parameter dec : V -> V -> bool.
Parameter dec_spec :
  forall x y : V, reflect (x = y) (dec x y).

Notation "x =? y" := (dec x y) (at level 70).

Inductive type : Type :=
| TBool : type
| TArr : type -> type -> type.

Inductive tm : Type :=
| TVar : V -> tm
| TApp : tm -> tm -> tm
| TLam : V -> tm -> tm
| TTrue : tm
| TFalse : tm
| TIf : tm -> tm -> tm -> tm
| TAnn : tm -> type -> tm.

Definition Ctx : Type := V -> option type.

Inductive infer_type : Ctx -> tm -> type -> Prop :=
| infer_Var :
    forall (G : Ctx) (x : V) (A : type),
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
    forall (G : Ctx) (x : V) (t : tm) (A B : type),
      check_type (fun v : V => if x =? v then Some A else G v) t B ->
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

Fixpoint type_eq_dec (t1 t2 : type) : bool :=
match t1, t2 with
| TBool, TBool => true
| TArr t11 t12, TArr t21 t22 => type_eq_dec t11 t21 && type_eq_dec t12 t22
| _, _ => false
end.

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
  | TArr X Y => check (fun v : V => if x =? v then Some X else G v) t Y
  | _ => false
  end
| TIf t1 t2 t3 => check G t1 TBool && check G t2 A && check G t3 A
(* Not very pretty, but it works. *)
| TVar x =>
  match G x with
  | Some B => type_eq_dec A B
  | _ => false
  end
| TApp t1 t2 =>
  match infer G t1 with
  | Some (TArr X Y) => check G t2 X && type_eq_dec Y A
  | _ => false
  end
| TTrue => type_eq_dec TBool A
| TFalse => type_eq_dec TBool A
| TAnn t' A' => check G t' A' && type_eq_dec A A'
end.

Lemma type_eq_dec_refl :
  forall A : type, type_eq_dec A A = true.
Proof.
  induction A; cbn; [easy |].
  now rewrite IHA1, IHA2; cbn.
Qed.

Ltac inv H := inversion H; subst; clear H.

Lemma infer_check :
  forall (G : Ctx) (t : tm) (A : type),
    infer G t = Some A -> check G t A = true.
Proof.
  destruct t; cbn; intros; only 3-6: now inversion H.
  - now rewrite H, type_eq_dec_refl.
  - destruct (infer G t1) as [[] |]; [easy | | easy].
    destruct (check G t2 t); cbn; [| easy].
    injection H as [= ->].
    now apply type_eq_dec_refl.
  - destruct (check G t t0); cbn; [| easy].
    injection H as [= ->].
    now apply type_eq_dec_refl.
Qed.

Lemma type_eq_dec_true :
  forall A B : type,
    type_eq_dec A B = true -> A = B.
Proof.
  induction A; destruct B; cbn; intros; only 1-3: easy.
  apply andb_prop in H as [H1 H2].
  now rewrite (IHA1 B1), (IHA2 B2).
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
    + case_eq (infer G t1); intros; rewrite H0 in H; [| easy].
      destruct t; inv H.
      case_eq (check G t2 t3); intro; rewrite H in H2; inv H2.
      apply infer_App with t3.
      * now apply infer_correct.
      * now apply check_correct.
    + easy.
    + now inversion H; subst; constructor.
    + now inversion H; subst; constructor.
    + easy.
    + case_eq (check G t t0); intros; rewrite H0 in H; inv H.
      constructor.
      now apply check_correct.
  - destruct t; cbn; intros.
    + case_eq (G v); intros; rewrite H0 in H; inv H.
      apply type_eq_dec_true in H2; subst.
      now do 2 constructor.
    + case_eq (infer G t1); intros; rewrite H0 in H.
      * destruct t; inv H.
        case_eq (check G t2 t3); intro; rewrite H in H2; inv H2.
        apply type_eq_dec_true in H3; subst.
        constructor.
        apply infer_App with t3.
        -- now apply infer_correct.
        -- now apply check_correct.
      * now congruence.
    + destruct A; inversion H.
      constructor.
      now apply check_correct.
    + destruct A; inversion H.
      now constructor.
    + destruct A; inversion H.
      now constructor.
    + apply andb_prop in H as [[H1 H2]%andb_prop H3].
      now constructor; apply check_correct.
    + apply andb_prop in H as [H1 [= ->]%type_eq_dec_true].
      do 2 constructor.
      now apply check_correct.
Qed.

Lemma infer_complete :
  forall (G : Ctx) (t : tm) (A : type),
    infer_type G t A -> infer G t = Some A

with check_complete :
  forall (G : Ctx) (t : tm) (A : type),
    check_type G t A -> check G t A = true.
Proof.
  - destruct 1; cbn; intros; only 1, 3-4: easy.
    + apply infer_complete in H as ->.
      now apply check_complete in H0 as ->.
    + now apply check_complete in H as ->.
  - destruct 1; cbn; intros.
    + now apply check_complete.
    + now rewrite !check_complete; cbn.
    + now apply infer_check, infer_complete.
Qed.

End Bidirectional_STLC_with_Booleans.

(** 1.3 Bidirectional STLC with Booleans using mutual induction *)

Module Bidirectional_STLC_with_Booleans_using_mutual_induction.

Parameter V : Type.
Parameter dec : V -> V -> bool.
Parameter dec_spec :
  forall x y : V, reflect (x = y) (dec x y).

Notation "x =? y" := (dec x y) (at level 70).

Inductive type : Type :=
| TBool : type
| TArr : type -> type -> type.

Inductive tmEx : Type :=
| TVar : V -> tmEx
| TApp : tmEx -> tmIn -> tmEx
| TTrue : tmEx
| TFalse : tmEx
| TAnn : tmIn -> type -> tmEx

with tmIn : Type :=
| TLam : V -> tmIn -> tmIn
| TIf : tmIn -> tmIn -> tmIn -> tmIn
| TEx : tmEx -> tmIn.

Definition Ctx : Type := V -> option type.

Inductive infer_type : Ctx -> tmEx -> type -> Prop :=
| infer_Var :
    forall (G : Ctx) (x : V) (A : type),
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
    forall (G : Ctx) (x : V) (t : tmIn) (A B : type),
      check_type (fun v : V => if x =? v then Some A else G v) t B ->
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

Fixpoint type_eq_dec (t1 t2 : type) : bool :=
match t1, t2 with
| TBool, TBool => true
| TArr t11 t12, TArr t21 t22 => type_eq_dec t11 t21 && type_eq_dec t12 t22
| _, _ => false
end.

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
  | TArr X Y => check (fun v : V => if x =? v then Some X else G v) t Y
  | _ => false
  end
| TIf t1 t2 t3 => check G t1 TBool && check G t2 A && check G t3 A
| TEx t' =>
  match infer G t' with
  | Some B => type_eq_dec A B
  | _ => false
  end
end.

Lemma type_eq_dec_refl :
  forall A : type, type_eq_dec A A = true.
Proof.
  induction A; cbn; [easy |].
  now rewrite IHA1, IHA2; cbn.
Qed.

Lemma type_eq_dec_true :
  forall A B : type,
    type_eq_dec A B = true -> A = B.
Proof.
  induction A; destruct B; cbn; intros;
    only 1-3: easy.
  apply andb_prop in H as [H1 H2].
  now rewrite (IHA1 B1), (IHA2 B2).
Qed.

Ltac inv H := inversion H; subst; clear H.

Lemma infer_correct :
  forall (G : Ctx) (t : tmEx) (A : type),
    infer G t = Some A -> infer_type G t A

with check_correct :
  forall (G : Ctx) (t : tmIn) (A : type),
    check G t A = true -> check_type G t A.
Proof.
  - destruct t; cbn; intros.
    + constructor. assumption.
    + case_eq (infer G t); intros; rewrite H0 in H.
      * destruct t1; inv H.
        case_eq (check G t0 t1_1); intro; rewrite H in H2; inv H2.
        eapply infer_App.
        -- eapply infer_correct. exact H0.
        -- apply check_correct. assumption.
      * inv H.
    + inv H. constructor.
    + inv H. constructor.
    + case_eq (check G t t0); intro; rewrite H0 in H; inv H.
      constructor. apply check_correct. assumption.
  - destruct t; cbn; intros.
    + destruct A.
      * inv H.
      * constructor. apply check_correct. assumption.
    + constructor; apply check_correct;
      destruct (check G t1 TBool), (check G t2 A), (check G t3 A); cbn in H;
      congruence.
    + constructor. apply infer_correct. destruct (infer G t).
      f_equal. symmetry. apply type_eq_dec_true. assumption.
      inv H.
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
    + now rewrite (infer_complete _ _ _ H), type_eq_dec_refl.
Qed.

End Bidirectional_STLC_with_Booleans_using_mutual_induction.

(** 1.4 Bidirectional STLC with lots of other stuff *)

Module Bidirectional_STLC_with_stuff.

Parameter V : Type.
Parameter dec : V -> V -> bool.
Parameter dec_spec :
  forall x y : V, reflect (x = y) (dec x y).

Notation "x =? y" := (dec x y) (at level 70).

Inductive type : Type :=
| TArr   : type -> type -> type
| TEmpty : type
| TUnit  : type
| TBool  : type
| TProd  : type -> type -> type
| TSum   : type -> type -> type.

Inductive tmEx : Type :=
| TVar : V -> tmEx
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
| TLam : V -> tmIn -> tmIn
| TExfalso : tmIn -> tmIn

| TInl : tmIn -> tmIn
| TInr : tmIn -> tmIn.

Definition Ctx : Type := V -> option type.

Inductive infer_type : Ctx -> tmEx -> type -> Prop :=
| infer_Var :
    forall (G : Ctx) (x : V) (A : type),
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
    forall (G : Ctx) (x : V) (t : tmIn) (A B : type),
      check_type (fun v : V => if x =? v then Some A else G v) t B ->
        check_type G (TLam x t) (TArr A B)
(*| check_Exfalso :
    forall (G : Ctx) (t : tmIn) (A : type),
      check_type G t TEmpty -> check_type G (TExfalso t A) A *)
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

Fixpoint type_eq_dec (t1 t2 : type) : bool :=
match t1, t2 with
| TArr t11 t12, TArr t21 t22 => type_eq_dec t11 t21 && type_eq_dec t12 t22
| TEmpty, TEmpty => true
| TUnit, TUnit => true
| TBool, TBool => true
| TProd t11 t12, TProd t21 t22 => type_eq_dec t11 t21 && type_eq_dec t12 t22
| TSum t11 t12, TSum t21 t22 => type_eq_dec t11 t21 && type_eq_dec t12 t22
| _, _ => false
end.

Lemma type_eq_dec_spec :
  forall A B : type, reflect (A = B) (type_eq_dec A B).
Proof.
  induction A; destruct B; cbn; try (now constructor; try inversion 1).
  - now destruct (IHA1 B1), (IHA2 B2); cbn; constructor; congruence.
  - now destruct (IHA1 B1), (IHA2 B2); cbn; constructor; congruence.
  - now destruct (IHA1 B1), (IHA2 B2); cbn; constructor; congruence.
Qed.

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
  | Some A, Some B => if check G t1 TBool && type_eq_dec A B then Some A else None
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
      if type_eq_dec A A' && type_eq_dec B B' && type_eq_dec C C'
      then Some C
      else None
  | _, _, _ => None
  end
end

with check (G : Ctx) (t : tmIn) (A : type) : bool :=
match t with
| TEx t' =>
  match infer G t' with
  | Some B => type_eq_dec A B
  | _ => false
  end
| TLam x t =>
  match A with
  | TArr X Y => check (fun v : V => if x =? v then Some X else G v) t Y
  | _ => false
  end
(*| TExfalso t' B => check G t' TEmpty && type_eq_dec A B *)
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

Ltac inv H := inversion H; subst; clear H.

Lemma infer_correct :
  forall (G : Ctx) (t : tmEx) (A : type),
    infer G t = Some A -> infer_type G t A

with check_correct :
  forall (G : Ctx) (t : tmIn) (A : type),
    check G t A = true -> check_type G t A.
Proof.
  - destruct t; cbn; intros.
    + now constructor.
    + case_eq (check G t t0); intro H'; rewrite H' in H; inv H.
      constructor.
      now apply check_correct.
    + case_eq (infer G t).
      * intros C H'.
        rewrite H' in H.
        destruct C as []; inv H.
        case_eq (check G t0 C1); intro H''; rewrite H'' in H1; inv H1.
        econstructor.
        -- now eapply infer_correct, H'.
        -- now apply check_correct.
      * now intros H'; rewrite H' in H.
    + now injection H as [= <-]; constructor.
    + now injection H as [= <-]; constructor.
    + now injection H as [= <-]; constructor.
    + case_eq (infer G t2); [intros t H' | intros H']; rewrite H' in H; [| easy].
      case_eq (infer G t3); [intros t' H'' | intros H'']; rewrite H'' in H; [| easy].
      case_eq (check G t1 TBool); intro H'''; rewrite H''' in H; [| easy].
      destruct (type_eq_dec_spec t t'); subst; [| easy].
      now cbn in H; inversion H; subst; auto.
    + case_eq (infer G t1); intros; rewrite H0 in *; inv H.
      case_eq (infer G t2); intros; rewrite H in *; inv H2.
      auto.
    + case_eq (infer G t); intros; rewrite H0 in *; inv H.
      destruct t0; inv H2. econstructor. apply infer_correct.
      cbn. rewrite H0. reflexivity.
    + case_eq (infer G t); intros; rewrite H0 in *; inv H.
      destruct t0; inv H2. econstructor. apply infer_correct.
      cbn. rewrite H0. reflexivity.
    + case_eq (infer G t1); intros; rewrite H0 in *; try destruct t; inv H.
      case_eq (infer G t2); intros; rewrite H in *; try destruct t; inv H2.
      case_eq (infer G t3); intros; rewrite H1 in *; try destruct t; inv H3.
      destruct
        (type_eq_dec_spec t4 t6),
        (type_eq_dec_spec t5 t8),
        (type_eq_dec_spec t7 t9);
      cbn in *; subst; inv H4; try congruence.
      econstructor; apply infer_correct; eassumption.
  - destruct t; cbn; intros.
    + constructor. apply infer_correct. destruct (infer G t).
      f_equal. destruct (type_eq_dec_spec A t0); congruence.
      inv H.
    + destruct A; inv H. constructor. apply check_correct. assumption.
(*
    destruct (type_eq_dec_spec A t0); subst.
      constructor. apply check_correct. rewrite andb_true_r in H. assumption.
      rewrite andb_false_r in H. inv H.
*)
    + constructor. apply check_correct. assumption.
    + destruct A; inv H. constructor. apply check_correct. assumption.
    + destruct A; inv H. constructor. apply check_correct. assumption.
Qed.

Lemma infer_correct'' :
  forall (G : Ctx) (t : tmEx) (A : type),
    infer G t = Some A <-> infer_type G t A

with check_correct'' :
  forall (G : Ctx) (t : tmIn) (A : type),
    reflect (check_type G t A) (check G t A).
Proof.
  split.
    destruct t; cbn; intros.
      constructor. assumption.
      destruct (check_correct'' G t t0); inv H. constructor. assumption.
      case_eq (infer G t).
        intros C H'. rewrite H' in H. destruct C as []; inv H.
          case_eq (check G t0 C1); intro H''; rewrite H'' in H1; inv H1.
          econstructor.
            apply infer_correct. exact H'.
            apply check_correct. assumption.
        intro H'. rewrite H' in H. inv H.
      1-3: inv H; constructor.
      case_eq (infer G t2); intros; rewrite H0 in H; inv H.
        case_eq (infer G t3); intros; rewrite H in H2; inv H2.
        destruct (check_correct'' G t1 TBool); inv H3.
        destruct (type_eq_dec_spec t t0); inv H2.
        constructor.
          assumption.
          1-2: apply infer_correct; assumption.
      case_eq (infer G t1); intros; rewrite H0 in *; inv H.
        case_eq (infer G t2); intros; rewrite H in *; inv H2.
        constructor; rewrite <- infer_correct''; assumption.
      case_eq (infer G t); intros; rewrite H0 in *; inv H.
        destruct t0; inv H2. econstructor. apply infer_correct.
        cbn. rewrite H0. reflexivity.
      case_eq (infer G t); intros; rewrite H0 in *; inv H.
        destruct t0; inv H2. econstructor. apply infer_correct.
        cbn. rewrite H0. reflexivity.
      case_eq (infer G t1); intros; rewrite H0 in *; try destruct t; inv H.
        case_eq (infer G t2); intros; rewrite H in *; try destruct t; inv H2.
        case_eq (infer G t3); intros; rewrite H1 in *; try destruct t; inv H3.
        destruct
          (type_eq_dec_spec t4 t6),
          (type_eq_dec_spec t5 t8),
          (type_eq_dec_spec t7 t9);
        cbn in *; subst; inv H4; try congruence.
        econstructor; apply infer_correct; eassumption.
    destruct t; cbn; intro H; inv H.
      assumption.
      destruct (check_correct'' G t A).
        reflexivity.
        contradiction.
      destruct (infer_correct'' G t (TArr A0 A)).
        rewrite (H0 H3). destruct (check_correct'' G t0 A0); subst.
          reflexivity.
          contradiction.
      1-3: reflexivity.
      destruct (infer_correct'' G t2 A), (infer_correct'' G t3 A).
        rewrite (H0 H6), (H2 H7).
        destruct (check_correct'' G t1 TBool); subst.
          cbn. destruct (type_eq_dec_spec A A); congruence.
          contradiction.
      destruct (infer_correct'' G t1 A0), (infer_correct'' G t2 B).
        rewrite (H0 H3), (H2 H5). reflexivity.
      destruct (infer_correct'' G t (TProd A B)).
        rewrite (H0 H2). reflexivity.
      destruct (infer_correct'' G t (TProd A0 A)).
        rewrite (H0 H2). reflexivity.
      destruct
            (infer_correct'' G t1 (TSum A0 B)),
            (infer_correct'' G t2 (TArr A0 A)),
            (infer_correct'' G t3 (TArr B A)).
        rewrite (H0 H4), (H2 H6), (H5 H7).
        destruct
          (type_eq_dec_spec A0 A0),
          (type_eq_dec_spec B B),
          (type_eq_dec_spec A A); subst; cbn; congruence.
  destruct t; cbn; intros.
    case_eq (infer G t); intros.
      destruct (type_eq_dec_spec A t0); constructor; subst.
        constructor. apply infer_correct. assumption.
        intro. inv H0. destruct (infer_correct'' G t A).
          specialize (H1 H3). congruence.
      constructor. intro. inv H0. destruct (infer_correct'' G t A).
        specialize (H1 H3). congruence.
    destruct A; try constructor; try inversion 1.
      destruct (check_correct''
        (fun v0 : V => if v =? v0 then Some A1 else G v0) t A2);
      constructor.
        constructor. assumption.
        intro. inv H. contradiction.
    destruct (check_correct'' G t TEmpty); subst; constructor.
      constructor. assumption.
      intro. inv H. contradiction.
    destruct A; try constructor; try inversion 1.
      destruct (check_correct'' G t A1); constructor.
        constructor. assumption.
        intro. inv H. contradiction.
    destruct A; try constructor; try inversion 1.
      destruct (check_correct'' G t A2); constructor.
        constructor. assumption.
        intro. inv H. contradiction.
Qed.

End Bidirectional_STLC_with_stuff.
