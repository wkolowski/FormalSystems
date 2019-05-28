Require Import List.
Import ListNotations.

Require Import Bool.
Require Import Arith.

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
    | TArr t11 t12, TArr t21 t22 =>
        type_eq_dec t11 t21 && type_eq_dec t12 t22
    | _, _ => false
end.

Fixpoint infer (G : Ctx) (t : tm) : option type :=
match t with
    | TVar x => G x
    | TApp t1 t2 =>
        match infer G t1, infer G t2 with
            | Some (TArr A B), Some A' =>
                if type_eq_dec A A' then Some B else None
            | _, _ => None
        end
    | TLam x t' => None
    | TTrue => Some TBool
    | TFalse => Some TBool
    | TIf t1 t2 t3 =>
        match infer G t1, infer G t2, infer G t3 with
            | Some TBool, Some A, Some A' =>
                if type_eq_dec A A' then Some A else None
            | _, _, _ => None
        end
end.

Lemma type_eq_dec_refl :
  forall A : type, type_eq_dec A A = true.
Proof.
  induction A; cbn.
    reflexivity.
    rewrite IHA1, IHA2. cbn. reflexivity.
Qed.

Lemma has_type_infer :
  forall (G : Ctx) (x : tm) (A : type),
    has_type G x A -> infer G x = Some A.
Proof.
  induction 1; cbn.
    assumption.
    rewrite IHhas_type1, IHhas_type2, type_eq_dec_refl. reflexivity.
    admit. (* lambda *)
    1-2: reflexivity.
    rewrite IHhas_type1, IHhas_type2, IHhas_type3, type_eq_dec_refl.
      reflexivity.
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

Fixpoint type_eq_dec (t1 t2 : type) : bool :=
match t1, t2 with
    | TBool, TBool => true
    | TArr t11 t12, TArr t21 t22 =>
        type_eq_dec t11 t21 && type_eq_dec t12 t22
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
            | TArr X Y =>
                check (fun v : V => if x =? v then Some X else G v) t Y
            | _ => false
        end
    | TIf t1 t2 t3 =>
        check G t1 TBool && check G t2 A && check G t3 A
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
  induction A; cbn.
    reflexivity.
    rewrite IHA1, IHA2. cbn. reflexivity.
Qed.

Ltac inv H := inversion H; subst; clear H.

Lemma infer_check :
  forall (G : Ctx) (t : tm) (A : type),
    infer G t = Some A -> check G t A = true.
Proof.
  destruct t; cbn; intros.
    rewrite H. apply type_eq_dec_refl.
    destruct (infer G t1) as [[] |]; inv H.
      destruct (check G t2 t); inv H1. cbn. apply type_eq_dec_refl.
    1-4: inv H; auto.
    destruct (check G t t0); inv H. cbn. apply type_eq_dec_refl.
Qed.

Lemma type_eq_dec_true :
  forall A B : type,
    type_eq_dec A B = true -> A = B.
Proof.
  induction A; destruct B; cbn; intros; try congruence.
  specialize (IHA1 B1). specialize (IHA2 B2).
  destruct (type_eq_dec A1 B1), (type_eq_dec A2 B2).
    all: firstorder; congruence.
Qed.

Lemma infer_correct :
  forall (G : Ctx) (t : tm) (A : type),
    infer G t = Some A -> infer_type G t A

with check_correct :
  forall (G : Ctx) (t : tm) (A : type),
    check G t A = true -> check_type G t A.
Proof.
  destruct t; cbn; intros.
    constructor. assumption.
    case_eq (infer G t1); intros; rewrite H0 in H.
      destruct t; inv H. case_eq (check G t2 t3); intro; rewrite H in H2; inv H2.
        eapply infer_App.
          eapply infer_correct. exact H0.
          apply check_correct. assumption.
    1-5: inversion H; subst; repeat constructor.
    case_eq (check G t t0); intro; rewrite H0 in H; inv H.
      constructor. apply check_correct. assumption.
  destruct t; cbn; intros.
    case_eq (G v); intros; rewrite H0 in H; inv H.
      apply type_eq_dec_true in H2; subst. do 2 constructor. assumption.
    case_eq (infer G t1); intros; rewrite H0 in H.
      destruct t; inv H. case_eq (check G t2 t3); intro; rewrite H in H2; inv H2.
        apply type_eq_dec_true in H3; subst.
          constructor. eapply infer_App.
            apply infer_correct. exact H0.
            apply check_correct. assumption.
      congruence.
    1-3: destruct A; inversion H.
      constructor. apply check_correct. assumption.
      do 2 constructor.
      do 2 constructor.
    constructor; apply check_correct;
      destruct (check G t1 TBool), (check G t2 A), (check G t3 A); cbn in H; auto.
    constructor. case_eq (check G t t0); intros; rewrite H0 in H; inv H.
      apply type_eq_dec_true in H2; subst. constructor.
        apply check_correct. assumption.
Qed.

Lemma infer_complete :
  forall (G : Ctx) (t : tm) (A : type),
    infer_type G t A -> infer G t = Some A

with check_complete :
  forall (G : Ctx) (t : tm) (A : type),
    check_type G t A -> check G t A = true.
Proof.
  destruct 1; cbn; intros.
    assumption.
    rewrite (infer_complete _ _ _ H), (check_complete _ _ _ H0). reflexivity.
    1-2: reflexivity.
    rewrite (check_complete _ _ _ H). reflexivity.
  destruct 1; cbn; intros.
    apply check_complete. assumption.
    rewrite !check_complete; cbn; auto.
    apply infer_check. apply infer_complete. apply H.
Qed.

End Bidirectional_STLC_with_Booleans.