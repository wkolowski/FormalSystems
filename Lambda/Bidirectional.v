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
(* PHOAS
    | ht_Abs :
        forall (G : Ctx) (f : V -> tm) (A B : type),
          (forall v : V, has_type G (f v) B) ->
            has_type G (TLam f) B
*)
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
    | _ => true
(*        match infer G t with
            | Some A' => type_eq_dec A A'
            | _ => false
        end
*)
end.

Lemma type_eq_dec_refl :
  forall A : type, type_eq_dec A A = true.
Proof.
  induction A; cbn.
    reflexivity.
    rewrite IHA1, IHA2. cbn. reflexivity.
Qed.

Lemma infer_ok :
  forall (G : Ctx) (t : tm) (A : type),
    infer_type G t A -> infer G t = Some A

with check_ok :
  forall (G : Ctx) (t : tm) (A : type),
    check_type G t A -> check G t A = true

with infer_check :
  forall (G : Ctx) (t : tm) (A : type),
    infer G t = Some A -> check G t A = true.
Proof.
  destruct 1; cbn; intros.
    assumption.
    rewrite (infer_ok _ _ _ H), (check_ok _ _ _ H0). reflexivity.
    1-2: reflexivity.
    rewrite (check_ok _ _ _ H). reflexivity.
  destruct 1; cbn; intros.
    apply check_ok. assumption.
    rewrite !check_ok; cbn; auto.
  induction t; cbn.
Admitted.