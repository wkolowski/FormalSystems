Require Import List.
Import ListNotations.

Require Import Bool.

Parameter V : Type.
Parameter dec : V -> V -> bool.
Parameter dec_spec :
  forall x y : V, reflect (x = y) (dec x y).

Require Import Arith.

Notation "x =? y" := (dec x y) (at level 70).

Inductive Term (Var : Type) : Type :=
    | Var : Var -> Term Var
    | Lam : (Var -> Term Var) -> Term Var
    | App : Term Var -> Term Var -> Term Var.

Definition Term' : Type := forall Var : Type, Term Var.

Arguments Var {Var} _.
Arguments Lam {Var} _.
Arguments App {Var} _ _.

Fixpoint numOfVars (t : Term unit) : nat :=
match t with
    | Var _ => 1
    | Lam t' => numOfVars (t' tt)
    | App t1 t2 => numOfVars t1 + numOfVars t2
end.

Fixpoint subst' {A : Type} (M : Term (Term A)) : Term A :=
match M with
    | Var v => v
    | Lam M' => Lam (fun x : A => subst' (M' (Var x)))
    | App P Q => App (subst' P) (subst' Q)
end.

Definition subst
  (M : forall A : Type, A -> Term A) (N : Term') : Term' :=
    fun A : Type => subst' (M (Term A) (N A)).

Compute
  subst (fun A x => App (Var x) (Var x)) (fun A => Lam (fun x : A => Var x)).

(*
Inductive Beta {A : Type} : Term A -> Term A -> Prop :=
    | BetaContraction :
        forall (M : A -> Term A) (N : Term A),
          Beta (App (Lam M) N) 
    | BetaAppL :
        forall P P' Q : Term',
          Beta P P' ->
            Beta (fun A => App (P A) (Q A)) (fun A => App (P' A) (Q A))
    | BetaAppR :
        forall P Q Q' : Term',
          Beta Q Q' ->
            Beta (fun A => App (P A) (Q A)) (fun A => App (P A) (Q' A))
    | BetaLam :
        forall M M' : forall A : Type, A -> Term A,
          Beta M M' ->
          Beta (fun A => Lam (M A)) (fun A => Lam (M' A)).
*)

(*
Inductive Beta : Term' -> Term' -> Prop :=
    | BetaContraction :
        forall (M : forall A : Type, A -> Term A) (N : Term'),
          Beta (fun A => App (Lam (M A)) (N A)) (fun A => subst M N A)
    | BetaAppL :
        forall P P' Q : Term',
          Beta P P' ->
            Beta (fun A => App (P A) (Q A)) (fun A => App (P' A) (Q A))
    | BetaAppR :
        forall P Q Q' : Term',
          Beta Q Q' ->
            Beta (fun A => App (P A) (Q A)) (fun A => App (P A) (Q' A))
    | BetaLam :
        forall M M' : forall A : Type, A -> Term A,
          (forall x : (forall A : Type, Term A),
            Beta (fun A => M (Term A) (x A)) (fun A => M' (Term A) (x A))) ->
          Beta (fun A => Lam (M A)) (fun A => Lam (M' A)).
*)