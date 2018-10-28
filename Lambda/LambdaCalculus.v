Require Import List.
Import ListNotations.

Require Import Bool.

Parameter V : Type.
Parameter dec : V -> V -> bool.
Parameter dec_spec :
  forall x y : V, reflect (x = y) (dec x y).

Require Import Arith.

Notation "x =? y" := (dec x y) (at level 70).

Inductive Term : Type :=
    | Var : V -> Term
    | Lam : (V -> Term) -> Term
    | App : Term -> Term -> Term.

Fixpoint subst (M : Term) (x : V) (N : Term) : Term :=
match M with
    | Var v => if x =? v then N else Var v
    | Lam M' => Lam (fun v : V => (subst (M' v) x N))
    | App P Q => App (subst P x N) (subst P x Q)
end.

(* TODO: it's high time to learn PHOAS properly *)
(*
Inductive Beta : Term -> Term -> Prop :=
    | BetaContraction :
        forall (M : V -> Term) (N : Term), Beta (App (Lam M) N)
*)