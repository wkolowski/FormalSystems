From FormalSystems Require Export LocallyNameless.STLC.Funs.Bidirectional.

Require Import Bool.

(** * Hint-based typing *)

Lemma size_open :
  forall (t : Tm) (i : nat) (x : Atom),
    size (t {{ i ~> x }}) = size t.
Proof.
  now induction t; cbn; intros; rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; auto.
Qed.

Require Import Program.

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