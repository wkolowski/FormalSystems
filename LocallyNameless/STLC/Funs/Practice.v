From FormalSystems Require Import LocallyNameless.STLC.Funs.

From Equations Require Import Equations.

Require Import Bool.

Equations isRedex (t : Tm) : bool :=
isRedex (fvar _)                 := false;
isRedex (bvar _)                 := false;
isRedex (abs _)                  := false;
isRedex (app (abs _) _)          := true;
isRedex (app _ _)                := false;
isRedex (annot _ _)              := true;
isRedex unit                     := false;
isRedex (elimUnit _ _)           := true;
isRedex (abort t')               := false;
isRedex (pair _ _)               := false;
isRedex (outl (pair _ _))        := true;
isRedex (outl _)                 := false;
isRedex (outr (pair _ _))        := true;
isRedex (outr _)                 := false;
isRedex (elimProd t1 (pair _ _)) := true;
isRedex (elimProd t1 _)          := false;
isRedex (inl _)                  := false;
isRedex (inr _)                  := false;
isRedex (case _ _ (inl _))       := true;
isRedex (case _ _ (inr _))       := true;
isRedex (case _ _ _)             := false;
isRedex zero                     := false;
isRedex (succ _)                 := false;
isRedex (rec _ _ zero)           := true;
isRedex (rec _ _ (succ _))       := true;
isRedex (rec _ _ _)              := false.

Lemma isRedex_spec :
  forall t : Tm,
    reflect (exists t', CbnContraction t t') (decide (lc t) && isRedex t).
Proof.
  intros t.
  decide (lc t); cbn; [| now constructor; intros [t' HC]; eauto].
  destruct t; simp isRedex; try constructor;
  try match goal with
  | H : lc _ |- exists _, _ => now inversion H; subst; eauto
  | |- ~ _ => intros [t' HC]; inversion HC; subst
  end.
  - destruct t1; simp isRedex; constructor; auto;
      try match goal with
      | |- ~ _ => intros [t' HC]; inversion HC; subst
      end.
    now inversion H; subst; inversion Hlc1; subst; eauto.
  - destruct t; simp isRedex; constructor; auto;
      try match goal with
      | |- ~ _ => intros [t' HC]; inversion HC; subst
      | H : lc _ |- _ => inversion H; subst; clear H
      end.
    now inversion Hlc'; eauto.
  - destruct t; simp isRedex; constructor; auto;
      try match goal with
      | |- ~ _ => intros [t' HC]; inversion HC; subst
      | H : lc _ |- _ => inversion H; subst; clear H
      end.
    now inversion Hlc'; eauto.
  - destruct t2; simp isRedex; constructor;
      try match goal with
      | |- ~ _ => intros [t' HC]; inversion HC; subst
      | H : lc _ |- _ => inversion H; subst; clear H
      end.
    now inversion Hlc2; eauto.
  - destruct t3; simp isRedex; constructor;
      try match goal with
      | |- ~ _ => intros [t' HC]; inversion HC; subst
      | H : lc _ |- _ => inversion H; subst; clear H
      end.
    + now inversion Hlc3; eauto.
    + now inversion Hlc3; eauto.
  - destruct t3; simp isRedex; constructor;
      try match goal with
      | |- ~ _ => intros [t' HC]; inversion HC; subst
      end.
    + now inversion H; eauto.
    + now inversion H; inversion Hlc3; eauto.
Qed.

(*
Module wut.

Require Import Recdef.

Function hasRedex (t : Tm) {measure size t} : bool :=
match t with
| fvar _ => false
| bvar _ => false
| abs t' => hasRedex t'
| app t1 t2 =>
    match t1 with
    | abs _ => true
    | _ => hasRedex t1 || hasRedex t2
    end
| annot _ _ => true
| unit => false
| elimUnit _ _ => true
| abort t' => false
| pair t1 t2 => hasRedex t1 || hasRedex t2
| outl t' =>
    match t' with
    | pair _ _ => true
    | _ => hasRedex t'
    end
| outr t' =>
    match t' with
    | pair _ _ => true
    | _ => hasRedex t'
    end
| elimProd t1 t2 =>
    match t2 with
    | pair _ _ => true
    | _ => hasRedex t1 || hasRedex t2
    end
| inl t' => hasRedex t'
| inr t' => hasRedex t'
| case t1 t2 t3 =>
    match t3 with
    | inl _ => true
    | inr _ => true
    | _ => hasRedex t1 || hasRedex t2 || hasRedex t3
    end
| zero => false
| succ t' => hasRedex t'
| rec t1 t2 t3 =>
    match t3 with
    | zero => true
    | succ _ => true
    | _ => hasRedex t1 || hasRedex t2 || hasRedex t3
    end
end.
Proof.
  all: intros; subst; cbn; lia.
Defined.

Lemma hasRedex_complete :
  forall t t' : Tm,
    CbnStep t t' -> hasRedex t = true.
Proof.
Admitted.

Lemma hasRedex_spec :
  forall t : Tm,
    reflect (exists t', CbnStep t t') (hasRedex t && decide (lc t)).
Proof.
  intros t.
  functional induction (hasRedex t); cbn [andb];
    try constructor;
    repeat match goal with
    | |- ~ _ => let t' := fresh "t" in intros [t' Hs]; inversion Hs; subst
    | HC : CbnContraction _ _ |- _ => now inversion HC
    | HA : CbnAbortion _ _ |- _ => now inversion HA
    | Hlc : lc ?t |- _ =>  tryif is_var t then fail else inversion Hlc; subst; clear Hlc
    | |- exists _, _ => now eauto
    end.
  - destruct IHb.
Abort.

End wut.
*)

Equations hasRedex (t : Tm) : bool :=
hasRedex (fvar _)                := false;
hasRedex (bvar _)                := false;
hasRedex (abs t')                := hasRedex t';
hasRedex (app t1 t2)             with t1 =>
{
  | abs _ => true;
  | _     => orb (hasRedex t1) (hasRedex t2);
};
hasRedex (annot _ _)             := true;
hasRedex unit                    := false;
hasRedex (elimUnit _ _)          := true;
hasRedex (abort t')              := false;
hasRedex (pair t1 t2)            := hasRedex t1 || hasRedex t2;
hasRedex (outl t') with t' =>
{
  | pair _ _ => true;
  | _        => hasRedex t';
};
hasRedex (outr t') with t' =>
{
  | pair _ _ => true;
  | _        => hasRedex t';
};
hasRedex (elimProd t1 t2) with t2 =>
{
  | pair _ _ => true;
  | _        => hasRedex t1 || hasRedex t2;
};
hasRedex (inl t')                := hasRedex t';
hasRedex (inr t')                := hasRedex t';
hasRedex (case t1 t2 t3) with t3 =>
{
  | inl _ => true;
  | inr _ => true;
  | _     => hasRedex t1 || hasRedex t2 || hasRedex t3;
};
hasRedex zero                    := false;
hasRedex (succ t')               := hasRedex t';
hasRedex (rec t1 t2 t3) with t3 =>
{
  | zero   => true;
  | succ _ => true;
  | _      =>  hasRedex t1 || hasRedex t2 || hasRedex t3;
}.

Lemma hasRedex_spec :
  forall t : Tm,
    reflect (exists t', CbnStep t t') (hasRedex t && decide (lc t)).
Proof.
  intros t.
  funelim (hasRedex t); cbn; try constructor;
    repeat match goal with
    | |- ~ _ => let t' := fresh "t" in intros [t' Hs]; inversion Hs; subst
    | HC : CbnContraction _ _ |- _ => now inversion HC
    | HA : CbnAbortion _ _ |- _ => now inversion HA
    | Hlc : lc ?t |- _ =>  tryif is_var t then fail else inversion Hlc; subst; clear Hlc
    | |- exists _, _ => now eauto
    end.
Restart.
  intros t.
  decide (lc t); cbn; [| now rewrite andb_false_r; constructor; intros [t' HC]; eauto].
  rewrite andb_true_r.
  destruct t; simp hasRedex; try constructor;
  repeat match goal with
  | H : lc _ |- exists _, _ => now inversion H; subst; eauto
  | |- ~ _ => intros [t' HC]; inversion HC; subst
  | H : CbnContraction _ _ |- _ => now inversion H
  | H : CbnAbortion _ _ |- _ => now inversion H
  end.
Abort.
