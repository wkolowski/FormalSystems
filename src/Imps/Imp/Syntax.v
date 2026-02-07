From FormalSystems Require Export Base.

Inductive AExp : Type :=
| AConst : nat -> AExp
| Var : Atom -> AExp
| ABinOp : (nat -> nat -> nat) -> AExp -> AExp -> AExp.

Inductive BExp : Type :=
| BConst : bool -> BExp
| BRelOp : (nat -> nat -> bool) -> AExp -> AExp -> BExp
| Not : BExp -> BExp
| BBinOp : (bool -> bool -> bool) -> BExp -> BExp -> BExp.

Inductive Com : Type :=
| Skip : Com
| Asgn : Atom -> AExp -> Com
| Seq : Com -> Com -> Com
| If : BExp -> Com -> Com -> Com
| While : BExp -> Com -> Com.

Definition State : Type := Atom -> nat.

Definition initialState : State := fun _ => 0.

Definition changeState (s : State) (x : Atom) (n : nat) : State :=
  fun y : Atom => if decide (x = y) then n else s y.

Fixpoint fva (a : AExp) : list Atom :=
match a with
| AConst _ => []
| Var x => [x]
| ABinOp f a1 a2 => fva a1 ++ fva a2
end.

Definition acompatible (a : AExp) (s1 s2 : State) : Prop :=
  forall x : Atom, In x (fva a) -> s1 x = s2 x.

Fixpoint fvb (b : BExp) : list Atom :=
match b with
| BConst _ => []
| BRelOp _ a1 a2 => fva a1 ++ fva a2
| Not b' => fvb b'
| BBinOp _ b1 b2 => fvb b1 ++ fvb b2
end.

Definition bcompatible (b : BExp) (s1 s2 : State) : Prop :=
  forall x : Atom, In x (fvb b) -> s1 x = s2 x.

(* The list of all variables which are assigned to by the instruction c. *)
Fixpoint fvw (c : Com) : list Atom :=
match c with
| Skip => []
| Asgn v _ => [v]
| Seq c1 c2 => fvw c1 ++ fvw c2
| If _ c1 c2 => fvw c1 ++ fvw c2
| While _ c => fvw c
end.

Definition wcompatible (c : Com) (s1 s2 : State) : Prop :=
  forall x : Atom, In x (fvw c) -> s1 x = s2 x.

(* The list of all variables mentioned in c. *)
Fixpoint fv (c : Com) : list Atom :=
match c with
| Skip => []
| Asgn v a => v :: fva a
| Seq c1 c2 => fv c1 ++ fv c2
| If b c1 c2 => fvb b ++ fv c1 ++ fv c2
| While b c => fvb b ++ fv c
end.

Definition ccompatible (c : Com) (s1 s2 : State) : Prop :=
  forall x : Atom, In x (fv c) -> s1 x = s2 x.
