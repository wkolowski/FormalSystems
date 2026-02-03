From Stdlib Require Export Recdef.

From FormalSystems Require Export Base.

Inductive AExp : Type :=
    | AConst : nat -> AExp
    | Var : Loc -> AExp
    | ABinOp : (nat -> nat -> nat) -> AExp -> AExp -> AExp.

Inductive BExp : Type :=
    | BConst : bool -> BExp
    | BRelOp : (nat -> nat -> bool) -> AExp -> AExp -> BExp
    | Not : BExp -> BExp
    | BBinOp : (bool -> bool -> bool) -> BExp -> BExp -> BExp.

Inductive Com : Type :=
    | Skip : Com
    | Asgn : Loc -> AExp -> Com
    | Seq : Com -> Com -> Com
    | If : BExp -> Com -> Com -> Com
    | While : BExp -> Com -> Com.

Definition State : Type := Loc -> nat.

Definition initialState : State := fun _ => 0.

Definition changeState (s : State) (x : Loc) (n : nat) : State :=
  fun y : Loc => if x =? y then n else s y.

Fixpoint loca (a : AExp) : list Loc :=
match a with
    | AConst _ => []
    | Var x => [x]
    | ABinOp f a1 a2 => loca a1 ++ loca a2
end.

Definition acompatible (a : AExp) (s1 s2 : State) : Prop :=
  forall x : Loc, In x (loca a) -> s1 x = s2 x.

Fixpoint locb (b : BExp) : list Loc :=
match b with
    | BConst _ => []
    | BRelOp _ a1 a2 => loca a1 ++ loca a2
    | Not b' => locb b'
    | BBinOp _ b1 b2 => locb b1 ++ locb b2
end.

Definition bcompatible (b : BExp) (s1 s2 : State) : Prop :=
  forall x : Loc, In x (locb b) -> s1 x = s2 x.

(* The list of all variables which are assigned to by the instruction c. *)
Fixpoint locw (c : Com) : list Loc :=
match c with
    | Skip => []
    | Asgn v _ => [v]
    | Seq c1 c2 => locw c1 ++ locw c2
    | If _ c1 c2 => locw c1 ++ locw c2
    | While _ c => locw c
end.

Definition wcompatible (c : Com) (s1 s2 : State) : Prop :=
  forall x : Loc, In x (locw c) -> s1 x = s2 x.

(* The list of all variables mentioned in c. *)
Fixpoint loc (c : Com) : list Loc :=
match c with
    | Skip => []
    | Asgn v a => v :: loca a
    | Seq c1 c2 => loc c1 ++ loc c2
    | If b c1 c2 => locb b ++ loc c1 ++ loc c2
    | While b c => locb b ++ loc c
end.

Definition ccompatible (c : Com) (s1 s2 : State) : Prop :=
  forall x : Loc, In x (loc c) -> s1 x = s2 x.