(*

  If there was anything like coinduction-coinduction in Coq, this is how we
  would use it to define Constant Games together with their Winners at the
  same time.
*)

(*
CoInductive Structure : Type :=
{
    winner : Player;
    Labmove : Type;
    who : Labmove -> Player;
    next : Labmove -> Structure;
}

with Winner (g : Structure) (p : Player) : Prop :=
{
    Winner0 : (Labmove g -> False) -> p = winner g;
    Winner1 :
      Labmove g ->
        (exists move : Labmove g,
          who g move = p /\ Winner (next g move) p) \/
        (forall move : Labmove g,
          who g move = swap p -> Winner (next g move) p);
}.
*)

Inductive Player : Type :=
    | Machine : Player
    | Nature  : Player.

Definition opposite (p : Player) : Player :=
match p with
    | Machine => Nature
    | Nature  => Machine
end.

CoInductive Structure : Type :=
{
    Labmove : Player -> Type;
    next : forall {p : Player}, Labmove p -> Structure;
}.

Inductive RunF (F : Structure -> Type) (g : Structure) : Type :=
    | Nil
    | Cons : forall {p : Player} (h : Labmove g p) (t : F (next g h)), RunF F g.

Arguments Nil  {F g}.
Arguments Cons {F g p} _ _.

CoInductive Run (g : Structure) : Type :=
{
    Out : RunF Run g;
}.

Arguments Out {g} _.

Inductive Position (g : Structure) : Type :=
    | In : RunF Position g -> Position g.

Arguments In {g} _.

Require F2.

CoFixpoint len {g : Structure} (r : Run g) : F2.conat :=
{|
    F2.out :=
      match Out r with
          | Nil => F2.Z
          | Cons _ t => F2.S (len t)
      end;
|}.

Definition isFinite {g : Structure} (r : Run g) : Prop :=
  F2.Finite (len r).

Definition PeriFinite (g : Structure) : Prop :=
  forall r : Run g, isFinite r.

Inductive FiniteDepth : nat -> Structure -> Type :=
    | FD_0 :
        forall (n : nat) (g : Structure),
          (forall p : Player, Labmove g p -> False) -> FiniteDepth n g
    | FD_s :
        forall (n : nat) (g : Structure),
          (forall {p : Player} (m : Labmove g p), FiniteDepth n (next g m)) ->
            FiniteDepth (S n) g.

Inductive Heterogenous (g : Structure) : Type :=
    | Htg (m : Labmove g Machine) (n : Labmove g Nature).

Inductive StrictF (X : Type) (g : Structure) : Type :=
    | NoMachineMoves : (Labmove g Machine -> False) -> X -> StrictF X g
    | NoNatureMoves  : (Labmove g Nature  -> False) -> X -> StrictF X g.

Arguments NoMachineMoves {X g} _ _.
Arguments NoNatureMoves  {X g} _ _.

CoInductive Strict (g : Structure) : Type :=
{
    StrictOut : StrictF (Strict g) g;
}.

Arguments StrictOut {g} _.



(*
Inductive Winner {g : Structure} : Run g -> Player -> Type :=
    | Winner_NoMoves :
        forall {p : Player}, (Labmove g (opposite p) -> False) -> Winner r p
    | Winner_Moves   :
        forall {p : Player}, Labmove g p -> Winner .
*)

CoInductive Winner {g : Structure} (r : Run g) (p : Player) : Prop :=
{
    Winner0 : (Labmove g -> False) -> p = winner g;
    Winner1 :
      Labmove g ->
        (exists move : Labmove g,
          who g move = p /\ Winner (next g move) p) \/
        (forall move : Labmove g,
          who g move = swap p -> Winner (next g move) p);
}.