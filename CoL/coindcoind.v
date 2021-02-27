(*

  If there was anything like coinduction-coinduction in Coq, this is how we
  would use it to define Constant Games together with their Winners at the
  same time.

CoInductive ConstantGame : Type :=
{
    winner : Player;
    Labmove : Type;
    who : Labmove -> Player;
    next : Labmove -> ConstantGame;
}

with Winner (g : ConstantGame) (p : Player) : Prop :=
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