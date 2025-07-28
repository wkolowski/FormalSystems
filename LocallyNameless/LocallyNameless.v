From FormalSystems Require Export LocallyNameless.Atom.

Class Open (Index Atom Term : Type) : Type :=
  open : Term -> Index -> Atom -> Term.

Class Close (Index Atom Term : Type) : Type :=
  close : Term -> Index -> Atom -> Term.

Arguments open Index Atom Term Open !_ _ _.
Arguments close Index Atom Term Close !_ _ _.

Notation "t {{ i ~> a }}" := (open t i a) (at level 68).
Notation "t {{ i <~ a }}" := (close t i a) (at level 68).

Class LocallyNameless
  (Index Atom Term : Type)
  (LNO : Open Index Atom Term)
  (LNC : Close Index Atom Term) : Type :=
{
  LocallyNameless_isAtom :: isAtom Atom;
  LocallyNameless_Decidable_eq_Index :: forall i j : Index, Decidable (i = j);
(*   LocallyNameless_Open :: Open Index Atom Term; *)
(*   LocallyNameless_Close :: Close Index Atom Term; *)
  open_open_eq : (* OC 1 *)
    forall (t : Term) (i : Index) (a b : Atom),
      t {{ i ~> a }} {{ i ~> b }} = t {{ i ~> a }};
  close_close_eq : (* OC 2 *)
    forall (t : Term) (i j : Index) (a : Atom),
      t {{ i <~ a }} {{ j <~ a }} = t {{ i <~ a }};
  open_close_eq : (* OC 3 *)
    forall (t : Term) (i : Index) (a : Atom),
      t {{ i ~> a }} {{ i <~ a }} = t {{ i <~ a }};
  close_open_eq : (* OC 4 *)
    forall (t : Term) (i : Index) (a : Atom),
      t {{ i <~ a }} {{ i ~> a }} = t {{ i ~> a }};
  open_open_neq : (* OC 5 *)
    forall (t : Term) (i j : Index) (a b : Atom),
      i <> j ->
        t {{ i ~> a }} {{ j ~> b }} = t {{ j ~> b }} {{ i ~> a }};
  close_close_neq : (* OC 6 *)
    forall (t : Term) (i j : Index) (a b : Atom),
      a <> b ->
        t {{ i <~ a }} {{ j <~ b }} = t {{ j <~ b }} {{ i <~ a }};
  open_close_neq : (* OC 7 *)
    forall (t : Term) (i j : Index) (a b : Atom),
      i <> j -> a <> b ->
        t {{ i ~> a }} {{ j <~ b }} = t {{ j <~ b }} {{ i ~> a }};
  open_close_open : (* OC 8 *)
    forall (t : Term) (i j : Index) (a b : Atom),
      t {{ i ~> a }} {{ j <~ a }} {{ j ~> b }}
        =
      t {{ j ~> b }} {{ i <~ a }} {{ i ~> b }};
  close_open_close : (* OC 9 *)
    forall (t : Term) (i j : Index) (a b : Atom),
      t {{ i <~ a }} {{ i ~> b }} {{ j <~ b }}
        =
      t {{ j <~ b }} {{ i ~> a }} {{ j <~ a }}
}.
