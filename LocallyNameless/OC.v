From FormalSystems Require Export LocallyNameless.Atom.

Class Open (Index Atom Term : Type) : Type :=
  open : Term -> Index -> Atom -> Term.

Class Close (Index Atom Term : Type) : Type :=
  close : Term -> Index -> Atom -> Term.

Arguments open Index Atom Term Open !_ _ _.
Arguments close Index Atom Term Close !_ _ _.

Notation "t {{ i ~> a }}" := (open t i a) (at level 68).
Notation "t {{ i <~ a }}" := (close t i a) (at level 68).

Class OC
  (Index Atom Term : Type)
  (OCO : Open Index Atom Term)
  (OCCC : Close Index Atom Term) : Type :=
{
  OC_isAtom :: isAtom Atom;
  OC_Decidable_eq_Index :: forall i j : Index, Decidable (i = j);
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

(** ** OC set of indices and atoms *)

Section IA.

Context
  {Index Atom : Type}
  {Decidable_eq_Index : forall i j : Index, Decidable (i = j)}
  {isAtom_Atom : isAtom Atom}.

Instance Open_IA : Open Index Atom (Index + Atom) :=
  fun (ia : Index + Atom) (i : Index) (a : Atom) =>
    match ia with
    | inl j => if decide (i = j) then inr a else inl j
    | inr x => inr x
    end.

Instance Close_IA : Close Index Atom (Index + Atom) :=
  fun (ia : Index + Atom) (i : Index) (a : Atom) =>
    match ia with
    | inl j => inl j
    | inr x => if decide (a = x) then inl i else inr x
    end.

#[refine] Instance OC_IA : OC Index Atom (Index + Atom) Open_IA Close_IA := {}.
Proof.
  all: intros [j | x] *; cbn; now decide_all.
Qed.

End IA.

(** ** Freshness from the paper *)

Section Fresh'_lemmas.

Context
  (Index Atom Term : Type)
  (Open_Term : Open Index Atom Term)
  (Close_Term : Close Index Atom Term)
  (OC_Term : OC Index Atom Term Open_Term Close_Term).

(* Lemma 2.4 from the paper *)
Lemma Fresh'_invariant_aux :
  forall (t : Term) (i j : Index) (a : Atom),
    t {{ i <~ a }} = t <-> t {{ j <~ a }} = t.
Proof.
  now split; intros [= <-]; rewrite close_close_eq.
Qed.

Lemma Fresh'_invariant_aux' :
  forall (t : Term) (i : Index) (a : Atom),
    t {{ i <~ a }} = t <-> forall j : Index, t {{ j <~ a }} = t.
Proof.
  split; [| easy].
  now intros [= <-] j; rewrite close_close_eq.
Qed.

Lemma Fresh'_invariant_aux_open :
  forall (t : Term) (i : Index) (a b : Atom),
    t {{ i ~> a }} = t <-> t {{ i ~> b }} = t.
Proof.
  now split; intros [= <-]; rewrite open_open_eq.
Qed.

End Fresh'_lemmas.

Section Fresh'.

Context
  {Atom Term : Type}
  {Open_Term : Open nat Atom Term}
  {Close_Term : Close nat Atom Term}
  {OC_Term : OC nat Atom Term Open_Term Close_Term}.

Definition Fresh' (a : Atom) (t : Term) : Prop :=
  t {{ 0 <~ a }} = t.

Lemma Fresh'_invariant :
  forall (t : Term) (i : nat) (a : Atom),
    Fresh' a t <-> t {{ i <~ a }} = t.
Proof.
  intros; unfold Fresh'.
  now rapply Fresh'_invariant_aux.
Qed.

End Fresh'.

Section lci.

Context
  {Atom Term : Type}
  {Open_Term : Open nat Atom Term}
  {Close_Term : Close nat Atom Term}
  {OC_Term : OC nat Atom Term Open_Term Close_Term}.

Definition lci (i : nat) (t : Term) : Prop :=
  forall j : nat, i <= j -> exists a : Atom, t {{ j ~> a }} = t.

End lci.

