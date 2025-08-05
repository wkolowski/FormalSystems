From FormalSystems Require Export LocallyNameless.OC.

(** * Locally nameless sets *)

Class LocallyNameless
  (Atom Term : Type)
  (OCO : Open nat Atom Term)
  (OCC : Close nat Atom Term)
  (OC : OC nat Atom Term OCO OCC)
 : Type :=
{
  fv : Term -> list Atom;
  supports_fv : forall t : Term, supports (fv t) t;
  finite_index_support : forall t : Term, exists i : nat, LocallyClosed i t;
}.

Section LocallyNameless_IA.

Context
  {Index Atom : Type}
  {Decidable_eq_Index : forall i j : Index, Decidable (i = j)}
  {isAtom_Atom : isAtom Atom}.

#[refine] Instance LocallyNameless_IA :
  LocallyNameless Atom (nat + Atom) Open_IA Close_IA OC_IA :=
{
  fv (ia : nat + Atom) :=
    match ia with
    | inl _ => []
    | inr a => [a]
    end;
}.
Proof.
  - intros [i | a]; unfold supports, Fresh'; cbn; [easy |].
    now intros b; decide_all; firstorder.
  - intros [i | a]; unfold LocallyClosed; cbn.
    + exists (S i).
      intros j Hle.
      exists (fresh []).
      now decide_all; lia.
    + exists 0.
      intros _ _.
      now exists (fresh []).
Defined.

End LocallyNameless_IA.

Section wut.

Context
  (Atom Term : Type)
  (OCO : Open nat Atom Term)
  (OCC : Close nat Atom Term)
  (OC : OC nat Atom Term OCO OCC).

Lemma finite_index_support_spec :
  (forall t : Term, exists i : nat, LocallyClosed i t)
    <->
  (exists bv : Term -> list nat,
    forall (t : Term) (i : nat) (a : Atom),
      ~ In i (bv t) -> t {{ i ~> a }} = t).
Proof.
  split.
  - intros HLocallyClosed.
Abort.

End wut.
