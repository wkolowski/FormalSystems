Require Export
  List
  Coq.Classes.DecidableClass
  Lia.

Export ListNotations.

Arguments decide : simpl never.

Ltac decide_all :=
repeat match goal with
| |- context [decide (?x = ?x)] => rewrite Decidable_complete by easy
| |- context [decide (?x = ?y)] => decide (x = y); subst; cbn; try easy
| H : context [decide (?x = ?y)] |- _ => decide (x = y); subst; try easy; cbn in H
end.

(** * Class of Atom-like types *)

Class isAtom (Atom : Type) : Type :=
{
  Decidable_isAtom :: forall x y : Atom, Decidable (x = y);
  fresh : list Atom -> Atom;
  Fresh (x : Atom) (l : list Atom) : Prop := ~ In x l;
  fresh_spec : forall l : list Atom, Fresh (fresh l) l;
}.

Arguments fresh Atom !_ : simpl nomatch.

Notation "x # l" := (Fresh x l) (at level 68).

(** ** Freshness tactics *)
Lemma incl_app_l :
  forall {A : Type} (l1 l2 l3 : list A),
    incl l1 l2 -> incl l1 (l2 ++ l3).
Proof.
  unfold incl.
  intros.
  rewrite in_app_iff.
  now firstorder.
Qed.

Lemma incl_app_r :
  forall {A : Type} (l1 l2 l3 : list A),
    incl l1 l3 -> incl l1 (l2 ++ l3).
Proof.
  unfold incl.
  intros.
  rewrite in_app_iff.
  now firstorder.
Qed.

Section sec_Fresh_lemmas.

Context
  {Atom : Type}
  {isAtom_Atom : isAtom Atom}.

Lemma Fresh_incl :
  forall (x : Atom) (l1 l2 : list Atom),
    incl l1 l2 -> x # l2 -> x # l1.
Proof.
  now firstorder.
Qed.

Lemma fresh_incl :
  forall (l1 l2 : list Atom),
    incl l1 l2 -> fresh l2 # l1.
Proof.
  intros.
  eapply Fresh_incl with l2; [easy |].
  now apply fresh_spec.
Qed.

Lemma Fresh_app :
  forall (x : Atom) (l1 l2 : list Atom),
    x # l1 ++ l2 <-> x # l1 /\ x # l2.
Proof.
  now unfold Fresh; intros; rewrite in_app_iff; firstorder.
Qed.

Lemma Fresh_nil :
  forall (x : Atom),
    x # [] <-> True.
Proof.
  now unfold Fresh; intros; cbn; firstorder.
Qed.

Lemma Fresh_cons :
  forall (x y : Atom) (l : list Atom),
    x # (y :: l) <-> x <> y /\ x # l.
Proof.
  now unfold Fresh; intros; cbn; firstorder.
Qed.

End sec_Fresh_lemmas.

Ltac solve_fresh :=
repeat match goal with
| |- fresh _ # _ => apply fresh_incl
| |- incl ?l ?l => apply incl_refl
| |- incl _ _ => now apply incl_app_l
| |- incl _ _ => apply incl_app_r
| H : ?x # ?l1 |- ?x # ?l2 => apply (Fresh_incl x l2 l1); [clear H | easy]
end.

Ltac rewrite_fresh :=
  repeat (rewrite ?map_app, ?Fresh_app, ?Fresh_cons, ?Fresh_nil).

Ltac rewrite_fresh_in H :=
  repeat (rewrite ?map_app, ?Fresh_app, ?Fresh_cons, ?Fresh_nil in H).

Ltac solve_fresh' := try
match goal with
| |- ?x # ?l =>
  rewrite_fresh;
  match goal with
  | H : x # ?l' |- _ =>
    rewrite_fresh_in H; firstorder
  end
| |- fresh ?l1 # ?l2 =>
  rewrite_fresh;
  let H := fresh "H" in
    assert (H := fresh_spec l1);
      rewrite_fresh_in H; firstorder
end.

(** * Inductive Atoms *)

Inductive Atom : Type :=
| mkAtom : list Atom -> Atom.

Fixpoint eq_dec_Atom (x y : Atom) : {x = y} + {x <> y}.
Proof.
  decide equality.
  exact (list_eq_dec eq_dec_Atom _ _).
Defined.

#[export, refine] Instance Decidable_eq_Atom :
  forall x y : Atom, Decidable (x = y) :=
{
  Decidable_witness :=
    match eq_dec_Atom x y with
    | left _ => true
    | right _ => false
    end;
}.
Proof.
  now destruct (eq_dec_Atom x y).
Defined.

Fixpoint size (x : Atom) : nat :=
match x with
| mkAtom l => 1 + fold_right (fun h t => size h + t) 0 l
end.

Definition sizes l := 1 + fold_right (fun h t => size h + t) 0 l.

Lemma In_size :
  forall (x : Atom) (l : list Atom),
    In x l -> size x < sizes l.
Proof.
  induction l as [| h t IH]; intros Hin; [easy |].
  destruct Hin as [-> | Hin]; cbn; [now lia |].
  unfold sizes in IH.
  specialize (IH Hin).
  now lia.
Qed.

#[export, refine] Instance isAtom_Atom : isAtom Atom :=
{
  fresh := mkAtom;
}.
Proof.
  intros l Hin.
  apply In_size in Hin. cbn in Hin.
  now lia.
Defined.

(** * Natural numbers as atoms *)

Fixpoint fresh_nat (l : list nat) : nat :=
match l with
| [] => 0
| h :: t => 1 + max h (fresh_nat t)
end.

Lemma fresh_nat_aux :
  forall (l : list nat) (n : nat),
    In n l -> n < fresh_nat l.
Proof.
  induction l as [| h t]; cbn; intros; [easy |].
  destruct H as [-> | H]; [now lia |].
  now specialize (IHt _ H); lia.
Qed.

#[export, refine] Instance isAtom_nat : isAtom nat :=
{
  fresh := fresh_nat;
}.
Proof.
  intros l Hin.
  apply fresh_nat_aux in Hin.
  now lia.
Defined.
