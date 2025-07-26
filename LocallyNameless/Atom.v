Require Import
  List
  Coq.Classes.DecidableClass
  Lia.

Import ListNotations.

Class isAtom (Atom : Type) : Type :=
{
  Decidable_isAtom :: forall x y : Atom, Decidable (x = y);
  fresh : list Atom -> Atom;
  fresh_spec : forall l : list Atom, ~ In (fresh l) l;
}.

Inductive Atom : Type :=
| Fresh : list Atom -> Atom.

Definition out (x : Atom) : list Atom :=
match x with
| Fresh l => l
end.

(*
Inductive Atom : Type := Fresh
{
  out : list Atom;
}.
*)

Fixpoint size (x : Atom) : nat :=
match x with
| Fresh l => 1 + fold_right (fun h t => size h + t) 0 l
end.

Definition sizes l := 1 + fold_right (fun h t => size h + t) 0 l.

Fixpoint eq_dec_Atom (x y : Atom) : {x = y} + {x <> y}.
Proof.
  refine
  (
    match x, y with
    | Fresh lx, Fresh ly =>
      match list_eq_dec eq_dec_Atom lx ly with
      | left eq => _
      | right neq => _
      end
    end
  ).
  - now left; f_equal.
  - now right; intros [=].
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
  fresh := Fresh;
}.
Proof.
  intros l Hin.
  apply In_size in Hin. cbn in Hin.
  now lia.
Defined.

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
