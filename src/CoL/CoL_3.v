(** * Computability Logic *)

(** This is an attempt at formalizing Giorgi Japaridze's Computability
    Logic based on "In the beginning was game semantics" from the book
    "Games: Unifying Logic, Language, and Philosophy".

    The approach is to replace Japaridze's "classical" definitions with
    mainly coinductive ones friendly to type theory. Currently it's
    rather experimental and certainly very broken, because he seems to
    define game operations by defining their structure and winner mutually
    at the same time. Here this would require mutual coinduction and I
    don't know how to do it properly. *)

From Stdlib Require Import Bool List Arith Setoid FunctionalExtensionality.
Import ListNotations.

Axiom LEM : forall P : Prop, P \/ ~ P.

Inductive Player : Type :=
| Machine : Player
| Nature : Player.

CoInductive ConstantGame : Type :=
{
  winner : Player;
  Labmove : Type;
  who : Labmove -> Player;
  next : Labmove -> ConstantGame;
}.

Definition Win : ConstantGame :=
{|
  winner := Machine;
  Labmove := Empty_set;
  who l := match l with end;
  next l := match l with end;
|}.

Definition Lose : ConstantGame :=
{|
  winner := Nature;
  Labmove := Empty_set;
  who l := match l with end;
  next l := match l with end;
|}.

Definition swap (p : Player) : Player :=
match p with
| Machine => Nature
| Nature => Machine
end.

Definition transport {A : Type} {P : A -> Type} {x y : A} (p : x = y) (u : P x) : P y :=
match p with
| eq_refl => u
end.

Lemma transport_cat :
  forall (A : Type) (P : A -> Type) (x y z : A) (p : x = y) (q : y = z) (u : P x),
    transport q (transport p u) = transport (eq_trans p q) u.
Proof.
  destruct p, q. cbn. reflexivity.
Defined.

Lemma cat_inv :
  forall (A : Type) (x y : A) (p : x = y),
    eq_trans (eq_sym p) p = eq_refl.
Proof.
  destruct p. cbn. reflexivity.
Defined.

CoInductive sim (g1 g2 : ConstantGame) : Prop :=
{
  winners : winner g1 = winner g2;
  Labmoves : Labmove g1 = Labmove g2;
  whos :
    forall move : Labmove g1,
      who g1 move = who g2 (@transport _ id _ _ Labmoves move);
  nexts :
    forall move : Labmove g1,
      sim (next g1 move)
        (next g2 (@transport _ id _ _ Labmoves move))
}.

Axiom sim_eq :
  forall g1 g2 : ConstantGame, sim g1 g2 -> g1 = g2.

(** The axiom is fine, because replacing [sim] with [=] in the definition
    of [sim] gives exactly what HoTT tells us is the characterization of
    paths for constant games. *)

Lemma sim_refl :
  forall g : ConstantGame, sim g g.
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros.
  - easy.
  - easy.
  - easy.
  - now cbn; apply CH.
Qed.

Lemma sim_sym :
  forall g1 g2 : ConstantGame,
    sim g1 g2 -> sim g2 g1.
Proof.
  cofix CH.
  intros g1 g2 [w p whos nexts].
  unshelve econstructor.
  - easy.
  - easy.
  - now intros; rewrite whos, transport_cat, cat_inv; cbn.
  - intros.
    apply CH.
    specialize (nexts (@transport _ id _ _ (eq_sym p) move)).
    now rewrite transport_cat, cat_inv in nexts; cbn in nexts.
Qed.

Lemma sim_trans :
  forall g1 g2 g3 : ConstantGame,
    sim g1 g2 -> sim g2 g3 -> sim g1 g3.
Proof.
  cofix CH.
  intros g1 g2 g3 [w1 p1 whos1 nexts1] [w2 p2 whos2 nexts2].
  unshelve econstructor.
  - exact (eq_trans p1 p2).
  - exact (eq_trans w1 w2).
  - now intros; rewrite whos1, whos2, transport_cat.
  - intros.
    apply (CH _ (next g2 (@transport _ id _ _ p1 move))).
    + now apply nexts1.
    + now rewrite <- transport_cat.
Qed.

#[export]
Instance Equivalence_sim : Equivalence sim.
Proof.
  split; red.
  - now apply sim_refl.
  - now apply sim_sym.
  - now apply sim_trans.
Defined.

(** Tactics *)

#[global] Hint Constructors Player : CoL.

#[global] Hint Extern 1 =>
  match goal with
  | |- exists p : Player, _ => exists Machine; cbn
  end : CoL.

#[global] Hint Extern 1 =>
  match goal with
  | |- exists p : Player, _ => exists Nature; cbn
  end : CoL.

(** Connectives *)

CoFixpoint Not (g : ConstantGame) : ConstantGame :=
{|
  winner := swap (winner g);
  Labmove := Labmove g;
  who move := swap (who g move);
  next move := Not (next g move);
|}.

Definition chor (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner := Nature;
  Labmove := bool;
  who move := Machine;
  next move := if move then g1 else g2;
|}.

Definition chand (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner := Machine;
  Labmove := bool;
  who move := Nature;
  next move := if move then g1 else g2;
|}.

Definition chexists {A : Type} (f : A -> ConstantGame) : ConstantGame :=
{|
  winner := Nature;
  Labmove := A;
  who move := Machine;
  next move := f move;
|}.

Definition chall {A : Type} (f : A -> ConstantGame) : ConstantGame :=
{|
  winner := Machine;
  Labmove := A;
  who move := Nature;
  next move := f move;
|}.

CoFixpoint por (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner :=
    match winner g1, winner g2 with
    | Nature, Nature => Nature
    | _, _ => Machine
    end;
  Labmove := Labmove g1 + Labmove g2;
  who move :=
    match move with
    | inl move' => who g1 move'
    | inr move' => who g2 move'
    end;
  next move :=
    match move with
    | inl move' => por (next g1 move') g2
    | inr move' => por g1 (next g2 move')
    end;
|}.

CoFixpoint pand (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner :=
    match winner g1, winner g2 with
    | Machine, Machine => Machine
    | _, _ => Nature
    end;
  Labmove := Labmove g1 + Labmove g2;
  who move :=
    match move with
    | inl move' => who g1 move'
    | inr move' => who g2 move'
    end;
  next move :=
    match move with
    | inl move' => pand (next g1 move') g2
    | inr move' => pand g1 (next g2 move')
    end;
|}.

Axiom LEM' : forall A : Type, A + (A -> False).

CoFixpoint pexists (f : nat -> ConstantGame) : ConstantGame :=
{|
  winner :=
    if LEM' (exists n : nat, winner (f n) = Machine)
    then Machine
    else Nature;
  Labmove := {n : nat & Labmove (f n)};
  who '(existT _ n move) := who (f n) move;
  next '(existT _ n move) := pexists (fun m : nat => if n =? m then next (f n) move else f m);
|}.

CoFixpoint pall (f : nat -> ConstantGame) : ConstantGame :=
{|
  winner :=
    if LEM' (forall n : nat, winner (f n) = Machine)
    then Machine
    else Nature;
  Labmove := {n : nat & Labmove (f n)};
  who '(existT _ n move) := who (f n) move;
  next '(existT _ n move) := pall (fun m : nat => if n =? m then next (f n) move else f m);
|}.

CoFixpoint sor (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner := winner g1;
  Labmove := option (Labmove g1);
  who move :=
    match move with
    | None => Machine
    | Some move' => who g1 move'
    end;
  next move :=
    match move with
    | None => g2
    | Some move' => sor (next g1 move') g2
    end;
|}.

CoFixpoint sand (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner := winner g1;
  Labmove := option (Labmove g1);
  who move :=
    match move with
    | None => Nature
    | Some move' => who g1 move'
    end;
  next move :=
    match move with
    | None => g2
    | Some move' => sand (next g1 move') g2
    end;
|}.

CoFixpoint sexists (f : nat -> ConstantGame) : ConstantGame :=
{|
  winner := winner (f 0);
  Labmove := option (Labmove (f 0));
  who move :=
    match move with
    | None => Machine
    | Some move' => who (f 0) move'
    end;
  next move :=
    match move with
    | None => sexists (fun n : nat => f (S n))
    | Some move' =>
        sexists (fun n : nat =>
          match n with
          | 0 => next (f 0) move'
          | S n' => f (S n')
          end)
    end;
|}.

CoFixpoint sall (f : nat -> ConstantGame) : ConstantGame :=
{|
  winner := winner (f 0);
  Labmove := option (Labmove (f 0));
  who move :=
    match move with
    | None => Nature
    | Some move' => who (f 0) move'
    end;
  next move :=
    match move with
    | None => sall (fun n : nat => f (S n))
    | Some move' =>
        sall (fun n : nat =>
          match n with
          | 0 => next (f 0) move'
          | S n' => f (S n')
          end)
    end;
|}.

CoFixpoint tor (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner := winner g1;
  Labmove := option (Labmove g1);
  who move :=
    match move with
    | None => Machine
    | Some move' => who g1 move'
    end;
  next move :=
    match move with
    | None => tor g2 g1
    | Some move' => tor (next g1 move') g2
    end;
|}.

CoFixpoint tand (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner := winner g1;
  Labmove := option (Labmove g1);
  who move :=
    match move with
    | None => Nature
    | Some move' => who g1 move'
    end;
  next move :=
    match move with
    | None => tand g2 g1
    | Some move' => tand (next g1 move') g2
    end;
|}.

CoFixpoint texists' (f : nat -> ConstantGame) (n : nat) : ConstantGame :=
{|
  winner := winner (f n);
  Labmove := Labmove (f n) + nat;
  who move :=
    match move with
    | inl move' => who (f n) move'
    | inr _ => Machine
    end;
  next move :=
    match move with
    | inl move' => texists' (fun m : nat => if n =? m then next (f n) move' else f m) n
    | inr m => texists' f m
    end;
|}.

CoFixpoint tall' (f : nat -> ConstantGame) (n : nat) : ConstantGame :=
{|
  winner := winner (f n);
  Labmove := Labmove (f n) + nat;
  who move :=
    match move with
    | inl move' => who (f n) move'
    | inr _ => Nature
    end;
  next move :=
    match move with
    | inl move' => tall' (fun m : nat => if n =? m then next (f n) move' else f m) n
    | inr m => tall' f m
    end;
|}.

Definition texists (f : nat -> ConstantGame) : ConstantGame :=
  texists' f 0.

Definition tall (f : nat -> ConstantGame) : ConstantGame :=
  tall' f 0.

(** Some proofs - de Morgan laws *)

Lemma Not_Not :
  forall g : ConstantGame,
    sim (Not (Not g)) g.
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros.
  - easy.
  - now destruct (winner g).
  - now cbn; destruct (who g move); cbn.
  - now apply CH.
Qed.

Lemma Not_chor :
  forall g1 g2 : ConstantGame,
    sim (Not (chor g1 g2)) (chand (Not g1) (Not g2)).
Proof.
  unshelve econstructor; cbn; intros; [easy.. |].
  now destruct move; cbn.
Qed.

Lemma Not_chand :
  forall g1 g2 : ConstantGame,
    sim (Not (chand g1 g2)) (chor (Not g1) (Not g2)).
Proof.
  unshelve econstructor; cbn; intros; [easy.. |].
  now destruct move; cbn.
Qed.

Lemma Not_chexists :
  forall (A : Type) (f : A -> ConstantGame),
    sim (Not (chexists f)) (chall (fun x : A => Not (f x))).
Proof.
  now unshelve econstructor; cbn.
Qed.

Lemma Not_chall :
  forall (A : Type) (f : A -> ConstantGame),
    sim (Not (chall f)) (chexists (fun x : A => Not (f x))).
Proof.
  now unshelve econstructor.
Qed.

Lemma Not_por :
  forall g1 g2 : ConstantGame,
    sim (Not (por g1 g2)) (pand (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; only 1: easy.
  - now destruct (winner g1), (winner g2); cbn.
  - now destruct move; cbn.
  - now destruct move; cbn; apply CH.
Qed.

Lemma Not_pand :
  forall g1 g2 : ConstantGame,
    sim (Not (pand g1 g2)) (por (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct g1, g2, winner0, winner1; cbn.
  - now destruct move; cbn.
  - now destruct move; apply CH.
Qed.

Lemma Not_pexists :
  forall f : nat -> ConstantGame,
    sim (Not (pexists f)) (pall (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - destruct (LEM' _) as [[n Hw] |], (LEM' _) as [Hw' |]; cbn; [| easy.. |].
    + specialize (Hw' n).
      now rewrite Hw in Hw'; cbn in *.
    + cut False; [easy |].
      apply f1; intros n.
      destruct (winner (f n)) eqn: Hw; cbn; [| easy].
      now firstorder.
  - now destruct move; cbn.
  - destruct move as [n move]; cbn.
    replace (pall _)
       with (pall (fun m : nat => Not (if n =? m then next (f n) move else f m))).
    + now apply CH.
    + f_equal.
      extensionality m.
      now destruct (n =? m).
Qed.
