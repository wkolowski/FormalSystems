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

Definition Win : ConstantGame.
Proof.
refine
{|
    winner := Machine;
    Labmove := Empty_set;
    who l := match l with end;
    next l := match l with end;
|}.
Defined.

CoFixpoint Lose : ConstantGame.
Proof.
refine
{|
    winner := Nature;
    Labmove := Empty_set;
    who l := match l with end;
    next l := match l with end;
|}.
Defined.

Definition swap (p : Player) : Player :=
match p with
    | Machine => Nature
    | Nature => Machine
end.

Definition transport
  {A : Type} (P : A -> Type) {x y : A} (p : x = y) : P x -> P y.
Proof.
  destruct p. intro. assumption.
Defined.

Lemma transport_cat :
  forall
    (A : Type) (P : A -> Type) (x y z : A) (p : x = y) (q : y = z) (u : P x),
      transport P q (transport P p u) = transport P (eq_trans p q) u.
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
  econstructor; cbn; intros. Unshelve.
    1, 4: reflexivity.
    reflexivity.
    apply CH.
Qed.

Lemma sim_sym :
  forall g1 g2 : ConstantGame,
    sim g1 g2 -> sim g2 g1.
Proof.
  cofix CH.
  destruct 1 as [w p whos nexts].
  econstructor. Unshelve.
    4: auto.
    auto.
    intro. rewrite whos, transport_cat, cat_inv. cbn. reflexivity.
    intro. apply CH.
      specialize (nexts (@transport _ id _ _ (eq_sym p) move)).
      rewrite transport_cat, cat_inv in *. cbn in *.
        assumption.
Qed.

Lemma sim_trans :
  forall g1 g2 g3 : ConstantGame,
    sim g1 g2 -> sim g2 g3 -> sim g1 g3.
Proof.
  cofix CH.
  destruct 1 as [w1 p1 whos1 nexts1],
           1 as [w2 p2 whos2 nexts2].
  econstructor. Unshelve.
    4: exact (eq_trans p1 p2).
    rewrite w1. assumption.
    intro. rewrite whos1, whos2, transport_cat. reflexivity.
    intro. apply (CH _ (next g2 (transport id p1 move))).
      apply nexts1.
      rewrite <- transport_cat. apply nexts2.
Qed.

#[export]
Instance Equivalence_sim : Equivalence sim.
Proof.
  split; red.
    apply sim_refl.
    apply sim_sym.
    apply sim_trans.
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

CoFixpoint Not (g : ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner := swap (winner g);
    Labmove := Labmove g;
    who move := swap (who g move);
    next move := Not (next g move);
|}.
Defined.

Definition chor (g1 g2 : ConstantGame) : ConstantGame.
Proof.
  refine
  {|
      winner := Nature;
      Labmove := bool;
      who move := Machine;
      next move := if move then g1 else g2;
  |}.
Defined.

Definition chand (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner := Machine;
    Labmove := bool;
    who move := Nature;
    next move := if move then g1 else g2;
|}.
Defined.

Definition chexists {A : Type} (f : A -> ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner := Nature;
    Labmove := A;
    who move := Machine;
    next move := f move;
|}.
Defined.

Definition chall {A : Type} (f : A -> ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner := Machine;
    Labmove := A;
    who move := Nature;
    next move := f move;
|}.
Defined.

CoFixpoint por (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
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
      end
|}.
Defined.

CoFixpoint pand (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
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
      end
|}.
Defined.

Axiom LEM' : forall A : Type, A + (A -> False).

CoFixpoint pexists (f : nat -> ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner :=
      if LEM' (exists n : nat, winner (f n) = Machine)
      then Machine
      else Nature;
    Labmove := {n : nat & Labmove (f n)};
    who move :=
      match move with
          | existT _ n move => who (f n) move
      end;
    next move :=
      match move with
          | existT _ n move =>
              pexists (fun m : nat => if n =? m then next (f n) move else f m)
      end
|}.
Defined.

CoFixpoint pall (f : nat -> ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner :=
      if LEM' (forall n : nat, winner (f n) = Machine)
      then Machine
      else Nature;
    Labmove := {n : nat & Labmove (f n)};
    who move :=
      match move with
          | existT _ n move => who (f n) move
      end;
    next move :=
      match move with
          | existT _ n move =>
              pall (fun m : nat => if n =? m then next (f n) move else f m)
      end
|}.
Defined.

CoFixpoint sor (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
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
Defined.

CoFixpoint sand (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
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
Defined.

CoFixpoint sexists (f : nat -> ConstantGame) : ConstantGame.
Proof.
refine
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
Defined.

CoFixpoint sall (f : nat -> ConstantGame) : ConstantGame.
Proof.
refine
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
Defined.

CoFixpoint tor (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
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
Defined.

CoFixpoint tand (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
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
Defined.

CoFixpoint texists' (f : nat -> ConstantGame) (n : nat) : ConstantGame.
Proof.
refine
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
          | inl move' => texists'
              (fun m : nat => if n =? m then next (f n) move' else f m) n
          | inr m => texists' f m
      end;
|}.
Defined.

CoFixpoint tall' (f : nat -> ConstantGame) (n : nat) : ConstantGame.
Proof.
refine
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
          | inl move' => tall'
              (fun m : nat => if n =? m then next (f n) move' else f m) n
          | inr m => tall' f m
      end;
|}.
Defined.

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
  econstructor; cbn; intros. Unshelve.
    4: cbn; reflexivity.
    destruct (winner g); reflexivity.
    cbn. destruct (who g move); cbn; reflexivity.
    apply CH.
Qed.

Lemma Not_chor :
  forall g1 g2 : ConstantGame,
    sim (Not (chor g1 g2)) (chand (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor; cbn; intros. Unshelve.
    4: cbn; reflexivity.
    1-2: reflexivity.
    cbn. destruct move; apply sim_refl.
Qed.

Lemma Not_chand :
  forall g1 g2 : ConstantGame,
    sim (Not (chand g1 g2)) (chor (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor; cbn; intros. Unshelve.
    all: cbn; try reflexivity.
    cbn. destruct move; apply sim_refl.
Qed.

Lemma Not_chexists :
  forall (A : Type) (f : A -> ConstantGame),
    sim (Not (chexists f)) (chall (fun x : A => Not (f x))).
Proof.
  cofix CH.
  econstructor. Unshelve.
    all: cbn; try reflexivity.
    intro. apply sim_refl.
Qed.

Lemma Not_chall :
  forall (A : Type) (f : A -> ConstantGame),
    sim (Not (chall f)) (chexists (fun x : A => Not (f x))).
Proof.
  cofix CH.
  econstructor. Unshelve.
    all: cbn; try reflexivity.
    intro. apply sim_refl.
Qed.

Lemma Not_por :
  forall g1 g2 : ConstantGame,
    sim (Not (por g1 g2)) (pand (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor. Unshelve.
    all: cbn; try reflexivity.
    destruct (winner g1), (winner g2); cbn; reflexivity.
    destruct move; reflexivity.
    destruct move; apply CH.
Qed.

(*
Lemma Not_pand :
  forall g1 g2 : ConstantGame,
    sim (Not (pand g1 g2)) (por (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor. Unshelve.
    4: cbn; reflexivity.
    all: cbn; intros.
      destruct p; firstorder.
      destruct move; reflexivity.
      destruct move; apply CH.
Qed.
*)

Lemma Not_pexists :
  forall f : nat -> ConstantGame,
    sim (Not (pexists f)) (pall (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  econstructor. Unshelve.
    all: cbn; try reflexivity.
      destruct (LEM' _), (LEM' _); cbn; try reflexivity.
        destruct e. specialize (e0 x). rewrite H in e0. inversion e0.
        cut False.
          destruct 1.
          apply f1. intro. case_eq (winner (f n)); cbn; intro.
            cut False. destruct 1. apply f0. eauto.
            reflexivity.
      destruct move. cbn. reflexivity.
      destruct move as [n move]. cbn.
        replace (pall _) with (pall
          (fun m : nat => Not (if n =? m then next (f n) move else f m))).
          apply CH.
          f_equal. extensionality m. destruct (n =? m); reflexivity.
Qed.