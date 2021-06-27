Require Import List.
Import ListNotations.

Require Import Bool.
Require Import Arith.

Require Import FunctionalExtensionality.

Axiom LEM : forall P : Prop, P \/ ~ P.

Inductive Player : Type :=
    | Machine : Player
    | Nature : Player.

CoInductive ConstantGame : Type :=
{
    winner : Player -> Prop;
    winner_spec :
      forall p p' : Player, winner p -> winner p' -> p = p';
    winner_spec' :
      exists p : Player, winner p;
    MoveM : Type;
    MoveN : Type;
    nextM : MoveM -> ConstantGame;
    nextN : MoveN -> ConstantGame;
}.

Definition Win : ConstantGame.
Proof.
refine
{|
    winner p :=
      match p with
          | Machine => True
          | Nature => False
      end;
    MoveM := Empty_set;
    MoveN := Empty_set;
    nextM move := match move with end;
    nextN move := match move with end;
|}.
  destruct p, p'; firstorder.
  exists Machine. trivial.
Defined.

CoFixpoint Lose : ConstantGame.
Proof.
refine
{|
    winner p :=
      match p with
          | Machine => False
          | Nature => True
      end;
    MoveM := Empty_set;
    MoveN := Empty_set;
    nextM move := match move with end;
    nextN move := match move with end;
|}.
  destruct p, p'; firstorder.
  exists Nature. trivial.
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
    winners : forall p : Player, winner g1 p <-> winner g2 p;
    MM : MoveM g1 = MoveM g2;
    MN : MoveN g1 = MoveN g2;
    nextMs :
      forall move : MoveM g1,
        sim (nextM g1 move)
          (nextM g2 (@transport _ id _ _ MM move));
    nextNs :
      forall move : MoveN g1,
        sim (nextN g1 move)
          (nextN g2 (@transport _ id _ _ MN move));
}.

Ltac sim :=
  intros;
  unshelve econstructor;
  intros; try (cbn;
  match goal with
      | |- ?x = ?x => reflexivity
      | |- ?x = ?y => congruence
      | |- winner _ _ <-> winner _ _ => firstorder
  end).

Lemma sim_refl :
  forall g : ConstantGame, sim g g.
Proof.
  cofix CH.
  sim; apply CH.
Qed.

Lemma sim_sym :
  forall g1 g2 : ConstantGame,
    sim g1 g2 -> sim g2 g1.
Proof.
  cofix CH.
  destruct 1. sim; apply CH.
    specialize (nextMs0 (@transport _ id _ _ (eq_sym MM0) move)).
      rewrite transport_cat, cat_inv in *. assumption.
    specialize (nextNs0 (@transport _ id _ _ (eq_sym MN0) move)).
      rewrite transport_cat, cat_inv in *. assumption.
Qed.

Lemma sim_trans :
  forall g1 g2 g3 : ConstantGame,
    sim g1 g2 -> sim g2 g3 -> sim g1 g3.
Proof.
  cofix CH.
  destruct 1 as [w1 p1 q1 nextMs1 nextNs1],
           1 as [w2 p2 q2 nextMs2 nextNs2].
  sim.
    apply (CH _ (nextM g2 (transport id p1 move))).
      apply nextMs1.
      rewrite <- transport_cat. apply nextMs2.
    apply (CH _ (nextN g2 (transport id q1 move))).
      apply nextNs1.
      rewrite <- transport_cat. apply nextNs2.
Qed.

(** Tactics *)

Global Hint Constructors Player : CoL.

Global Hint Extern 1 =>
match goal with
    | |- exists p : Player, _ => exists Machine; cbn
end : CoL.

Global Hint Extern 1 =>
match goal with
    | |- exists p : Player, _ => exists Nature; cbn
end : CoL.

(** Connectives *)

Ltac des g :=
  let winner := fresh "winner" in
  let spec1 := fresh "spec1" in
  let p := fresh "p" in
  let spec2 := fresh "spec2" in
  let MoveM := fresh "MoveM" in
  let MoveN := fresh "MoveN" in
  let nextM := fresh "nextM" in
  let nextN := fresh "nextN" in
    destruct g as [winner spec1 [p spec2] MoveM MoveN nextM nextN]; cbn in *.

CoFixpoint Not (g : ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p :=
      match p with
          | Machine => winner g Nature
          | Nature => winner g Machine
      end;
    MoveM := MoveN g;
    MoveN := MoveM g;
    nextM move := Not (nextN g move);
    nextN move := Not (nextM g move);
|}.
  des g.
 intros.
  
  repeat match goal with
      | H : context [match ?p with _ => _ end] |- _ => destruct p
  end. auto.
  all: repeat match goal with
      | winner : Player -> Prop,
        spec : forall p1 p2 : Player, ?winner p1 -> ?winner p2 -> p1 = p2,
        H1 : ?winner Machine,
        H2 : ?winner Nature |- _ => specialize (spec _ _ H1 H2); congruence
  end.
  reflexivity. (* TODO *)
  des g. exists (swap p). destruct p; cbn; assumption.
Defined.

Definition chor (g1 g2 : ConstantGame) : ConstantGame.
Proof.
  refine
  {|
      winner p := p = Nature;
      MoveM := bool;
      MoveN := Empty_set;
      nextM move := if move then g1 else g2;
      nextN move := match move with end;
  |}.
  destruct p, p'; firstorder.
  exists Nature. trivial.
Defined.

Definition chand (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p := p = Machine;
      MoveM := Empty_set;
      MoveN := bool;
      nextM move := match move with end;
      nextN move := if move then g1 else g2;
|}.
  destruct p, p'; firstorder.
  exists Machine. trivial.
Defined.

Definition chexists (f : nat -> ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p := p = Nature;
    MoveM := nat;
    MoveN := Empty_set;
    nextM move := f move;
    nextN move := match move with end;
|}.
  destruct p, p'; firstorder.
  exists Nature. reflexivity.
Defined.

Definition chall (f : nat -> ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p := p = Machine;
    MoveM := Empty_set;
    MoveN := nat;
    nextM move := match move with end;
    nextN move := f move;
|}.
  destruct p, p'; firstorder.
  exists Machine. reflexivity.
Defined.

CoFixpoint por (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p :=
      match p with
          | Machine => winner g1 Machine \/ winner g2 Machine
          | Nature => winner g1 Nature /\ winner g2 Nature
      end;
    MoveM := MoveM g1 + MoveM g2;
    MoveN := MoveN g1 + MoveN g2;
    nextM move :=
      match move with
          | inl move' => por (nextM g1 move') g2
          | inr move' => por g1 (nextM g2 move')
      end;
    nextN move :=
      match move with
          | inl move' => por (nextN g1 move') g2
          | inr move' => por g1 (nextN g2 move')
      end;
|}.
  destruct g1, g2, p, p'; firstorder.
  destruct (LEM (winner g1 Machine)).
    exists Machine. auto.
    destruct (LEM (winner g2 Machine)).
      exists Machine. auto.
      exists Nature. des g1; des g2. destruct p, p0; auto; contradiction.
Defined.

CoFixpoint pand (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p :=
      match p with
          | Machine => winner g1 Machine /\ winner g2 Machine
          | Nature => winner g1 Nature \/ winner g2 Nature
      end;
    MoveM := MoveM g1 + MoveM g2;
    MoveN := MoveN g1 + MoveN g2;
    nextM move :=
      match move with
          | inl move' => pand (nextM g1 move') g2
          | inr move' => pand g1 (nextM g2 move')
      end;
    nextN move :=
      match move with
          | inl move' => pand (nextN g1 move') g2
          | inr move' => pand g1 (nextN g2 move')
      end;
|}.
  destruct g1, g2, p, p'; firstorder.
  destruct (LEM (winner g1 Nature)).
    exists Nature. auto.
    destruct (LEM (winner g2 Nature)).
      exists Nature. auto.
      exists Machine. des g1; des g2. destruct p, p0; auto; contradiction.
Defined.

CoFixpoint pexists (f : nat -> ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p :=
      match p with
          | Machine => exists n : nat, winner (f n) Machine
          | Nature => forall n : nat, winner (f n) Nature
      end;
    MoveM := {n : nat & MoveM (f n)};
    MoveN := {n : nat & MoveN (f n)};
    nextM move :=
      match move with
          | existT _ n move =>
              pexists (fun m => if n =? m then nextM (f n) move else f m)
      end;
    nextN move :=
      match move with
          | existT _ n move =>
              pexists (fun m => if n =? m then nextN (f n) move else f m)
      end;
|}.
  destruct p, p'; try reflexivity.
    intros [n H] H'. specialize (H' n). destruct (f n). auto.
    intros H [n H']. specialize (H n). destruct (f n). auto.
  destruct (LEM (exists n : nat, winner (f n) Machine)).
    exists Machine. assumption.
    exists Nature. intro. destruct (LEM (winner (f n) Nature)).
      assumption.
      contradict H. exists n. destruct (LEM (winner (f n) Machine)).
        assumption.
        destruct (f n), winner_spec'0 as [[] H']; cbn in *; contradiction.
Defined.

CoFixpoint pall (f : nat -> ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p := 
      match p with
          | Machine => forall n : nat, winner (f n) Machine
          | Nature => exists n : nat, winner (f n) Nature
      end;
    MoveM := {n : nat & MoveM (f n)};
    MoveN := {n : nat & MoveN (f n)};
    nextM move :=
      match move with
          | existT _ n move =>
              pall (fun m : nat => if n =? m then nextM (f n) move else f m)
      end;
    nextN move :=
      match move with
          | existT _ n move =>
              pall (fun m : nat => if n =? m then nextN (f n) move else f m)
      end;
|}.
  destruct p, p'; try reflexivity.
    intros H [n H']. specialize (H n). destruct (f n). auto.
    intros [n H] H'. specialize (H' n). destruct (f n). auto.
  destruct (LEM (exists n : nat, winner (f n) Nature)).
    exists Nature. assumption.
    exists Machine. intro. destruct (LEM (winner (f n) Machine)).
      assumption.
      contradict H. exists n. destruct (LEM (winner (f n) Nature)).
        assumption.
        destruct (f n), winner_spec'0 as [[] H']; cbn in *; contradiction.
Defined.

CoFixpoint sor (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p := winner g1 p;
    MoveM := option (MoveM g1);
    MoveN := MoveN g1;
    nextM move :=
      match move with
          | None => g2
          | Some move' => sor (nextM g1 move') g2
      end;
    nextN move := sor (nextN g1 move) g2;
|}.
  all: destruct g1; auto.
Defined.

CoFixpoint sand (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p := winner g1 p;
    MoveM := MoveM g1;
    MoveN := option (MoveN g1);
    nextM move := sand (nextM g1 move) g2;
    nextN move :=
      match move with
          | None => g2
          | Some move' => sand (nextN g1 move') g2
      end;
|}.
  all: destruct g1; auto.
Defined.

CoFixpoint sexists (f : nat -> ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p := winner (f 0) p;
    MoveM := option (MoveM (f 0));
    MoveN := MoveN (f 0);
    nextM move :=
      match move with
          | None => sexists (fun n : nat => f (S n))
          | Some move' =>
              sexists (fun n : nat =>
                      match n with
                          | 0 => nextM (f 0) move'
                          | S n' => f (S n')
                      end)
      end;
    nextN move :=
      sexists (fun n : nat =>
        match n with
            | 0 => nextN (f 0) move
            | S n' => f (S n')
        end);
|}.
  all: destruct (f 0); auto.
Defined.