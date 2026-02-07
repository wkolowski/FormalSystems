From Stdlib Require Import FunctionalExtensionality.

From FormalSystems Require Export Base.

Axiom LEM : forall P : Prop, P \/ ~ P.

Inductive Player : Type :=
| Machine : Player
| Nature : Player.

CoInductive ConstantGame : Type :=
{
  winner : Player -> Prop;
  winner_spec : forall p p' : Player, winner p -> winner p' -> p = p';
  winner_spec' : exists p : Player, winner p;
  MoveM : Type;
  MoveN : Type;
  nextM : MoveM -> ConstantGame;
  nextN : MoveN -> ConstantGame;
}.

#[refine]
Definition Win : ConstantGame :=
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
Proof.
  - now destruct p, p'.
  - now exists Machine.
Defined.

#[refine]
Definition Lose : ConstantGame :=
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
Proof.
  - now destruct p, p'.
  - now exists Nature.
Defined.

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
  now destruct p, q; cbn.
Defined.

Lemma cat_inv :
  forall (A : Type) (x y : A) (p : x = y),
    eq_trans (eq_sym p) p = eq_refl.
Proof.
  now destruct p; cbn.
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
  now sim; apply CH.
Qed.

Lemma sim_sym :
  forall g1 g2 : ConstantGame,
    sim g1 g2 -> sim g2 g1.
Proof.
  cofix CH.
  intros g1 g2 []; sim; apply CH.
  - specialize (nextMs0 (@transport _ id _ _ (eq_sym MM0) move)).
    now rewrite transport_cat, cat_inv in *.
  - specialize (nextNs0 (@transport _ id _ _ (eq_sym MN0) move)).
    now rewrite transport_cat, cat_inv in *.
Qed.

Lemma sim_trans :
  forall g1 g2 g3 : ConstantGame,
    sim g1 g2 -> sim g2 g3 -> sim g1 g3.
Proof.
  cofix CH.
  intros g1 g2 g3 [w1 p1 q1 nextMs1 nextNs1] [w2 p2 q2 nextMs2 nextNs2].
  sim.
  - apply (CH _ (nextM g2 (@transport _ id _ _ p1 move))); [easy |].
    now rewrite <- transport_cat.
  - apply (CH _ (nextN g2 (@transport _ id _ _ q1 move))); [easy |].
    now rewrite <- transport_cat.
Qed.

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

#[refine]
CoFixpoint Not (g : ConstantGame) : ConstantGame :=
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
Proof.
  - des g.
    intros.
    now destruct p0, p'; auto.
  - des g.
    exists (swap p).
    now destruct p; cbn.
Defined.

#[refine]
Definition chor (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner p := p = Nature;
  MoveM := bool;
  MoveN := Empty_set;
  nextM move := if move then g1 else g2;
  nextN move := match move with end;
|}.
Proof.
  - now destruct p, p'.
  - now exists Nature.
Defined.

#[refine]
Definition chand (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner p := p = Machine;
  MoveM := Empty_set;
  MoveN := bool;
  nextM move := match move with end;
  nextN move := if move then g1 else g2;
|}.
Proof.
  - now destruct p, p'.
  - now exists Machine.
Defined.

#[refine]
Definition chexists (f : nat -> ConstantGame) : ConstantGame :=
{|
  winner p := p = Nature;
  MoveM := nat;
  MoveN := Empty_set;
  nextM move := f move;
  nextN move := match move with end;
|}.
Proof.
  - now destruct p, p'.
  - now exists Nature.
Defined.

#[refine]
Definition chall (f : nat -> ConstantGame) : ConstantGame :=
{|
  winner p := p = Machine;
  MoveM := Empty_set;
  MoveN := nat;
  nextM move := match move with end;
  nextN move := f move;
|}.
Proof.
  - now destruct p, p'.
  - now exists Machine.
Defined.

#[refine]
CoFixpoint por (g1 g2 : ConstantGame) : ConstantGame :=
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
Proof.
  - now destruct g1, g2, p, p'; cbn; firstorder.
  - destruct (LEM (winner g1 Machine)); [now exists Machine; auto |].
    destruct (LEM (winner g2 Machine)); [now exists Machine; auto |].
    exists Nature.
    des g1; des g2.
    now destruct p, p0; cbn in *.
Defined.

#[refine]
CoFixpoint pand (g1 g2 : ConstantGame) : ConstantGame :=
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
Proof.
  - now destruct g1, g2, p, p'; cbn; firstorder.
  - destruct (LEM (winner g1 Nature)); [now exists Nature; auto |].
    destruct (LEM (winner g2 Nature)); [now exists Nature; auto |].
    exists Machine.
    des g1; des g2.
    now destruct p, p0; cbn in *.
Defined.

#[refine]
CoFixpoint pexists (f : nat -> ConstantGame) : ConstantGame :=
{|
  winner p :=
    match p with
    | Machine => exists n : nat, winner (f n) Machine
    | Nature => forall n : nat, winner (f n) Nature
    end;
  MoveM := {n : nat & MoveM (f n)};
  MoveN := {n : nat & MoveN (f n)};
  nextM '(existT _ n move) := pexists (fun m => if decide (n = m) then nextM (f n) move else f m);
  nextN '(existT _ n move) := pexists (fun m => if decide (n = m) then nextN (f n) move else f m);
|}.
Proof.
  - destruct p, p'; [easy | | | easy].
    + intros [n H] H'.
      specialize (H' n).
      now destruct (f n); cbn in *; auto.
    + intros H [n H'].
      specialize (H n).
      now destruct (f n); cbn in *; auto.
  - destruct (LEM (exists n : nat, winner (f n) Machine)); [now exists Machine |].
    exists Nature; intros n.
    destruct (LEM (winner (f n) Nature)); [easy |].
    contradict H.
    exists n.
    destruct (LEM (winner (f n) Machine)); [easy |].
    now destruct (f n), winner_spec'0 as [[] H']; cbn in *.
Defined.

#[refine]
CoFixpoint pall (f : nat -> ConstantGame) : ConstantGame :=
{|
  winner p :=
    match p with
    | Machine => forall n : nat, winner (f n) Machine
    | Nature => exists n : nat, winner (f n) Nature
    end;
  MoveM := {n : nat & MoveM (f n)};
  MoveN := {n : nat & MoveN (f n)};
  nextM '(existT _ n move) := pall (fun m : nat => if decide (n = m) then nextM (f n) move else f m);
  nextN '(existT _ n move) := pall (fun m : nat => if decide (n = m) then nextN (f n) move else f m);
|}.
Proof.
  - destruct p, p'; [easy | | | easy].
    + intros H [n H'].
      specialize (H n).
      now destruct (f n); cbn in *; auto.
    + intros [n H] H'.
      specialize (H' n).
      now destruct (f n); cbn in *; auto.
  - destruct (LEM (exists n : nat, winner (f n) Nature)); [now exists Nature |].
    exists Machine; intros n.
    destruct (LEM (winner (f n) Machine)); [easy |].
    contradict H.
    exists n.
    destruct (LEM (winner (f n) Nature)); [easy |].
    now destruct (f n), winner_spec'0 as [[] H']; cbn in *.
Defined.

#[refine]
CoFixpoint sor (g1 g2 : ConstantGame) : ConstantGame :=
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
Proof.
  - now destruct g1; cbn.
  - now destruct g1; cbn.
Defined.

#[refine]
CoFixpoint sand (g1 g2 : ConstantGame) : ConstantGame :=
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
Proof.
  - now destruct g1; cbn.
  - now destruct g1; cbn.
Defined.

#[refine]
CoFixpoint sexists (f : nat -> ConstantGame) : ConstantGame :=
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
Proof.
  - now destruct (f 0); cbn.
  - now destruct (f 0); cbn.
Defined.
