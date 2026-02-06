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
  winner : Player -> Prop;
  winner_spec :
    forall p p' : Player, winner p -> winner p' -> p = p';
  winner_spec' :
    exists p : Player, winner p;
  Labmove : Type;
  who : Labmove -> Player;
  next : Labmove -> ConstantGame;
}.

#[refine]
Definition Win : ConstantGame :=
{|
  winner p :=
    match p with
    | Machine => True
    | Nature => False
    end;
  Labmove := Empty_set;
  who l := match l with end;
  next l := match l with end;
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
  Labmove := Empty_set;
  who l := match l with end;
  next l := match l with end;
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
  unshelve econstructor; cbn; intros; [easy.. |].
  now apply CH.
Qed.

Lemma sim_sym :
  forall g1 g2 : ConstantGame,
    sim g1 g2 -> sim g2 g1.
Proof.
  cofix CH.
  intros g1 g2 [w p whos nexts].
  unshelve econstructor; intros; [easy.. | |].
  - now rewrite whos, transport_cat, cat_inv; cbn.
  - apply CH.
    specialize (nexts (@transport _ id _ _ (eq_sym p) move)).
    now rewrite transport_cat, cat_inv in nexts; cbn in nexts.
Qed.

Lemma sim_trans :
  forall g1 g2 g3 : ConstantGame,
    sim g1 g2 -> sim g2 g3 -> sim g1 g3.
Proof.
  cofix CH.
  intros g1 g2 g3 [w1 p1 whos1 nexts1] [w2 p2 whos2 nexts2].
  unshelve econstructor; cbn; intros.
  - exact (eq_trans p1 p2).
  - now firstorder.
  - now rewrite whos1, whos2, transport_cat.
  - apply (CH _ (next g2 (@transport _ id _ _ p1 move))).
    apply nexts1.
    now rewrite <- transport_cat.
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

Ltac des g :=
  let winner := fresh "winner" in
  let spec1 := fresh "spec1" in
  let p := fresh "p" in
  let spec2 := fresh "spec2" in
  let Labmove := fresh "Labmove" in
  let who := fresh "who" in
  let next := fresh "next" in
    destruct g as [winner spec1 [p spec2] Labmove who next]; cbn in *.

#[refine]
CoFixpoint Not (g : ConstantGame) : ConstantGame :=
{|
  winner p :=
    match p with
    | Machine => winner g Nature
    | Nature => winner g Machine
    end;
  Labmove := Labmove g;
  who move := swap (who g move);
  next move := Not (next g move);
|}.
Proof.
  - now destruct g, p, p'; cbn; firstorder.
  - des g.
    exists (swap p).
    now destruct p; cbn.
Defined.

#[refine]
Definition chor (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner p := p = Nature;
  Labmove := bool;
  who move := Machine;
  next move := if move then g1 else g2;
|}.
Proof.
  - now destruct p, p'.
  - now exists Nature.
Defined.

#[refine]
Definition chand (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner p := p = Machine;
  Labmove := bool;
  who move := Nature;
  next move := if move then g1 else g2;
|}.
Proof.
  - now destruct p, p'.
  - now exists Machine.
Defined.

#[refine]
Definition chexists {A : Type} (f : A -> ConstantGame) : ConstantGame :=
{|
  winner p := p = Nature;
  Labmove := A;
  who move := Machine;
  next move := f move;
|}.
Proof.
  - now destruct p, p'.
  - now exists Nature.
Defined.

#[refine]
Definition chall {A : Type} (f : A -> ConstantGame) : ConstantGame :=
{|
  winner p := p = Machine;
  Labmove := A;
  who move := Nature;
  next move := f move;
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
Proof.
  - now destruct g1, g2, p, p'; firstorder.
  - destruct (LEM (winner g1 Machine)); [now exists Machine; auto |].
    destruct (LEM (winner g2 Machine)); [now exists Machine; auto |].
    exists Nature.
    des g1; des g2.
    now destruct p, p0; auto.
Defined.

#[refine]
CoFixpoint pand (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner p :=
    match p with
    | Machine => winner g1 Machine /\ winner g2 Machine
    | Nature => winner g1 Nature \/ winner g2 Nature
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
Proof.
  - now destruct g1, g2, p, p'; firstorder.
  - destruct (LEM (winner g1 Nature)); [now exists Nature; auto |].
    destruct (LEM (winner g2 Nature)); [now exists Nature; auto |].
    exists Machine.
    des g1; des g2.
    now destruct p, p0; auto.
Defined.

#[refine]
CoFixpoint pexists (f : nat -> ConstantGame) : ConstantGame :=
{|
  winner p :=
    match p with
    | Machine => exists n : nat, winner (f n) Machine
    | Nature => forall n : nat, winner (f n) Nature
    end;
  Labmove := {n : nat & Labmove (f n)};
  who '(existT _ n move) := who (f n) move;
  next '(existT _ n move) := pexists (fun m : nat => if n =? m then next (f n) move else f m);
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
  Labmove := {n : nat & Labmove (f n)};
  who '(existT _ n move) := who (f n) move;
  next '(existT _ n move) := pall (fun m : nat => if n =? m then next (f n) move else f m);
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
Proof.
  - now destruct g1.
  - now destruct g1.
Defined.

#[refine]
CoFixpoint sand (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner p := winner g1 p;
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
Proof.
  - now destruct g1.
  - now destruct g1.
Defined.

#[refine]
CoFixpoint sexists (f : nat -> ConstantGame) : ConstantGame :=
{|
  winner p := winner (f 0) p;
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
Proof.
  - now destruct (f 0).
  - now destruct (f 0).
Defined.

#[refine]
CoFixpoint sall (f : nat -> ConstantGame) : ConstantGame :=
{|
  winner p := winner (f 0) p;
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
Proof.
  - now destruct (f 0).
  - now destruct (f 0).
Defined.

#[refine]
CoFixpoint tor (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner p := winner g1 p;
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
Proof.
  - now destruct g1.
  - now destruct g1.
Defined.

#[refine]
CoFixpoint tand (g1 g2 : ConstantGame) : ConstantGame :=
{|
  winner p := winner g1 p;
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
Proof.
  - now destruct g1.
  - now destruct g1.
Defined.

#[refine]
CoFixpoint texists' (f : nat -> ConstantGame) (n : nat) : ConstantGame :=
{|
  winner p := winner (f n) p;
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
Proof.
  - now destruct (f n).
  - now destruct (f n).
Defined.

#[refine]
CoFixpoint tall' (f : nat -> ConstantGame) (n : nat) : ConstantGame :=
{|
  winner p := winner (f n) p;
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
Proof.
  - now destruct (f n).
  - now destruct (f n).
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
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now cbn; destruct (who g move); cbn.
  - now apply CH.
Qed.

Lemma Not_chor :
  forall g1 g2 : ConstantGame,
    sim (Not (chor g1 g2)) (chand (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; [easy | | easy |].
  - now destruct p.
  - now cbn; destruct move; cbn.
Qed.

Lemma Not_chand :
  forall g1 g2 : ConstantGame,
    sim (Not (chand g1 g2)) (chor (Not g1) (Not g2)).
Proof.
  unshelve econstructor; cbn; intros; [easy | | easy |].
  - now destruct p.
  - now cbn; destruct move.
Qed.

Lemma Not_chexists :
  forall (A : Type) (f : A -> ConstantGame),
    sim (Not (chexists f)) (chall (fun x : A => Not (f x))).
Proof.
  unshelve econstructor; cbn; intros; [easy | | easy | easy].
  now destruct p.
Qed.

Lemma Not_chall :
  forall (A : Type) (f : A -> ConstantGame),
    sim (Not (chall f)) (chexists (fun x : A => Not (f x))).
Proof.
  unshelve econstructor; cbn; intros; [easy | | easy | easy].
  now destruct p.
Qed.

Lemma Not_por :
  forall g1 g2 : ConstantGame,
    sim (Not (por g1 g2)) (pand (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now destruct move; cbn.
  - now destruct move; cbn; apply CH.
Qed.

Lemma Not_pand :
  forall g1 g2 : ConstantGame,
    sim (Not (pand g1 g2)) (por (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now destruct move.
  - now destruct move; apply CH.
Qed.

Lemma Not_pexists :
  forall f : nat -> ConstantGame,
    sim (Not (pexists f)) (pall (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now destruct move; cbn.
  - destruct move as [n move]; cbn.
    replace (pall _)
       with (pall (fun m : nat => Not (if n =? m then next (f n) move else f m))).
    + now apply CH.
    + f_equal.
      extensionality m.
      now destruct (n =? m).
Qed.

Lemma Not_pall :
  forall f : nat -> ConstantGame,
    sim (Not (pall f)) (pexists (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now destruct move; cbn.
  - destruct move as [n move]; cbn.
    replace (pexists _)
       with (pexists (fun m : nat => Not (if n =? m then next (f n) move else f m))).
    + now apply CH.
    + f_equal.
      extensionality m.
      now destruct (n =? m).
Qed.

Lemma Not_sor :
  forall g1 g2 : ConstantGame,
    sim (Not (sor g1 g2)) (sand (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now destruct move; cbn.
  - now destruct move; cbn; [apply CH |].
Qed.

Lemma Not_sand :
  forall g1 g2 : ConstantGame,
    sim (Not (sand g1 g2)) (sor (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now destruct move; cbn.
  - now destruct move; cbn; [apply CH |].
Qed.

Lemma Not_sexists :
  forall f : nat -> ConstantGame,
    sim (Not (sexists f)) (sall (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now destruct move; cbn.
  - destruct move; cbn; [| now apply CH].
    replace (sall _) with (sall
      (fun n : nat => Not
      match n with
      | 0 => next (f 0) l
      | S n' => f (S n')
      end)).
    apply CH.
    f_equal.
    extensionality n.
    now destruct n.
Qed.

Lemma Not_sall :
  forall f : nat -> ConstantGame,
    sim (Not (sall f)) (sexists (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now destruct move; cbn.
  - destruct move; cbn; [| now apply CH].
    replace (sexists _) with (sexists
      (fun n : nat => Not
      match n with
      | 0 => next (f 0) l
      | S n' => f (S n')
      end)).
    apply CH.
    f_equal.
    extensionality n.
    now destruct n.
Qed.

Lemma Not_tor :
  forall g1 g2 : ConstantGame,
    sim (Not (tor g1 g2)) (tand (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now destruct move; cbn.
  - now destruct move; cbn; apply CH.
Qed.

Lemma Not_tand :
  forall g1 g2 : ConstantGame,
    sim (Not (tand g1 g2)) (tor (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now destruct move; cbn.
  - now destruct move; cbn; apply CH.
Qed.

Lemma Not_texists' :
  forall (f : nat -> ConstantGame) (n : nat),
    sim (Not (texists' f n)) (tall' (fun n : nat => Not (f n)) n).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now destruct move; cbn.
  - destruct move; cbn; [| now apply CH].
    replace (tall' _ _)
       with (tall' (fun m : nat => Not (if n =? m then next (f n) l else f m)) n).
    + now apply CH.
    + f_equal.
      extensionality m.
      now destruct (n =? m).
Qed.

Lemma Not_tall' :
  forall (f : nat -> ConstantGame) (n : nat),
    sim (Not (tall' f n)) (texists' (fun n : nat => Not (f n)) n).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now destruct move; cbn.
  - destruct move; cbn; [| now apply CH].
    replace (texists' _ _)
       with (texists' (fun m : nat => Not (if n =? m then next (f n) l else f m)) n).
    + now apply CH.
    + f_equal.
      extensionality m.
      now destruct (n =? m).
Qed.

Lemma Not_texists :
  forall f : nat -> ConstantGame,
    sim (Not (texists f)) (tall (fun n : nat => Not (f n))).
Proof.
  now intros; apply Not_texists'.
Qed.

Lemma Not_tall :
  forall f : nat -> ConstantGame,
    sim (Not (tall f)) (texists (fun n : nat => Not (f n))).
Proof.
  now intros; apply Not_tall'.
Qed.

(** Connectives preserve bisimilarity *)

Lemma sim_Not :
  forall g1 g2 : ConstantGame,
    sim g1 g2 -> sim (Not g1) (Not g2).
Proof.
  cofix CH.
  intros g1 g2 [].
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct p.
  - now rewrite whos0.
  - now apply CH, nexts0.
Qed.

Lemma sim_chor :
  forall g1 g1' g2 g2' : ConstantGame,
    sim g1 g1' -> sim g2 g2' -> sim (chor g1 g2) (chor g1' g2').
Proof.
  unshelve econstructor; cbn; [easy.. |].
  now destruct move.
Qed.

Lemma sim_chand :
  forall g1 g1' g2 g2' : ConstantGame,
    sim g1 g1' -> sim g2 g2' -> sim (chand g1 g2) (chand g1' g2').
Proof.
  unshelve econstructor; cbn; [easy.. |].
  now destruct move.
Qed.

(** And so on *)

(** * Strictness *)

(** A constant game is strict if players make moves in turns. *)
CoInductive Strict (g : ConstantGame) : Prop :=
{
  strict :
    (forall move : Labmove g, who g move = Machine) \/
    (forall move : Labmove g, who g move = Nature);
  stricts :
    forall move : Labmove g, Strict (next g move);
}.

Lemma Strict_Win : Strict Win.
Proof.
  constructor; cbn.
  - now left; destruct move.
  - now destruct move.
Qed.

Lemma Strict_Lose : Strict Lose.
Proof.
  constructor; cbn.
  - now left; destruct move.
  - now destruct move.
Qed.

Lemma Strict_Not :
  forall g : ConstantGame,
    Strict g -> Strict (Not g).
Proof.
  cofix CH.
  intros g [H1 H2].
  constructor.
  - now destruct H1 as [H1 | H1]; [right | left]; cbn; intros; rewrite H1.
  - now cbn; intros; apply CH.
Qed.

Lemma Strict_chor :
  forall g1 g2 : ConstantGame,
    Strict g1 -> Strict g2 -> Strict (chor g1 g2).
Proof.
  constructor; cbn.
  - now left.
  - now destruct move.
Qed.

Lemma Strict_chand :
  forall g1 g2 : ConstantGame,
    Strict g1 -> Strict g2 -> Strict (chand g1 g2).
Proof.
  constructor; cbn.
  - now right.
  - now destruct move.
Qed.

Lemma Strict_chexists :
  forall (A : Type) (f : A -> ConstantGame),
    (forall x : A, Strict (f x)) -> Strict (chexists f).
Proof.
  now constructor; cbn; [left |].
Qed.

Lemma Strict_chall :
  forall (A : Type) (f : A -> ConstantGame),
    (forall x : A, Strict (f x)) -> Strict (chall f).
Proof.
  now constructor; cbn; [right |].
Qed.

(** Parallel, sequential and toggling connectives (and therefore quantifiers)
    need not preserve strictness, because:
    - for parallel, both players can make moves
    - for sequential, one player may make moves but the other may change
    - for toggling, the same as for sequential *)

(*
Lemma Strict_sor :
  forall g1 g2 : ConstantGame,
    Strict g1 -> Strict g2 -> Strict (sor g1 g2).
Proof.
  cofix CH.
  destruct 1 as [H11 H12], 1 as [H21 H22]. constructor; cbn.
    left. destruct move.
    apply right. auto.
    destruct move; assumption.
Qed.

Lemma Strict_por :
  forall g1 g2 : ConstantGame,
    Strict g1 -> Strict g2 -> Strict (por g1 g2).
Proof.
  cofix CH.
  destruct 1 as [H11 H12], 1 as [H21 H22]. constructor.
    destruct H11 as [H11 | H11], H21 as [H21 | H21]. cbn.
      left. destruct move; auto.
      left. cbn. destruct move; auto.
Abort.
*)

(** * A game should have a winner... *)

(** Beware: a game can have two winners if it is not a static game. *)
CoInductive Winner (g : ConstantGame) (p : Player) : Prop :=
{
  Winner0 : (Labmove g -> False) -> winner g p;
  Winner1 :
    Labmove g ->
      (exists move : Labmove g,
        who g move = p /\ Winner (next g move) p) \/
      (forall move : Labmove g,
        who g move = swap p -> Winner (next g move) p);
}.

Lemma Winner_Win_Machine :
  Winner Win Machine.
Proof.
  now constructor; cbn.
Qed.

Lemma Winner_Win_not_Nature :
  ~ Winner Win Nature.
Proof.
  intros []; cbn in *.
  now apply Winner2.
Qed.

Lemma Winner_Lose_Nature :
  Winner Lose Nature.
Proof.
  now constructor; cbn.
Qed.

#[refine]
Definition nonstatic : ConstantGame :=
{|
  winner p := p = Machine;
  Labmove := bool;
  who move := if move then Machine else Nature;
  next move := if move then Win else Lose;
|}.
Proof.
  - now destruct p, p'.
  - now exists Machine.
Defined.

Lemma Winner_not_unique :
  exists g : ConstantGame,
    Winner g Machine /\ Winner g Nature.
Proof.
  exists nonstatic.
  split.
  - constructor; cbn; intros _; [easy |].
    now left; exists true.
  - constructor; cbn; intros H.
    + now destruct (H true).
    + now left; exists false.
Qed.

Lemma Winner_spec' :
  forall g : ConstantGame, exists p : Player, Winner g p.
Proof.
  intros.
  destruct (LEM (Winner g Machine)).
  - now exists Machine.
  - exists Nature.
Abort.

Lemma Winner_sim :
  forall (g1 g2 : ConstantGame) (p : Player),
    sim g1 g2 -> Winner g1 p -> Winner g2 p.
Proof.
  cofix CH.
  intros g1 g2 p [] [].
  constructor; intros.
  - apply winners0, Winner2.
    intros.
    apply H.
    now congruence.
  - rewrite <- Labmoves0 in X.
    decompose [ex or and] (Winner3 X).
    + left.
      exists (@transport _ id _ _ Labmoves0 x).
      split.
      * now rewrite <- whos0.
      * now apply CH with (next g1 x).
    + right; intros.
      apply CH with (next g1 (@transport _ id _ _ (eq_sym Labmoves0) move)).
      * now rewrite nexts0, transport_cat, cat_inv; cbn.
      * apply H.
        now rewrite whos0, transport_cat, cat_inv; cbn.
Qed.

Lemma Winner_Not :
  forall (g : ConstantGame) (p : Player),
    Winner (Not g) p <-> Winner g (swap p).
Proof.
  split; revert g p.
  - cofix CH.
    intros g p []; constructor; cbn in *.
    + now destruct p; cbn; apply Winner2.
    + intros move.
      decompose [and or ex] (Winner3 move).
      * left; exists x; split; [| now apply CH].
        now destruct (who g x); subst; cbn in *.
      * right; intros.
        apply CH, H.
        rewrite H0.
        now destruct p; cbn.
  - cofix CH.
    intros g p []; constructor; cbn in *; intros move.
    + specialize (Winner2 move).
      now destruct p; cbn.
    + decompose [ex or and] (Winner3 move).
      * left; exists x; split; [| now apply CH].
        rewrite H.
        now destruct p; cbn.
      * right; intros.
        apply CH, H.
        rewrite <- H0.
        now destruct (who g move0); cbn.
Qed.

Lemma Winner_Not' :
  forall (g : ConstantGame) (p : Player),
    Winner g p <-> Winner (Not g) (swap p).
Proof.
  intros.
  rewrite Winner_Not.
  now destruct p; cbn.
Qed.

Lemma Winner_chor_Machine :
  forall (g1 g2 : ConstantGame),
    Winner (chor g1 g2) Machine <-> Winner g1 Machine \/ Winner g2 Machine.
Proof.
  split; revert g1 g2.
  - intros. destruct H; cbn in *. destruct (Winner3 true).
    destruct H, x, H; auto.
    specialize (H false). cbn in H.
    admit.
  - intros g1 g2 [].
    + revert g1 g2 H.
      cofix CH.
      intros; constructor; cbn; intros.
      * now destruct (H0 true).
      * now left; exists true.
    + revert g1 g2 H.
      cofix CH.
      intros; constructor; cbn; intros.
      * now destruct (H0 true).
      * now left; exists false.
Admitted.

Lemma Winner_chor_Nature :
  forall (g1 g2 : ConstantGame),
    Winner (chor g1 g2) Nature <-> Winner g1 Nature /\ Winner g2 Nature.
Proof.
Admitted.

Lemma Winner_chor :
  forall (g1 g2 : ConstantGame) (p : Player),
    Winner (chor g1 g2) p <->
    match p with
    | Machine => Winner g1 Machine \/ Winner g2 Machine
    | Nature => Winner g1 Nature /\ Winner g2 Nature
    end.
Proof.
  destruct p.
  - now apply Winner_chor_Machine.
  - now apply Winner_chor_Nature.
Qed.

Lemma Winner_chand :
  forall (g1 g2 : ConstantGame) (p : Player),
    Winner (chand g1 g2) p <->
    match p with
    | Machine => Winner g1 Machine /\ Winner g2 Machine
    | Nature => Winner g1 Nature \/ Winner g2 Nature
    end.
Proof.
  intros.
  rewrite Winner_Not'.
  assert (forall g1 g2, Not (chand g1 g2) = chor (Not g1) (Not g2))
    by (now intros; apply sim_eq, Not_chand).
  rewrite H, Winner_chor.
  now destruct p; cbn; rewrite !Winner_Not; cbn.
Qed.

Lemma Winner_chexists :
  forall (A : Type) (f : A -> ConstantGame) (p : Player),
    Winner (chexists f) p <->
    match p with
    | Machine => exists x : A, Winner (f x) Machine
    | Nature => forall x : A, Winner (f x) Nature
    end.
Proof.
Admitted.

Lemma Winner_chall :
  forall (A : Type) (f : A -> ConstantGame) (p : Player),
    Winner (chall f) p <->
    match p with
    | Machine => forall x : A, Winner (f x) Machine
    | Nature => exists x : A, Winner (f x) Nature
    end.
Proof.
Admitted.

Lemma Winner_por_1 :
  forall g1 g2 : ConstantGame,
    Winner g1 Machine -> Winner g2 Machine -> Winner (por g1 g2) Machine.
Proof.
  cofix CH.
  intros g1 g2 H1 H2.
  decompose [Winner] H1.
  decompose [Winner] H2.
  constructor; cbn in *; [now auto |].
  - destruct 1.
    + destruct (Winner3 l).
      * destruct H as [move [H1' H2']]. left. exists (inl move). auto.
      * destruct (LEM (exists move : Labmove g2, who g2 move = Machine)).
        -- destruct H0.
           destruct (Winner5 x); [| now right; intros []; cbn; auto].
           destruct H3.
           left; exists (inr x0).
           now destruct H3; auto.
        -- right.
           destruct move; [now auto |].
           intro.
           apply CH; [easy |].
           destruct (Winner5 l0); [| now apply H4].
           destruct H4 as [move [H41 H42]]. contradiction H0.
           now exists move.
    + destruct (Winner5 l).
      * destruct H as [move [H1' H2']].
        now left; exists (inr move); auto.
      * destruct (LEM (exists move : Labmove g1, who g1 move = Machine)).
        -- destruct H0.
           destruct (Winner3 x); [| now right; intros []; cbn; auto].
           destruct H3.
           now left; exists (inl x0); destruct H3; auto.
        -- right.
           destruct move; [| now auto].
           intros.
           apply CH; [| easy].
           destruct (Winner3 l0); [| now apply H4].
           destruct H4 as [move [H41 H42]].
           contradiction H0.
           now exists move.
Qed.

Lemma Winner_por :
  forall g1 g2 : ConstantGame,
    Winner (por g1 g2) Nature -> Winner g1 Nature.
Proof.
Admitted.

Lemma Winner_pand :
  forall (g1 g2 : ConstantGame) (p : Player),
    Winner (pand g1 g2) p <-> False.
Proof.
Admitted.

Lemma Winner_pexists :
  forall (f : nat -> ConstantGame) (p : Player),
    Winner (pexists f) p <-> False.
Proof.
Admitted.

Lemma Winner_pall :
  forall (f : nat -> ConstantGame) (p : Player),
    Winner (pall f) p <-> False.
Proof.
Admitted.

Lemma excluded_middle :
  forall g : ConstantGame,
    Winner (por g (Not g)) Machine.
Proof.
  intro. destruct (LEM (Winner g Machine)).
Abort.

(** * Static constant games *)

(** Insight: a game is static if it has at most one winner. *)

Definition Static (g : ConstantGame) : Prop :=
  forall p p' : Player, Winner g p -> Winner g p' -> p = p'.

Lemma Static_Not :
  forall g : ConstantGame,
    Static g -> Static (Not g).
Proof.
  unfold Static.
  intros.
  apply Winner_Not in H0, H1.
  specialize (H _ _ H0 H1).
  now destruct p, p'; cbn in *.
Qed.

Lemma Static_chor :
  forall g1 g2 : ConstantGame,
    Static g1 -> Static g2 -> Static (chor g1 g2).
Proof.
  unfold Static.
  intros.
  apply Winner_chor in H1, H2.
  now destruct p, p', H1, H2; cbn in *; auto.
Qed.

Lemma Static_chand :
  forall g1 g2 : ConstantGame,
    Static g1 -> Static g2 -> Static (chand g1 g2).
Proof.
  unfold Static.
  intros.
  apply Winner_chand in H1, H2.
  now destruct p, p', H1, H2; auto.
Qed.

Lemma Static_chexists :
  forall (A : Type) (f : A -> ConstantGame),
    (forall x : A, Static (f x)) -> Static (chexists f).
Proof.
  unfold Static. intros.
  apply Winner_chexists in H0, H1.
  destruct p, p'; [easy | | | easy].
  - destruct H0.
    now apply (H _ _ _ H0 (H1 x)).
  - destruct H1.
    now apply (H _ _ _ (H0 x) H1).
Qed.

Lemma Static_por :
  forall g1 g2 : ConstantGame,
    Static g1 -> Static g2 -> Static (por g1 g2).
Proof.
Abort.

(** ** Static 2 *)

(** The definition of static constant games must be coinductive or
    we are doomed to fail. *)

(* This won't work. *)
(*
CoInductive Static' (g : ConstantGame) : Prop :=
{
  victor : Player;
  Static'_1 : (Labmove g -> False) -> winner g victor;
  Static'_2 :
    forall move : Labmove g,
      exists s : Static' (next g move), victor s = victor;
}.
*)

(** ** Static 3 *)

(** A game is Static' if it has exactly one winner. *)
Definition Static' (g : ConstantGame) : Prop :=
  exists p : Player, Winner g p /\ forall p' : Player, Winner g p' -> p = p'.

Lemma Static'_Not :
  forall g : ConstantGame,
    Static' g -> Static' (Not g).
Proof.
  unfold Static'.
  destruct 1 as (p & H & Heq).
  exists (swap p).
  split.
  - apply Winner_Not.
    now destruct p; cbn.
  - intros.
    rewrite (Heq (swap p')); [now destruct p'; cbn |].
    now apply Winner_Not.
Qed.

Lemma Static'_por :
  forall g1 g2 : ConstantGame,
    Static' g1 -> Static' g2 -> Static' (por g1 g2).
Proof.
Abort.

(** Miscellaneous *)

Inductive Position (g : ConstantGame) : Type :=
| EmptyPosition : Position g
| ConsPosition :
    forall move : Labmove g,
      Position (next g move) -> Position g.

Arguments EmptyPosition {g}.
Arguments ConsPosition {g} _ _.

CoInductive Run (g : ConstantGame) : Type :=
{
  run : option {move : Labmove g & Run (next g move)}
}.

Arguments run {g}.

Definition EmptyRun (g : ConstantGame) : Run g :=
{|
  run := None;
|}.

Inductive Finite' : ConstantGame -> nat -> Prop :=
| Finite'_Win : Finite' Win 0
| Finite'_Lose : Finite' Lose 0
| Finite'_move :
    forall (g : ConstantGame) (n : nat),
      (forall move : Labmove g, Finite' (next g move) n) ->
        Finite' g (S n)
| Finite'_pump :
    forall (g : ConstantGame) (n : nat),
      Finite' g n -> Finite' g (S n).

Definition Finite (G : ConstantGame) : Prop :=
  exists n : nat, Finite' G n.

Inductive Perifinite : ConstantGame -> Prop :=
| Perfinite_Win : Perifinite Win
| Perfinite_Lose : Perifinite Lose
| Perfinite_move :
    forall g : ConstantGame,
      (forall move : Labmove g, Perifinite (next g move)) ->
        Perifinite g.

Fixpoint prefix (g : ConstantGame) (p : Position g) : ConstantGame :=
match p with
| EmptyPosition => g
| ConsPosition move p' => prefix (next g move) p'
end.

Axioms V C : Type.

Axioms V_eqb : V -> V -> bool.

Axiom V_eqb_spec :
  forall v1 v2 : V, reflect (v1 = v2) (V_eqb v1 v2).

Definition Valuation : Type := V -> C.

Definition Game : Type := Valuation -> ConstantGame.

Definition ElementaryConstantGame (g : ConstantGame) : Prop :=
  Labmove g -> False.

Lemma ElementaryConstantGame_Win :
  ElementaryConstantGame Win.
Proof.
  red. destruct 1.
Qed.

Lemma ElementaryConstantGame_Lose :
  ElementaryConstantGame Lose.
Proof.
  red. destruct 1.
Qed.

Definition Elementary (g : Game) : Prop :=
  forall e : Valuation, ElementaryConstantGame (g e).

Definition depends (g : Game) (v : V) : Prop :=
  exists e1 e2 : Valuation,
    (forall v' : V, v' <> v -> e1 v' = e2 v') /\ g e1 <> g e2.

Lemma not_depends_ConstantGame :
  forall (g : ConstantGame) (v : V),
    ~ depends (fun _ => g) v.
Proof.
  unfold depends. intros g v [e1 [e2 [H1 H2]]]. contradiction.
Qed.

Definition Finitary (g : Game) : Prop :=
  exists l : list V,
    forall e1 e2 : Valuation,
      (Forall (fun v => e1 v = e2 v) l) -> g e1 = g e2.

Inductive Term : Type :=
| Var : V -> Term
| Const : C -> Term.

Definition extend (e : Valuation) (t : Term) : C :=
match t with
| Var v => e v
| Const c => c
end.
