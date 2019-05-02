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
      (*exists p : Player, winner p;*)
      ~ forall p : Player, ~ winner p;
    Labmove : Type;
    who : Labmove -> Player;
    next : Labmove -> ConstantGame;
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
    Labmove := Empty_set;
    who l := match l with end;
    next l := match l with end;
|}.
  destruct p, p'; firstorder.
  intro. apply (H Machine). trivial.
(*  exists Machine. trivial.*)
(*  intro. specialize (H Machine). cbn in H. contradiction.*)
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
    Labmove := Empty_set;
    who l := match l with end;
    next l := match l with end;
|}.
  destruct p, p'; firstorder.
  intro. apply (H Nature). trivial.
(*  exists Nature. trivial.*)
(*  intro H. specialize (H Nature). cbn in H. contradiction.*)
Defined.

Inductive Position (g : ConstantGame) : Type :=
    | EmptyPosition : Position g
    | ConsPosition :
        forall move : Labmove g,
          Position (next g move) -> Position g.

Arguments EmptyPosition {g}.
Arguments ConsPosition {g} _ _.

CoInductive Run (g : ConstantGame) : Type :=
{
    run :
      option {move : Labmove g & Run (next g move)}
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

Require Import Bool.

Variables V C : Type.

Variable V_eqb : V -> V -> bool.

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

Require Import List.
Import ListNotations.

Definition Finitary (g : Game) : Prop :=
  exists l : list V,
    forall e1 e2 : Valuation,
      (Forall (fun v => e1 v = e2 v) l) -> g e1 = g e2.

(** TODO: arity *)

Inductive Term : Type :=
    | Var : V -> Term
    | Const : C -> Term.

Definition extend (e : Valuation) (t : Term) : C :=
match t with
    | Var v => e v
    | Const c => c
end.

(** TODO: various not too interesting things *)

Definition swap (p : Player) : Player :=
match p with
    | Machine => Nature
    | Nature => Machine
end.

Definition transport
  {A : Type} {P : A -> Type} {x y : A} (p : x = y) : P x -> P y.
Proof.
  destruct p. intro. assumption.
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

Lemma sim_refl :
  forall g : ConstantGame, sim g g.
Proof.
  cofix CH.
  econstructor; cbn; intros. Unshelve.
    Focus 4. reflexivity.
    all: cbn; try reflexivity.
    apply CH.
Qed.

CoFixpoint Not (g : ConstantGame) : ConstantGame.
Proof.
refine
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
  destruct g, p, p'; firstorder.
  intro. destruct g. cbn in *.
    apply winner_spec'0. do 2 intro. apply (H (swap p)).
    destruct p; cbn; assumption.
(*  destruct g as [winner spec [p H]]. cbn in *.
    exists (swap p). destruct p; cbn; assumption.*)
(*  intro H. destruct g. cbn in *. apply winner_spec'0.
    do 2 intro. apply (H (swap p)). destruct p; cbn; assumption.*)
Defined.

Lemma Not_Not :
  forall g : ConstantGame,
    sim (Not (Not g)) g.
Proof.
  cofix CH.
  econstructor; cbn; intros. Unshelve.
    Focus 4. cbn. reflexivity.
    destruct p; firstorder.
    cbn. destruct (who g move); cbn; reflexivity.
    apply CH.
Qed.

Definition chor (g1 g2 : ConstantGame) : ConstantGame.
Proof.
  refine
  {|
      winner p := p = Nature;
      Labmove := bool;
      who move := Machine;
      next move := if move then g1 else g2;
  |}.
  destruct p, p'; firstorder.
  intro. apply (H Nature). reflexivity.
(*  exists Nature. trivial.*)
Defined.

Definition chand (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p := p = Machine;
    Labmove := bool;
    who move := Nature;
    next move := if move then g1 else g2;
|}.
  destruct p, p'; firstorder.
  intro. apply (H Machine). reflexivity.
(*  exists Machine. trivial. *)
Defined.

Lemma Not_chor :
  forall g1 g2 : ConstantGame,
    sim (Not (chor g1 g2)) (chand (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor; cbn; intros. Unshelve.
    Focus 4. cbn. reflexivity.
    destruct p; firstorder congruence.
    reflexivity.
    cbn. destruct move; apply sim_refl.
Qed.

Lemma Not_chand :
  forall g1 g2 : ConstantGame,
    sim (Not (chand g1 g2)) (chor (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor; cbn; intros. Unshelve.
    Focus 4. cbn. reflexivity.
    destruct p; firstorder congruence.
    reflexivity.
    cbn. destruct move; apply sim_refl.
Qed.

CoFixpoint por (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
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
  destruct g1, g2, p, p'; firstorder.
  intro. destruct g1, g2. cbn in *.
    apply winner_spec'0. do 2 intro.
    apply winner_spec'1. do 2 intro.
    destruct p, p0.
      1-3: apply (H Machine); auto.
      apply (H Nature). auto.
(*  destruct g1 as [winner1 spec1 [p1 H1]], g2 as [winner2 spec2 [p2 H2]].
    cbn in *. destruct p1.
      exists Machine. auto.
      destruct p2.
        exists Machine. auto.
        exists Nature. auto.
*)
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
  destruct g1, g2, p, p'; firstorder.
  intro. destruct g1, g2. cbn in *.
    apply winner_spec'0. do 2 intro.
    apply winner_spec'1. do 2 intro.
    destruct p, p0.
      apply (H Machine); auto.
      1-3: apply (H Nature); auto.
(*  destruct g1 as [winner1 spec1 [p1 H1]], g2 as [winner2 spec2 [p2 H2]].
    cbn in *. destruct p1, p2.
      exists Machine. auto.
      1-3: exists Nature; auto.*)
Defined.

Lemma Not_por :
  forall g1 g2 : ConstantGame,
    sim (Not (por g1 g2)) (pand (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; intros.
      destruct p; firstorder.
      destruct move; reflexivity.
      destruct move; apply CH.
Qed.

Lemma Not_pand :
  forall g1 g2 : ConstantGame,
    sim (Not (pand g1 g2)) (por (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; intros.
      destruct p; firstorder.
      destruct move; reflexivity.
      destruct move; apply CH.
Qed.

Definition chexists {A : Type} (f : A -> ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p := p = Nature;
    Labmove := A;
    who move := Machine;
    next move := f move;
|}.
  destruct p, p'; firstorder.
  intro. apply (H Nature). reflexivity.
(*  exists Nature. reflexivity.*)
Defined.

Definition chall {A : Type} (f : A -> ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p := p = Machine;
    Labmove := A;
    who move := Nature;
    next move := f move;
|}.
  destruct p, p'; firstorder.
  intro. apply (H Machine). reflexivity.
(*  exists Machine. reflexivity.*)
Defined.

Lemma Not_chexists :
  forall (A : Type) (f : A -> ConstantGame),
    sim (Not (chexists f)) (chall (fun x : A => Not (f x))).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn.
      destruct p; firstorder congruence.
      reflexivity.
      intro. apply sim_refl.
Qed.

Lemma Not_chall :
  forall (A : Type) (f : A -> ConstantGame),
    sim (Not (chall f)) (chexists (fun x : A => Not (f x))).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn.
      destruct p; firstorder congruence.
      reflexivity.
      intro. apply sim_refl.
Qed.

CoFixpoint sor (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
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
  destruct g1, g2; firstorder.
  destruct g1. auto.
Defined.

CoFixpoint sand (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
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
  destruct g1, g2, p, p'; firstorder.
  destruct g1; auto.
Defined.

Lemma Not_sor :
  forall g1 g2 : ConstantGame,
    sim (Not (sor g1 g2)) (sand (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; intros.
      reflexivity.
      destruct move; reflexivity.
      destruct move.
        apply CH.
        apply sim_refl.
Qed.

Lemma Not_sand :
  forall g1 g2 : ConstantGame,
    sim (Not (sand g1 g2)) (sor (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; intros.
      reflexivity.
      destruct move; reflexivity.
      destruct move.
        apply CH.
        apply sim_refl.
Qed.

CoFixpoint sexists (f : nat -> ConstantGame) : ConstantGame.
Proof.
refine
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
  destruct (f 0). cbn. firstorder.
  destruct (f 0). auto.
Defined.

CoFixpoint sall (f : nat -> ConstantGame) : ConstantGame.
Proof.
refine
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
  destruct (f 0). cbn. firstorder.
  destruct (f 0). auto.
Defined.

Require Import FunctionalExtensionality.

Lemma Not_sexists :
  forall f : nat -> ConstantGame,
    sim (Not (sexists f)) (sall (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; intros.
      reflexivity.
      destruct move; reflexivity.
      destruct move.
        replace (sall _) with (sall
          (fun n : nat => Not
          match n with
              | 0 => next (f 0) l
              | S n' => f (S n')
          end)).
          apply CH.
          f_equal. extensionality n. destruct n; reflexivity.
        apply CH.
Qed.

Lemma Not_sall :
  forall f : nat -> ConstantGame,
    sim (Not (sall f)) (sexists (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; intros.
      reflexivity.
      destruct move; reflexivity.
      destruct move.
        replace (sexists _) with (sexists
          (fun n : nat => Not
          match n with
              | 0 => next (f 0) l
              | S n' => f (S n')
          end)).
          apply CH.
          f_equal. extensionality n. destruct n; reflexivity.
        apply CH.
Qed.

CoFixpoint tor (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
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
  destruct g1, g2. cbn. firstorder.
  destruct g1; auto.
Defined.

CoFixpoint tand (g1 g2 : ConstantGame) : ConstantGame.
Proof.
refine
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
  destruct g1, g2. cbn. firstorder.
  destruct g1; auto.
Defined.

Lemma Not_tor :
  forall g1 g2 : ConstantGame,
    sim (Not (tor g1 g2)) (tand (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn.
      reflexivity.
      destruct move; reflexivity.
      destruct move; apply CH.
Qed.

Lemma Not_tand :
  forall g1 g2 : ConstantGame,
    sim (Not (tand g1 g2)) (tor (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn.
      reflexivity.
      destruct move; reflexivity.
      destruct move; apply CH.
Qed.

Require Import Arith.

CoFixpoint texists' (f : nat -> ConstantGame) (n : nat) : ConstantGame.
Proof.
refine
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
          | inl move' => texists'
              (fun m : nat => if n =? m then next (f n) move' else f m) n
          | inr m => texists' f m
      end;
|}.
  destruct (f n). cbn. firstorder.
  destruct (f n); auto.
Defined.

CoFixpoint tall' (f : nat -> ConstantGame) (n : nat) : ConstantGame.
Proof.
refine
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
          | inl move' => tall'
              (fun m : nat => if n =? m then next (f n) move' else f m) n
          | inr m => tall' f m
      end;
|}.
  destruct (f n). cbn. firstorder.
  destruct (f n); auto.
Defined.

Lemma Not_texists' :
  forall (f : nat -> ConstantGame) (n : nat),
    sim (Not (texists' f n)) (tall' (fun n : nat => Not (f n)) n).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; intros.
      reflexivity.
      destruct move; reflexivity.
      destruct move.
        2: apply CH.
        replace (tall' _ _) with (tall'
          (fun m : nat => Not (if n =? m then next (f n) l else f m)) n).
          apply CH.
          f_equal. extensionality m. destruct (n =? m); reflexivity.
Qed.

Lemma Not_tall' :
  forall (f : nat -> ConstantGame) (n : nat),
    sim (Not (tall' f n)) (texists' (fun n : nat => Not (f n)) n).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; intros.
      reflexivity.
      destruct move; reflexivity.
      destruct move.
        2: apply CH.
        replace (texists' _ _) with (texists'
          (fun m : nat => Not (if n =? m then next (f n) l else f m)) n).
          apply CH.
          f_equal. extensionality m. destruct (n =? m); reflexivity.
Qed.

Definition texists (f : nat -> ConstantGame) : ConstantGame :=
  texists' f 0.

Definition tall (f : nat -> ConstantGame) : ConstantGame :=
  tall' f 0.

Lemma Not_texists :
  forall f : nat -> ConstantGame,
    sim (Not (texists f)) (tall (fun n : nat => Not (f n))).
Proof.
  intros. apply Not_texists'.
Qed.

Lemma Not_tall :
  forall f : nat -> ConstantGame,
    sim (Not (tall f)) (texists (fun n : nat => Not (f n))).
Proof.
  intros. apply Not_tall'.
Qed.

CoFixpoint pexists (f : nat -> ConstantGame) : ConstantGame.
Proof.
refine
{|
    winner p :=
      match p with
          | Machine => exists n : nat, winner (f n) Machine
          | Nature => forall n : nat, winner (f n) Nature
      end;
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
  destruct p, p'; try reflexivity.
    intros [n H] H'. specialize (H' n). destruct (f n). auto.
    intros H [n H']. specialize (H n). destruct (f n). auto.
  intro. destruct (LEM (exists n : nat, winner (f n) Machine)).
    apply (H Machine). assumption.
    apply (H Nature). intro. destruct (LEM (winner (f n) Nature)).
      assumption.
      contradict H0. exists n. destruct (f n). cbn in *.
        destruct (LEM (winner0 Machine)).
          assumption.
          contradict winner_spec'0. destruct p; assumption.
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
  destruct p, p'; try reflexivity.
    intros H [n H']. specialize (H n). destruct (f n). auto.
    intros [n H] H'. specialize (H' n). destruct (f n). auto.
  intro. destruct (LEM (exists n : nat, winner (f n) Nature)).
    apply (H Nature). assumption.
    apply (H Machine). intro. destruct (LEM (winner (f n) Machine)).
      assumption.
      contradict H0. exists n. destruct (f n). cbn in *.
        destruct (LEM (winner0 Nature)).
          assumption.
          contradict winner_spec'0. destruct p; assumption.
Defined.

Lemma Not_pexists :
  forall f : nat -> ConstantGame,
    sim (Not (pexists f)) (pall (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; intros.
      reflexivity.
      destruct move. reflexivity.
      destruct move as [n move].
        replace (pall _) with (pall
          (fun m : nat => Not (if n =? m then next (f n) move else f m))).
          apply CH.
          f_equal. extensionality m. destruct (n =? m); reflexivity.
Qed.

Lemma Not_pall :
  forall f : nat -> ConstantGame,
    sim (Not (pall f)) (pexists (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; intros.
      reflexivity.
      destruct move. reflexivity.
      destruct move as [n move].
        replace (pexists _) with (pexists
          (fun m : nat => Not (if n =? m then next (f n) move else f m))).
          apply CH.
          f_equal. extensionality m. destruct (n =? m); reflexivity.
Qed.

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
    left. destruct move.
    destruct move.
Qed.

Lemma Strict_Lose : Strict Lose.
Proof.
  constructor; cbn.
    left. destruct move.
    destruct move.
Qed.

Lemma Strict_Not :
  forall g : ConstantGame,
    Strict g -> Strict (Not g).
Proof.
  cofix CH.
  destruct 1 as [H1 H2]. constructor.
    destruct H1 as [H1 | H1]; [right | left];
      cbn; intro; rewrite H1; reflexivity.
    intro. cbn. apply CH. apply H2.
Qed.

Lemma Strict_chor :
  forall g1 g2 : ConstantGame,
    Strict g1 -> Strict g2 -> Strict (chor g1 g2).
Proof.
  cofix CH.
  constructor; cbn.
    left. auto.
    destruct move; assumption.
Qed.

Lemma Strict_chand :
  forall g1 g2 : ConstantGame,
    Strict g1 -> Strict g2 -> Strict (chand g1 g2).
Proof.
  cofix CH.
  constructor; cbn.
    right. auto.
    destruct move; assumption.
Qed.

Lemma Strict_chexists :
  forall (A : Type) (f : A -> ConstantGame),
    (forall x : A, Strict (f x)) -> Strict (chexists f).
Proof.
  cofix CH.
  intros. constructor; cbn.
    left. auto.
    apply H.
Qed.

Lemma Strict_chall :
  forall (A : Type) (f : A -> ConstantGame),
    (forall x : A, Strict (f x)) -> Strict (chall f).
Proof.
  cofix CH.
  intros. constructor; cbn.
    right. auto.
    apply H.
Qed.

(** Parallel, sequential and toggling connectives need not preserve
    strictness, because:
    - for parallel, both players can make moves
    - for sequential, one player may make moves but the other may change
    - for toggling, the same as for sequential
*)

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