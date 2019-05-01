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

CoFixpoint Win : ConstantGame :=
{|
    winner := Machine;
    Labmove := Empty_set;
    who l := match l with end;
    next l := match l with end;
|}.

CoFixpoint Lose : ConstantGame :=
{|
    winner := Nature;
    Labmove := Empty_set;
    who l := match l with end;
    next l := match l with end;
|}.

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

CoInductive Strict (g : ConstantGame) : Prop :=
{
    strict :
      (forall move : Labmove g, who g move = Machine) \/
      (forall move : Labmove g, who g move = Nature);
    stricts :
      forall move : Labmove g, Strict (next g move);
}.

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

(** TODO: różne pierdoły *)

Definition swap (p : Player) : Player :=
match p with
    | Machine => Nature
    | Nature => Machine
end.

Print ConstantGame.

Definition transport
  {A : Type} {P : A -> Type} {x y : A} (p : x = y) : P x -> P y.
Proof.
  destruct p. intro. assumption.
Defined.

Definition ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y.
Proof.
  destruct p. reflexivity.
Defined.

Check @transport Type id _ _.

Print ConstantGame.

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

Lemma sim_endo :
  forall (g1 g2 : ConstantGame) (f : ConstantGame -> ConstantGame),
    sim g1 g2 -> sim (f g1) (f g2).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4.
Abort.

Lemma sim_refl :
  forall g : ConstantGame, sim g g.
Proof.
  cofix CH.
  econstructor; cbn; intros. Unshelve.
    Focus 4. reflexivity.
    all: cbn; try reflexivity.
    apply CH.
Qed.

CoFixpoint Not (g : ConstantGame) : ConstantGame :=
{|
    winner := swap (winner g);
    Labmove := Labmove g;
    who move := swap (who g move);
    next move := Not (next g move);
|}.

Lemma Not_Not :
  forall g : ConstantGame,
    sim (Not (Not g)) g.
Proof.
  cofix CH.
  econstructor; cbn; intros. Unshelve.
    Focus 4. cbn. reflexivity.
    destruct (winner g); cbn; reflexivity.
    cbn. destruct (who g move); cbn; reflexivity.
    apply CH.
Qed.

Definition chor (g1 g2 : ConstantGame) : ConstantGame :=
{|
    winner := Nature;
(*      match winner g1, winner g2 with
          | Nature, Nature => Nature
          | _, _ => Machine
      end;*)
    Labmove := bool;
    who move := Machine;
    next move := if move then g1 else g2;
|}.

Definition chand (g1 g2 : ConstantGame) : ConstantGame :=
{|
    winner := Machine;
(*      match winner g1, winner g2 with
          | Machine, Machine => Machine
          | _, _ => Nature
      end;*)
    Labmove := bool;
    who move := Nature;
    next move := if move then g1 else g2;
|}.

Lemma Not_chor :
  forall g1 g2 : ConstantGame,
    sim (Not (chor g1 g2)) (chand (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor; cbn; intros. Unshelve.
    Focus 4. cbn. reflexivity.
    1-2: reflexivity.
    cbn. destruct move; apply sim_refl.
Qed.

Lemma Not_chand :
  forall g1 g2 : ConstantGame,
    sim (Not (chand g1 g2)) (chor (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor; cbn; intros. Unshelve.
    Focus 4. cbn. reflexivity.
    1-2: reflexivity.
    cbn. destruct move; apply sim_refl.
Qed.

Print ConstantGame.

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
      end
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
      end
|}.

Lemma Not_por :
  forall g1 g2 : ConstantGame,
    sim (Not (por g1 g2)) (pand (Not g1) (Not g2)).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; intros.
      destruct (winner g1), (winner g2); reflexivity.
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
      destruct (winner g1), (winner g2); reflexivity.
      destruct move; reflexivity.
      destruct move; apply CH.
Qed.

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

Lemma Not_chexists :
  forall (A : Type) (f : A -> ConstantGame),
    sim (Not (chexists f)) (chall (fun x : A => Not (f x))).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; try reflexivity.
    intro. apply sim_refl.
Qed.

Lemma Not_chall :
  forall (A : Type) (f : A -> ConstantGame),
    sim (Not (chall f)) (chexists (fun x : A => Not (f x))).
Proof.
  cofix CH.
  econstructor. Unshelve.
    Focus 4. cbn. reflexivity.
    all: cbn; try reflexivity.
    intro. apply sim_refl.
Qed.

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

CoFixpoint texists'
  (f : nat -> ConstantGame) (n : nat) : ConstantGame :=
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

CoFixpoint tall'
  (f : nat -> ConstantGame) (n : nat) : ConstantGame :=
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