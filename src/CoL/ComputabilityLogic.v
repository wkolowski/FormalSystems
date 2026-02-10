(** * Computability Logic *)

(**
  This is an attempt at formalizing Giorgi Japaridze's Computability
  Logic based on "In the beginning was game semantics" from the book
  "Games: Unifying Logic, Language, and Philosophy".

  The approach is to replace Japaridze's "classical" definitions with
  mainly coinductive ones friendly to type theory. Currently it's
  rather experimental and certainly very broken, because he seems to
  define game operations by defining their structure and winner mutually
  at the same time. Here this would require mutual coinduction and I
  don't know how to do it properly.
*)

From Stdlib Require Export FunctionalExtensionality.

From FormalSystems Require Export Base.

Axiom LEM : forall P : Prop, P \/ ~ P.

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

Inductive Player : Type :=
| Machine : Player
| Nature : Player.

Definition swap (p : Player) : Player :=
match p with
| Machine => Nature
| Nature => Machine
end.

Lemma swap_swap :
  forall p : Player,
    swap (swap p) = p.
Proof.
  now destruct p.
Qed.

Lemma injective_swap :
  forall p1 p2 : Player,
    swap p1 = swap p2 -> p1 = p2.
Proof.
  now destruct p1, p2.
Qed.

Lemma swap_neq :
  forall p : Player,
    swap p <> p.
Proof.
  now destruct p.
Qed.

CoInductive ConstantGame : Type :=
{
  machineWins : Prop;
  Labmove : Type;
  who : Labmove -> Player;
  next : Labmove -> ConstantGame;
}.

Definition Win : ConstantGame :=
{|
  machineWins := True;
  Labmove := Empty_set;
  who l := match l with end;
  next l := match l with end;
|}.

Definition Lose : ConstantGame :=
{|
  machineWins := False;
  Labmove := Empty_set;
  who l := match l with end;
  next l := match l with end;
|}.

CoInductive sim (g1 g2 : ConstantGame) : Prop :=
{
  winners : machineWins g1 <-> machineWins g2;
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
  unshelve econstructor; cbn; intros; [easy.. |].
  now cbn; apply CH.
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
  unshelve econstructor; intros.
  - exact (eq_trans p1 p2).
  - now rewrite w1.
  - now rewrite whos1, whos2, transport_cat.
  - apply (CH _ (next g2 (@transport _ id _ _ p1 move))).
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

(** * Tactics *)

#[global] Hint Constructors Player : CoL.

#[global] Hint Extern 1 =>
  match goal with
  | |- exists p : Player, _ => exists Machine; cbn
  end : CoL.

#[global] Hint Extern 1 =>
  match goal with
  | |- exists p : Player, _ => exists Nature; cbn
  end : CoL.

(** * Connectives *)

CoFixpoint Not (g : ConstantGame) : ConstantGame :=
{|
  machineWins := ~ machineWins g;
  Labmove := Labmove g;
  who move := swap (who g move);
  next move := Not (next g move);
|}.

Definition chor (g1 g2 : ConstantGame) : ConstantGame :=
{|
  machineWins := False;
  Labmove := bool;
  who move := Machine;
  next move := if move then g1 else g2;
|}.

Definition chand (g1 g2 : ConstantGame) : ConstantGame :=
{|
  machineWins := True;
  Labmove := bool;
  who move := Nature;
  next move := if move then g1 else g2;
|}.

Definition chexists {A : Type} (f : A -> ConstantGame) : ConstantGame :=
{|
  machineWins := False;
  Labmove := A;
  who move := Machine;
  next move := f move;
|}.

Definition chall {A : Type} (f : A -> ConstantGame) : ConstantGame :=
{|
  machineWins := True;
  Labmove := A;
  who move := Nature;
  next move := f move;
|}.

CoFixpoint por (g1 g2 : ConstantGame) : ConstantGame :=
{|
  machineWins := machineWins g1 \/ machineWins g2;
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
  machineWins := machineWins g1 /\ machineWins g2;
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

CoFixpoint pexists (f : nat -> ConstantGame) : ConstantGame :=
{|
  machineWins := exists n : nat, machineWins (f n);
  Labmove := {n : nat & Labmove (f n)};
  who '(existT _ n move) := who (f n) move;
  next '(existT _ n move) :=
    pexists (fun m : nat => if decide (n = m) then next (f n) move else f m);
|}.

CoFixpoint pall (f : nat -> ConstantGame) : ConstantGame :=
{|
  machineWins := forall n : nat, machineWins (f n);
  Labmove := {n : nat & Labmove (f n)};
  who '(existT _ n move) := who (f n) move;
  next '(existT _ n move) :=
    pall (fun m : nat => if decide (n = m) then next (f n) move else f m);
|}.

CoFixpoint sor (g1 g2 : ConstantGame) : ConstantGame :=
{|
  machineWins := machineWins g1;
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
  machineWins := machineWins g1;
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
  machineWins := machineWins (f 0);
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
  machineWins := machineWins (f 0);
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
  machineWins := machineWins g1;
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
  machineWins := machineWins g1;
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
  machineWins := machineWins (f n);
  Labmove := Labmove (f n) + nat;
  who move :=
    match move with
    | inl move' => who (f n) move'
    | inr _ => Machine
    end;
  next move :=
    match move with
    | inl move' => texists' (fun m : nat => if decide (n = m) then next (f n) move' else f m) n
    | inr m => texists' f m
    end;
|}.

CoFixpoint tall' (f : nat -> ConstantGame) (n : nat) : ConstantGame :=
{|
  machineWins := machineWins (f n);
  Labmove := Labmove (f n) + nat;
  who move :=
    match move with
    | inl move' => who (f n) move'
    | inr _ => Nature
    end;
  next move :=
    match move with
    | inl move' => tall' (fun m : nat => if decide (n = m) then next (f n) move' else f m) n
    | inr m => tall' f m
    end;
|}.

Definition texists (f : nat -> ConstantGame) : ConstantGame :=
  texists' f 0.

Definition tall (f : nat -> ConstantGame) : ConstantGame :=
  tall' f 0.

(** ** Connectives preserve bisimilarity *)

Lemma sim_Not :
  forall g1 g2 : ConstantGame,
    sim g1 g2 -> sim (Not g1) (Not g2).
Proof.
  cofix CH.
  intros g1 g2 [].
  unshelve econstructor; cbn; intros; only 1: easy.
  - now rewrite winners0.
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

Lemma sim_chexists :
  forall (A : Type) (f1 f2 : A -> ConstantGame),
    (forall x : A, sim (f1 x) (f2 x)) ->
      sim (chexists f1) (chexists f2).
Proof.
  now unshelve econstructor; cbn.
Qed.

Lemma sim_chall :
  forall (A : Type) (f1 f2 : A -> ConstantGame),
    (forall x : A, sim (f1 x) (f2 x)) ->
      sim (chall f1) (chall f2).
Proof.
  now unshelve econstructor; cbn.
Qed.

(** ** Some laws *)

Lemma Not_Not :
  forall g : ConstantGame,
    sim (Not (Not g)) g.
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct (LEM (machineWins g)).
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
  now unshelve econstructor; cbn.
Qed.

Lemma Not_por :
  forall g1 g2 : ConstantGame,
    sim (Not (por g1 g2)) (pand (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; only 1: easy.
  - now tauto.
  - now destruct move; cbn.
  - now destruct move; cbn; apply CH.
Qed.

Lemma Not_pand :
  forall g1 g2 : ConstantGame,
    sim (Not (pand g1 g2)) (por (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now destruct (LEM (machineWins g1)), (LEM (machineWins g2)); tauto.
  - now destruct move; cbn.
  - now destruct move; apply CH.
Qed.

Lemma Not_pexists :
  forall f : nat -> ConstantGame,
    sim (Not (pexists f)) (pall (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - now firstorder.
  - now destruct move; cbn.
  - destruct move as [n move]; cbn.
    replace (pall _)
       with (pall (fun m : nat => Not (if decide (n = m) then next (f n) move else f m))).
    + now apply CH.
    + f_equal.
      extensionality m.
      now decide (n = m).
Qed.

Lemma Not_pall :
  forall f : nat -> ConstantGame,
    sim (Not (pall f)) (pexists (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; only 1: easy.
  - split; [| now firstorder].
    intros Hall.
    destruct (LEM (exists n : nat, ~ machineWins (f n))); [easy |].
    cut False; [easy |].
    apply Hall; intros n.
    destruct (LEM (machineWins (f n))); [easy |].
    cut False; [easy |].
    now apply H; exists n.
  - now destruct move; cbn.
  - destruct move as [n move]; cbn.
    replace (pexists _)
       with (pexists (fun m : nat => Not (if decide (n = m) then next (f n) move else f m))).
    + now apply CH.
    + f_equal.
      extensionality m.
      now decide (n = m).
Qed.

Lemma Not_sor :
  forall g1 g2 : ConstantGame,
    sim (Not (sor g1 g2)) (sand (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; [easy.. | |].
  - now destruct move; cbn.
  - destruct move; cbn; [| easy].
    now apply CH.
Qed.

Lemma Not_sand :
  forall g1 g2 : ConstantGame,
    sim (Not (sand g1 g2)) (sor (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; [easy.. | |].
  - now destruct move; cbn.
  - destruct move; cbn; [| easy].
    now apply CH.
Qed.

Lemma Not_sexists :
  forall f : nat -> ConstantGame,
    sim (Not (sexists f)) (sall (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; [easy.. | now destruct move; cbn |].
  destruct move; cbn; [| now apply CH].
  replace (sall _) with (sall
    (fun n : nat => Not
    match n with
    | 0 => next (f 0) l
    | S n' => f (S n')
    end)).
  - now apply CH.
  - f_equal.
    extensionality n.
    now destruct n.
Qed.

Lemma Not_sall :
  forall f : nat -> ConstantGame,
    sim (Not (sall f)) (sexists (fun n : nat => Not (f n))).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; [easy.. | now destruct move; cbn |].
  destruct move; cbn; [| now apply CH].
  replace (sexists _) with (sexists
    (fun n : nat => Not
    match n with
    | 0 => next (f 0) l
    | S n' => f (S n')
    end)).
  - now apply CH.
  - f_equal.
    extensionality n.
    now destruct n.
Qed.

Lemma Not_tor :
  forall g1 g2 : ConstantGame,
    sim (Not (tor g1 g2)) (tand (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; [easy.. | |].
  - now destruct move; cbn.
  - now destruct move; cbn; apply CH.
Qed.

Lemma Not_tand :
  forall g1 g2 : ConstantGame,
    sim (Not (tand g1 g2)) (tor (Not g1) (Not g2)).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; [easy.. | |].
  - now destruct move; cbn.
  - now destruct move; cbn; apply CH.
Qed.

Lemma Not_texists' :
  forall (f : nat -> ConstantGame) (n : nat),
    sim (Not (texists' f n)) (tall' (fun n : nat => Not (f n)) n).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; [easy.. | now destruct move; cbn |].
  destruct move; cbn; [| now apply CH].
  replace (tall' _ _)
     with (tall' (fun m : nat => Not (if decide (n = m) then next (f n) l else f m)) n).
  - now apply CH.
  - f_equal.
    extensionality m.
    now decide (n = m).
Qed.

Lemma Not_tall' :
  forall (f : nat -> ConstantGame) (n : nat),
    sim (Not (tall' f n)) (texists' (fun n : nat => Not (f n)) n).
Proof.
  cofix CH.
  unshelve econstructor; cbn; intros; [easy.. | now destruct move; cbn |].
  destruct move; cbn; [| now apply CH].
  replace (texists' _ _)
     with (texists' (fun m : nat => Not (if decide (n = m) then next (f n) l else f m)) n).
  - now apply CH.
  - f_equal.
    extensionality m.
    now decide (n = m).
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

(**
  Parallel, sequential and toggling connectives (and therefore quantifiers)
  need not preserve strictness, because:
  - for parallel, both players can make moves
  - for sequential, one player may make moves but the other may change
  - for toggling, the same as for sequential
*)

(** * A game should have a winner... *)

(** [winsAt g p] holds when player [p] wins at the root of [g]. *)
Definition winsAt (g : ConstantGame) (p : Player) : Prop :=
match p with
| Machine => machineWins g
| Nature => ~ machineWins g
end.

Inductive WinnerF
  (Winner : ConstantGame -> Player -> Prop) (g : ConstantGame) (p : Player) : Prop :=
| WinnerF_Stay :
    winsAt g p ->
    (forall move : Labmove g, who g move = swap p -> Winner (next g move) p) ->
      WinnerF Winner g p
| WinnerF_Move :
    (exists move : Labmove g, who g move = p /\ Winner (next g move) p) ->
      WinnerF Winner g p.

CoInductive Winner (g : ConstantGame) (p : Player) : Prop :=
{
  out : WinnerF Winner g p;
}.

Lemma Winner_Stay :
  forall (g : ConstantGame) (p : Player),
    winsAt g p ->
    (forall move : Labmove g, who g move = swap p -> Winner (next g move) p) ->
    Winner g p.
Proof.
  now intros; constructor; apply WinnerF_Stay.
Defined.

Lemma Winner_Move :
  forall (g : ConstantGame) (p : Player),
    (exists move : Labmove g, who g move = p /\ Winner (next g move) p) ->
    Winner g p.
Proof.
  now intros; constructor; apply WinnerF_Move.
Defined.

Lemma Winner_Win_Machine :
  Winner Win Machine.
Proof.
  apply Winner_Stay; cbn; [easy |].
  now intros [].
Qed.

Lemma Winner_Win_not_Nature :
  ~ Winner Win Nature.
Proof.
  now intros [[? _ | []]]; cbn in *; [easy |].
Qed.

Lemma Winner_Lose_Nature :
  Winner Lose Nature.
Proof.
  apply Winner_Stay; cbn; [easy |].
  now intros [].
Qed.

Lemma Winner_Lose_not_Machine :
  ~ Winner Lose Machine.
Proof.
  now intros [[? _ | []]]; cbn in *; [easy |].
Qed.

Definition nonstatic : ConstantGame :=
{|
  machineWins := True;
  Labmove := bool;
  who move := if move then Machine else Nature;
  next move := if move then Win else Lose;
|}.

Lemma Winner_not_unique :
  exists g : ConstantGame,
    Winner g Machine /\ Winner g Nature.
Proof.
  exists nonstatic.
  split.
  - apply Winner_Move; cbn.
    exists true.
    split; [easy |].
    now apply Winner_Win_Machine.
  - apply Winner_Move; cbn.
    exists false.
    split; [easy |].
    now apply Winner_Lose_Nature.
Qed.

Lemma Winner_sim :
  forall (g1 g2 : ConstantGame) (p : Player),
    sim g1 g2 -> Winner g1 p -> Winner g2 p.
Proof.
  cofix CH.
  intros g1 g2 p [w lm wh nx] [[Hp Hk | (move1 & Hwho1 & Hnext)]].
  - apply Winner_Stay; [now destruct p; cbn in *; rewrite <- w |].
    intros move2 Hwho2.
    eapply CH.
    + specialize (nx (@transport _ id _ _ (eq_sym lm) move2)).
      rewrite transport_cat, cat_inv in nx; cbn in nx.
      now apply nx.
    + apply Hk.
      now rewrite wh, transport_cat, cat_inv; cbn.
  - apply Winner_Move.
    exists (@transport _ id _ _ lm move1).
    split; [now rewrite <- wh |].
    now eapply CH.
Qed.

#[export] Instance Proper_Winner_sim_eq :
  Proper (sim ==> eq ==> iff) Winner.
Proof.
  intros g1 g2 Hsim p ? <-.
  split; apply Winner_sim; [easy |].
  now symmetry.
Qed.

Lemma Winner_sim' :
  forall (g1 g2 : ConstantGame) (p : Player),
    sim g1 g2 -> Winner g1 p <-> Winner g2 p.
Proof.
  intros g1 g2 p Hsim.
  now split; apply Winner_sim.
Qed.

Lemma winsAt_Not :
  forall (g : ConstantGame) (p : Player),
    winsAt (Not g) p <-> winsAt g (swap p).
Proof.
  intros g []; cbn; [easy |].
  now destruct (LEM (machineWins g)); tauto.
Qed.

Lemma Winner_Not' :
  forall (g : ConstantGame) (p : Player),
    Winner (Not g) p -> Winner g (swap p).
Proof.
  cofix CH.
  intros g p [[Hp Hk | (move & Hwho & Hnext)]]; cbn in *.
  - apply Winner_Stay; [now apply winsAt_Not |].
    intros move Hwho.
    apply CH, Hk.
    now rewrite Hwho, swap_swap.
  - apply Winner_Move; exists move; split.
    + now rewrite <- Hwho, swap_swap.
    + now apply CH.
Qed.

Lemma Winner_Not :
  forall (g : ConstantGame) (p : Player),
    Winner (Not g) p <-> Winner g (swap p).
Proof.
  split; [now apply Winner_Not' |].
  intros Hw.
  rewrite <- swap_swap.
  apply Winner_Not'.
  now rewrite Not_Not.
Qed.

Lemma Winner_Not_swap :
  forall (g : ConstantGame) (p : Player),
    Winner g p <-> Winner (Not g) (swap p).
Proof.
  now intros g p; rewrite Winner_Not, swap_swap.
Qed.

Lemma Winner_chor_Machine :
  forall (g1 g2 : ConstantGame),
    Winner (chor g1 g2) Machine <-> Winner g1 Machine \/ Winner g2 Machine.
Proof.
  split.
  - intros [[| (b & _ & Hb)]]; cbn in *; [easy |].
    now destruct b; cbn in *; [left | right].
  - intros [H | H]; apply Winner_Move; cbn.
    + now exists true; split.
    + now exists false; split.
Qed.

Lemma Winner_chor_Nature :
  forall (g1 g2 : ConstantGame),
    Winner (chor g1 g2) Nature <-> Winner g1 Nature /\ Winner g2 Nature.
Proof.
  split.
  - intros [[Hp Hk | (b & Hb & _)]]; cbn in *; [| easy].
    now split; [apply (Hk true) | apply (Hk false)].
  - intros [H1 H2].
    now apply Winner_Stay; cbn; [| intros [] _].
Qed.

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
  rewrite Winner_Not_swap, Not_chand, Winner_chor.
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
  intros A f []; cbn.
  - split.
    + intros [[| (x & _ & Hx)]]; cbn in *; [easy |].
      now exists x.
    + intros (x & Hx).
      now apply Winner_Move; exists x; split.
  - split.
    + intros [[Hp Hk | (x & Hx & _)]]; intros; cbn in *; [| easy].
      now apply (Hk x).
    + intros Hall.
      now apply Winner_Stay; cbn.
Qed.

Lemma Winner_chall :
  forall (A : Type) (f : A -> ConstantGame) (p : Player),
    Winner (chall f) p <->
    match p with
    | Machine => forall x : A, Winner (f x) Machine
    | Nature => exists x : A, Winner (f x) Nature
    end.
Proof.
  intros.
  rewrite Winner_Not_swap, Not_chall, Winner_chexists.
  now destruct p; cbn; setoid_rewrite Winner_Not; cbn.
Qed.

Definition Static (g : ConstantGame) : Prop :=
  forall p1 p2 : Player, Winner g p1 -> Winner g p2 -> p1 = p2.

Lemma Static_Not :
  forall g : ConstantGame,
    Static g -> Static (Not g).
Proof.
  unfold Static.
  intros * Heq p1 p2 Hw1 Hw2.
  apply Winner_Not in Hw1, Hw2.
  now apply injective_swap, Heq.
Qed.

Lemma Static_chor :
  forall g1 g2 : ConstantGame,
    Static g1 -> Static g2 -> Static (chor g1 g2).
Proof.
  unfold Static.
  intros * Heq1 Heq2 p1 p2 Hw1 Hw2.
  apply Winner_chor in Hw1, Hw2.
  now destruct p1, p2, Hw1, Hw2; cbn in *; auto.
Qed.

Lemma Static_chand :
  forall g1 g2 : ConstantGame,
    Static g1 -> Static g2 -> Static (chand g1 g2).
Proof.
  unfold Static.
  intros * Heq1 Heq2 p1 p2 Hw1 Hw2.
  apply Winner_chand in Hw1, Hw2.
  now destruct p1, p2, Hw1, Hw2; cbn in *; auto.
Qed.

Lemma Static_chexists :
  forall (A : Type) (f : A -> ConstantGame),
    (forall x : A, Static (f x)) -> Static (chexists f).
Proof.
  unfold Static.
  intros * Heq p1 p2 Hw1 Hw2.
  apply Winner_chexists in Hw1, Hw2.
  destruct p1, p2; [easy | | | easy].
  - destruct Hw1 as [x Hwm].
    now apply (Heq x).
  - destruct Hw2 as [x Hwm].
    now apply (Heq x).
Qed.

Definition Static' (g : ConstantGame) : Prop :=
  exists p : Player,
    Winner g p /\ forall p2 : Player, Winner g p2 -> p = p2.

Lemma Static'_Not :
  forall g : ConstantGame,
    Static' g -> Static' (Not g).
Proof.
  unfold Static'.
  intros g (p1 & H & Heq).
  exists (swap p1).
  split; [now rewrite Winner_Not, swap_swap |].
  intros p2 Hw.
  rewrite Winner_Not in Hw.
  apply Heq in Hw as ->.
  now rewrite swap_swap.
Qed.
