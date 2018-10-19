Require Import List.
Import ListNotations.

Require Import Bool.

Parameter Loc : Type.
Parameter dec : Loc -> Loc -> bool.
Parameter dec_spec :
  forall x y : Loc, reflect (x = y) (dec x y).

Require Import Arith.

Notation "x =? y" := (dec x y) (at level 70).

Inductive AExp : Type :=
    | Const : nat -> AExp
    | Var : Loc -> AExp
    | Add : AExp -> AExp -> AExp
    | Sub : AExp -> AExp -> AExp
    | Mul : AExp -> AExp -> AExp.

Inductive BExp : Type :=
    | BTrue : BExp
    | BFalse : BExp
    | Eq : AExp -> AExp -> BExp
    | Le : AExp -> AExp -> BExp
    | Not : BExp -> BExp
    | And : BExp -> BExp -> BExp
    | Or : BExp -> BExp -> BExp.

Inductive Com : Type :=
    | Skip : Com
    | Asgn : Loc -> AExp -> Com
    | Seq : Com -> Com -> Com
    | If : BExp -> Com -> Com -> Com
    | While : BExp -> Com -> Com.

Definition State : Type := Loc -> nat.

Definition initialState : State := fun _ => 0.

Definition changeState (s : State) (x : Loc) (n : nat) : State :=
  fun y : Loc => if x =? y then n else s y.

Inductive AEval : AExp -> State -> nat -> Prop :=
    | EvalConst :
        forall (n : nat) (s : State), AEval (Const n) s n
    | EvalVar :
        forall (v : Loc) (s : State), AEval (Var v) s (s v)
    | EvalAdd :
        forall (a1 a2 : AExp) (s : State) (n1 n2 : nat),
          AEval a1 s n1 -> AEval a2 s n2 -> AEval (Add a1 a2) s (n1 + n2)
    | EvalSub :
        forall (a1 a2 : AExp) (s : State) (n1 n2 : nat),
          AEval a1 s n1 -> AEval a2 s n2 -> AEval (Sub a1 a2) s (n1 - n2)
    | EvalMul :
        forall (a1 a2 : AExp) (s : State) (n1 n2 : nat),
          AEval a1 s n1 -> AEval a2 s n2 -> AEval (Mul a1 a2) s (n1 * n2).

Hint Constructors AEval.

Ltac inv H :=
  inversion H; subst; clear H.

Lemma AEval_det :
  forall {a : AExp} {s : State} {n m : nat},
    AEval a s n -> AEval a s m -> n = m.
Proof.
  intros a s n m H. revert m.
  induction H; inversion 1; subst; clear H.
    1-2: reflexivity.
    rewrite (IHAEval1 _ H4), (IHAEval2 _ H7). reflexivity.
    rewrite (IHAEval1 _ H4), (IHAEval2 _ H7). reflexivity.
    rewrite (IHAEval1 _ H4), (IHAEval2 _ H7). reflexivity.
Qed.

Fixpoint aeval (a : AExp) (s : State) : nat :=
match a with
    | Const n => n
    | Var v => s v
    | Add a1 a2 => aeval a1 s + aeval a2 s
    | Sub a1 a2 => aeval a1 s - aeval a2 s
    | Mul a1 a2 => aeval a1 s * aeval a2 s
end.

Lemma AEval_aeval :
  forall {a : AExp} {s : State} {n : nat},
    AEval a s n -> aeval a s = n.
Proof.
  induction 1; cbn; rewrite ?IHAEval1, ?IHAEval2; reflexivity.
Qed.

Lemma aeval_AEval :
  forall {a : AExp} {s : State} {n : nat},
    aeval a s = n -> AEval a s n.
Proof.
  induction a; cbn; intros; rewrite <- H; auto.
Defined.

Inductive BEval : BExp -> State -> bool -> Prop :=
    | EvalTrue :
        forall s : State, BEval BTrue s true
    | EvalFalse :
        forall s : State, BEval BFalse s false
    | EvalEq :
        forall (a1 a2 : AExp) (s : State) (n m : nat),
          AEval a1 s n -> AEval a2 s m -> BEval (Eq a1 a2) s (Nat.eqb n m)
    | EvalLe :
        forall (a1 a2 : AExp) (s : State) (n m : nat),
          AEval a1 s n -> AEval a2 s m -> BEval (Le a1 a2) s (Nat.leb n m)
    | EvalNot :
        forall (e : BExp) (s : State) (b : bool),
          BEval e s b -> BEval (Not e) s (negb b)
    | EvalAnd :
        forall (e1 e2 : BExp) (s : State) (b1 b2 : bool),
          BEval e1 s b1 -> BEval e2 s b2 -> BEval (And e1 e2) s (andb b1 b2)
    | EvalOr :
        forall (e1 e2 : BExp) (s : State) (b1 b2 : bool),
          BEval e1 s b1 -> BEval e2 s b2 -> BEval (Or e1 e2) s (orb b1 b2).

Hint Constructors BEval.

Lemma BEval_det :
  forall {e : BExp} {s : State} {b1 : bool},
    BEval e s b1 -> forall {b2 : bool}, BEval e s b2 -> b1 = b2.
Proof.
  induction 1; intros.
    inv H. reflexivity.
    inv H. reflexivity.
    inv H1. rewrite (AEval_det H H4), (AEval_det H0 H7). reflexivity.
    inv H1. rewrite (AEval_det H H4), (AEval_det H0 H7). reflexivity.
    inv H0. rewrite (IHBEval _ H2). reflexivity.
    inv H1. rewrite (IHBEval1 _ H4), (IHBEval2 _ H7). reflexivity.
    inv H1. rewrite (IHBEval1 _ H4), (IHBEval2 _ H7). reflexivity.
Qed.

Fixpoint beval (e : BExp) (s : State) : bool :=
match e with
    | BTrue => true
    | BFalse => false
    | Eq a1 a2 => Nat.eqb (aeval a1 s) (aeval a2 s)
    | Le a1 a2 => Nat.leb (aeval a1 s) (aeval a2 s)
    | Not e' => negb (beval e' s)
    | And e1 e2 => andb (beval e1 s) (beval e2 s)
    | Or e1 e2 => orb (beval e1 s) (beval e2 s)
end.

Lemma BEval_beval :
  forall {e : BExp} {s : State} {b : bool},
    BEval e s b -> beval e s = b.
Proof.
  induction 1; cbn.
    1-2: reflexivity.
    rewrite (AEval_aeval H), (AEval_aeval H0). reflexivity.
    rewrite (AEval_aeval H), (AEval_aeval H0). reflexivity.
    rewrite IHBEval. reflexivity.
    rewrite IHBEval1, IHBEval2. reflexivity.
    rewrite IHBEval1, IHBEval2. reflexivity.
Qed.

Lemma beval_BEval :
  forall {e : BExp} {s : State} {b : bool},
    beval e s = b -> BEval e s b.
Proof.
  induction e; cbn; intros; subst; auto.
    constructor; apply aeval_AEval; reflexivity.
    constructor; apply aeval_AEval; reflexivity.
Qed.

Inductive CEval : Com -> State -> State -> Prop :=
    | EvalSkip :
        forall s : State, CEval Skip s s
    | EvalAsgn :
        forall (v : Loc) (a : AExp) (s : State) (n : nat),
          AEval a s n -> CEval (Asgn v a) s (changeState s v n)
    | EvalSeq :
        forall (c1 c2 : Com) (s1 s2 s3 : State),
          CEval c1 s1 s2 -> CEval c2 s2 s3 -> CEval (Seq c1 c2) s1 s3
    | EvalIfFalse :
        forall (b : BExp) (c1 c2 : Com) (s1 s2 : State),
          BEval b s1 false -> CEval c2 s1 s2 -> CEval (If b c1 c2) s1 s2
    | EvalIfTrue :
        forall (b : BExp) (c1 c2 : Com) (s1 s2 : State),
          BEval b s1 true -> CEval c1 s1 s2 -> CEval (If b c1 c2) s1 s2
    | EvalWhileFalse :
        forall (b : BExp) (c : Com) (s : State),
          BEval b s false -> CEval (While b c) s s
    | EvalWhileTrue :
        forall (b : BExp) (c : Com) (s1 s2 s3 : State),
          BEval b s1 true ->
          CEval c s1 s2 -> CEval (While b c) s2 s3 ->
            CEval (While b c) s1 s3.

Hint Constructors CEval.

Lemma CEval_det :
  forall (c : Com) (s s1 : State),
    CEval c s s1 -> forall s2 : State, CEval c s s2 -> s1 = s2.
Proof.
  induction 1; intros.
    inv H. reflexivity.
    inv H0. rewrite (AEval_det H H5). reflexivity.
    inv H1. specialize (IHCEval1 _ H4). subst.
      specialize (IHCEval2 _ H7). subst. reflexivity.
    inv H1.
      rewrite (IHCEval _ H8). reflexivity.
      pose (BEval_det H H7). congruence.
    inv H1.
      pose (BEval_det H H7). congruence.
      rewrite (IHCEval _ H8). reflexivity.
    inv H0.
      reflexivity.
      pose (BEval_det H H3). congruence.
    inv H2.
      pose (BEval_det H H7). congruence.
      specialize (IHCEval1 _ H6). subst.
        specialize (IHCEval2 _ H9). subst. reflexivity.
Defined.

Require Import Recdef.

Function ceval (n : nat) (c : Com) (s : State) : option State :=
match n with
    | 0 => None
    | S n' =>
        match c with
            | Skip => Some s
            | Asgn x a => Some (changeState s x (aeval a s))
            | Seq c1 c2 =>
                match ceval n' c1 s with
                    | None => None
                    | Some s' => ceval n' c2 s'
                end
            | If b c1 c2 =>
                if beval b s then ceval n' c1 s else ceval n' c2 s
            | While b c =>
                if beval b s
                then
                  match ceval n' c s with
                      | None => None
                      | Some s' => ceval n' (While b c) s'
                  end
                else Some s
        end
end.

Hint Immediate aeval_AEval beval_BEval.

Lemma ceval_CEval :
  forall (n : nat) (c : Com) (s1 s2 : State),
    ceval n c s1 = Some s2 -> CEval c s1 s2.
Proof.
  intros n c s1. functional induction ceval n c s1; intros; inv H; eauto.
Qed.

Lemma while_true_do_skip :
  forall s1 s2 : State,
    ~ CEval (While BTrue Skip) s1 s2.
Proof.
  intros s1 s2 H.
  remember (While BTrue Skip) as w. revert Heqw.
  induction H; intros; inv Heqw.
    inv H.
    apply IHCEval2. reflexivity.
Qed.

Definition equivalent (c1 c2 : Com) : Prop :=
  forall s1 s2 : State,
    CEval c1 s1 s2 <-> CEval c2 s1 s2.

Notation "c1 ~ c2" := (equivalent c1 c2) (at level 50).

Example equivalent_ex1 :
  forall (b : BExp) (c : Com),
    While b c ~ If b (Seq c (While b c)) Skip.
Proof.
  unfold equivalent. split; intros.
    remember (While b c) as w. revert b c Heqw.
      induction H; intros; inv Heqw; eauto.
    inv H; inv H6; eauto.
Defined.

(* Let's prove that ~ is a congruence. *)

Print Com.

Inductive Context : Type :=
    | CContext : Context
    | CSeqL : Context -> Com -> Context
    | CSeqR : Com -> Context -> Context
    | CIfL : BExp -> Context -> Com -> Context
    | CIfR : BExp -> Com -> Context -> Context
    | CWhile : BExp -> Context -> Context.

Fixpoint put (G : Context) (c : Com) : Com :=
match G with
    | CContext => c
    | CSeqL G' c' => Seq (put G' c) c'
    | CSeqR c' G' => Seq c' (put G' c)
    | CIfL b G' c' => If b (put G' c) c'
    | CIfR b c' G' => If b c' (put G' c)
    | CWhile b G' => While b (put G' c)
end.

Lemma equivalent_in_Context :
  forall c1 c2 : Com,
    c1 ~ c2 -> forall G : Context, put G c1 ~ put G c2.
Proof.
  intros c1 c2 H G. revert c1 c2 H.
  induction G; cbn; intros.
    assumption.
    all: unfold equivalent in *; split; intros.
      inv H0. econstructor.
        rewrite IHG; eauto. firstorder.
        assumption.
      inv H0. econstructor; rewrite 1?IHG; eauto.
      inv H0. econstructor; rewrite 1?IHG; eauto. firstorder.
      inv H0. econstructor; rewrite 1?IHG; eauto.
      inv H0.
        econstructor; rewrite 1?IHG; eauto.
        apply EvalIfTrue; eauto. rewrite IHG; eauto. firstorder.
      inv H0.
        econstructor; rewrite 1?IHG; eauto.
        apply EvalIfTrue; eauto. rewrite IHG; eauto.
      inv H0.
        econstructor; rewrite 1?IHG; eauto. firstorder.
        apply EvalIfTrue; eauto.
      inv H0.
        econstructor; rewrite 1?IHG; eauto.
        firstorder.
      remember (While b (put G c1)) as w. revert Heqw.
      induction H0; intro; inv Heqw.
        eauto.
        econstructor; eauto. rewrite IHG; eauto. firstorder.
      remember (While b (put G c2)) as w. revert Heqw.
      induction H0; intro; inv Heqw.
        eauto.
        econstructor; eauto. rewrite IHG; eauto.
Qed.

(* [equivalent is congruence] *)

Print Com.

Lemma equivalent_Seq_l :
  forall c c1 c2 : Com,
    c1 ~ c2 -> Seq c1 c ~ Seq c2 c.
Proof.
  unfold equivalent. split; intros.
    inv H0. econstructor.
      rewrite <- H. eassumption.
      assumption.
    inv H0. econstructor.
      rewrite H. eassumption.
      assumption.
Qed.

Lemma equivalent_Seq_r :
  forall c c1 c2 : Com,
    c1 ~ c2 -> Seq c c1 ~ Seq c c2.
Proof.
  unfold equivalent. split; intros.
    inv H0. econstructor.
      eassumption.
      rewrite <- H. eassumption.
    inv H0. econstructor.
      eassumption.
      rewrite H. eassumption.
Qed.

Lemma equivalent_If_l :
  forall (b : BExp) (c c1 c2 : Com),
    c1 ~ c2 -> If b c1 c ~ If b c2 c.
Proof.
  unfold equivalent. split; intros.
    inv H0.
      constructor; assumption.
      apply EvalIfTrue.
        assumption.
        rewrite <- H. assumption.
    inv H0.
      constructor; assumption.
      apply EvalIfTrue.
        assumption.
        rewrite H. assumption.
Qed.

Lemma equivalent_If_r :
  forall (b : BExp) (c c1 c2 : Com),
    c1 ~ c2 -> If b c c1 ~ If b c c2.
Proof.
  unfold equivalent. split; intros.
    inv H0.
      constructor.
        assumption.
        rewrite <- H. assumption.
      apply EvalIfTrue; assumption.
    inv H0.
      constructor.
        assumption.
        rewrite H. assumption.
      apply EvalIfTrue; assumption.
Qed.

Lemma equivalent_While :
  forall (b : BExp) (c c1 c2 : Com),
    c1 ~ c2 -> While b c1 ~ While b c2.
Proof.
  unfold equivalent. split; intros.
    remember (While b c1) as w. revert Heqw. induction H0; intro; inv Heqw.
      constructor. assumption.
      eapply EvalWhileTrue.
        assumption.
        rewrite <- H. eassumption.
        apply IHCEval2. reflexivity.
    remember (While b c2) as w. revert Heqw. induction H0; intro; inv Heqw.
      constructor. assumption.
      eapply EvalWhileTrue.
        assumption.
        rewrite H. eassumption.
        apply IHCEval2. reflexivity.
Qed.

Fixpoint loc (c : Com) : list Loc :=
match c with
    | Skip => []
    | Asgn v _ => [v]
    | Seq c1 c2 => loc c1 ++ loc c2
    | If _ c1 c2 => loc c1 ++ loc c2
    | While _ c => loc c
end.

Lemma CEval_not_In_eq :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 -> forall x : Loc, ~ In x (loc c) -> s1 x = s2 x.
Proof.
  induction 1; cbn; intros.
    reflexivity.
    unfold changeState. destruct (dec_spec v x).
      subst. contradiction H0. left. reflexivity.
      reflexivity.
    rewrite IHCEval1, IHCEval2.
      reflexivity.
      intro. apply H1. apply in_or_app. right. assumption.
      intro. apply H1. apply in_or_app. left. assumption.
    rewrite IHCEval.
      reflexivity.
      intro. apply H1. apply in_or_app. right. assumption.
    rewrite IHCEval.
      reflexivity.
      intro. apply H1. apply in_or_app. left. assumption.
    reflexivity.
    rewrite IHCEval1, IHCEval2.
      reflexivity.
      intro. apply H2. cbn in H3. assumption.
      assumption.
Qed.

(* TODO: division and errors, for loop *)

(* Zadania *)

Fixpoint loca (a : AExp) : list Loc :=
match a with
    | Const _ => []
    | Var x => [x]
    | Add a1 a2 => loca a1 ++ loca a2
    | Sub a1 a2 => loca a1 ++ loca a2
    | Mul a1 a2 => loca a1 ++ loca a2
end.

Lemma loca_same :
  forall (a : AExp) (s1 s2 : State) (n : nat),
    (forall x : Loc, In x (loca a) -> s1 x = s2 x) ->
      AEval a s1 n -> AEval a s2 n.
Proof.
  induction 2.
    constructor.
    rewrite H.
      constructor.
      cbn. left. reflexivity.
    constructor.
      apply IHAEval1. intros. apply H. cbn. apply in_or_app.
        left. assumption.
      apply IHAEval2. intros. apply H. cbn. apply in_or_app.
        right. assumption.
    constructor.
      apply IHAEval1. intros. apply H. cbn. apply in_or_app.
        left. assumption.
      apply IHAEval2. intros. apply H. cbn. apply in_or_app.
        right. assumption.
    constructor.
      apply IHAEval1. intros. apply H. cbn. apply in_or_app.
        left. assumption.
      apply IHAEval2. intros. apply H. cbn. apply in_or_app.
        right. assumption.
Qed.

Lemma loca_same' :
  forall (a : AExp) (s1 s2 : State) (n : nat),
    (forall x : Loc, In x (loca a) -> s1 x = s2 x) ->
      AEval a s1 n <-> AEval a s2 n.
Proof.
  split; intro.
    apply loca_same with s1; firstorder.
    apply loca_same with s2; firstorder.
Qed.

Print BExp.

Fixpoint locb (b : BExp) : list Loc :=
match b with
    | BTrue => []
    | BFalse => []
    | Eq a1 a2 => loca a1 ++ loca a2
    | Le a1 a2 => loca a1 ++ loca a2
    | Not b' => locb b'
    | And b1 b2 => locb b1 ++ locb b2
    | Or b1 b2 => locb b1 ++ locb b2
end.

Lemma locb_same :
  forall (e : BExp) (s1 s2 : State) (b : bool),
    (forall x : Loc, In x (locb e) -> s1 x = s2 x) ->
      BEval e s1 b -> BEval e s2 b.
Proof.
  induction 2.
    constructor.
    constructor.
    constructor.
      apply loca_same with s.
        intros. apply H. cbn. apply in_or_app. left. assumption.
        assumption.
      apply loca_same with s.
        intros. apply H. cbn. apply in_or_app. right. assumption.
        assumption.
    constructor.
      apply loca_same with s.
        intros. apply H. cbn. apply in_or_app. left. assumption.
        assumption.
      apply loca_same with s.
        intros. apply H. cbn. apply in_or_app. right. assumption.
        assumption.
    constructor. apply IHBEval. intros. apply H. cbn. assumption.
    constructor.
      apply IHBEval1. intros. apply H. cbn. apply in_or_app.
        left. assumption.
      apply IHBEval2. intros. apply H. cbn. apply in_or_app.
        right. assumption.
    constructor.
      apply IHBEval1. intros. apply H. cbn. apply in_or_app.
        left. assumption.
      apply IHBEval2. intros. apply H. cbn. apply in_or_app.
        right. assumption.
Qed.

Lemma loc_same :
  forall (c : Com) (s1 s1' s2 s2' : State),
    (forall x : Loc, In x (loc c) -> s1 x = s1' x) ->
      CEval c s1 s2 -> CEval c s1' s2' ->
        forall x : Loc, In x (loc c) -> s2 x = s2' x.
Proof.
  intros c s1 s1' s2 s2' H H1. revert s1' s2' H.
  induction H1; cbn; intros.
    inv H1.
    inv H1. assert (n = n0).
      assert (AEval a s1' n).
        apply loca_same with s.
          intros. apply H0. 
Abort.