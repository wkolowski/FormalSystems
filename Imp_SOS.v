(** * Structural operational semantics for IMP *)

Require Import List.
Import ListNotations.

Require Import Bool.

Parameter Loc : Type.
Parameter dec : Loc -> Loc -> bool.
Parameter dec_spec :
  forall x y : Loc, reflect (x = y) (dec x y).

Require Import Arith.

Notation "x =? y" := (dec x y) (at level 70).

Ltac inv H :=
  inversion H; subst; clear H.

Inductive AExp : Type :=
    | Var : Loc -> AExp
    | Const : nat -> AExp
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

Inductive AEval (s : State) : AExp -> AExp -> Prop :=
    | EvalVar :
        forall x : Loc, AEval s (Var x) (Const (s x))
(*    | EvalConst :
        forall n : nat, AEval s (Const n) (Const n)*)
    | EvalAddL :
        forall a1 a1' a2 : AExp,
          AEval s a1 a1' -> AEval s (Add a1 a2) (Add a1' a2)
    | EvalAddR :
        forall (n : nat) (a2 a2' : AExp),
          AEval s a2 a2' -> AEval s (Add (Const n) a2) (Add (Const n) a2')
    | EvalAdd :
        forall (a1 a2 : AExp) (n1 n2 : nat),
          AEval s (Add (Const n1) (Const n2)) (Const (n1 + n2))
    | EvalSubL :
        forall a1 a1' a2 : AExp,
          AEval s a1 a1' -> AEval s (Sub a1 a2) (Sub a1' a2)
    | EvalSubR :
        forall (n : nat) (a2 a2' : AExp),
          AEval s a2 a2' -> AEval s (Sub (Const n) a2) (Sub (Const n) a2')
    | EvalSub :
        forall (a1 a2 : AExp) (n1 n2 : nat),
          AEval s (Sub (Const n1) (Const n2)) (Const (n1 - n2))
    | EvalMulL :
        forall a1 a1' a2 : AExp,
          AEval s a1 a1' -> AEval s (Mul a1 a2) (Mul a1' a2)
    | EvalMulR :
        forall (n : nat) (a2 a2' : AExp),
          AEval s a2 a2' -> AEval s (Mul (Const n) a2) (Mul (Const n) a2')
    | EvalMul :
        forall (a1 a2 : AExp) (n1 n2 : nat),
          AEval s (Mul (Const n1) (Const n2)) (Const (n1 * n2)).

Hint Constructors AEval.

Fixpoint aeval (s : State) (a : AExp) : nat :=
match a with
    | Const n => n
    | Var v => s v
    | Add a1 a2 => aeval s a1 + aeval s a2
    | Sub a1 a2 => aeval s a1 - aeval s a2
    | Mul a1 a2 => aeval s a1 * aeval s a2
end.

Lemma AEval_aeval :
  forall {s : State} {a1 a2 : AExp},
    AEval s a1 a2 -> aeval s a1 = aeval s a2.
Proof.
  induction 1; cbn; auto.
Qed.

Lemma AEval_det :
  forall {s : State} {a a1 a2 : AExp},
    AEval s a a1 -> AEval s a a2 -> a1 = a2.
Proof.
  intros s a a1 a2 H. revert a2.
  induction H; intros; repeat
  match goal with
      | H : AEval _ (?f _) _ |- _ => inv H
      | |- ?f _ _ = ?f _ _ => f_equal
  end; auto.
Qed.

(*
Fixpoint loca (a : AExp) : list Loc :=
match a with
    | Const _ => []
    | Var x => [x]
    | Add a1 a2 => loca a1 ++ loca a2
    | Sub a1 a2 => loca a1 ++ loca a2
    | Mul a1 a2 => loca a1 ++ loca a2
end.

Definition acompatible (a : AExp) (s1 s2 : State) : Prop :=
  forall x : Loc, In x (loca a) -> s1 x = s2 x.


Lemma AEval_acompatible :
  forall {a : AExp} {s1 : State} {n : nat},
    AEval s1 a n -> forall {s2 : State},
      acompatible a s1 s2 ->
        AEval s2 a n.
Proof.
  Hint Resolve in_or_app.
  unfold acompatible.
  induction 1; cbn in *; intros; try rewrite H; auto 6.
Qed.

Lemma AEval_acompatible_det :
  forall {a : AExp} {s1 : State} {n1 : nat},
    AEval a s1 n1 ->
    forall {s2 : State} {n2 : nat},
      AEval a s2 n2 ->
      (forall x : Loc, In x (loca a) -> s1 x = s2 x) ->
        n1 = n2.
Proof.
  induction 1; cbn; intros; auto.
    inv H. reflexivity.
    inv H. apply H0. left. reflexivity.
    inv H1. erewrite IHAEval1, IHAEval2; eauto.
    inv H1. erewrite IHAEval1, IHAEval2; eauto.
    inv H1. erewrite IHAEval1, IHAEval2; eauto.
Qed.
*)

Print BExp.

(* TODO

Inductive BEval (s : State) : BExp -> BExp -> Prop :=
    | EvalEqL :
        forall a1 a1' a2 : AExp,
          AEval s a1 a1' -> BEval s (Eq a1 a2) (Eq a1' a2)
    | EvalEqR :
        forall (a1 a2 a2' : AExp) (n : nat),
          BEval s (Eq (Const n) a2) (Eq (Const n) a2')
    | EvalEq :
        forall n1 n2 : nat,
          BEval s (Eq (Const n1) (Const n2))
                  (if Nat.eqb n1 n2 then BTrue else BFalse)
    | EvalLeL :
        forall a1 a1' a2 : AExp,
          AEval s a1 a1' -> BEval s (Le a1 a2) (Le a1' a2)
    | EvalLeR :
        forall (a1 a2 a2' : AExp) (n : nat),
          BEval s (Eq (Const n) a2) (Eq (Const n) a2')
    | EvalEq :
        forall n1 n2 : nat,
          BEval s (Eq (Const n1) (Const n2))
                  (if Nat.eqb n1 n2 then BTrue else BFalse)
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
Restart.
  intros.
  apply BEval_beval in H.
  apply BEval_beval in H0.
  rewrite <- H, <- H0.
  reflexivity.
Qed.

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

Definition bcompatible (b : BExp) (s1 s2 : State) : Prop :=
  forall x : Loc, In x (locb b) -> s1 x = s2 x.

Lemma BEval_bcompatible :
  forall {e : BExp} {s1 : State} {b : bool},
    BEval e s1 b -> forall {s2 : State},
      bcompatible e s1 s2 -> BEval e s2 b.
Proof.
  Hint Resolve AEval_acompatible.
  Hint Unfold acompatible.
  unfold bcompatible.
  induction 1; cbn in *; intros; constructor; eauto 6.
Qed.

Lemma BEval_bcompatible_det :
  forall {e : BExp} {s1 : State} {b1 : bool},
    BEval e s1 b1 -> forall {s2 : State} {b2 : bool},
    BEval e s2 b2 ->
      bcompatible e s1 s2 -> b1 = b2.
Proof.
  intros.
  assert (BEval e s2 b1).
    eapply BEval_bcompatible; eauto.
  eapply BEval_det; eauto.
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
Restart.
  Hint Rewrite @AEval_det.
  Hint Resolve AEval_det BEval_det.
  induction 1; intros.
  Ltac wut :=
  match goal with
      | H : CEval ?c _ _ |- _ => is_var c + inv H
  end;
  repeat match goal with
      | IH : forall _, CEval _ _ _ -> _, H : CEval _ _ _ |- _ =>
          let H' := fresh "H" in
            assert (H' := IH _ H); clear H; rename H' into H; subst
      | H : BEval ?b ?s _, H' : BEval ?b ?s _ |- _ =>
          let H'' := fresh "H" in
            assert (H'' := BEval_det H H'); clear H H'
  end; eauto; try congruence.
  all: wut.
Qed.

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

Lemma ceval_plus :
  forall (n k : nat) (c : Com) (s1 s2 : State),
    ceval n c s1 = Some s2 -> ceval (n + k) c s1 = Some s2.
Proof.
  induction n as [| n']; cbn; intros.
    inv H.
    destruct c; auto.
      destruct (ceval n' c1 s1) eqn: Heq.
        erewrite IHn'; eauto.
        inv H.
      destruct (beval b s1) eqn: Hb; eauto.
      destruct (beval b s1) eqn: Hb; eauto.
        destruct (ceval n' c s1) eqn: Heq.
          erewrite IHn'; eauto.
          inv H.
Qed.

Lemma CEval_ceval :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 -> exists n : nat, ceval n c s1 = Some s2.
Proof.
  induction 1.
    exists 1. cbn. reflexivity.
    exists 1. cbn. do 2 f_equal. apply AEval_aeval. assumption.
    destruct IHCEval1 as [n1 IH1], IHCEval2 as [n2 IH2].
      exists (S (n1 + n2)). (* Should be S (max n1 n2) *)
      cbn. rewrite (ceval_plus n1 n2 _ _ _ IH1), plus_comm.
        apply ceval_plus. assumption.
    destruct IHCEval as [n IH]. exists (S n). cbn.
      apply BEval_beval in H. rewrite H. assumption.
    destruct IHCEval as [n IH]. exists (S n). cbn.
      apply BEval_beval in H. rewrite H. assumption.
    exists 1. cbn. apply BEval_beval in H. rewrite H. reflexivity.
    destruct IHCEval1 as [n1 IH1], IHCEval2 as [n2 IH2].
      exists (S (n1 + n2)). cbn. (* Should be S (max n1 n2) *)
      apply BEval_beval in H. rewrite H.
      rewrite (ceval_plus _ _ _ _ _ IH1), plus_comm.
      apply ceval_plus. assumption.
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

(* The list of all variables which are assigned to by the instruction c. *)
Fixpoint locw (c : Com) : list Loc :=
match c with
    | Skip => []
    | Asgn v _ => [v]
    | Seq c1 c2 => locw c1 ++ locw c2
    | If _ c1 c2 => locw c1 ++ locw c2
    | While _ c => locw c
end.

Definition wcompatible (c : Com) (s1 s2 : State) : Prop :=
  forall x : Loc, In x (locw c) -> s1 x = s2 x.

Lemma CEval_not_In_locw_eq :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 -> forall x : Loc, ~ In x (locw c) -> s1 x = s2 x.
Proof.
  induction 1; cbn in *; intros; auto.
    unfold changeState. destruct (dec_spec v x).
      subst. contradiction H0. left. reflexivity.
      reflexivity.
    all: rewrite ?IHCEval, ?IHCEval1, ?IHCEval2; auto.
Qed.

(* The list of all variables mentioned in c. *)
Fixpoint loc (c : Com) : list Loc :=
match c with
    | Skip => []
    | Asgn v a => v :: loca a
    | Seq c1 c2 => loc c1 ++ loc c2
    | If b c1 c2 => locb b ++ loc c1 ++ loc c2
    | While b c => locb b ++ loc c
end.

Definition ccompatible (c : Com) (s1 s2 : State) : Prop :=
  forall x : Loc, In x (loc c) -> s1 x = s2 x.

Lemma CEval_not_In_loc_eq :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 -> forall x : Loc, ~ In x (loc c) -> s1 x = s2 x.
Proof.
  induction 1; cbn in *; intros; auto.
    unfold changeState. destruct (dec_spec v x).
      subst. contradiction H0. left. reflexivity.
      reflexivity.
    all: rewrite ?IHCEval, ?IHCEval1, ?IHCEval2; auto 7.
Qed.

Lemma CEval_ccompatible :
  forall (c : Com) (s1 s2 : State),
    CEval c s1 s2 ->
    forall {s1' s2' : State},
      CEval c s1' s2' ->
        ccompatible c s1 s1' -> ccompatible c s2 s2'.
Proof.
  unfold ccompatible.
  Hint Unfold bcompatible.
  induction 1; cbn; intros.
    inv H1.
    inv H0. unfold changeState. inv H2.
      destruct (dec_spec x x).
        eapply AEval_acompatible_det; eauto.
        contradiction.
      destruct (dec_spec v x).
        eapply AEval_acompatible_det; eauto.
        auto.
    Focus 4. inv H0.
      apply H1. assumption.
      assert (false = true).
        eapply BEval_bcompatible_det; eauto. congruence.
(* If *)
(*
    Focus 2. inv H1.
      eapply IHCEval; eauto 6.
*)
(* Seq *)
(*
    inv H1. apply in_app_or in H3. destruct H3.
      assert (In x (loc c2) \/ ~ In x (loc c2)).
        admit.
        destruct H3.
          assert (ccompatible c1 s2 s4).
            red. intros. eapply IHCEval1; eauto.
            red in H4. eapply IHCEval2; eauto. intros.
              apply H4. assumption.
*)
(* While *)
(*
    Focus 4. inv H2; cbn in *.
      assert (false = true); try congruence.
        eapply BEval_bcompatible_det; eauto. unfold bcompatible.
          intros. symmetry. auto.
      assert (s1 x = s1' x).
        apply H3. assumption.
        assert (s3 x = s2' x).
          eapply IHCEval2; eauto. intros. apply in_app_or in H5. inv H5.
*)
Abort.

(* Program equivalence. *)

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

(* TODO: for loop *)

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
Restart.
  intros c1 c2 H G. revert c1 c2 H.
  induction G; cbn; intros; eauto;
  unfold equivalent in *; split; intros;
  match goal with
      | H : CEval ?c _ _ |- _ =>
          let c' := fresh "c" in
          let Heqc' := fresh "Heq" c' in
            remember c as c'; revert Heqc';
            induction H; intros; inv Heqc'
  end; eauto.
    5-6: apply EvalIfTrue; rewrite 1?IHG; eauto; firstorder.
    all: econstructor; rewrite 1?IHG; eauto; firstorder.
Qed.

(** [equivalent] is a congruence *)

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

(** * Observational equivalence *)

Definition Observation (A : Type) : Type := Com -> A.

Definition oequiv {A : Type} (c1 c2 : Com) : Prop :=
  forall (G : Context) (f : Observation A),
    f (put G c1) = f (put G c2).
*)