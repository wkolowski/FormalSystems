From FormalSystems Require Export Imp.Syntax.

Fixpoint aeval (s : State) (a : AExp) : nat :=
match a with
    | AConst n => n
    | Var v => s v
    | ABinOp f a1 a2 => f (aeval s a1) (aeval s a2)
end.

Fixpoint beval (s : State) (e : BExp) : bool :=
match e with
    | BConst b => b
    | BRelOp f a1 a2 => f (aeval s a1) (aeval s a2)
    | Not e' => negb (beval s e')
    | BBinOp f e1 e2 => f (beval s e1) (beval s e2)
end.

Function ceval (n : nat) (c : Com) (s : State) : option State :=
match n with
    | 0 => None
    | S n' =>
        match c with
            | Skip => Some s
            | Asgn x a => Some (changeState s x (aeval s a))
            | Seq c1 c2 =>
                match ceval n' c1 s with
                    | None => None
                    | Some s' => ceval n' c2 s'
                end
            | If b c1 c2 =>
                if beval s b then ceval n' c1 s else ceval n' c2 s
            | While b c =>
                if beval s b
                then
                  match ceval n' c s with
                      | None => None
                      | Some s' => ceval n' (While b c) s'
                  end
                else Some s
        end
end.

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
      destruct (beval s1 b) eqn: Hb; eauto.
      destruct (beval s1 b) eqn: Hb; eauto.
        destruct (ceval n' c s1) eqn: Heq.
          erewrite IHn'; eauto.
          inv H.
Qed.

Lemma ceval_plus' :
  forall {n : nat} {c : Com} {s1 s2 : State},
    ceval n c s1 = Some s2 ->
      forall k : nat, ceval (k + n) c s1 = Some s2.
Proof.
  intros. rewrite plus_comm. apply ceval_plus. assumption.
Qed.