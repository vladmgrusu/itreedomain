From Stdlib Require Export Bool Arith NArith.

Lemma Nsucc_inj (x y : N) : (N.succ x =? N.succ y)%N = (x =? y)%N.
Proof.
destruct (x =? y)%N eqn: Heq.
- rewrite N.eqb_eq in Heq.
  subst y.
  apply N.eqb_refl.
- rewrite N.eqb_neq in Heq.
  rewrite N.eqb_neq.
  contradict Heq.
  apply N.succ_inj, Heq.
Qed.

Lemma Neqb2nat (x y : N) : (x =? y)%N = (N.to_nat x =? N.to_nat y).
Proof.
rewrite <- (N2Nat.id x) at 1.
rewrite <- (N2Nat.id y) at 1.
generalize (N.to_nat x), (N.to_nat y).
clear x y.
intro x.
induction x as [ | x IH]; intros [ | y].
- reflexivity.
- reflexivity.
- reflexivity.
- cbn [Nat.eqb].
  rewrite <- IH, Nat2N.inj_succ, Nat2N.inj_succ, Nsucc_inj.
  reflexivity.
Qed.

Lemma Nevenodd2nat (x : N) :
N.even x = Nat.even (N.to_nat x) /\ N.odd x = Nat.odd (N.to_nat x).
Proof.
rewrite <- (N2Nat.id x) at 1 3.
generalize (N.to_nat x).
clear x.
intro x.
induction x as [ | x [IHeven IHodd]]; [split; reflexivity | ].
rewrite Nat.even_succ, Nat.odd_succ, <- IHeven, <- IHodd, Nat2N.inj_succ,
 N.even_succ, N.odd_succ.
split; reflexivity.
Qed.

Lemma Neven2nat (x : N) : N.even x = Nat.even (N.to_nat x).
Proof.
apply Nevenodd2nat.
Qed.

Fixpoint pos_nb_zeros (p : positive) : nat :=
match p with
| xI _ => 0
| xO p' => 1 + pos_nb_zeros p'
| xH => 0
end.

Definition nb_zeros (n : N) : nat :=
match n with
| N0 => 0
| Npos p => pos_nb_zeros p
end.

Fixpoint pos_while_even_div2 (p : positive) : positive :=
match p with
| xI _ => p
| xO p' => pos_while_even_div2 p'
| 1%positive => 1
end.

Definition while_even_div2 (n : N) : N :=
match n with
| N0 => 0
| Npos p => Npos (pos_while_even_div2 p)
end.
