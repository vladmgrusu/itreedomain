From Prob Require Export Equiv.

Local Open Scope R_scope.

Definition fchoice
  (p : Bounded 0 1) [X : Type] (m1 m2 : itree_monad prob_effect X) :
itree_monad prob_effect X :=
do b <- fflip p; if b then m1 else m2.

Local Notation "m1 <| p |> m2" :=
  (@fchoice p _ m1 m2) (at level 50, m2 at next level, left associativity).
  
Program Fixpoint uniform [X : Type] (l : list X) (Hne : [] <> l) :
itree_monad prob_effect X :=
match l with
| [] => False_rect _ ltac:(congruence)
| x :: l' => match l' with
  | [] => ret _ x
  | _ :: l'' =>
    ret _ x <| {| bounded_val := / INR (length l) |} |>
    (@uniform _ l' ltac:(congruence))
  end
end.

Next Obligation.
intros X l Hne _ _ _ _ _ _.
assert (Hle : 1 <= INR (length l)).
{
  destruct l; [congruence | ].
  cbn [length].
  rewrite S_INR.
  assert (H := pos_INR (length l)).
  lra.
}
revert Hle.
generalize (length l).
clear.
intros n Hle.
split.
- apply Rlt_le, Rinv_0_lt_compat.
  lra.
- rewrite <- Rinv_1.
  apply Rinv_le_contravar; [exact Rlt_0_1 | exact Hle].
Qed.

Local Notation "m1 == m2" := (itree_equiv prob_effect prob_step m1 m2)
 (at level 70, m2 at next level, no associativity).

Lemma fchoice_0 [X : Type] (m1 m2 : itree_monad prob_effect X) :
fchoice pr_0 m1 m2 == m2.
Proof.
unfold fchoice.
rewrite equiv_fflip_0, ret_left.
reflexivity.
Qed.

Lemma fchoice_1 [X : Type] (m1 m2 : itree_monad prob_effect X) :
fchoice pr_1 m1 m2 == m1.
Proof.
unfold fchoice.
rewrite equiv_fflip_1, ret_left.
reflexivity.
Qed.

Lemma fchoice_comm
  [X : Type] (m1 m2 : itree_monad prob_effect X) (p : Bounded 0 1) :
fchoice (pr_opp p) m1 m2 == fchoice p m2 m1.
Proof.
unfold fchoice.
rewrite equiv_fflip_opp, bind_assoc.
setoid_rewrite (equiv_ret_left _ prob_step).
replace (do b <- fflip p; if negb b then m1 else m2)
 with (do b <- fflip p; if b then m2 else m1).
- apply itree_refl.
- f_equal.
  extensionality b.
  rewrite negb_if.
  reflexivity.
Qed.

Lemma fchoice_idempotent
  [X : Type] (m : itree_monad prob_effect X) (p : Bounded 0 1) :
fchoice p m m == m.
Proof.
unfold fchoice.
replace (do b <- fflip p; (if b then m else m)) with (fflip p;; m).
- apply equiv_fflip_ignored.
- f_equal.
  extensionality b.
  destruct b; reflexivity.
Qed.

Lemma fchoice_assoc
  [X : Type] (m1 m2 m3 : itree_monad prob_effect X) (p q r s : Bounded 0 1) :
p = pr_mult r s -> pr_opp s = pr_mult (pr_opp p) (pr_opp q) ->
fchoice p m1 (fchoice q m2 m3) == fchoice s (fchoice r m1 m2) m3.
Proof.
intros Hp Hs_.
unfold fchoice.
setoid_rewrite else_flip.
setoid_rewrite then_flip.
apply equiv_fflip_assoc; [exact Hp | exact Hs_].
Qed.

Lemma fchoice_bind
  [X Y : Type] (m1 m2 : itree_monad prob_effect X)
  (f : X -> itree_monad prob_effect Y) (p : Bounded 0 1) :
do x <- fchoice p m1 m2 ; f x ==
fchoice p (do x <- m1; f x) (do x <- m2; f x).
Proof.
unfold fchoice.
rewrite bind_assoc.
apply itree_bind_congr; [reflexivity | ].
intros [ | ]; reflexivity.
Qed.

(*
Lemma bind_fchoice
  [X Y : Type] (m : itree_monad prob_effect X)
  (f g : X -> itree_monad prob_effect Y) (p : Bounded 0 1) :
do x <- m; fchoice p (f x) (g x) ==
fchoice p (do x <- m; f x) (do x <- m; g x).
Proof.
unfold fchoice.
rewrite equiv_fflip_comm.
apply itree_bind_congr; [reflexivity | ].
intros [ | ]; reflexivity.
Qed.
*)
