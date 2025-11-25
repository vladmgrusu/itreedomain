From Prob Require Export Equiv.

Local Open Scope R_scope.

Example fflip_while_true (p : Bounded 0 1) : itree_monad prob_effect unit :=
While fflip p {{
  ret _ tt
}}.

Example fflip_while_false (p : Bounded 0 1) : itree_monad prob_effect unit :=
While do b <- fflip (pr_opp p); ret _ (negb b) {{
  ret _ tt
}}.

Local Notation "m1 == m2" :=
  (itree_equiv prob_effect prob_step m1 m2)
  (at level 70, m2 at next level, no associativity).

Lemma fflip_while_false_true_equiv (p : Bounded 0 1) :
fflip_while_false p == fflip_while_true p.
Proof.
unfold fflip_while_true, fflip_while_false.
apply itree_while_congr; [ | reflexivity].
rewrite equiv_fflip_opp, bind_assoc.
setoid_rewrite (equiv_ret_left _ prob_step).
etransitivity.
{
  apply itree_bind_congr; [reflexivity | ].
  intro b.
  rewrite negb_involutive.
  reflexivity.
}
apply equiv_ret_right.
Qed.
(**
Lemma fflip_while_true_equiv_ret (p : Bounded 0 1) :
p < 1 -> fflip_while_true p == ret (itree_monad prob_effect) tt.
Proof.
intro Hp.
Abort.


Lemma fflip_while_false_terminates (p : Bounded 0 1) :
p < 1 -> fflip_while_false p == ret (itree_monad prob_effect) tt.
Proof.
intro Hlt.
rewrite fflip_while_false_true_equiv.
apply fflip_while_true_terminates, Hlt.
Qed.
*)

Example flip_while_true (p : Bounded 0 1) : prob_monad unit :=
While flip p {{
  ret _ tt
}}.

Lemma flip_while_true_prob (p : Bounded 0 1) :
p < 1 -> probability (fun t => true) (flip_while_true p) = pr_1.
Proof.
intro Hlt.
apply bounded_equal.
cbn -[while].
assert (Heq :
  p * probability (fun _ => true) (flip_while_true p) + (1 - p) =
  probability (fun _ => true) (flip_while_true p)
).
{
  unfold flip_while_true at 2.
  rewrite while_fixpoint.
  fold (flip_while_true p).
  cbn -[while].
  fold (probability (fun _ => true) (flip_while_true p)).
  lra.
}
nra.
Qed.
