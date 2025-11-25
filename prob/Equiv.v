From Itree Require Export Equiv.
From Prob Require Export Itree.

Local Open Scope R_scope.

Inductive prob_step :
  forall [X], itree prob_effect X -> itree prob_effect X -> Prop :=
| fflip_ignored : forall p [X] (m : itree_monad prob_effect X),
  prob_step (fflip p;; m) m
| fflip_0 : prob_step (fflip pr_0) (ret (itree_monad prob_effect) false)
| fflip_1 : prob_step (fflip pr_1) (ret (itree_monad prob_effect) true)
| fflip_opp : forall p,
  prob_step (fflip (pr_opp p)) (do b <- fflip p; ret _ (negb b))
| fflip_assoc :
  forall p q r s [X]
    (m1 m2 m3 : itree_monad prob_effect X),
  p = pr_mult r s -> pr_opp s = pr_mult (pr_opp p) (pr_opp q) ->
  prob_step
    (do b <- fflip p; do b' <- fflip q;
     if b then m1 else if b' then m2 else m3)
    (do b <- fflip s; do b' <- fflip r;
     if b then if b' then m1 else m2 else m3)
| fflip_comm : forall [X] p q
   (f : bool -> bool -> itree_monad prob_effect X),
  prob_step
    (do b <- fflip p; do b' <- fflip q; f b b')
    (do b' <- fflip q; do b <- fflip p; f b b').
(*
| fflip_comm : forall [X Y]
   (m : itree_monad prob_effect X) p
   (f : X -> bool -> itree_monad prob_effect Y),
  prob_step
    (do x <- m; do b <- fflip p; f x b) (do b <- fflip p; do x <- m; f x b).
*)

Definition prob_equiv [X : Type] (m1 m2 : itree prob_effect X) : Prop :=
itree_equiv prob_effect prob_step m1 m2.

Local Notation "m1 == m2" := (itree_equiv prob_effect prob_step m1 m2)
 (at level 70, m2 at next level, no associativity).

Lemma equiv_fflip_ignored
  (p : Bounded 0 1) [X : Type] (m : itree_monad prob_effect X) :
fflip p;; m == m.
Proof.
apply itree_step, fflip_ignored.
Qed.

Lemma then_flip
  (p : Bounded 0 1) [X : Type] (b : bool)
  (m : itree_monad prob_effect X) (f : bool -> itree_monad prob_effect X) :
(if b then  do b' <- fflip p; f b' else m) ==
do b' <- fflip p; if b then f b' else m.
Proof.
destruct b; [reflexivity | ].
rewrite equiv_fflip_ignored.
reflexivity.
Qed.

Lemma else_flip
  (p : Bounded 0 1) [X : Type] (b : bool)
  (m : itree_monad prob_effect X) (f : bool -> itree_monad prob_effect X) :
(if b then m else do b' <- fflip p; f b') ==
do b' <- fflip p; if b then m else f b'.
Proof.
destruct b; [ | reflexivity].
rewrite equiv_fflip_ignored.
reflexivity.
Qed.

Lemma equiv_fflip_0 : fflip pr_0 == ret (itree_monad prob_effect) false.
Proof.
apply itree_step, fflip_0.
Qed.

Lemma equiv_fflip_1 : fflip pr_1 == ret (itree_monad prob_effect) true.
Proof.
apply itree_step, fflip_1.
Qed.

Lemma equiv_fflip_opp (p : Bounded 0 1) :
fflip (pr_opp p) == do b <- fflip p; ret _ (negb b).
Proof.
apply itree_step, fflip_opp.
Qed.

Lemma equiv_fflip_opp_rev (p : Bounded 0 1) :
fflip p == do b <- fflip (pr_opp p); ret _ (negb b).
Proof.
rewrite equiv_fflip_opp, bind_assoc.
setoid_rewrite (equiv_ret_left _ prob_step).
setoid_rewrite <- equiv_ret_right at 1.
apply itree_bind_congr; [reflexivity | ].
intro b.
rewrite negb_involutive.
apply itree_refl.
Qed.

Lemma equiv_fflip_assoc
  (p q r s : Bounded 0 1) [X : Type] (m1 m2 m3 : itree_monad prob_effect X) :
p = pr_mult r s -> pr_opp s = pr_mult (pr_opp p) (pr_opp q) ->
do b <- fflip p; do b' <- fflip q; (if b then m1 else if b' then m2 else m3) ==
do b <- fflip s; do b' <- fflip r; (if b then if b' then m1 else m2 else m3).
Proof.
intros; apply itree_step, fflip_assoc; assumption.
Qed.

Lemma equiv_fflip_comm
  [X : Type]
  (m : itree_monad prob_effect X) (p q : Bounded 0 1)
  (f : bool -> bool -> itree_monad prob_effect X) :
  (do b <- fflip p; do b' <- fflip q; f b b') ==
  (do b' <- fflip q; do b <- fflip p; f b b').
Proof.
intros; apply itree_step, fflip_comm.
Qed.

(*
Lemma equiv_fflip_and (p q : Bounded 0 1) :
do b1 <- fflip p; do b2 <- fflip q; ret _ (b1 && b2) == fflip (pr_mult p q).
Proof.
apply itree_step, fflip_and.
Qed.

Lemma equiv_fflip_or (p q : Bounded 0 1) :
do b1 <- fflip p; do b2 <- fflip q; ret _ (b1 || b2) == fflip (pr_or p q).
Proof.
apply itree_step, fflip_or.
Qed.
*)

Lemma prob_step_correct (X : Type) (m1 m2 : itree prob_effect X) :
prob_step m1 m2 -> denote_prob m1 = denote_prob m2.
Proof.
intro Hstep.
destruct Hstep as [ | | | | p q r s X m1 m2 m3 Hp Hs_ | ].
- unfold denote_prob at 1.
  unfold fflip, trigger.
  rewrite denote_monad_fbind; [ | apply denote_prob_effect_bind].
  rewrite denote_monad_impure.
  cbn [denote_prob_effect].
  etransitivity.
  {
    apply f_equal2; [ | reflexivity].
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret.
    reflexivity.
  }
  rewrite ret_right, flip_ignored.
  reflexivity.
- unfold denote_prob at 1.
  unfold fflip, trigger.
  rewrite denote_monad_impure.
  cbn [denote_prob_effect].
  rewrite flip_0, ret_left.
  reflexivity.
- unfold denote_prob at 1.
  unfold fflip, trigger.
  rewrite denote_monad_impure.
  cbn [denote_prob_effect].
  rewrite flip_1, ret_left.
  reflexivity.
- unfold denote_prob.
  unfold fflip, trigger.
  rewrite denote_monad_impure.
  cbn [denote_prob_effect].
  rewrite flip_opp, bind_assoc.
  etransitivity.
  {
    apply f_equal.
    extensionality b.
    rewrite ret_left, denote_monad_fret.
    reflexivity.
  }
  rewrite denote_monad_fbind; [ | apply denote_prob_effect_bind].
  rewrite denote_monad_impure.
  cbn [denote_prob_effect].
  rewrite bind_assoc.
  etransitivity.
  2:{
    symmetry.
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret, ret_left, denote_monad_fret.
    reflexivity.
  }
  reflexivity.
- unfold denote_prob.
  unfold fflip, trigger.
  rewrite denote_monad_fbind; [ | apply denote_prob_effect_bind].
  rewrite denote_monad_impure.
  cbn [denote_prob_effect].
  rewrite bind_assoc.
  etransitivity.
  {
    apply f_equal2; [reflexivity | ].
    extensionality b.
    rewrite denote_monad_fret, ret_left.
    rewrite denote_monad_fbind; [ | apply denote_prob_effect_bind].
    rewrite denote_monad_impure.
    cbn [denote_prob_effect].
    rewrite bind_assoc.
    etransitivity.
    {
      apply f_equal2; [reflexivity | ].
      extensionality b'.
      rewrite denote_monad_fret, ret_left, denote_monad_if, denote_monad_if.
      reflexivity.
    }
    reflexivity.
  }
  rewrite denote_monad_fbind; [ | apply denote_prob_effect_bind].
  rewrite denote_monad_impure.
  cbn [denote_prob_effect].
  rewrite bind_assoc.
  etransitivity.
  2:{
    symmetry.
    apply f_equal2; [reflexivity | ].
    extensionality b.
    rewrite denote_monad_fret, ret_left.
    rewrite denote_monad_fbind; [ | apply denote_prob_effect_bind].
    rewrite denote_monad_impure.
    cbn [denote_prob_effect].
    rewrite bind_assoc.
    etransitivity.
    {
      apply f_equal2; [reflexivity | ].
      extensionality b'.
      rewrite denote_monad_fret, ret_left, denote_monad_if, denote_monad_if.
      reflexivity.
    }
    reflexivity.
  }
  apply flip_assoc; [exact Hp | exact Hs_].
- unfold denote_prob.
  do 2 (rewrite denote_monad_fbind; [ | apply denote_prob_effect_bind] ).
  etransitivity.
  {
    unfold fflip, trigger.
    rewrite denote_monad_impure.
    cbn [denote_prob_effect].
    rewrite bind_assoc.
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret, ret_left.
    rewrite denote_monad_fbind; [ | apply denote_prob_effect_bind].
    rewrite denote_monad_impure.
    cbn [denote_prob_effect].
    rewrite bind_assoc.
    etransitivity.
    {
      apply f_equal.
      extensionality b'.
      rewrite denote_monad_fret, ret_left.
      reflexivity.
    }
    reflexivity.
  }
  etransitivity.
  2:{
    symmetry.
    unfold fflip, trigger.
    rewrite denote_monad_impure.
    cbn [denote_prob_effect].
    rewrite bind_assoc.
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret, ret_left.
    rewrite denote_monad_fbind; [ | apply denote_prob_effect_bind].
    rewrite denote_monad_impure.
    cbn [denote_prob_effect].
    rewrite bind_assoc.
    etransitivity.
    {
      apply f_equal.
      extensionality b'.
      rewrite denote_monad_fret, ret_left.
      reflexivity.
    }
    reflexivity.
  }
  apply flip_flip_comm.
(*
- unfold denote_prob.
  do 2 (rewrite denote_monad_fbind; [ | apply denote_prob_effect_bind] ).
  etransitivity.
  {
    apply f_equal.
    extensionality x.
    rewrite denote_monad_fbind; [ | apply denote_prob_effect_bind].
    unfold fflip, trigger.
    rewrite denote_monad_impure.
    cbn [denote_prob_effect].
    rewrite bind_assoc.
    etransitivity.
    {
      apply f_equal.
      extensionality b.
      rewrite denote_monad_fret, ret_left.
      reflexivity.
    }
    reflexivity.
  }
  etransitivity.
  2:{
    symmetry.
    unfold fflip, trigger.
    rewrite denote_monad_impure.
    cbn [denote_prob_effect].
    rewrite bind_assoc.
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret, ret_left.
    rewrite denote_monad_fbind; [ | apply denote_prob_effect_bind].
    reflexivity.
  }
  apply flip_comm.
*)
Qed.

Lemma prob_equiv_correct (X : Type) (m1 m2 : itree prob_effect X) :
m1 == m2 -> denote_prob m1 = denote_prob m2.
Proof.
apply itree_equiv_correct.
- apply denote_prob_effect_bind.
- apply prob_step_correct.
Qed.
