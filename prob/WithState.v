From StateT Require Export Left.
From Prob Require Export Equiv.

Definition denote_prob_stateT_effect
  [S X Y : Type] (fy : prob_effect Y) (k : Y -> stateT_monad S prob_monad X) :
stateT_monad S prob_monad X :=
match fy in prob_effect Y
 return (Y -> stateT_monad S prob_monad X) -> stateT_monad S prob_monad X with
| Flip p => fun k => do b <- stateT_lift (flip p); k b
end k.

Lemma denote_prob_stateT_effect_bind
  [S X Y Z : Type] (fz : prob_effect Z)
  (m : Z -> stateT_monad S prob_monad X)
  (f : X -> stateT_monad S prob_monad Y) :
denote_prob_stateT_effect fz (fun z => do x <- m z; f x) =
do x <- denote_prob_stateT_effect fz m; f x.
Proof.
destruct fz.
cbn [denote_prob_stateT_effect].
rewrite bind_assoc.
reflexivity.
Qed.

Lemma denote_prob_stateT_effect_is_continuous
  [S X Y : Type] (fy : prob_effect Y) :
@is_continuous (EXP_DCPO _ _) _ (@denote_prob_stateT_effect S X _ fy).
Proof.
destruct fy.
unfold denote_prob_stateT_effect,stateT_lift,cont_ret.
remember (fun s : S =>
do x <- flip b;
ret prob_monad (x, s)) as h.
match goal with
| |- is_continuous ?ff => change ff with
(fun (k : bool ->
stateT_monad S prob_monad X) => (stateT_bind h k))
end.
apply bind_continuous_snd.
Qed.

Definition denote_prob_stateT (S : Type) [X : Type] (m : itree prob_effect X) :
stateT_monad S prob_monad X :=
denote_monad
  prob_effect (stateT_monad S prob_monad) (@denote_prob_stateT_effect S)
  (@denote_prob_stateT_effect_is_continuous S) X m.

Arguments denote_prob_stateT _ [_] _.

Lemma flip_stateT_ignored
  [S : Type] (p : Bounded 0 1) [X : Type] (m : stateT_monad S prob_monad X) :
stateT_lift (flip p);; m = m.
Proof.
extensionality s.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
lra.
Qed.

Lemma flip_stateT_0 (S : Type) :
stateT_lift (flip pr_0) = ret (stateT_monad S prob_monad) false.
Proof.
extensionality s.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
lra.
Qed.

Lemma flip_stateT_1 (S : Type) :
stateT_lift (flip pr_1) = ret (stateT_monad S prob_monad) true.
Proof.
extensionality s.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
lra.
Qed.

Lemma flip_stateT_opp (S : Type) (p : Bounded 0 1) :
stateT_lift (flip (pr_opp p)) =
do b <- stateT_lift (flip p); ret (stateT_monad S prob_monad) (negb b).
Proof.
extensionality s.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
lra.
Qed.

Lemma flip_stateT_assoc
  (p q r s : Bounded 0 1) [S X : Type]
  (m1 m2 m3 : stateT_monad S prob_monad X) :
p = pr_mult r s -> pr_opp s = pr_mult (pr_opp p) (pr_opp q) ->
do b <- stateT_lift (flip p);
do b' <- stateT_lift (flip q);
(if b then m1 else if b' then m2 else m3) =
do b <- stateT_lift (flip s);
do b' <- stateT_lift (flip r);
(if b then if b' then m1 else m2 else m3).
Proof.
intros Hp Hs_.
extensionality s'.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
assert (Hp' := f_equal (@bounded_val _ _) Hp).
assert (Hs_' := f_equal (@bounded_val _ _) Hs_).
clear Hp Hs_.
cbn in Hp', Hs_'.
assert (Heq : ((1 - p) * q = (1 - r) * s)%R) by lra.
generalize (fonc (m1 s') g), (fonc (m2 s') g), (fonc (m3 s') g).
cbn.
clear m1 m2 m3 g.
intros (x & Hx0 & Hx1) (y & Hy0 & Hy1) (z & Hz0 & Hz1).
cbn.
destruct
 p as (p & Hp0 & Hp1), q as (q & Hq0 & Hq1),
 r as (r & Hr0 & Hr1), s as (s & Hs0 & Hs1).
cbn in *.
nra.
Qed.

Lemma flip_flip_stateT_comm [S X : Type] (p q : Bounded 0 1)
  (f : bool -> bool -> stateT_monad S prob_monad X) :
do b <- stateT_lift (flip p); do b' <- stateT_lift (flip q); f b b' =
do b' <- stateT_lift (flip q); do b <- stateT_lift (flip p); f b b'.
Proof.
extensionality s.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
nra.
Qed.

(*
Lemma flip_stateT_comm [S X Y : Type] (p : Bounded 0 1)
  (m : stateT_monad S prob_monad X)
  (f : X -> bool -> stateT_monad S prob_monad Y) :
do x <- m; do b <- stateT_lift (flip p); f x b =
do b <- stateT_lift (flip p); do x <- m; f x b.
Proof.
extensionality s.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
Admtted.
*)

Lemma prob_stateT_step_correct
  (S : Type) [X : Type] (m1 m2 : itree prob_effect X) :
prob_step m1 m2 -> denote_prob_stateT S m1 = denote_prob_stateT S m2.
Proof.
intro Hstep.
destruct Hstep as [p X m | | | | p q r s X m1 m2 m3 Hp Hs_ | ].
- unfold denote_prob_stateT.
  rewrite denote_monad_fbind; [ | apply denote_prob_stateT_effect_bind].
  unfold fflip, trigger.
  rewrite denote_monad_impure.
  cbn [denote_prob_stateT_effect].
  etransitivity.
  {
    apply f_equal2; [ | reflexivity].
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret.
    reflexivity.
  }
  rewrite ret_right.
  apply flip_stateT_ignored.
- unfold denote_prob_stateT.
  unfold fflip, trigger.
  rewrite denote_monad_impure.
  cbn [denote_prob_stateT_effect].
  etransitivity.
  {
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret.
    reflexivity.
  }
  rewrite denote_monad_fret, ret_right.
  apply flip_stateT_0.
- unfold denote_prob_stateT.
  unfold fflip, trigger.
  rewrite denote_monad_impure.
  cbn [denote_prob_stateT_effect].
  etransitivity.
  {
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret.
    reflexivity.
  }
  rewrite denote_monad_fret, ret_right.
  apply flip_stateT_1.
- unfold denote_prob_stateT.
  unfold fflip, trigger.
  rewrite denote_monad_impure.
  cbn [denote_prob_stateT_effect].
  etransitivity.
  {
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret.
    reflexivity.
  }
  etransitivity.
  2:{
    symmetry.
    rewrite denote_monad_fbind; [ | apply denote_prob_stateT_effect_bind].
    rewrite denote_monad_impure.
    cbn [denote_prob_stateT_effect].
    rewrite bind_assoc.
    reflexivity.
  }
  etransitivity.
  2:{
    symmetry.
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret, ret_left, denote_monad_fret.
    reflexivity.
  }
  rewrite ret_right.
  apply flip_stateT_opp.
- unfold denote_prob_stateT.
  do 2 (rewrite denote_monad_fbind; [ | apply denote_prob_stateT_effect_bind]).
  unfold fflip, trigger.
  do 2 rewrite denote_monad_impure.
  cbn [denote_prob_stateT_effect].
  do 2 rewrite bind_assoc.
  etransitivity.
  {
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret, ret_left.
    rewrite denote_monad_fbind; [ | apply denote_prob_stateT_effect_bind].
    rewrite denote_monad_impure.
    cbn [denote_prob_stateT_effect].
    rewrite bind_assoc.
    reflexivity.
  }
  etransitivity.
  2:{
    symmetry.
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret, ret_left.
    rewrite denote_monad_fbind; [ | apply denote_prob_stateT_effect_bind].
    rewrite denote_monad_impure.
    cbn [denote_prob_stateT_effect].
    rewrite bind_assoc.
    reflexivity.
  }
  etransitivity.
  {
    apply f_equal.
    extensionality b1.
    etransitivity.
    {
      apply f_equal.
      extensionality b2.
      rewrite denote_monad_fret, ret_left, denote_monad_if, denote_monad_if.
      reflexivity.
    }
    reflexivity.
  }
  etransitivity.
  2:{
    symmetry.
    apply f_equal.
    extensionality b1.
    etransitivity.
    {
      apply f_equal.
      extensionality b2.
      rewrite denote_monad_fret, ret_left, denote_monad_if, denote_monad_if.
      reflexivity.
    }
    reflexivity.
  }
  apply flip_stateT_assoc; assumption.
- unfold denote_prob_stateT.
  do 2 (rewrite denote_monad_fbind; [ | apply denote_prob_stateT_effect_bind] ).
  etransitivity.
  {
    unfold fflip, trigger.
    rewrite denote_monad_impure.
    cbn [denote_prob_stateT_effect].
    rewrite bind_assoc.
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret, ret_left.
    rewrite denote_monad_fbind; [ | apply denote_prob_stateT_effect_bind].
    rewrite denote_monad_impure.
    cbn [denote_prob_stateT_effect].
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
    cbn [denote_prob_stateT_effect].
    rewrite bind_assoc.
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fret, ret_left.
    rewrite denote_monad_fbind; [ | apply denote_prob_stateT_effect_bind].
    rewrite denote_monad_impure.
    cbn [denote_prob_stateT_effect].
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
  apply flip_flip_stateT_comm.
(*
- unfold denote_prob_stateT.
  do 2 (rewrite denote_monad_fbind; [ | apply denote_prob_stateT_effect_bind]).
  unfold fflip, trigger.
  etransitivity.
  {
    apply f_equal.
    extensionality x.
    rewrite denote_monad_fbind; [ | apply denote_prob_stateT_effect_bind].
    rewrite denote_monad_impure.
    cbn [denote_prob_stateT_effect].
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
    apply f_equal2; [ | reflexivity].
    rewrite denote_monad_impure.
    cbn [denote_prob_stateT_effect].
    etransitivity.
    {
      apply f_equal.
      extensionality b.
      rewrite denote_monad_fret.
      reflexivity.
    }
    rewrite ret_right.
    reflexivity.
  }
  etransitivity.
  2:{
    symmetry.
    apply f_equal.
    extensionality b.
    rewrite denote_monad_fbind; [ | apply denote_prob_stateT_effect_bind].
    reflexivity.
  }
  apply flip_stateT_comm.
*)
Qed.

Lemma prob_stateT_equiv_correct
  (S : Type) [X : Type] (m1 m2 : itree prob_effect X) :
prob_equiv m1 m2 -> denote_prob_stateT S m1 = denote_prob_stateT S m2.
Proof.
apply itree_equiv_correct.
- apply denote_prob_stateT_effect_bind.
- apply prob_stateT_step_correct.
Qed.

Definition denote_probstate
  [S X : Type] (m : itree (stateT_effect S + prob_effect) X) :
stateT_monad S prob_monad X :=
denote_stateT_left
  prob_effect (@denote_prob_stateT_effect S) (@denote_prob_stateT_effect_bind S)
  (@denote_prob_stateT_effect_is_continuous S) m.

Local Notation "m1 == m2" :=
  (itree_equiv
    (stateT_effect _ + prob_effect) (coprod_step (stateT_step _) prob_equiv)
    m1 m2)
  (at level 70, m2 at next level, no associativity).

Lemma equiv_probstate_correct
  (S X : Type) (m1 m2 : itree (stateT_effect S + prob_effect) X) :
m1 == m2 -> denote_probstate m1 = denote_probstate m2.
Proof.
intro Hequiv.
eapply equiv_stateT_correct in Hequiv.
- exact Hequiv.
- clear.
  intros X m1 m2 Hequiv.
  apply prob_stateT_equiv_correct, Hequiv.
- clear.
  intros X Y [ | s] [p].
  + extensionality s.
    apply CONT_equal.
    extensionality f.
    apply bounded_equal.
    reflexivity.
  + extensionality s'.
    apply CONT_equal.
    extensionality f.
    apply bounded_equal.
    reflexivity.
Qed.

Definition probability
  (S X : Type) (E : X * S -> bool) (m : stateT_monad S prob_monad X) (s : S) :
Bounded 0 1 :=
fonc (m s) (fun x => if E x then pr_1 else pr_0).

Definition ffget {S : Type} : itree_monad (stateT_effect S + prob_effect) S :=
itree_in_left prob_effect fget.

Definition ffput [S : Type] (s : S) :
itree_monad (stateT_effect S + prob_effect) unit :=
itree_in_left prob_effect (fput s).

Definition ffflip (p : Bounded 0 1) :
itree_monad (stateT_effect nat + prob_effect) bool :=
itree_in_right (stateT_effect nat) (fflip p).

Lemma ffput_ffput [S : Type] (s s' : S) : ffput s;; ffput s' == ffput s'.
Proof.
unfold ffput.
rewrite <- itree_in_left_fbind.
apply equiv_left, fput_fput.
Qed.

Lemma ffput_ffget [S : Type] (s : S) : ffput s;; ffget == ffput s;; ret _ s.
Proof.
unfold ffput, ffget.
rewrite <- itree_in_left_fbind, equiv_fput_fget, itree_in_left_fbind,
 itree_in_left_fret.
reflexivity.
Qed.

Lemma ffput_ffflip
  [X : Type] (p : Bounded 0 1) (n : nat)
  (f : bool -> itree_monad (stateT_effect nat + prob_effect) X) :
ffput n;; do b <- ffflip p; f b == do b <- ffflip p; ffput n;; f b.
Proof.
apply equiv_swap.
Qed.

Lemma push_ffput_in_if{Y:Type}(p:Bounded 0 1):
forall (z:nat)
(m1 m2: itree_monad (stateT_effect nat + prob_effect) Y),
ffput z;; do y <- ffflip p; (if y then m1 else m2) ==
do y <- ffflip p; if y then (ffput z;; m1) else (ffput z;; m2).
Proof.
intros z m1 m2.
rewrite ffput_ffflip.
apply itree_bind_congr; [reflexivity | ].
intros [ | ]; reflexivity.
Qed.

Lemma push_fget_in_if{Y:Type}(p:Bounded 0 1):
forall
(m1 m2: itree_monad (stateT_effect _ + prob_effect) Y),
(do y <- ffflip p; if y then m1 else m2);; ffget ==
do y <- ffflip p; if y then m1;; ffget else  m2;; ffget.
Proof.
intros m1 m2.
rewrite bind_assoc.
apply itree_bind_congr; [reflexivity | ].
intros [ | ]; reflexivity.
Qed.

Lemma if_flip_cont
(p: Bounded 0 1)
(m1: EXP nat (itree (stateT_effect nat + prob_effect) nat) ->
  itree (stateT_effect nat + prob_effect) nat)
(m2:EXP nat (itree (stateT_effect nat + prob_effect) nat) ->
  itree (stateT_effect nat + prob_effect) nat):
 is_continuous (P1 := EXP_DCPO _ (itree _ _)) (P2 :=itree _ _) m1 -> 
 is_continuous (P1 := EXP_DCPO _ (itree _ _)) (P2 :=itree _ _) m2 ->
 is_continuous (P1 := EXP_DCPO _ (itree _ _)) (P2 := itree _ _)
  (fun a => do b <- ffflip p; (if b then m1 a else m2 a)).
Proof.
intros Hc1 Hc2.
remember (fun a (b:bool) =>
if b
then m1 a
else m2 a) as h.
match goal with
| |- is_continuous ?ff =>
replace  ff with (
((fbind (ffflip p)) °h)) by (now subst)
end.
remember (fbind (ffflip p)) as g.
apply (comp_is_continuous 
(P1 := (EXP_DCPO _ (itree _ _))) (P2 := (EXP_DCPO _ (itree _ _)))
(P3 := itree _ _ )).
-
 subst g.
 apply fbind_is_continuous_snd.
-
 subst h.
 now apply if_continuous.
Qed.  
