From Prob Require Export WithState.

Program Example fflip_incr_while_true (p : Bounded 0 1) :
itree_monad (stateT_effect nat + prob_effect) nat :=
ffput 0 ;;
While ffflip p {{
  do n <- ffget;
  ffput (S n)
}} ;;
ffget.

Definition geomF
  (p : Bounded 0 1) (rec : nat -> itree (stateT_effect nat + prob_effect) nat) :
nat -> itree (stateT_effect nat + prob_effect) nat :=
fun n =>
  do b <- ffflip p;
  if b then
    do dummy <- ffget;
    ffput (S dummy);;
    rec (1 + n)%nat
  else ret _ n.

Lemma geomF_is_monotonic (p : Bounded 0 1) :
@is_monotonic (EXP_Poset _ (itree _ _)) (EXP_Poset _ (itree _ _)) (geomF p).
Proof.
intros u v Hle.
unfold geomF.
cbn in *.
intro d.
specialize (@fbind_is_continuous_snd 
(stateT_effect nat + prob_effect) bool nat  (ffflip p)
) as Hcs.
apply continuous_implies_monotonic in Hcs.
apply Hcs.
intro b.
destruct b; auto.
-
 specialize (@fbind_is_continuous_snd 
(stateT_effect nat + prob_effect) _ nat ffget
) as Hcs'.
 apply continuous_implies_monotonic in Hcs'.
 apply Hcs'.
 intro d'.

specialize (@fbind_is_continuous_snd 
(stateT_effect nat + prob_effect) _ nat (ffput (S d')))
as Hcs''. 
apply continuous_implies_monotonic in Hcs''.
apply Hcs''.
intros [].
apply Hle.
- 
apply refl.
Qed.

Lemma geomF_is_monotonic_aux
(p: Bounded 0 1)
(n:nat):
is_monotonic 
 (P1 := (EXP_Poset _ (itree _ _))) (P2 := itree _ _)
(fun
     a : EXP nat
           (itree (stateT_effect nat + prob_effect) nat) =>
   do b <- ffflip p;
   (if b
    then do dummy <- ffget; ffput (S dummy);; a (S n)
    else
     ret (itree_monad (stateT_effect nat + prob_effect))
       n)).
Proof.
intros u v Hle.
cbn in *.
specialize (@fbind_is_continuous_snd 
(stateT_effect nat + prob_effect) bool nat  (ffflip p)
) as Hcs.
apply continuous_implies_monotonic in Hcs.
apply Hcs.
intro b.
destruct b; auto.
-
 specialize (@fbind_is_continuous_snd 
(stateT_effect nat + prob_effect) _ nat ffget
) as Hcs'.
 apply continuous_implies_monotonic in Hcs'.
 apply Hcs'.
 intro d'.

specialize (@fbind_is_continuous_snd 
(stateT_effect nat + prob_effect) _ nat (ffput (S d')))
as Hcs''. 
apply continuous_implies_monotonic in Hcs''.
apply Hcs''.
intros [].
apply Hle.
- 
apply refl.
Qed.

Lemma geomF_is_continuous_aux_true_aux:
is_continuous
(P1 := itree _ _ ) (P2 := itree _ _ )
(fun x : itree (stateT_effect nat + prob_effect) nat =>
   do dummy <- ffget; ffput (S dummy);; x).
Proof.
remember (( do dummy <- ffget; ffput (S dummy) )) as m.
match goal with
| |- is_continuous ?ff =>
replace  ff with (fun x : itree
      (stateT_effect nat + prob_effect) nat => m;; x)
end.
2:{
subst.
extensionality x.
now setoid_rewrite fbind_assoc.
}
apply fbind_ignore_is_continuous_snd.
Qed.

Lemma geomF_is_continuous_aux_true(n:nat) :
@is_continuous
  (EXP_DCPO nat (itree (stateT_effect nat + prob_effect) nat))
  (itree (stateT_effect nat + prob_effect) nat)
(fun
   a : EXP nat (itree (stateT_effect nat + prob_effect) nat) =>
 do dummy <- ffget; ffput (S dummy);; a (S n)).
 Proof.
remember (S n) as m.
remember (fun a : EXP nat(itree(stateT_effect nat + prob_effect) nat)  
                => a m) as h.
remember (fun (x:(itree (stateT_effect nat + prob_effect) nat)) => 
 do dummy <- ffget; ffput (S dummy);; x) as g.
assert (Hgc : is_continuous (P1 := itree _ _ ) (P2 := itree _ _ ) g) by 
(now subst; apply geomF_is_continuous_aux_true_aux).
remember ({| fonc := g ; cont := Hgc|}) as gc.
match goal with
| |- is_continuous ?ff => replace ff 
  with (eval ° (pair gc ) ° h)  by (now subst)
end.
apply (comp_is_continuous
(P1 := EXP_DCPO _ (itree _ _)) (P2 := (itree _ _))).
-
  remember (pair gc) as q.
  apply (comp_is_continuous
  (P1 := (itree _ _))
  (P2 := PROD_DCPO (CONT_DCPO(itree _ _)(itree _ _))(itree _ _))
  (P3 := itree _ _)).
  +
   apply eval_is_continuous.
  +
   subst q.
   apply (is_continuous_pair_snd
   (P2 := (CONT_DCPO(itree _ _)(itree _ _)))).
 -
  subst h.
  apply apply_exp_cont.
  Qed.

Lemma geomF_is_continuous_aux
(p: Bounded 0 1)
(n:nat):
is_continuous 
 (P1 := (EXP_DCPO _ (itree _ _))) (P2 := itree _ _)
(fun a : EXP_DCPO nat
           (itree (stateT_effect nat + prob_effect) nat) =>
   do b <- ffflip p;
   (if b
    then do dummy <- ffget; ffput (S dummy);; a (S n)
    else
     ret (itree_monad (stateT_effect nat + prob_effect)) n)).
Proof.   
match goal with 
| |- is_continuous ?ff => remember ff as f
end.
remember (fun (a : EXP nat (itree (stateT_effect nat + prob_effect) nat)) 
 => do dummy <- ffget; ffput (S dummy);; a (S n) ) as m1.

remember (fun (_ : EXP nat (itree (stateT_effect nat + prob_effect) nat)) 
 => ret (itree_monad (stateT_effect nat + prob_effect)) n) as m2.
assert (Heqf' :
        f = (fun (a: EXP nat(itree(stateT_effect nat + prob_effect) nat)) 
        => do b <- ffflip p; (if b then m1 a else m2 a))).
{
  extensionality a.
  rewrite Heqm1, Heqm2.
  now subst.
}
 cbn in f,m1,m2.  
 rewrite Heqf'.
 apply if_flip_cont.
 -
  subst m1.
  apply geomF_is_continuous_aux_true.
 -
  subst m2.
  apply (cst_is_continuous
    (P1 := (EXP_DCPO _ (itree _ _))) 
    (P2 := itree _ _)). 
Qed.

Lemma geomF_is_continuous (p : Bounded 0 1) :
@is_continuous (EXP_DCPO _ (itree _ _))(EXP_DCPO _ (itree _ _)) (geomF p).
Proof.
unfold geomF.
cbn -  [itree_monad].
match goal with
| |- is_continuous ?ff =>
 remember ff as f
end.
change f with (curry (uncurry f)).
remember (uncurry f) as g.
apply (curry_preserves_cont
(A := (EXP_DCPO _ (itree _ _))) 
(B:= discrete_DCPO _ 0)).
subst.
apply (uncurry_preserves_cont
(A := (EXP_DCPO _ (itree _ _))) 
(B:= discrete_DCPO _ 0)).
-
 intro f.
 apply from_discrete_cont.
-
   intro n; cbn in n.
   apply geomF_is_continuous_aux.
Qed.

Definition geom (p : Bounded 0 1) :
nat -> itree_monad (stateT_effect nat + prob_effect) nat :=
@ffix (EXP_CPO _ itree_CPO) (geomF p).

Lemma geom_fixpoint (p : Bounded 0 1) (n : nat) : geom p n =
do b <- ffflip p; if b then do dummy <- ffget; ffput (S dummy);; 
 geom p (1 + n)%nat else ret _ n.
Proof.
destruct (@Kleene (EXP_CPO _ itree_CPO) (geomF p) (geomF_is_continuous p))
 as [Hfixp _].
unfold Kleene.is_fixpoint in Hfixp.
unfold geom at 1.
rewrite <- Hfixp.
reflexivity.
Qed.

Local Notation "m1 == m2" :=
(itree_equiv (stateT_effect _ + prob_effect) 
             (coprod_step (stateT_step _) prob_equiv) m1 m2)
  (at level 70, m2 at next level, no associativity).

Lemma flip_incr_while_true_correct_fuel (n:nat)(p:Bounded 0 1):
forall k,
(ffput k ;; (while_fuel _ n (ffflip p) (do x <- ffget; ffput (S x))));; ffget ==
ffput k;; iterate n (fun _ : nat => fbot) (geomF p) k.
Proof.
induction n as [ | n IH]; intros k.
-
  rewrite bind_assoc.
  cbn.
  now rewrite fbind_fbot.
-
 rewrite while_fuel_S.
 cbn [iterate].
 setoid_rewrite push_ffput_in_if.
 setoid_rewrite push_fget_in_if.
 apply itree_bind_congr;
 [reflexivity |].
 intros [].
 +
 repeat rewrite bind_assoc in *.
 specialize (IH ( S k)).
 cbn [plus].
 rewrite <- bind_assoc.
 rewrite <- bind_assoc.
 rewrite ffput_ffget, bind_assoc, bind_assoc, ret_left, <-bind_assoc,
  ffput_ffput.
 rewrite bind_assoc in IH.
 rewrite IH.
 clear IH.
 symmetry.
 rewrite <- bind_assoc, ffput_ffget, bind_assoc, ret_left, <- bind_assoc,
  ffput_ffput.
  reflexivity.
 +
  rewrite bind_assoc, ret_left, ffput_ffget.
  reflexivity.
Qed.

Lemma flip_incr_while_true_correct (p : Bounded 0 1) :
fflip_incr_while_true p == ffput 0;; do n <- geom p 0; ret _ n.
Proof.
unfold fflip_incr_while_true.
rewrite while_lub_while_fuel.
unfold geom, ffix.
rewrite <- bind_assoc.
match goal with
| |- (?m ;; lub ?S) ;; _ == _ => 
 eassert (H := @fbind_ignore_is_continuous_snd _ _ _ m S _)
end.
destruct H as (Hd1 & Heq).
setoid_rewrite Heq.
clear Heq.
match goal with
| |- (lub ?S) ;; ?m == _ => 
 eassert (H := @fbind_is_continuous_fst _ _ _ (fun _ => m) S _)
end.
rewrite <- fmap_comp in *.
unfold comp in *.
destruct H as (Hd2 & Heq).
setoid_rewrite Heq.
clear Heq.
cbn.
unfold proj.
match goal with
| |- _ == fbind ?m (fun _ => fbind (lub ?S) _)  =>
 eassert (H := @fbind_ignore_is_continuous_snd _ _ _ m S _)
end.
destruct H as (Hd3 & Heq).
rewrite <- fbind_assoc.
setoid_rewrite Heq.
clear Heq.
rewrite <- fmap_comp in *.
unfold comp in *.
rewrite fbind_fret_right.
apply itree_lub_congr; auto.
-
 intros m1 (m & (n & Hn) & Heq); subst.
 eexists.
 split.
 +
  eexists.
  split.
  *
   now exists n.
  *
   reflexivity.
 +
   apply flip_incr_while_true_correct_fuel.
-
intros m2 (m & (n & Hn) & Heq); subst. 
eexists.
 split.
 +
  eexists.
  split.
  *
   now exists n.
  *
   reflexivity.
 +
  apply itree_sym,flip_incr_while_true_correct_fuel.
  Unshelve.
  {
    unfold while_fuel,iter_fuel.
    apply (iterate_directed (X := @itree_CPO _ _ )).
    cbn.
    apply (@iterF_is_monotonic (itree_monad
    (stateT_effect nat +
     prob_effect))unit).
  }
  {
  apply monotonic_directed; auto.
  -
  intros u v Hle.
  apply fbind_ignore_is_monotonic_snd.
  apply Hle.
  -
   apply (iterate_directed (X := @itree_CPO _ _ )).
   cbn.
   apply (@iterF_is_monotonic (itree_monad(stateT_effect nat +
    prob_effect))unit).
  }
  {
    apply monotonic_directed.
    -
    intros u v Hle.
    now apply Hle.
    -
    apply (iterate_directed (X :=  (EXP_CPO _  (@itree_CPO _ _ )))).
    apply geomF_is_monotonic.
  }
Qed.
(***
Example flip_incr_while_true (p : Bounded 0 1) :
stateT_monad nat prob_monad nat :=
put 0 ;;
While stateT_lift (flip p) {{
  do n <- get; put (S n)
}};;
get.

Local Open Scope R_scope.

Program Definition pr_geom (p : Bounded 0 1) (n : nat) : Bounded 0 1 := {|
  bounded_val := (1 - p) * p ^ n
|}.

Next Obligation.
intros [p [H0 H1] ] n.
cbn.
split.
- apply Rmult_le_pos; [lra | ].
  apply pow_le, H0.
- replace 1 with (1 * 1) at 2 by apply Rmult_1_l.
  apply Rmult_le_compat; [lra | | lra | ].
  + apply pow_le, H0.
  + induction n as [ | n IH]; [apply Rle_refl | ].
    cbn.
    nra.
Qed.


Lemma flip_incr_while_true_prob (p : Bounded 0 1) (init n : nat) :
probability (fun res => Nat.eqb (fst res) n) (flip_incr_while_true p) init =
pr_geom p n.
Proof.
Abort.
*)