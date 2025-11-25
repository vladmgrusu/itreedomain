From Itree Require Export Equiv DenoteCoprod.

Section Equiv.

Variables F G : Type -> Type.

Variable step1 : forall [X], itree F X -> itree F X -> Prop.

Variable step2 : forall [X], itree G X -> itree G X -> Prop. 

Inductive coprod_step :
forall [X : Type], itree (F + G) X -> itree (F + G) X -> Prop :=
| step_left :
  forall X m m', step1 m m' ->
  @coprod_step X
    (in_left (itree_coproduct F G) _ m) (in_left (itree_coproduct F G) _ m')
| step_right :
  forall X m m', step2 m m' ->
  @coprod_step X
    (in_right (itree_coproduct F G) _ m) (in_right (itree_coproduct F G) _ m')
| step_swap : forall [X Y : Type] (fx : F X) (fy : G Y),
  coprod_step (
    do x <- in_left (itree_coproduct F G) _ (trigger fx);
    do y <- in_right (itree_coproduct F G) _ (trigger fy);
    ret _ (x, y)) (
    do y <- in_right (itree_coproduct F G) _ (trigger fy);
    do x <- in_left (itree_coproduct F G) _ (trigger fx);
    ret _ (x, y)).

Local Notation "m1 == m2" := (itree_equiv (F + G) coprod_step m1 m2)
  (at level 70, m2 at next level, no associativity).

Lemma equiv_left [X : Type] (m m' : itree F X) :
step1 m m' ->
in_left (itree_coproduct F G) X m == in_left (itree_coproduct F G) X m'.
Proof.
intro Hstep1.
apply itree_step, step_left, Hstep1.
Qed.

Lemma equiv_right [X : Type] (m m' : itree G X) :
step2 m m' ->
in_right (itree_coproduct F G) X m == in_right (itree_coproduct F G) X m'.
Proof.
intro Hstep2.
apply itree_step, step_right, Hstep2.
Qed.

Lemma equiv_swap_ret [X Y : Type] (fx : F X) (fy : G Y) :
do x <- itree_in_left G (trigger fx);
do y <- itree_in_right F (trigger fy);
ret _ (x, y) ==
do y <- itree_in_right F (trigger fy);
do x <- itree_in_left G (trigger fx);
ret _ (x, y).
Proof.
apply itree_step, step_swap.
Qed.

Lemma equiv_swap
  [X Y Z : Type] (fx : F X) (fy : G Y) (f : X -> Y -> itree (F + G) Z) :
do x <- itree_in_left G (trigger fx);
do y <- itree_in_right F (trigger fy);
f x y ==
do y <- itree_in_right F (trigger fy);
do x <- itree_in_left G (trigger fx);
f x y.
Proof.
transitivity (
  do xy <- (
    do x <- itree_in_left G (trigger fx);
    do y <- itree_in_right F (trigger fy);
    ret _ (x, y)
  );
  f (fst xy) (snd xy)
).
{
  rewrite bind_assoc.
  etransitivity.
  2:{
    apply itree_bind_congr; [reflexivity | ].
    intro x.
    rewrite bind_assoc.
    apply itree_refl.
  }
  cbn beta.
  etransitivity.
  2:{
    apply itree_bind_congr; [reflexivity | ].
    intro x.
    apply itree_bind_congr; [reflexivity | ].
    intro y.
    rewrite ret_left.
    cbn.
    apply itree_refl.
  }
  cbn beta.
  apply itree_refl.
}
symmetry.
 transitivity (
  do xy <- (
    do y <- itree_in_right F (trigger fy);
    do x <- itree_in_left G (trigger fx);
    ret _ (x, y)
  );
  f (fst xy) (snd xy)
).
{
  rewrite bind_assoc.
  etransitivity.
  2:{
    apply itree_bind_congr; [reflexivity | ].
    intro x.
    rewrite bind_assoc.
    apply itree_refl.
  }
  cbn beta.
  etransitivity.
  2:{
    apply itree_bind_congr; [reflexivity | ].
    intro x.
    apply itree_bind_congr; [reflexivity | ].
    intro y.
    rewrite ret_left.
    cbn.
    apply itree_refl.
  }
  cbn beta.
  apply itree_refl.
}
rewrite equiv_swap_ret.
reflexivity.
Qed.

Variable M : MONAD.

Variable denote_effect1 : forall X Y, F Y -> (Y -> M X) -> M X.

Variable denote_effect2 : forall X Y, G Y -> (Y -> M X) -> M X.

Hypothesis denote_effect_bind1 :
  forall X Y Z fz m (f : X -> M Y),
   @denote_effect1 Y Z fz (fun z => do x <- m z; f x) =
   do x <- @denote_effect1 X Z fz (fun z => m z); f x.

Hypothesis denote_effect_bind2 :
  forall X Y Z fz m (f : X -> M Y),
   @denote_effect2 Y Z fz (fun z => do x <- m z; f x) =
   do x <- @denote_effect2 X Z fz (fun z => m z); f x.

Hypothesis denote_effect_is_continuous1 :
forall X Y fy, @is_continuous (EXP_DCPO _ _) _ (@denote_effect1 X Y fy).

Hypothesis denote_effect_is_continuous2 :
forall X Y fy, @is_continuous (EXP_DCPO _ _) _ (@denote_effect2 X Y fy).

Hypothesis step_correct1 :
forall X m m',
step1 m m' ->
denote_monad_mmor
  F M denote_effect1 denote_effect_bind1 denote_effect_is_continuous1 X m =
denote_monad_mmor
  F M denote_effect1 denote_effect_bind1 denote_effect_is_continuous1 X m'.

Hypothesis step_correct2 :
forall X m m',
step2 m m' ->
denote_monad_mmor
  G M denote_effect2 denote_effect_bind2 denote_effect_is_continuous2 X m =
denote_monad_mmor
  G M denote_effect2 denote_effect_bind2 denote_effect_is_continuous2 X m'.

Hypothesis denote_effect_swap :
forall X Y fx fy,
do z <- denote_effect2 Y fy (@ret M Y);
do y <- denote_effect1 X fx (@ret M X);
ret M (y, z) =
do y <- denote_effect1 X fx (@ret M X);
do z <- denote_effect2 Y fy (@ret M Y);
ret M (y, z).

Lemma coprod_step_correct
  [X : Type] (m1 m2 : itree (F + G) X) :
coprod_step m1 m2 ->
denote_coprod
  _ _ _ _ _ denote_effect_bind1 denote_effect_bind2
  denote_effect_is_continuous1 denote_effect_is_continuous2 m1 =
denote_coprod
  _ _ _ _ _ denote_effect_bind1 denote_effect_bind2
  denote_effect_is_continuous1 denote_effect_is_continuous2 m2.
Proof.
intros [Y m m' HR1 | Y m m' HR2 | Y Z fy fz]; clear m1 m2.
- cbn.
  do 2 rewrite (
    @itree_in_left_law F G M 
      (denote_monad_mmor F M denote_effect1 denote_effect_bind1 denote_effect_is_continuous1)
      (denote_monad_mmor G M denote_effect2 denote_effect_bind2 denote_effect_is_continuous2)).
  apply step_correct1, HR1.
- cbn.
  do 2 rewrite (
    @itree_in_right_law F G M 
      (denote_monad_mmor F M denote_effect1 denote_effect_bind1 denote_effect_is_continuous1)
      (denote_monad_mmor G M denote_effect2 denote_effect_bind2 denote_effect_is_continuous2)).
  apply step_correct2, HR2.
- cbn -[denote_monad_mmor].
  unfold trigger.
  do 2 rewrite itree_from_coproduct_fbind.
  rewrite itree_in_left_impure, itree_from_coproduct_impure, bind_assoc.
  rewrite itree_in_right_impure, itree_from_coproduct_impure, bind_assoc.
  etransitivity.
  {
    apply f_equal.
    extensionality y.
    rewrite itree_in_left_fret, itree_from_coproduct_fret, ret_left,
     itree_from_coproduct_fbind, itree_from_coproduct_impure, bind_assoc.
    reflexivity.
  }
  etransitivity.
  2:{
    symmetry.
    apply f_equal.
    extensionality z.
    rewrite itree_in_right_fret, itree_from_coproduct_fret, ret_left,
     itree_from_coproduct_fbind, itree_from_coproduct_impure, bind_assoc.
    reflexivity.
  }
  etransitivity.
  {
    apply f_equal.
    extensionality y.
    etransitivity.
    {
      apply f_equal.
      extensionality z.
      rewrite itree_in_right_fret, itree_from_coproduct_fret, ret_left,
       itree_from_coproduct_fret.
      reflexivity.
    }
    reflexivity.
  }
  etransitivity.
  2:{
    symmetry.
    apply f_equal.
    extensionality y.
    etransitivity.
    {
      apply f_equal.
      extensionality z.
      rewrite itree_in_left_fret, itree_from_coproduct_fret, ret_left,
       itree_from_coproduct_fret.
      reflexivity.
    }
    reflexivity.
  }
  cbn.
  unfold trigger.
  do 2 rewrite denote_monad_impure.
  etransitivity.
  {
    apply f_equal2; [ | reflexivity].
    apply f_equal.
    extensionality y.
    rewrite denote_monad_fret.
    reflexivity.
  }
  etransitivity.
  2:{
    symmetry.
    apply f_equal2; [ | reflexivity].
    apply f_equal.
    extensionality y.
    rewrite denote_monad_fret.
    reflexivity.
  }
  etransitivity.
  {
    apply f_equal.
    extensionality y.
    etransitivity.
    {
      apply f_equal2; [ | reflexivity].
      apply f_equal.
      extensionality z.
      rewrite denote_monad_fret.
      reflexivity.
    }
    reflexivity.
  }
  etransitivity.
  2:{
    symmetry.
    apply f_equal.
    extensionality y.
    etransitivity.
    {
      apply f_equal2; [ | reflexivity].
      apply f_equal.
      extensionality z.
      rewrite denote_monad_fret.
      reflexivity.
    }
    reflexivity.
  }
  symmetry.
  apply denote_effect_swap.
Qed.

Lemma coprod_equiv_correct [X : Type] (m1 m2 : itree (F + G) X) :
m1 == m2 ->
denote_coprod
  _ _ _ _ _ denote_effect_bind1 denote_effect_bind2
  denote_effect_is_continuous1 denote_effect_is_continuous2 m1 =
denote_coprod
  _ _ _ _ _ denote_effect_bind1 denote_effect_bind2
  denote_effect_is_continuous1 denote_effect_is_continuous2 m2.
Proof.
intro Hequiv.
eapply itree_equiv_correct; [ | | exact Hequiv].
- clear.
  intros X Y Z [fz | gz] f g.
  + rewrite bind_assoc.
    reflexivity.
  + rewrite bind_assoc.
    reflexivity.
- clear X m1 m2 Hequiv.
  intros X m1 m2 Hstep.
  apply coprod_step_correct in Hstep.
  exact Hstep.
Qed.

End Equiv.

Arguments coprod_step [_ _] _ _ [_] _ _.
Arguments denote_coprod_mmor [_ _ _] _ _.

Instance Proper_itree_in_left F G step1 step2 X :
Proper
  (@itree_equiv F step1 X ==> @itree_equiv (F + G) (coprod_step step1 step2) X)
  (@itree_in_left F G X).
Proof.
intros m1 m2 Hequiv.
induction Hequiv  as [
 X m1 m2 Hstep1 | X m | X m1 m2 _ IH | X m1 m2 m3 _ IH1 _ IH2 |
 X Y m1 m2 f1 f2 Jm IHm HF IHf | X S1 S2 Hdir1 Hdir2 IH1 IH2] 
 using itree_equiv_ind'.
- apply equiv_left, Hstep1.
- reflexivity.
- symmetry.
  exact IH.
- etransitivity; [exact IH1 | exact IH2].
- do 2 rewrite itree_in_left_fbind.
  apply itree_bind_congr; [exact IHm | exact IHf].
- eassert
    (denote_effect_is_continuous1 := itree_in_left_is_continuous _ _ _ Hdir1).
  destruct denote_effect_is_continuous1 as [Hd1 denote_effect_is_continuous1].
  rewrite denote_effect_is_continuous1.
  eassert
    (denote_effect_is_continuous2 := itree_in_left_is_continuous _ _ _ Hdir2).
  destruct denote_effect_is_continuous2 as [Hd2 denote_effect_is_continuous2].
  rewrite denote_effect_is_continuous2.
  apply itree_lub_congr;auto.
  + intros m (m1 & Hm1 & Heq);subst.
    destruct (IH1 _ Hm1) as (m2 & Hm2 & Heqv1 & Heqv2).
    eexists.
    split;auto.
    * eexists;split;eauto.
    * exact Heqv2.
  + intros m (m2 & Hm2 & Heq);subst.
    destruct (IH2 _ Hm2) as (m1 & Hm1 & Heqv1 & Heqv2).
    eexists.
    split;auto.
    * eexists;split;eauto.
    * exact Heqv2.
Qed.

Instance Proper_itree_in_right F G step1 step2 X :
Proper
  (@itree_equiv G step2 X ==> @itree_equiv (F + G) (coprod_step step1 step2) X)
  (@itree_in_right F G X).
Proof.
intros m1 m2 Hequiv.
induction Hequiv  as [
 X m1 m2 Hstep1 | X m | X m1 m2 _ IH | X m1 m2 m3 _ IH1 _ IH2 |
 X Y m1 m2 f1 f2 Jm IHm HF IHf | X S1 S2 Hdir1 Hdir2 IH1 IH2] 
 using itree_equiv_ind'.
- apply equiv_right, Hstep1.
- reflexivity.
- symmetry.
  exact IH.
- etransitivity; [exact IH1 | exact IH2].
- do 2 rewrite itree_in_right_fbind.
  apply itree_bind_congr; [exact IHm | exact IHf].
- eassert
    (denote_effect_is_continuous1 := itree_in_right_is_continuous _ _ _ Hdir1).
  destruct denote_effect_is_continuous1 as [Hd1 denote_effect_is_continuous1].
  rewrite denote_effect_is_continuous1.
  eassert
    (denote_effect_is_continuous2 := itree_in_right_is_continuous _ _ _ Hdir2).
  destruct denote_effect_is_continuous2 as [Hd2 denote_effect_is_continuous2].
  rewrite denote_effect_is_continuous2.
  apply itree_lub_congr;auto.
  + intros m (m1 & Hm1 & Heq);subst.
    destruct (IH1 _ Hm1) as (m2 & Hm2 & Heqv1 & Heqv2).
    eexists.
    split;auto.
    * eexists;split;eauto.
    * exact Heqv2.
  + intros m (m2 & Hm2 & Heq);subst.
    destruct (IH2 _ Hm2) as (m1 & Hm1 & Heqv1 & Heqv2).
    eexists.
    split;auto.
    * eexists;split;eauto.
    * exact Heqv2.
Qed.
