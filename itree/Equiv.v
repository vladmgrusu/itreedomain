From Stdlib Require Export Morphisms Lia.
From Monad Require Export  Iter.
From Itree Require Export Denote.

Section Itree.

Variable F : Type -> Type.

Variable R : forall [X], itree F X -> itree F X -> Prop.

Inductive itree_equiv : forall [X], itree F X -> itree F X -> Prop :=
| itree_step : forall X m1 m2, R m1 m2 -> @itree_equiv X m1 m2
| itree_refl : forall X m, @itree_equiv X m m
| itree_sym : forall X m1 m2, itree_equiv m1 m2 -> @itree_equiv X m2 m1
| itree_trans : forall X m1 m2 m3,
  itree_equiv m1 m2 -> itree_equiv m2 m3 -> @itree_equiv X m1 m3
| itree_bind_congr :
forall X Y (m1 m2 : itree_monad _ _) f1 f2,
itree_equiv m1 m2 ->
pointwise_relation X (@itree_equiv Y) f1 f2 ->
(*forall x : X, itree_equiv (f1 x) (f2 x) ->*)
@itree_equiv Y (do x <- m1; f1 x) (do x <- m2; f2 x)  
| itree_lub_congr :
forall X (S1 S2: Setof (itree F X)), 
is_directed S1 -> is_directed S2 -> 
 (forall m1, member S1 m1 -> exists m2, member S2 m2 /\ itree_equiv m1 m2)
->
( forall m2, member S2 m2 -> exists m1, member S1 m1 /\ itree_equiv m2 m1) 
  -> itree_equiv (lub S1) (lub S2).

Hint Constructors itree_equiv : itree.

Lemma itree_equiv_ind' 
	 : forall P : forall X : Type, itree F X -> itree F X -> Prop,
       (forall (X : Type) (m1 m2 : itree F X), R m1 m2 -> P X m1 m2) ->
       (forall (X : Type) (m : itree F X), P X m m) ->
       (forall (X : Type) (m1 m2 : itree F X),
        itree_equiv m1 m2 -> P X m1 m2 -> P X m2 m1) ->
       (forall (X : Type) (m1 m2 m3 : itree F X),
        itree_equiv m1 m2 ->
        P X m1 m2 -> itree_equiv m2 m3 -> P X m2 m3 -> P X m1 m3) ->
        (forall (X Y : Type) (m1 m2 : itree_monad F X)
          (f1 f2 : X -> itree F Y),
        itree_equiv m1 m2 ->
        P X m1 m2 ->
        (forall x : X, itree_equiv (f1 x) (f2 x)) ->
        (forall x : X, P Y (f1 x) (f2 x)) ->
        P Y (do x <- m1; f1 x) (do x <- m2; f2 x)) ->
       (forall (X : Type) (S1 S2 : Setof (itree F X)),
        is_directed S1 ->
        is_directed S2 ->
        (forall m1 : itree F X,
         member S1 m1 ->
         exists m2 : itree F X, 
         member S2 m2 /\ itree_equiv m1 m2 /\ P X m1 m2) ->
        (forall m2 : itree F X,
         member S2 m2 ->
         exists m1 : itree F X, 
         member S1 m1 /\ itree_equiv m2 m1 /\ P X m2 m1) ->
        P X (lub S1) (lub S2)) ->
       forall (X : Type) (c c0 : itree F X), 
        itree_equiv c c0 -> P X c c0.
Proof.
fix H 11.
intros.
destruct H6; auto with itree.
- apply H2; auto.
  apply H; auto.
- eapply H3; eauto; apply H; auto.
- 
 apply H4; auto.
 +
  apply H; auto.
 +
  intro x.
  apply H; auto. 
-
apply H5; auto.
  + intros m1 Hm1.
    destruct (H8 m1 Hm1) as (m2 & Hm2 & Hequiv).
    exists m2.
    repeat split; auto.
    apply H; auto.
  + intros m2 Hm2.
    destruct (H9 m2 Hm2) as (m1 & Hm1 & Hequiv).
    exists m1.
    repeat split; auto.
    apply H; auto.
Qed.

Notation "m1 == m2" := (@itree_equiv _ m1 m2) (at level 70, no associativity) :
  monad_scope.

Lemma trans_eq_equiv (X : Type) (x y z : itree F X) :
x = y -> y == z -> x == z.
Proof.
now intros [].
Qed.

Lemma equiv_ret_left (X Y : Type) (a : X) (f : X -> itree F Y) :
do x <- ret (itree_monad F) a; f x == f a.
Proof.
rewrite ret_left.
apply itree_refl.
Qed.

Lemma equiv_ret_right (X : Type) (m : itree_monad F X) :
do x <- m; ret (itree_monad F) x == m.
Proof.
rewrite ret_right.
apply itree_refl.
Qed.

Lemma equiv_bind_assoc
  (X Y Z : Type)
  (m : itree_monad F X) (f : X -> itree_monad F Y) (g : Y -> itree_monad F Z) :
do y <- (do x <- m; f x); g y ==
do x <- m; do y <- f x; g y.
Proof.
rewrite bind_assoc.
apply itree_refl.
Qed.

Lemma equiv_ret_if (b : bool) [X : Type] (x1 x2 : X) :
ret (itree_monad F) (if b then x1 else x2) ==
if b then ret (itree_monad F) x1 else ret (itree_monad F) x2.
Proof.
destruct b; apply itree_refl.
Qed.

Variable M : MONAD.

Variable denote_effect : forall X Y, F Y -> (Y -> M X) -> M X.

Hypothesis denote_effect_bind :
forall X Y Z (fz : F Z) m (f : X -> M Y),
denote_effect Y fz (fun z => do x <- m z; f x) =
do x <- denote_effect X fz (fun z => m z); f x.

Hypothesis denote_effect_is_continuous :
forall X Y (fy :F Y), @is_continuous (EXP_DCPO _ _) _ (denote_effect X fy).

Hypothesis R_correct :
forall X m1 m2,
R m1 m2 ->
denote_monad F M denote_effect denote_effect_is_continuous X m1 =
denote_monad F M denote_effect denote_effect_is_continuous X m2.

Lemma itree_equiv_correct (X : Type) (m1 m2 : itree F X) :
m1 == m2 ->
denote_monad F M denote_effect denote_effect_is_continuous X m1 =
denote_monad F M denote_effect denote_effect_is_continuous X m2.
Proof.
intro Hequiv.
induction Hequiv as 
[ X m1 m2 HR | X m | X m1 m2 _ IH | X m1 m2 m3 _ IH1 _ IH2 | 
X Y m1 m2 f1 f2 Heqm IHm Heqf IHf|
X S1 S2 Hd1 Hd2 Hinc1 Hinc2] using itree_equiv_ind' .
- apply R_correct, HR.
- reflexivity.
- symmetry.
  exact IH.
- etransitivity; [exact IH1 | exact IH2].
-
rewrite (denote_monad_fbind _ _ _ denote_effect_bind),
(denote_monad_fbind _ _ _ denote_effect_bind), IHm.
f_equal.
extensionality x.
apply IHf.
-
 destruct (denote_monad_is_continuous F M 
 denote_effect denote_effect_is_continuous X Hd1) as 
 (_ & Heq1).
 destruct (denote_monad_is_continuous F M 
 denote_effect denote_effect_is_continuous X Hd2) as 
 (_ & Heq2).
 rewrite Heq1,Heq2.
 clear Heq1 Heq2.
 f_equal.
 apply set_equal; intro x; 
 split; intro Hmx.
 + 
   destruct Hmx as (y & Hy & Heqy);subst.
   destruct (Hinc1 _ Hy) as (m2 & Hm2 & Heqv & Hind).
   now exists m2.
 +  
  destruct Hmx as (y & Hy & Heqy);subst.
  destruct (Hinc2 _ Hy) as (m1 & Hm1 & Heqv & Hind).
  now exists m1.
Qed.

Lemma itree_while_congr
  (cond1 cond2 : itree F bool) (body1 body2 : itree F unit) :
cond1 == cond2 -> body1 == body2 ->
while (itree_monad F) cond1 body1 == while (itree_monad F) cond2 body2.
Proof.
intros Hcond Hbody.
do 2 rewrite while_lub_while_fuel.
apply itree_lub_congr.
- apply (@iterate_directed itree_CPO).
  apply (iterF_is_monotonic (itree_monad F)).
- apply (@iterate_directed itree_CPO).
  apply (iterF_is_monotonic (itree_monad F)).
- intros m1 (n & Hn).
  subst.
  exists (while_fuel (itree_monad F) n cond2 body2).
  split.
  + exists n.
    reflexivity.
  + revert cond1 cond2 body1 body2 Hcond Hbody.
    induction n as [ | n IH]; intros cond1 cond2 body1 body2 Hcond Hbody;
     [apply itree_refl | ].
    do 2 rewrite while_fuel_S.
    apply itree_bind_congr; auto.
    intros [ | ].
    * apply itree_bind_congr; unfold pointwise_relation; auto.
    * apply itree_refl.
- intros m2 (n & Hn).
  subst.
  exists (while_fuel (itree_monad F) n cond1 body1).
  split.
  + exists n.
    reflexivity.
  + revert cond1 cond2 body1 body2 Hcond Hbody.
    induction n as [ | n IH]; intros cond1 cond2 body1 body2 Hcond Hbody;
     [apply itree_refl | ].
    do 2 rewrite while_fuel_S.
    apply itree_bind_congr.
    * apply itree_sym, Hcond.
    * intros [ | ].
      -- apply itree_bind_congr.
         ++ apply itree_sym, Hbody.
         ++ intros [].
            apply IH; auto.
      -- apply itree_refl.
Qed.

End Itree.

Instance Equivalence_itree_equiv F R X :
Equivalence (@itree_equiv F R X).
Proof.
split.
- intro m.
  apply itree_refl.
- intros m1 m2 Hequiv.
  apply itree_sym.
  exact Hequiv.
- intros m1 m2 m3 Hequiv12 Hequiv23.
  eapply itree_trans; [exact Hequiv12 | exact Hequiv23].
Qed.

Instance Proper_bind F R X Y :
Proper
  (@itree_equiv F R X ==> pointwise_relation X (@itree_equiv F R Y) ==>
   @itree_equiv F R Y)
  (@bind (itree_monad F) X Y).
Proof.
intros m1 m2 Hm f1 f2 Hf.
exact (itree_bind_congr Hm Hf).
Qed.

Instance Proper_while F R :
Proper
  (@itree_equiv F R bool ==> @itree_equiv F R unit ==> @itree_equiv F R unit)
  (while (itree_monad F)).
Proof.
intros cond1 cond2 Hcond body1 body2 Hbody.
exact (itree_while_congr Hcond Hbody).
Qed.
