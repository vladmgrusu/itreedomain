From Itree Require Export DenoteCoprod EquivCoprod.
From StateT Require Export Equiv. 

Section State.

Variable S : Type.

Variable F : Type -> Type.

Variable M : MONAD.

Hypothesis denote_effect :
forall X Y, F Y -> (Y -> stateT_monad S M X) -> stateT_monad S M X.

Hypothesis denote_effect_bind :
  forall X Y Z fz m (f : X -> stateT_monad S M Y),
   @denote_effect Y Z fz (fun z => do x <- m z; f x) =
   do x <- @denote_effect X Z fz (fun z => m z); f x.

Hypothesis denote_effect_is_continuous :
forall X Y fy, @is_continuous (EXP_DCPO _ _) _ (@denote_effect X Y fy).

Definition denote_stateT_left_mmor :
MONAD_MORPHISM (itree_monad (stateT_effect S + F)) (stateT_monad S M).
Proof.
unshelve eapply denote_coprod_mmor.
- exact (@denote_stateT_effect S M).
- exact denote_effect.
- intros; apply denote_stateT_effect_bind.
- exact denote_effect_bind.
- apply denote_stateT_effect_is_continuous.
- exact denote_effect_is_continuous.
Defined.

Definition denote_stateT_left [X : Type] (m : itree (stateT_effect S + F) X) :
stateT_monad S M X :=
denote_stateT_left_mmor X m.

Variable R : forall X, itree F X -> itree F X -> Prop.

Hypothesis step_correct :
forall (X : Type) (m1 m2 : itree F X),
R X m1 m2 ->
denote_monad_mmor F
  (stateT_monad S M)
  denote_effect
  denote_effect_bind
  denote_effect_is_continuous X
  m1 =
denote_monad_mmor F
  (stateT_monad S M)
  denote_effect
  denote_effect_bind
  denote_effect_is_continuous X
  m2.

Local Notation "m1 == m2" :=
  (itree_equiv (stateT_effect S + F) (coprod_step (stateT_step S) R) m1 m2)
  (at level 70, m2 at next level, no associativity).

Hypothesis denote_effect_swap :
forall (X Y : Type) (sx : stateT_effect S X) (fy : F Y),
do z <- denote_effect fy (ret _ (X:=Y));
do y <- denote_stateT_effect sx (ret (stateT_monad S M) (X:=X));
ret (stateT_monad S M) (y, z) =
do y <- denote_stateT_effect sx (ret (stateT_monad S M) (X:=X));
do z <- denote_effect fy (ret (stateT_monad S M) (X:=Y));
ret (stateT_monad S M) (y, z).

Lemma step_stateT_correct
  (X : Type) (m1 m2 : itree (stateT_effect S + F) X) :
coprod_step (stateT_step S) R m1 m2 ->
denote_stateT_left m1 = denote_stateT_left m2.
Proof.
intro Hstep.
unshelve eapply coprod_step_correct in Hstep.
- exact (stateT_monad S M).
- exact (@denote_stateT_effect S M).
- exact denote_effect.
- intros; apply denote_stateT_effect_bind.
- exact denote_effect_bind.
- apply denote_stateT_effect_is_continuous.
- exact denote_effect_is_continuous.
- exact Hstep.
- exact (@stateT_step_correct S M).
- exact step_correct.
- apply denote_effect_swap.
Qed.

Lemma equiv_stateT_correct
  [X : Type] (m1 m2 : itree (stateT_effect S + F) X) :
m1 == m2 -> denote_stateT_left m1 = denote_stateT_left m2.
Proof.
intro Hequiv.
unshelve eapply coprod_equiv_correct in Hequiv.
- exact (stateT_monad S M).
- exact (@denote_stateT_effect S M).
- exact denote_effect.
- intros; apply denote_stateT_effect_bind.
- exact denote_effect_bind.
- apply denote_stateT_effect_is_continuous.
- exact denote_effect_is_continuous.
- apply Hequiv.
- exact (@stateT_step_correct S M).
- exact step_correct.
- apply denote_effect_swap.
Qed.

Lemma denote_stateT_left_mmor_cont (X:Type):
is_continuous (denote_stateT_left_mmor X).
Proof.
exact (mmor_continuous denote_stateT_left_mmor X).
Qed.

End State.
