From Stdlib Require Export FunctionalExtensionality.
From Monad Require Export Monad.
From Itree Require Export Itree Bind Fold.

Program Definition itree_mor
  (F G : Type -> Type) (N : forall X : Type, F X -> G X)
  (X : Type) (m : itree F X) :
itree G X :=
@ffold _ _ (@itree_CPO G X) fret (fun Y fy k => impure (N Y fy) k) _ m.

Next Obligation.
cbn.
intros F G N X m Y fy.
apply impure_is_continuous.
Qed.

Definition trigger [F : Type -> Type] [X : Type] (fx : F X) : itree F X :=
impure fx fret.

Definition itree_monad (F : Type -> Type) : MONAD := {|
  functor := @itree_CPO F;
  ret := @fret F;
  bind := @fbind F;
  bind_continuous_fst := @fbind_is_continuous_fst F;
  bind_continuous_snd := @fbind_is_continuous_snd F;
  bind_strict := @fbind_fbot F;
  ret_right := @fbind_fret_right F;
  ret_left := @fbind_fret_left F;
  bind_assoc := @fbind_assoc F
|}.

Lemma mmor_impure
  (F : Type -> Type) (M : MONAD) (f : MONAD_MORPHISM (itree_monad F) M)
  (X Y: Type) (fx : F X) (k : X -> itree F Y) :
f Y (impure fx k) = do x <- f X (trigger fx); f Y (k x).
Proof.
unfold trigger.
rewrite <- mmor_bind.
cbn.
rewrite fbind_impure.
do 2 apply f_equal.
extensionality x.
rewrite fbind_fret_left.
reflexivity.
Qed.
