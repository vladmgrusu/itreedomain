From Itree Require Export Coprod Denote.

Section Denote.

Variables F G : Type -> Type.

Variable M : MONAD.

Variable denote_effect1 : forall [X Y], F Y -> (Y -> M X) -> M X.

Variable denote_effect2 : forall [X Y], G Y -> (Y -> M X) -> M X.

Definition coprod_denote_effect
  [X Y : Type] (fgy : (F + G)%monad Y) (k : Y -> M X) : M X :=
match fgy with
| inl fy => denote_effect1 fy k
| inr gy => denote_effect2 gy k
end.

Hypothesis denote_effect_bind1 :
  forall X Y Z fz m (f : X -> M Y),
   @denote_effect1 Y Z fz (fun z => do x <- m z; f x) =
   do x <- @denote_effect1 X Z fz (fun z => m z); f x.

Hypothesis denote_effect_bind2 :
  forall X Y Z fz m (f : X -> M Y),
   @denote_effect2 Y Z fz (fun z => do x <- m z; f x) =
   do x <- @denote_effect2 X Z fz (fun z => m z); f x.

Lemma coprod_denote_effect_bind
 [X Y Z : Type] (fgz : (F + G)%monad Z) (f : Z -> M X) (g : X -> M Y) :
   @coprod_denote_effect _ _ fgz (fun z => do x <- f z; g x) =
   do x <- @coprod_denote_effect _ _ fgz (fun z => f z); g x.
Proof.
destruct fgz as [fz | gz].
- apply denote_effect_bind1.
- apply denote_effect_bind2.
Qed.

Hypothesis denote_effect_is_continuous1 :
forall X Y fy, @is_continuous (EXP_DCPO _ _) _ (@denote_effect1 X Y fy).

Hypothesis denote_effect_is_continuous2 :
forall X Y fy, @is_continuous (EXP_DCPO _ _) _ (@denote_effect2 X Y fy).

Lemma coprod_denote_effect_is_continuous
  [X Y : Type] (fgy : (F + G)%monad Y) :
@is_continuous (EXP_DCPO _ _) _ (@coprod_denote_effect X Y fgy).
Proof.
destruct fgy as [fy | gy].
- apply denote_effect_is_continuous1.
- apply denote_effect_is_continuous2.
Qed.

(*
Definition denote_coprod_mmor' : MONAD_MORPHISM (itree_monad (F + G)) M :=
denote_monad_mmor
  (F + G) M coprod_denote_effect coprod_denote_effect_bind
  coprod_denote_effect_is_continuous.

Definition denote_coprod' [X : Type] (m : itree_monad (F + G) X) : M X :=
denote_coprod_mmor' X m.
*)

Definition denote_coprod_mmor : MONAD_MORPHISM (itree_monad (F + G)) M :=
itree_from_coproduct_mmor (
  denote_monad_mmor
    F M denote_effect1 denote_effect_bind1 denote_effect_is_continuous1) (
  denote_monad_mmor
    G M denote_effect2 denote_effect_bind2 denote_effect_is_continuous2).

Definition denote_coprod [X : Type] (m : itree_monad (F + G) X) : M X :=
denote_coprod_mmor X m.

(*
Lemma denote_coprod_mmor_unique [X : Type] (m : itree_monad (F + G) X) :
denote_coprod' m = denote_coprod m.
Proof.
apply itree_from_coproduct_unique.
- cbn.
  clear.
  intros X m.
*)

End Denote.
