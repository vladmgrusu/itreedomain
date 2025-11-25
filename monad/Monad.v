From Stdlib Require Export FunctionalExtensionality.
From Domain Require Export Cont.

Global Set Implicit Arguments.

Global Obligation Tactic := idtac.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.

Global Open Scope monad_scope.

Reserved Notation "'do' x <- m1 ; m2"
  (at level 60, x name, m1 at level 50, m2 at level 60).

Record MONAD : Type := {
  functor :> Type -> CPO;
  ret : forall (X : Type), X -> functor X;
  bind : forall (X Y : Type), functor X -> (X -> functor Y) -> functor Y
   where "'do' x <- m1 ; m2" := (@bind _ _ m1 (fun x => m2));
  bind_continuous_fst :
    forall (X Y : Type) (k : X -> functor Y),
    is_continuous (fun m : functor X => do x <- m; k x);
  bind_continuous_snd :
    forall (X Y : Type) (m : functor X),
    @is_continuous (EXP_DCPO X (functor Y)) (functor Y)
      (fun k : X -> functor Y => do x <- m; k x);
  bind_strict :
    forall (X Y : Type) (f : X -> functor Y),
    do x <- @bot (functor X); f x = @bot (functor Y);
  ret_right :
    forall (X : Type) (m : functor X), do x <- m; ret x = m;
  ret_left :
    forall (X Y : Type) (a : X) (f : X -> functor Y), do x <- ret a; f x = f a;
  bind_assoc :
    forall
      (X Y Z : Type) (m : functor X) (f : X -> functor Y) (g : Y -> functor Z),
    do y <- (do x <- m; f x); g y = do x <- m; do y <- f x; g y
}.

Notation "'do' x <- m1 ; m2" := (@bind _ _ _ m1 (fun x => m2))
  (at level 60, x name, m1 at level 50, m2 at level 60) : monad_scope.

Notation "m1 ;; m2" := (@bind _ _ _ m1 (fun _ => m2))
  (at level 60, m2 at level 60) : monad_scope.

Notation "'If' c 'then' m1 'else' m2" :=
(do b <- c ; if b then m1 else m2) (at level 200, only parsing) : monad_scope.

Lemma seq_continuous_snd (M : MONAD) (X Y : Type) (m : M X) :
is_continuous (fun p : M Y => m;; p).
Proof.
intros.
apply seq_continuous_snd_gen, bind_continuous_snd.
Qed.

Lemma ret_if (M : MONAD) (b : bool) [X : Type] (x1 x2 : X) :
ret M (if b then x1 else x2) = if b then ret M x1 else ret M x2.
Proof.
destruct b; reflexivity.
Qed.

Lemma bind_ignore_monotonic_snd [M : MONAD] [X : Type] (Y : Type) (m : M X) :
is_monotonic (fun k : M Y => m;; k).
Proof.
intros u v Hle.
specialize (bind_continuous_snd M Y m) as Hcs.
apply continuous_implies_monotonic in Hcs.
apply Hcs.
now intros _.
Qed.

Lemma bind_ignore_continuous_snd [M : MONAD] [X : Type] (Y : Type) (m : M X) :
is_continuous (fun k : M Y => m;; k).
Proof.
intros S Hd.
specialize (bind_continuous_snd M Y m) as Hcs.
split.
{
  apply monotonic_directed; auto.
  apply bind_ignore_monotonic_snd.
}
remember (fmap S (fun x  => (fun _:X => x))) as S'.
assert (HS': is_directed (P := EXP_Poset _ _) S').
{
  subst.
  apply 
   (monotonic_directed (P2 := EXP_Poset _ _)); auto.
  now intros u v Hle _.
}
specialize (Hcs _ HS').
clear HS'.
destruct Hcs as (_ & Heq).
subst.
rewrite <- fmap_comp in Heq.
unfold comp in Heq.
cbn in *.
rewrite <- Heq.
unfold proj.
f_equal.
extensionality x.
rewrite <- fmap_comp.
unfold comp.
now rewrite fmap_id.
Qed.



Record MONAD_MORPHISM (M1 M2 : MONAD) : Type := {
  mmor :> forall X, M1 X -> M2 X;
  mmor_continuous : forall X, is_continuous (mmor X);
  mmor_strict : forall X, mmor X bot = bot;
  mmor_ret : forall X x, mmor X (ret M1 x) = ret M2 x;
  mmor_bind :
    forall X Y m f, mmor Y (do x <- m; f x) = do x <- mmor X m; mmor Y (f x)
}.

Program Definition mmor_comp
  (M1 M2 M3 : MONAD) (g : MONAD_MORPHISM M2 M3) (f : MONAD_MORPHISM M1 M2) :
MONAD_MORPHISM M1 M3 := {|
  mmor := fun X => comp (g X) (f X)
|}.

Next Obligation.
intros; apply comp_is_continuous; apply mmor_continuous.
Qed.

Next Obligation.
unfold comp.
cbn.
intros M1 M2 M3 f g X.
rewrite mmor_strict, mmor_strict.
reflexivity.
Qed.

Next Obligation.
unfold comp.
cbn.
intros M1 M2 M3 f g X x.
rewrite mmor_ret, mmor_ret.
reflexivity.
Qed.

Next Obligation.
unfold comp.
cbn.
intros M1 M2 M3 f g X Y m h.
rewrite mmor_bind, mmor_bind.
reflexivity.
Qed.

Record COPRODUCT (M1 M2 : MONAD) : Type := {
  coproduct :> MONAD;
  in_left : MONAD_MORPHISM M1 coproduct;
  in_right : MONAD_MORPHISM M2 coproduct;
  from_coproduct :
    forall M : MONAD,
    MONAD_MORPHISM M1 M -> MONAD_MORPHISM M2 M -> MONAD_MORPHISM coproduct M;
  in_left_law :
    forall
      (M : MONAD) (f : MONAD_MORPHISM M1 M) (g : MONAD_MORPHISM M2 M)
      (X : Type) (m1 : M1 X),
    from_coproduct f g X (in_left X m1) = f X m1;
  in_right_law :
    forall
      (M : MONAD) (f : MONAD_MORPHISM M1 M) (g : MONAD_MORPHISM M2 M)
      (X : Type) (m2 : M2 X),
    from_coproduct f g X (in_right X m2) = g X m2;
  from_coproduct_unique :
     forall
       (M : MONAD) (f : MONAD_MORPHISM M1 M) (g : MONAD_MORPHISM M2 M)
       (h : MONAD_MORPHISM coproduct M),
       (forall X m1, h X (in_left X m1) = f X m1) ->
       (forall X m2, h X (in_right X m2) = g X m2) ->
       forall X m, from_coproduct f g X m = h X m
}.

Notation "'defined'" := Some : monad_scope.
Notation "'undefined'" := None : monad_scope.
