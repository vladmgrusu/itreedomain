From Itree Require Export Monad.

Local Close Scope nat_scope.

Notation "F + G" := (fun X => F X + G X) : monad_scope.

Section itreeCoproduct.

Variables F G : Type -> Type.

Program Definition itree_in_left [X : Type] (m : itree F X) :
itree_monad (F + G) X :=
@ffold _ _ (@itree_CPO (F + G) X)
  (fun x => fret x) (fun Y fy k => impure (inl fy) k) _ m.

Next Obligation.
cbn.
intros X m Y fy.
apply impure_is_continuous.
Qed.

Lemma itree_in_left_is_continuous (X : Type) :
is_continuous (@itree_in_left X).
Proof.
unfold itree_in_left.
repeat change (fun x => ?f x) with f.
match goal with
| |- is_continuous (@ffold ?F ?X ?Y ?f ?g ?Hc) =>
  exact (@ffold_is_continuous F X Y f g Hc)
end.
Qed.

Lemma itree_in_left_fbot (X : Type) : itree_in_left (@fbot _ X) = fbot.
Proof.
unfold itree_in_left.
rewrite ffold_fbot.
reflexivity.
Qed.

Lemma itree_in_left_fret (X : Type) (x : X) : itree_in_left (fret x) = fret x.
Proof.
unfold itree_in_left.
rewrite ffold_pure.
reflexivity.
Qed.

Lemma itree_in_left_impure (X Y : Type) (fx : F X) (k : X -> itree F Y) :
itree_in_left (impure fx k) = impure (inl fx) (fun x => itree_in_left (k x)).
Proof.
unfold itree_in_left.
rewrite ffold_impure.
reflexivity.
Qed.

Lemma itree_in_left_fbind
  (X Y : Type) (m : itree_monad F X) (f : X -> itree F Y) :
itree_in_left (do x <- m; f x) =
do x <- itree_in_left m; itree_in_left (f x).
Proof.
cbn.
rewrite <- fbisim_iff_eq.
apply fbisim_strong_coind with 
(R := fun x y => exists m,
  x = itree_in_left (fbind m f) /\
  y = fbind (itree_in_left m) (fun x : X => itree_in_left (f x)));
 [ | now exists m].
clear.
intros m1 m2 (m & Hm1 & Hm2).
subst m1 m2.
destruct (fcases m) as [ [[x Hm] | (Z & fz & k & Hm)] | Hm];
 rewrite Hm; clear m Hm.
- right.
  rewrite fbind_fret_left, itree_in_left_fret, fbind_fret_left, fbisim_iff_eq.
  reflexivity.
- left.
  right.
  right.
  do 4 eexists.
  rewrite fbind_impure, itree_in_left_impure, itree_in_left_impure,
   fbind_impure.
  split; [reflexivity | ].
  split; [reflexivity | ].
  intro z.
  eexists.
  split; reflexivity.
- left.
  left.
  rewrite fbind_fbot, itree_in_left_fbot, itree_in_left_fbot, fbind_fbot.
  split; reflexivity.
Qed.

Program Definition itree_in_left_mmor :
MONAD_MORPHISM (itree_monad F) (itree_monad (F + G)) := {|
  mmor := itree_in_left;
  mmor_continuous := itree_in_left_is_continuous;
  mmor_strict := itree_in_left_fbot;
  mmor_ret := itree_in_left_fret;
  mmor_bind := itree_in_left_fbind
|}.

Program Definition itree_in_right [X : Type] (m : itree G X) :
itree_monad (F + G) X :=
@ffold _ _ (@itree_CPO (F + G) X)
  (fun x => fret x) (fun Y fy k => impure (inr fy) k) _ m.

Next Obligation.
cbn.
intros X m Y fy.
apply impure_is_continuous.
Qed.

Lemma itree_in_right_is_continuous (X : Type) :
is_continuous (@itree_in_right X).
Proof.
unfold itree_in_right.
repeat change (fun x => ?f x) with f.
match goal with
| |- is_continuous (@ffold ?F ?X ?Y ?f ?g ?Hc) =>
  exact (@ffold_is_continuous F X Y f g Hc)
end.
Qed.

Lemma itree_in_right_fbot (X : Type) : itree_in_right (@fbot _ X) = fbot.
Proof.
unfold itree_in_right.
rewrite ffold_fbot.
reflexivity.
Qed.

Lemma itree_in_right_fret (X : Type) (x : X) : itree_in_right (fret x) = fret x.
Proof.
unfold itree_in_right.
rewrite ffold_pure.
reflexivity.
Qed.

Lemma itree_in_right_impure (X Y : Type) (gx : G X) (k : X -> itree G Y) :
itree_in_right (impure gx k) = impure (inr gx) (fun x => itree_in_right (k x)).
Proof.
unfold itree_in_right.
rewrite ffold_impure.
reflexivity.
Qed.

Lemma itree_in_right_fbind (X Y : Type) (m : itree G X) (g : X -> itree G Y) :
itree_in_right (fbind m g) =
fbind (itree_in_right m) (fun x => itree_in_right (g x)).
Proof.
cbn.
rewrite <- fbisim_iff_eq.
apply fbisim_strong_coind with 
(R := fun x y => exists m,
  x = itree_in_right (fbind m g) /\
  y = fbind (itree_in_right m) (fun x : X => itree_in_right (g x)));
 [ | now exists m].
clear.
intros m1 m2 (m & Hm1 & Hm2).
subst m1 m2.
destruct (fcases m) as [ [[x Hm] | (Z & fz & k & Hm)] | Hm];
 rewrite Hm; clear m Hm.
- right.
  rewrite fbind_fret_left, itree_in_right_fret, fbind_fret_left, fbisim_iff_eq.
  reflexivity.
- left.
  right.
  right.
  do 4 eexists.
  rewrite fbind_impure, itree_in_right_impure, itree_in_right_impure,
   fbind_impure.
  split; [reflexivity | ].
  split; [reflexivity | ].
  intro z.
  eexists.
  split; reflexivity.
- left.
  left.
  rewrite fbind_fbot, itree_in_right_fbot, itree_in_right_fbot, fbind_fbot.
  split; reflexivity.
Qed.

Program Definition itree_in_right_mmor :
MONAD_MORPHISM (itree_monad G) (itree_monad (F + G)) := {|
  mmor := itree_in_right;
  mmor_continuous := itree_in_right_is_continuous;
  mmor_strict := itree_in_right_fbot;
  mmor_ret := itree_in_right_fret;
  mmor_bind := itree_in_right_fbind
|}.

Program Definition itree_from_coproduct
  (M : MONAD) (f : forall X, itree F X -> M X) (g : forall X, itree G X -> M X)
  [X : Type] (m : itree (F + G) X) :
M X :=
ffold (@ret M X) (fun Y fgy =>
match fgy with
 | inl fx => fun k => do x <- f _ (trigger fx); k x
 | inr gx => fun k => do x <- g _ (trigger gx); k x
 end
) _ m.

Next Obligation.
cbn.
intros M f g X m Y [fy | gy]; apply bind_continuous_snd.
Qed.

Lemma itree_from_coproduct_is_continuous
  (M : MONAD)
  (f : MONAD_MORPHISM (itree_monad F) M) (g : MONAD_MORPHISM (itree_monad G) M)
  (X : Type) :
is_continuous (@itree_from_coproduct M f g X).
Proof.
unfold itree_from_coproduct.
apply ffold_is_continuous.
Qed.

Lemma itree_from_coproduct_fbot
  (M : MONAD)
  (f : MONAD_MORPHISM (itree_monad F) M) (g : MONAD_MORPHISM (itree_monad G) M)
  (X : Type) :
@itree_from_coproduct M f g X fbot = bot.
Proof.
unfold itree_from_coproduct.
apply ffold_fbot.
Qed.

Lemma itree_from_coproduct_fret
  (M : MONAD)
  (f : MONAD_MORPHISM (itree_monad F) M) (g : MONAD_MORPHISM (itree_monad G) M)
  (X : Type) (x : X) :
itree_from_coproduct M f g (fret x) = ret M x.
Proof.
unfold itree_from_coproduct.
apply ffold_pure.
Qed.

Lemma itree_from_coproduct_impure
  (M : MONAD)
  (f : MONAD_MORPHISM (itree_monad F) M) (g : MONAD_MORPHISM (itree_monad G) M)
  (X Y : Type) (fgx : (F X + G X)) (k : X -> itree (F + G) Y) :
itree_from_coproduct M f g (impure fgx k) =
match fgx with
| inl fx => do x <- f X (trigger fx); itree_from_coproduct M f g (k x)
| inr gx => do x <- g X (trigger gx); itree_from_coproduct M f g (k x)
end.
Proof.
unfold itree_from_coproduct.
rewrite ffold_impure.
destruct fgx; reflexivity.
Qed.

Lemma itree_from_coproduct_fbind
  (M : MONAD)
  (f : MONAD_MORPHISM (itree_monad F) M) (g : MONAD_MORPHISM (itree_monad G) M)
  (X Y : Type) (m : itree (F + G) X) (h : X -> itree (F + G) Y) :
itree_from_coproduct M f g (fbind m h) =
do x <- itree_from_coproduct M f g m; itree_from_coproduct M f g (h x).
Proof.
change (
  ((@itree_from_coproduct M f g _) ° (fun m => fbind m h)) m =
  ((fun m' => do x <- m';  itree_from_coproduct M f g (h x)) °
   (@itree_from_coproduct M f g _)) m).
apply corr_eq_reduce_to_compacts.
- apply comp_is_continuous.
  + apply itree_from_coproduct_is_continuous.
  + apply fbind_is_continuous_fst.
- apply comp_is_continuous.
  + apply bind_continuous_fst.
  + apply itree_from_coproduct_is_continuous.
- cbn.
  clear.
  intro m.
  change (finite_itree (F + G) X) in m.
  induction m as [ | x | Z fgz k IH] using (finite_itree_ind X).
  + unfold comp.
    change (inject (c := itree (F + G) X) Lcbot) with (@fbot (F + G) X).
    rewrite fbind_fbot, itree_from_coproduct_fbot, itree_from_coproduct_fbot,
     bind_strict.
    reflexivity.
  + unfold comp.
    rewrite inject_fpure, fbind_fret_left, itree_from_coproduct_fret, ret_left.
    reflexivity.
  + unfold comp in IH |- *.
    rewrite inject_fimpure, fbind_impure, itree_from_coproduct_impure,
     itree_from_coproduct_impure.
    destruct fgz as [fz | gz].
    * rewrite bind_assoc.
      apply f_equal.
      extensionality z.
      apply IH.
   * rewrite bind_assoc.
      apply f_equal.
      extensionality z.
      apply IH.
Qed.

Program Definition itree_from_coproduct_mmor
  (M : MONAD)
  (f : MONAD_MORPHISM (itree_monad F) M)
  (g : MONAD_MORPHISM (itree_monad G) M) :
MONAD_MORPHISM (itree_monad (F + G)) M := {|
  mmor := itree_from_coproduct M f g;
  mmor_continuous := itree_from_coproduct_is_continuous f g;
  mmor_strict := itree_from_coproduct_fbot f g;
  mmor_ret := itree_from_coproduct_fret f g;
  mmor_bind := itree_from_coproduct_fbind f g
|}.

Lemma itree_in_left_law
  (M : MONAD)
  (f : MONAD_MORPHISM (itree_monad F) M) (g : MONAD_MORPHISM (itree_monad G) M)
  (X : Type) (m1 : itree F X) :
itree_from_coproduct M f g (itree_in_left m1) = f X m1.
Proof.
change (
  ((@itree_from_coproduct M f g X) ° (@itree_in_left X)) m1 = f X m1).
apply corr_eq_reduce_to_compacts.
- apply comp_is_continuous.
  + apply itree_from_coproduct_is_continuous.
  + apply itree_in_left_is_continuous.
- apply (mmor_continuous f).
- cbn.
  clear.
  intro m1.
  change (finite_itree F X) in m1.
  induction m1 as [ | x | Y fy k IH] using (finite_itree_ind X).
  + unfold comp.
    change (inject (c := itree F X) Lcbot) with (@fbot F X).
    rewrite itree_in_left_fbot, itree_from_coproduct_fbot, mmor_strict.
    reflexivity.
  + unfold comp.
    rewrite inject_fpure, itree_in_left_fret, itree_from_coproduct_fret,
     mmor_ret.
    reflexivity.
  + unfold comp.
    rewrite inject_fimpure, itree_in_left_impure, itree_from_coproduct_impure.
    etransitivity.
    {
      apply f_equal2; [reflexivity | ].
      extensionality y.
      apply IH.
    }
    rewrite <- mmor_bind.
    cbn.
    unfold trigger.
    rewrite fbind_impure.
    do 2 apply f_equal.
    extensionality y.
    rewrite fbind_fret_left.
    reflexivity.
Qed.

Lemma itree_in_right_law
  (M : MONAD)
  (f : MONAD_MORPHISM (itree_monad F) M) (g : MONAD_MORPHISM (itree_monad G) M)
  (X : Type) (m2 : itree G X) :
itree_from_coproduct M f g (itree_in_right m2) = g X m2.
Proof.
change (
  ((@itree_from_coproduct M f g X) ° (@itree_in_right X)) m2 = g X m2).
apply corr_eq_reduce_to_compacts.
- apply comp_is_continuous.
  + apply itree_from_coproduct_is_continuous.
  + apply itree_in_right_is_continuous.
- apply (mmor_continuous g).
- cbn.
  clear.
  intro m2.
  change (finite_itree G X) in m2.
  induction m2 as [ | x | Y fy k IH] using (finite_itree_ind X).
  + unfold comp.
    change (inject (c := itree G X) Lcbot) with (@fbot G X).
    rewrite itree_in_right_fbot, itree_from_coproduct_fbot, mmor_strict.
    reflexivity.
  + unfold comp.
    rewrite inject_fpure, itree_in_right_fret, itree_from_coproduct_fret,
     mmor_ret.
    reflexivity.
  + unfold comp.
    rewrite inject_fimpure, itree_in_right_impure, itree_from_coproduct_impure.
    etransitivity.
    {
      apply f_equal2; [reflexivity | ].
      extensionality y.
      apply IH.
    }
    rewrite <- mmor_bind.
    cbn.
    unfold trigger.
    rewrite fbind_impure.
    do 2 apply f_equal.
    extensionality y.
    rewrite fbind_fret_left.
    reflexivity.
Qed.

Lemma itree_from_coproduct_unique
  (M : MONAD)
  (f : MONAD_MORPHISM (itree_monad F) M) (g : MONAD_MORPHISM (itree_monad G) M)
  (h : MONAD_MORPHISM (itree_monad (F + G)) M) :
(forall X m1, h X (itree_in_left m1) = f X m1) ->
(forall X m2, h X (itree_in_right m2) = g X m2) ->
forall X m, itree_from_coproduct M f g m = h X m.
Proof.
intros Hf Hg X m.
apply corr_eq_reduce_to_compacts.
- apply itree_from_coproduct_is_continuous.
- apply (mmor_continuous h).
- cbn.
  clear m.
  intro m.
  change (finite_itree (F + G) X) in m.
  induction m as [ | x | Y fgy k IH] using (finite_itree_ind X).
  + change (inject (c := itree (F + G) X) Lcbot) with (@fbot (F + G) X).
    rewrite itree_from_coproduct_fbot, mmor_strict.
    reflexivity.
  + rewrite inject_fpure, itree_from_coproduct_fret, mmor_ret.
    reflexivity.
  + rewrite inject_fimpure, itree_from_coproduct_impure.
    destruct fgy as [fy | gy].
    * rewrite <- Hf.
      unfold trigger.
      rewrite itree_in_left_impure, mmor_impure, bind_assoc, mmor_impure.
      etransitivity.
      {
        apply f_equal2; [reflexivity | ].
        extensionality y.
        rewrite itree_in_left_fret, mmor_ret, ret_left.
        apply IH.
      }
      reflexivity.
    * rewrite <- Hg.
      unfold trigger.
      rewrite itree_in_right_impure, mmor_impure, bind_assoc, mmor_impure.
      etransitivity.
      {
        apply f_equal2; [reflexivity | ].
        extensionality y.
        rewrite itree_in_right_fret, mmor_ret, ret_left.
        apply IH.
      }
      reflexivity.
Qed.

Program Definition itree_coproduct :
COPRODUCT (itree_monad F) (itree_monad G) := {|
  coproduct := itree_monad (F + G);
  in_left := itree_in_left_mmor;
  in_right := itree_in_right_mmor;
  from_coproduct := itree_from_coproduct_mmor;
  in_left_law := itree_in_left_law;
  in_right_law := itree_in_right_law;
  from_coproduct_unique := itree_from_coproduct_unique
|}.

End itreeCoproduct.

Arguments itree_in_left [_] _ [_] _.
Arguments itree_in_right _ [_ _] _.
