From Stdlib Require Import PropExtensionality.

From Monad Require Export Iter.
From Itree Require Export Monad.

Local Close Scope nat_scope.

Definition denote_monad
  (F : Type -> Type) (M : MONAD)
  (g : forall X Y, F Y -> (Y -> M X) -> M X)
  (Hcont : forall X Y fy, @is_continuous (EXP_DCPO _ _) _ (g X Y fy))
  (X : Type) (m : itree F X) :
M X :=
ffold (@ret M X) (g X) (Hcont X) m.

Lemma denote_monad_is_continuous
  (F : Type -> Type) (M : MONAD)
  (g : forall X Y, F Y -> (Y -> M X) -> M X)
  (Hcont : forall X Y fy, @is_continuous (EXP_DCPO _ _) _ (g X Y fy))
  (X : Type) :
is_continuous (denote_monad F M g Hcont X).
Proof.
apply ffold_is_continuous.
Qed.

Lemma denote_monad_fbot
  (F : Type -> Type) (M : MONAD)
  (g : forall X Y, F Y -> (Y -> M X) -> M X)
  (Hcont : forall X Y fy, @is_continuous (EXP_DCPO _ _) _ (g X Y fy))
  (X : Type) :
denote_monad F M g Hcont X fbot = bot.
Proof.
apply ffold_fbot.
Qed.

Lemma denote_monad_fret
  (F : Type -> Type) (M : MONAD)
  (g : forall X Y, F Y -> (Y -> M X) -> M X)
  (Hcont : forall X Y fy, @is_continuous (EXP_DCPO _ _) _ (g X Y fy))
  (X : Type) (x : X) :
denote_monad F M g Hcont X (fret x) = ret M x.
Proof.
apply ffold_pure.
Qed.

Lemma denote_monad_impure
  (F : Type -> Type) (M : MONAD)
  (g : forall Y Z, F Z -> (Z -> M Y) -> M Y)
  (Hcont : forall Y Z fz, @is_continuous (EXP_DCPO _ _) _ (g Y Z fz))
  (X Y : Type) (fx : F X) (k : X -> itree F Y) :
denote_monad F M g Hcont Y (impure fx k) =
g Y X fx (fun x => denote_monad F M g Hcont Y (k x)).
Proof.
unfold denote_monad at 1.
rewrite ffold_impure.
reflexivity.
Qed.

Lemma denote_monad_fbind
  (F : Type -> Type) (M : MONAD)
  (g : forall Y Z, F Z -> (Z -> M Y) -> M Y)
  (Hg : forall X Y Z fz m (f : X -> M Y),
     g Y Z fz (fun z => do x <- m z; f x) =
     do x <- g X Z fz (fun z => m z); f x)
  (Hcont : forall Y Z fz, @is_continuous (EXP_DCPO _ _) _ (g Y Z fz))
  (X Y : Type) (m : itree F X) (h : X -> itree F Y) :
denote_monad F M g Hcont Y (fbind m h) =
do x <- denote_monad F M g Hcont X m;
denote_monad F M g Hcont Y (h x).
Proof.
change (
  comp
    (denote_monad F M g Hcont Y)
    (fun m => fbind m h)
    m =
  comp
    (fun m => do x <- m; denote_monad F M g Hcont Y (h x))
    (denote_monad F M g Hcont X)
    m
).
apply corr_eq_reduce_to_compacts.
- apply comp_is_continuous.
  + apply denote_monad_is_continuous.
  + apply fbind_is_continuous_fst.
- apply comp_is_continuous.
  + apply bind_continuous_fst.
  + apply denote_monad_is_continuous.
- cbn.
  clear m.
  intro m.
  change (finite_itree F X) in m.
  induction m as [ | x | Z fz k IH] using (finite_itree_ind X).
  + unfold comp.
    change (inject (c := itree F X) Lcbot) with (@fbot F X).
    rewrite fbind_fbot, denote_monad_fbot, denote_monad_fbot, bind_strict.
    reflexivity.
  + unfold comp.
    rewrite inject_fpure, fbind_fret_left, denote_monad_fret, ret_left.
    reflexivity.
  + unfold comp in IH |- *.
    rewrite inject_fimpure, fbind_impure, denote_monad_impure,
     denote_monad_impure.
    etransitivity.
    {
      apply f_equal.
      extensionality z.
      apply IH.
    }
    apply Hg.
Qed.

Program Definition denote_monad_mmor
  (F : Type -> Type) (M : MONAD)
  (g : forall X Y, F Y -> (Y -> M X) -> M X)
  (Hg : forall X Y Z fz m (f : X -> M Y),
     g Y Z fz (fun z => do x <- m z; f x) =
     do x <- g X Z fz (fun z => m z); f x)
  (Hcont : forall X Y fy, @is_continuous (EXP_DCPO Y (M X)) (M X) (g X Y fy)) :
MONAD_MORPHISM (itree_monad F) M := {|
  mmor := denote_monad F M g Hcont;
  mmor_continuous := denote_monad_is_continuous F M g Hcont;
  mmor_strict := denote_monad_fbot F M g Hcont;
  mmor_ret := denote_monad_fret F M g Hcont;
  mmor_bind := denote_monad_fbind F M g Hg Hcont
|}.

Lemma denote_monad_if
  (F : Type -> Type) (M : MONAD)
  (g : forall X Y, F Y -> (Y -> M X) -> M X)
  (*Hg : forall X Y Z fz m (f : X -> M Y),
     g Y Z fz (fun z => do x <- m z; f x) =
     do x <- g X Z fz (fun z => m z); f x*)
  (Hcont : forall X Y fy, @is_continuous (EXP_DCPO _ _) _ (g X Y fy))
  (X : Type) (b : bool) (m1 m2 : itree_monad F X) :
denote_monad F M g Hcont X (if b then m1 else m2) =
if b then denote_monad F M g Hcont X m1 else denote_monad F M g Hcont X m2.
Proof.
destruct b; reflexivity.
Qed.

Lemma denote_monad_iter
  (F : Type -> Type) (M : MONAD)
  (g : forall Y Z, F Z -> (Z -> M Y) -> M Y)
  (Hg : forall X Y Z fz m (f : X -> M Y),
     g Y Z fz (fun z => do x <- m z; f x) =
     do x <- g X Z fz (fun z => m z); f x)
  (Hcont : forall Y Z fz, @is_continuous (EXP_DCPO _ _) _ (g Y Z fz))
  (Y : Type) (m: itree F (unit + Y)) :
denote_monad F M g Hcont Y (iter (itree_monad F) m) =
iter M (denote_monad F M g Hcont (unit + Y) m) .
Proof.
change (denote_monad F M g Hcont Y ?m)
 with (mmor (denote_monad_mmor F M g Hg Hcont) Y m).
apply mmor_iter.
Qed.

Lemma denote_monad_while
  (F : Type -> Type) (M : MONAD)
  (g : forall X Y, F Y -> (Y -> M X) -> M X)
  (Hg : forall X Y Z fz m (f : X -> M Y),
     g Y Z fz (fun z => do x <- m z; f x) =
     do x <- g X Z fz (fun z => m z); f x)
  (Hcont : forall X Y fy, @is_continuous (EXP_DCPO _ _) _ (g X Y fy))
  (cond : itree_monad F bool) (body : itree F unit) :
denote_monad F M g Hcont unit (While cond {{ body }}) =
While (denote_monad F M g Hcont bool cond) {{
  denote_monad F M g Hcont unit body
}}.
Proof.
unfold while.
rewrite denote_monad_iter; [ | exact Hg].
f_equal.
rewrite denote_monad_fbind; [ | exact Hg].
f_equal.
extensionality b.
destruct b.
- rewrite denote_monad_fbind; [ | exact Hg].
  rewrite denote_monad_fret.
  reflexivity.
- apply denote_monad_fret.
Qed.
