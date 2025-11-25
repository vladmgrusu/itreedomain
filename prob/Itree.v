From Itree Require Export Denote.
From Prob Require Export  Prob.

Local Open Scope R_scope.

Inductive prob_effect : Type -> Type :=
| Flip : Bounded 0 1 -> prob_effect bool.

Definition denote_prob_effect
  [X Y : Type] (fy : prob_effect Y) (k : Y -> prob_monad X) : prob_monad X :=
match fy in prob_effect Y return (Y -> prob_monad X) -> prob_monad X with
| Flip p => fun k => do b <- flip p; k b
end k.
 

Lemma denote_prob_effect_is_monotonic [X Y : Type]
 (fy : prob_effect Y) :
@is_monotonic (EXP_Poset _ _) _ (@denote_prob_effect X _ fy).
Proof.
intros u v Hle.
cbn.
intro f.
unfold denote_prob_effect.
destruct fy.
cbn in *.
destruct b as (b & Hbl & Hbh).
cbn in *.
specialize (Hle true f) as Ht.
specialize (Hle false f) as Hf.
nra.
Qed.


Lemma denote_prob_effect_is_continuous [X Y : Type] (fy : prob_effect Y) :
@is_continuous (EXP_DCPO _ _) _ (@denote_prob_effect X _ fy).
Proof.
intros K Hd.
assert (HdK : is_directed
(fmap K (denote_prob_effect fy))).
{
  apply monotonic_directed; auto;
  apply denote_prob_effect_is_monotonic.
}
split; auto.
unfold denote_prob_effect.
destruct fy.
cbn -[lub].
specialize (cont_bind_is_continuous_snd 
(Y := X) (flip b)) as Hcs.
unfold is_continuous in Hcs.
cbn in K.
unfold cont_functor in Hcs.
cbn -[lub] in Hcs.
destruct (Hcs _ Hd) as (Hd' & Heq).
replace ((fun b0 : bool =>
@lub
  (EXP_DCPO _
     (CONT_DCPO
        (EXP_DCPO _
           (Bounded_DCPO _))
        (Bounded_DCPO _)))
  K b0))  with
(lub (d := EXP_DCPO _ (CONT_DCPO _ _) ) K).
{
 rewrite Heq.
 reflexivity.
}
cbn.
extensionality d.
destruct oracle.
-
 apply CONT_equal.
 reflexivity.
-
 contradict n.
 now apply directed_proj.
Qed.  

Lemma denote_prob_effect_bind [X Y Z : Type] (fz : prob_effect Z)
  (m : Z -> prob_monad X) (f : X -> prob_monad Y) :
denote_prob_effect fz (fun z => do x <- m z; f x) =
do x <- denote_prob_effect fz m; f x.
Proof.
destruct fz.
cbn [denote_prob_effect].
rewrite bind_assoc.
reflexivity.
Qed.

Definition denote_prob [X : Type] (m : itree prob_effect X) : prob_monad X :=
denote_monad
  prob_effect prob_monad denote_prob_effect denote_prob_effect_is_continuous
  X m.

Definition denote_prob_mmor :
MONAD_MORPHISM (itree_monad prob_effect) prob_monad :=
denote_monad_mmor
  prob_effect prob_monad denote_prob_effect denote_prob_effect_bind
  denote_prob_effect_is_continuous.

Definition fflip (p : Bounded 0 1) : itree_monad prob_effect bool :=
trigger (Flip p).

Example flip_while_true (p : Bounded 0 1) : itree_monad prob_effect unit :=
While fflip p {{
  ret _ tt
}}.
