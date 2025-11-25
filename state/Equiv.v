From Itree Require Export Equiv.
From StateT Require Export Itree.

Section Equiv.

Variable S : Type.

Inductive stateT_step :
  forall [X], itree (stateT_effect S) X -> itree (stateT_effect S) X -> Prop :=
| fput_fput : forall s s', stateT_step (fput s;; fput s') (fput s')
| fput_fget : forall s, stateT_step (fput s;; fget) (fput s;; fret s)
| fget_fput : stateT_step (do x <- fget; fput x) (fret tt)
| fget_fget : forall X (f : S -> S -> itree (stateT_effect S) X),
  stateT_step (do x <- fget; do y <- fget; f x y) (do x <- fget; f x x).

Definition stateT_equiv [X : Type] (m1 m2 : itree (stateT_effect S) X) :
Prop :=
itree_equiv (stateT_effect S) stateT_step m1 m2.

Local Notation "m1 == m2" := (itree_equiv (stateT_effect S) stateT_step m1 m2)
 (at level 70, m2 at next level, no associativity).

Lemma equiv_fput_fput (s s' : S) : fput s;; fput s' == fput s'.
Proof.
apply itree_step, fput_fput.
Qed.

Lemma equiv_fput_fget (s : S) :fput s;; fget == fput s;; fret s.
Proof.
apply itree_step, fput_fget.
Qed.

Lemma equiv_fget_fput : do x <- fget; fput x == fret tt.
Proof.
apply itree_step, fget_fput.
Qed.

Lemma equiv_fget_fget (X : Type) (f : S -> S -> itree (stateT_effect S) X) :
do x <- fget; do y <- fget; f x y == do x <- fget; f x x.
Proof.
apply itree_step, fget_fget.
Qed.

Variable M : MONAD.

Lemma stateT_step_correct (X : Type) (m1 m2 : itree (stateT_effect S) X) :
stateT_step m1 m2 -> denote_stateT M m1 = denote_stateT M m2.
Proof.
intro Hstep.
destruct Hstep as [s1 s2 | s | | X f].
- rewrite denote_stateT_fbind, denote_fput, denote_fput, put_put.
  reflexivity.
- rewrite denote_stateT_fbind, denote_stateT_fbind, denote_fput, denote_fget,
   denote_stateT_fret, put_get.
  reflexivity.
- rewrite denote_stateT_fbind, denote_fget, denote_stateT_fret.
  etransitivity.
  {
    apply f_equal.
    extensionality s.
    apply denote_fput.
  }
  apply get_put.
- rewrite denote_stateT_fbind, denote_stateT_fbind, denote_fget.
  etransitivity.
  {
    apply f_equal.
    extensionality s.
    rewrite denote_stateT_fbind, denote_fget.
    reflexivity.
  }
  apply get_get.
Qed.

Lemma stateT_equiv_correct (X : Type) (m1 m2 : itree (stateT_effect S) X) :
m1 == m2 -> denote_stateT M m1 = denote_stateT M m2.
Proof.
apply itree_equiv_correct.
-
 intros.
 apply denote_stateT_effect_bind.
-
apply stateT_step_correct.
Qed.

End Equiv.

(**
Lemma fput_fbind_is_monotonic_snd{X:Type}:
forall (n:X),
is_monotonic 
(fun k : itree_monad (stateT_effect X) unit => fput n;; k).
Proof.
intros n u v Hle.
specialize (@fbind_is_continuous_snd  (stateT_effect X) unit unit (fput n)) as Hcs.
apply continuous_implies_monotonic in Hcs.
apply Hcs.
now intros [].
Qed.

Lemma fput_fbind_is_continuous_snd{X:Type}:
forall (n:X),
is_continuous (fun k : itree_monad (stateT_effect X) unit => fput n;; k).
Proof.
intros n S Hd.
specialize (@fbind_is_continuous_snd  (stateT_effect X) unit unit (fput n)) as Hcs.
split.
{
  apply monotonic_directed; auto.
  apply fput_fbind_is_monotonic_snd.
}
remember (fmap S (fun x  => (fun _:unit => x))) as S'.
assert (HS': is_directed (P := EXP_Poset _ _) S').
{
  subst.
  apply 
   (monotonic_directed (P2 := EXP_Poset _ _)); auto.
  now intros u v Hle [].
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
destruct x.
rewrite <- fmap_comp.
unfold comp.
now rewrite fmap_id.
Qed.
*)
