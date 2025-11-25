From Stdlib Require Import Classical  List.
From Domain Require Export Setof.
Import ListNotations.


Definition is_finite{T: Type}(S: Setof T) : Prop :=
    exists (l : list T), forall x, member S x -> In x l.

Lemma is_finite_iff{T: Type}(S: Setof T): 
is_finite S -> exists l, NoDup l /\ forall x, member S x <-> In x l.
Proof.
intros (l & Ha).
revert S Ha.
induction l; intros S Ha.
-
  exists []; split; auto; constructor; [apply (Ha x) |].
  intro Habs; destruct Habs.
-
  destruct (oracle (In a l)) as [Hl | Hr].
  +
   apply IHl.
   intros x Hmx.
   destruct (Ha _ Hmx) ; subst; auto.
  +
  assert (Ha' :  forall x : T,
  member (remove S a) x -> In x l).
  {
    intros x (Hmx & Hneq).
    destruct (Ha _ Hmx); subst; auto.
    now contradict Hneq.
  }
  specialize (IHl _ Ha').
  destruct IHl as (l' & (Hnd & Heqv)).
  destruct (oracle (member S a)) as [Hm | Hnm].
  *
    exists (a :: l').
    split; [constructor; auto |].
    -- intro Hinl'; apply Hr.
       apply Ha'.
       now rewrite Heqv.
    --
      split; intro Hmx.
      ++ 
      destruct (oracle ( x = a)); subst; [now constructor|constructor 2].
      rewrite <- Heqv.
      split; auto.
      ++
      inversion Hmx; subst; auto.
      rewrite <- Heqv in H.
      now destruct H.
  *
   rewrite not_member_remove_eq in Heqv; auto.
   now exists l'.
 Qed.  
  

Lemma is_finite_subset{T:Type}(S S' : Setof T) : 
is_finite S' -> subset S S' -> is_finite S.
Proof.
intros (l & Ha) Hs.
exists l.
intros x Hmx.
specialize (Hs _ Hmx).
now apply Ha.
Qed.

Definition is_finite_type(T: Type) : Prop :=
  exists (l : list T), forall x, In x l.

Lemma is_finite_type_iff(T: Type): is_finite_type T <-> is_finite (fun x: T => True).
Proof.
split; intro Hf.
-
  destruct Hf as (l & Ha).
  now exists l.
-
  destruct Hf as (l & Ha).
  exists l.
  intro x.
  apply Ha.
  now unfold member.
Qed.
     

Lemma finite_type_all_sets_finite{T:Type} : 
is_finite_type T -> forall (S:Setof T), is_finite S.
Proof.
intros Hft S.
rewrite is_finite_type_iff in Hft.
apply is_finite_subset with (S := S) in Hft; auto.
now intros x Hmx.
Qed.


