From Stdlib Require Import FunctionalExtensionality ProofIrrelevance Lia.
From Domain Require Export CPO Exp.


Definition is_prefixpoint{A : Poset} (f : A -> A)(x:A) :=
  f x <= x.


Definition is_least_prefixpoint{A : Poset} (f : A -> A)(x:A) :=
    is_prefixpoint f x /\ forall y, is_prefixpoint f y -> x <= y.


Definition is_fixpoint{X :Type} (f : X -> X) (x:X)
:= f x = x.


Definition is_least_fixpoint{X :Poset} (f : X -> X) (x:X) :=
    is_fixpoint f x /\ forall y, is_fixpoint f y -> x <= y.

Lemma is_least_prefixpoint_is_least_fixpoint
{X :Poset} (f : X -> X) (x:X):
is_monotonic f ->
is_least_prefixpoint f x -> is_least_fixpoint f x.
Proof.
intros Hm (Hp & Hmin).
split.
-
 apply antisym; auto.
 apply Hmin.
 apply Hm,Hp.
-
 intros y Hpre.
 apply Hmin.
 unfold is_fixpoint,is_prefixpoint in *.
 rewrite Hpre; apply refl.
 Qed. 



Fixpoint iterate{X: Type} (n : nat)(d:X) (f :  X -> X):=
    match n with 
    | S n' => f (iterate n' d f) 
    | 0 => d
    end.


Lemma iterate_mono_aux{X: CPO} : forall  n (f : X -> X),
    is_monotonic f -> 
    (iterate n bot f) <= (iterate (S n) bot f).
Proof.
induction n ; intros f Hm.
-
  apply bot_least.
-
  cbn.
  now apply Hm, IHn.
Qed.  


Lemma iterate_mono{X: CPO} : forall  n m (f : X -> X),
    is_monotonic f -> 
    (n <= m)%nat -> 
    (iterate  n bot f) <= (iterate m bot f).
Proof.
intros n m f Hm  Hle.
induction Hle.
-
 apply refl.
-
 eapply trans; eauto.
 now apply iterate_mono_aux.
Qed. 


Lemma iterate_directed{X: CPO} : forall (f : X -> X),
is_monotonic f -> 
is_directed (fun x => exists n, x = iterate n bot f ).
Proof.
intros f Hm.
split.
-
 apply not_empty_member.
 exists bot.
 now exists 0.
-
 intros x y Hmx Hmy.
 destruct Hmx as (n & Heq); subst.
 destruct Hmy as (m & Heq); subst.
 exists (iterate (max n m) bot f); repeat split.
 +
   now exists (max n m).
 +
   apply iterate_mono; auto.
   apply PeanoNat.Nat.le_max_l.
 +
   apply iterate_mono; auto.
   apply PeanoNat.Nat.le_max_r.
Qed.   

Definition ffix{X:CPO}(f : X -> X) :=
lub (fun x => exists n, x = iterate n bot f ).

Lemma ffix_fixpoint{X:CPO}(f : X -> X)(Hc:is_continuous f):
  is_fixpoint f (ffix f ).
Proof.
  unfold is_fixpoint,ffix.
  remember (iterate_directed f
  (continuous_implies_monotonic _ Hc)) as Hd.
  specialize (lub_is_lub _  Hd) as Hl.
  specialize 
  (continuous_implies_commutes_with_lub _ Hc _ _
  Hd Hl) as Hcl.
  assert ( Hd' : is_directed (fmap
  (fun x : X =>
   exists n : nat, x = iterate n bot f ) f))
  by
   (apply monotonic_directed; auto;
   now apply continuous_implies_monotonic).
  apply is_lub_lub_eq1 in Hcl; auto.
  rewrite Hcl.
  apply antisym; auto.
  -
   apply forallex_lelub; auto.
   intros x Hmx.
   destruct Hmx as (y & (n & Heq) & Heq'); 
   subst.
   exists (iterate (S n) bot f);split; [| apply refl].
   now exists (S n).
  -
   apply forallex_lelub; auto.
   intros x (n & Heq); subst.
   exists (iterate (S n) bot f); split.
   +
     exists (iterate n bot f); split; auto.
     now exists n.
   +
    apply iterate_mono_aux.
    now apply continuous_implies_monotonic.
Qed.  

Lemma ffix_fixpoint_eq{X:CPO}(f : X -> X)(Hc:is_continuous f):
  f (ffix f) = ffix f.
Proof.
now apply ffix_fixpoint.
Qed.

Lemma lub_iter_prefix_is_least_aux{A:CPO} : forall n (G: A -> A) 
(a a':A),
is_monotonic G -> is_prefixpoint G a' -> 
iterate n bot G  <= a'.
Proof.
induction n ; intros G a a' Hm Hf; [apply bot_least|].
cbn.
unfold is_prefixpoint in Hf.
specialize (IHn _ a a' Hm Hf).
apply trans with (y := G a'); auto.
Qed.


Lemma lub_iter_prefix_is_least{A:CPO}: forall (F: A -> A) l,
is_monotonic F ->
is_lub (P:= A) (fun x => exists n, x = iterate n bot F) l ->
is_prefixpoint F l ->
is_least_prefixpoint F l.
Proof.
intros F l Hm Hl Hf.
split; auto.
intros a' Hf'.
assert (Hup : is_upper ((fun x : A =>
exists n : nat,
  x = iterate n bot F)) a').
{
 intros y (n & Heq); subst.
 now apply lub_iter_prefix_is_least_aux.
}
destruct Hl as (_ & Hmin).
now apply Hmin.
Qed.


Lemma StrongKleene{A:CPO}(f : A ->A )(Hc : is_continuous f) :
is_least_prefixpoint f 
 (ffix f).
Proof. 
split.
 - 
  apply ffix_fixpoint in Hc.
  unfold is_fixpoint,is_prefixpoint in *.
  rewrite Hc.
  apply refl.
 -
  apply lub_iter_prefix_is_least.
  +
    now apply continuous_implies_monotonic.
  +
    apply lub_is_lub.
    apply iterate_directed.
    now apply continuous_implies_monotonic.
  +
   apply ffix_fixpoint in Hc.
   unfold is_fixpoint,is_prefixpoint in *.
   rewrite Hc.
   apply refl.
Qed.   


Lemma Kleene{A:CPO}(f : A ->A )(Hc : is_continuous f) :
  is_least_fixpoint f 
   (ffix f).
Proof.
apply is_least_prefixpoint_is_least_fixpoint.
-
 now apply continuous_implies_monotonic.
-
 now apply StrongKleene. 
Qed.   



Definition is_nat_mono(f:nat -> nat):=
  forall n m, (n <= m)%nat -> (f n <= f m)%nat.


Definition is_above_diag(f:nat -> nat):=
    forall n, (n <= f n)%nat.
  

Definition ffix_subset{X:CPO}(f : X -> X) 
(h: nat -> nat) :=
lub (fun x => exists n, x = iterate (h n) bot f ).

Lemma iterate_subset_directed{X: CPO}(f: X -> X)
(h: nat -> nat) :
is_monotonic f ->
is_above_diag h ->
is_directed
  (fun x : X =>
   exists n : nat,
     x = iterate (h n) bot f).
Proof.
intros Hm Hh.
split.
-
 rewrite not_empty_member.
 exists (iterate (h 0) bot f).
 now exists 0.
-
intros x y (u & Hmu) (v & Hmv);subst.
eexists (iterate (max (h (h u)) (h (h v))) bot f).
repeat split.
+
 destruct
 (PeanoNat.Nat.max_spec_le (h (h u)) (h (h v)))
 as [ (Ho  & Heq) | ( Ho & Heq) ]; rewrite Heq;
 eexists; eauto.
+
 apply iterate_mono; [assumption |].
 destruct
 (PeanoNat.Nat.max_spec_le (h (h u)) (h (h v)))
 as [ (Ho  & Heq) | ( Ho & Heq) ]; rewrite Heq.
 * eapply PeanoNat.Nat.le_trans; eauto.
 * apply Hh.
+
apply iterate_mono; [assumption |].
destruct
 (PeanoNat.Nat.max_spec_le (h (h u)) (h (h v)))
 as [ (Ho  & Heq) | ( Ho & Heq) ]; rewrite Heq.
* apply Hh.
* eapply PeanoNat.Nat.le_trans; eauto.
Qed.



Lemma ffix_subset_enough{X:CPO}(f:X -> X)
(h: nat -> nat):
is_monotonic f ->
is_above_diag h ->
ffix f = ffix_subset f h.
Proof.
intros Hm Ha.
apply antisym.
-
apply forallex_lelub.
+
 apply iterate_directed;auto.
+
apply iterate_subset_directed;auto.
+
intros x (n & Hn);subst.
exists (iterate (h n) bot f);split.
*
 now exists n.
*
 apply iterate_mono;auto.
-
 apply forallex_lelub.
 +
 apply iterate_subset_directed;auto.
 +
 apply iterate_directed;auto.
 +
 intros x (n & Hn);subst.
 exists (iterate (h n) bot f);split; [| apply refl].
 now exists (h n).
Qed.


Definition ffix_suffix{X:CPO}(f : X -> X) 
(m:nat) :=
lub (fun x => exists n, (m <= n)%nat /\ x = iterate n bot f ).

Lemma iterate_suffix_directed{X: CPO}(f: X -> X)
(m:nat) :
is_monotonic f ->
is_directed
  (fun x : X =>
   exists n : nat, (m <= n)%nat /\
     x = iterate n bot f).
Proof.
intro Hm.
split.
-
 rewrite not_empty_member.
 exists (iterate m bot f).
 now exists m.
-
intros x y (u & Hleu & Hmu) (v & Hlev & Hmv);subst.
exists (iterate (max u v) bot f).
repeat split.
+
 exists (max u v); split; [lia |reflexivity].
+
 apply iterate_mono; [assumption | lia].
+
 apply iterate_mono; [assumption | lia].
Qed.


Lemma ffix_suffix_enough{X:CPO}(f:X -> X)
(m:nat):
is_monotonic f ->
ffix f = ffix_suffix f m.
Proof.
intro Hm.
unfold ffix, ffix_suffix.
apply antisym.
{
  apply forallex_lelub; [now apply iterate_directed | now apply iterate_suffix_directed |].
  intros x (n & Hn); subst.
  eexists.
  split.
  -
   exists (max n m); split; [lia|reflexivity].
  - 
   apply iterate_mono; auto; lia. 
}
{
  apply forallex_lelub; [now apply iterate_suffix_directed| now apply iterate_directed |].
  intros x (n & Hnm & Heq); subst.
  eexists.
  split.
  -
   exists n;reflexivity.
  - 
   apply refl.
}
Qed.


Lemma iterate_sum{X:CPO}(n m : nat)(f : X -> X):
iterate  (n+m) bot f = iterate  n (iterate m bot f) f.
Proof.
induction n; auto.
replace (S n + m) with (S (n +m)) by lia.
cbn.
now rewrite IHn.
Qed.

Lemma iterate_mono_func{X:CPO}(n : nat)(f f' : X -> X):
ord (p := EXP_Poset _ _) f f' ->
is_monotonic f ->
is_monotonic f' ->
ord (p := X)  
(iterate n bot f) (iterate n bot f').
Proof.
intros Hle Hm Hm'.
induction n; [apply refl |].
cbn.
eapply trans.
-
 apply Hm,IHn.
-
 apply Hle.
Qed.