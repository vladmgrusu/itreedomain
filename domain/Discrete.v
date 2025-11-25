From Stdlib Require Import Classical IndefiniteDescription.
From Domain Require Export CPO.

Definition discrete_le{A:Type} : A -> A -> Prop := eq.


Lemma discrete_le_refl{A:Type} (a:A): discrete_le a a.
Proof.
reflexivity.
Qed.

Lemma discrete_le_trans{A:Type} (a a' a'': A):
    discrete_le a a' -> discrete_le a' a'' -> discrete_le a a''.
Proof.
intros Hle1 Hle2.
etransitivity;eauto.
Qed.

Lemma discrete_le_antisym{A:Type} (a a': A):
discrete_le a a' -> discrete_le a' a -> a = a'.
Proof.
intros Hleq _; assumption.
Qed.

Definition discrete_Poset (A:Type)(a:A) : Poset :=
{|
  carrier :=  A;
  default := a;
  ord := discrete_le;
  refl := discrete_le_refl;
  trans := discrete_le_trans;
  antisym := discrete_le_antisym
|}.

    

Lemma discrete_directed{A:Type}(a:A)(T:Setof A):
 is_directed (P := discrete_Poset A a) T <-> (exists x, T = single x).
Proof.
split; intro Hs.
-
  destruct Hs as (Hne & Hd).
  rewrite not_empty_member in Hne.
  destruct Hne as (y & Hmy).
  cbn in y.
  exists y.
  apply set_equal; intro u; split; intro Hmu.
  +
   rewrite member_single_iff.
   specialize (Hd _ _ Hmy Hmu).
   destruct Hd as (z & Hmz & He1 & He2).
   etransitivity;eauto.
  +
   rewrite member_single_iff in Hmu; now subst.   
 -
   destruct Hs as (x & Hx);subst.
   split.
   +
    apply single_not_empty.
   +
    intros u v Hmu Hmv.
    rewrite member_single_iff in Hmu,Hmv; subst.
    exists x; repeat split; reflexivity.
 Qed.      

Lemma discrete_lub{A:Type}(a:A)(T: Setof A):
is_directed (P :=(discrete_Poset A a)) T -> 
 {x : A | is_lub (P :=(discrete_Poset A a)) T x}.
Proof.
intro Hd.
rewrite  discrete_directed in Hd; subst.
apply constructive_indefinite_description.
destruct Hd as (y & Heq);subst.
exists y.
apply @is_lub_single.
Qed.



Program Definition discrete_DCPO (A:Type)(a:A) : DCPO :=
    {|
      dcpo_poset := discrete_Poset A a;
      lub  := fun S => match (oracle (is_directed S))
      with
        left Hd =>  proj1_sig (discrete_lub a S Hd)
      | right _ => a end
    |}.
    
Next Obligation.
cbn.
intros.
destruct
     (oracle
       (is_directed  (P := discrete_Poset A a) S)) ; [| contradiction].

now destruct (discrete_lub a S i).
Qed. 




Lemma from_discrete_mono{A:Type}{B:DCPO} (a:A)
(f : A -> B): is_monotonic (P1 := discrete_Poset _ a) f.
Proof.
intros u v Hle.
inversion Hle; subst; apply refl.
Qed.

Lemma from_discrete_cont{A:Type}{B:DCPO} (a:A)
(f : A -> B): is_continuous (P1 := discrete_DCPO _ a) f.
Proof.
apply continuous_alt_implies_continuous;
[apply from_discrete_mono | ].
intros K Hd.
apply  discrete_directed in Hd.
destruct Hd as (x & Hk); subst.
split.
-
 rewrite fmap_single.
 apply single_is_directed.
-
 rewrite fmap_single, lub_single.
 rewrite (lub_single (D := discrete_DCPO _ a)).
 apply refl.
Qed.