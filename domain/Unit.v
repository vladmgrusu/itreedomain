From Stdlib Require Import Classical IndefiniteDescription.
From Domain Require Export Discrete.


Definition UNIT_Poset : Poset :=
{|
  carrier :=  unit;
  default := tt;
  ord := discrete_le;
  refl := discrete_le_refl;
  trans := discrete_le_trans;
  antisym := discrete_le_antisym
|}.

    
(**
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
 *)

Lemma unit_lub(T: Setof unit):
is_directed (P :=(UNIT_Poset)) T -> 
 {x : unit | is_lub (P :=(UNIT_Poset )) T x}.
Proof.
intro Hd.
rewrite  (@discrete_directed _ tt) in Hd; subst.
apply constructive_indefinite_description.
destruct Hd as (y & Heq);subst.
exists y.
apply @is_lub_single.
Qed.


Program Definition UNIT_DCPO : DCPO :=
    {|
      dcpo_poset := UNIT_Poset;
      lub  := fun S => tt
    |}.
    
Next Obligation.
apply unit_lub in H.
destruct H; now destruct x.
Qed. 



Program Definition UNIT_CPO : CPO :=
    {|
      dcpo_cpo := UNIT_DCPO;
      bot  := tt
    |}.
    
Next Obligation.
destruct x.
constructor.
Qed. 