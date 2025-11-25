From Stdlib Require Import IndefiniteDescription FunctionalExtensionality
 PropExtensionality List Lia.
From Domain Require Export Setof.


Global Set Primitive Projections.
Global Set Printing Primitive Projection Parameters.

(* only nonempty posets*)
Record Poset : Type :=
{
carrier :> Type;
default: carrier;
ord : carrier -> carrier -> Prop;
refl : forall x, ord x x;
trans : forall x y z, ord x y -> ord y z ->
   ord x z;
antisym : forall x y, ord x y -> ord y x -> x = y;
}.


Arguments carrier {_}.
Arguments default {_}.
Arguments ord {_} _ _.
Arguments refl {_} _.
Arguments trans {_} _ _ _ _ _.
Arguments antisym {_} _ _ _ _.


Infix "<=" := (@ord _) (at level 70, no associativity).


Definition is_upper {P : Poset} (S : Setof P) (x : P) : Prop :=
  forall (y:P), member S y -> ord y x.


Definition is_lub {P : Poset} (S : Setof P) (x : P) : Prop :=
  is_upper S x /\ forall y, is_upper S y -> ord  x  y.

Lemma is_lub_unique {P : Poset} (S : Setof P): forall x y,
    is_lub S x -> is_lub S y -> x = y.
Proof.
intros x y (Hux & Hlx) (Huy & Hly).
apply antisym.
-
  apply Hlx, Huy.
-
  apply Hly, Hux.
Qed.


Definition is_directed {P : Poset} (S : Setof P):=
  ~is_empty S /\
  forall x y, member S x -> member S y -> exists z,
                  member S z /\ x <= z /\ y <= z. 
  
Definition is_dclosed{P : Poset} (S : Setof P):=
  forall x, member S x -> forall y, y <= x -> member S y.

Definition dclosure {P : Poset} (S : Setof P):=
  fun x => exists y, member S y /\ x <= y.


Lemma dclosure_is_dclosed{P : Poset} : forall (S: Setof P), is_dclosed (dclosure S).
  Proof.
  intros S x Hm y Hle.  
  destruct Hm as (z & Hmz & Hlez).
  exists z; split; auto; eapply trans; eauto.
  Qed.


  Lemma dclosure_is_directed{P:Poset}:
  forall (S: Setof P), is_directed S -> is_directed (dclosure S).
Proof.
intros S (Hne & Hd).
apply not_empty_member in Hne.
split.
-
  apply not_empty_member.
  destruct Hne as (x & Hm).
  do 2 exists x; split; auto.
  apply refl.  
- 
  intros x y Hmx Hmy.
  destruct Hmx as (x' & Hmx' & Hlex').
  destruct Hmy as (y' & Hmy' & Hley').
  specialize (Hd _ _ Hmx' Hmy').
  destruct Hd as (z & Hmz & Hlex'z & Hley'z).
  exists z; repeat split; try now (eapply trans; eauto).
  exists z; split; auto.
  apply refl.
Qed.

Lemma is_lub_dclosure{P:Poset}:
  forall (S: Setof P) l,
    is_lub S l <-> is_lub (dclosure S) l.
Proof.
split; intro Hl.
-
  split.
  + 
    intros w Hm.
    destruct Hm as (x & Hmx & Hlex).
    destruct Hl as (Hu & _).
    specialize (Hu _ Hmx).
    eapply trans; eauto.
  +
    intros y Huy.
    destruct Hl as (Hu & Hmm).
    apply Hmm.
    intros z Hmz.
    apply Huy.
    exists z; split ; auto.
    apply refl.
-
  split.
  +   
    intros w Hm.
    destruct Hl as (Hu & _).
    apply Hu.
    exists w; split; auto.
    apply refl.
  +
    intros z Hmz.
    destruct Hl as ( Hu & Hmm).
    apply Hmm.
    intros x Hmx.
    destruct Hmx as (x' & Hmx' & Hlex').
    specialize (Hmz _ Hmx').
    eapply trans; eauto.
Qed.

Lemma single_is_directed{P : Poset}: forall  (x : P),
    is_directed (single  x).
Proof.
intros x.
split.
- 
 apply single_not_empty.
-
  intros y z Hmy Hmz.
  rewrite member_single_iff in *; subst.
  exists x; repeat split; try (apply refl).
Qed.

Lemma is_lub_single{P:Poset}: forall (x:P),
    is_lub(single x) x.
Proof.
intro x.
split.
- 
  intros y Hm.
  rewrite member_single_iff in Hm;  subst.
  apply refl.
-
  intros y Hu.
  apply Hu.
  apply member_single.
Qed.

Lemma ordered_pair_is_directed{P : Poset} : forall (x y : P),
 x <= y -> is_directed (fun z => z = x \/ z = y).   
Proof.
intros x y Hle.
split.  
-
  rewrite not_empty_member.
  exists x; now left.
-
  intros x' y' Hm1 Hm2.
  destruct Hm1, Hm2; subst.
  +
    exists y; repeat split; auto.
    now right.
  +
    exists y; repeat split; auto ; try apply refl.
    now right.
  +
     exists y; repeat split; auto ; try apply refl.
     now right.
  +
      exists y; repeat split; auto ; try apply refl.
      now right.
Qed.


Lemma ordered_pair_has_lub{P:Poset}: forall (x y : P),
    x <= y -> is_lub (fun z => z = x \/ z = y) y.
Proof.
intros x y Hle.
split.  
- 
  intros z Hm.
  destruct Hm; subst; auto; apply refl.
-
  intros z Hu.
  apply  (Hu y).
  now right.
Qed.


Definition is_ideal{P:Poset} (S: Setof P) :=
  is_directed S /\ is_dclosed S.


  Definition principal{P:Poset} (x: P) : Setof P := dclosure(single x).

  Lemma member_principal{P:Poset}: forall (x:P), member (principal x) x.
  Proof.
  intros x.
  exists x;repeat split;  try apply refl.
  Qed.
  
  
  Lemma member_principal_iff{P:Poset}: forall (x y : P), member (principal x) y <-> y <= x.
  Proof.
  split ; intro HH.
  -   
    destruct HH as (u & Hmu & Hou).
    rewrite member_single_iff in Hmu; now subst.
  -
    exists x; split; auto.
    apply member_single.
  Qed.  
  
  Lemma subset_principal_iff{P:Poset}:
    forall (x: P) (S: Setof P), (forall y, member S y -> y <= x) <-> subset S (principal x).
  Proof.
  split.  
  -
   intros Hall y Hm.
   exists x; split.
   +
    apply member_single.
   +
     now apply Hall.
  -
    intros Hs y Hle.
    specialize (Hs _ Hle).
    now rewrite member_principal_iff in Hs.
  Qed.
  
  
  Lemma principal_injective{P:Poset} : forall (x y:P),
      principal x = principal y -> x = y.
  Proof.  
  intros x y Heq.
  rewrite set_equal in Heq.
  apply antisym.
  -
    rewrite <- member_principal_iff.
    rewrite <- Heq.
    apply member_principal.
  - 
    rewrite <- member_principal_iff.
    rewrite Heq.
    apply member_principal.
  Qed.
  
  
  Lemma principal_is_ideal{P:Poset} : forall (x:P), is_ideal (principal x).
  Proof.
  repeat split.        
  -
    rewrite not_empty_member.
    exists x.
    apply member_principal.
  -
    intros z y Hm1 Hm2.
    rewrite member_principal_iff in Hm1,Hm2.
    exists x ; repeat split; auto.
    apply member_principal.
  -
    apply dclosure_is_dclosed.
  Qed.


  Lemma dclosed_equal_union_principals{P:Poset} :
  forall (S : Setof P), is_dclosed S ->
    S = union (fun V : Setof P => exists x, member S x /\ V = principal x).
Proof.  
intros S Hd.
rewrite set_equal.
split; intro Hm.
- 
  apply member_union with (S := principal x) ; [apply member_principal | ].
  now exists x.
-  
  apply member_union_member_one in Hm.
  destruct Hm as (S' & Hm & Hm').
  destruct Hm as (y & Hmy & Heqy); subst.
  rewrite member_principal_iff in Hm'.
  now apply (Hd y).
Qed.  

Lemma principal_subset {P:Poset} : forall (x : P)(S: Setof P),
    is_dclosed S -> (subset (principal x) S <-> member S x).
Proof.
intros x S Hd.  
split; intro HH.
-   
  unfold subset in HH.
  apply HH, member_principal.
-
  intros y Hm.
  rewrite member_principal_iff in Hm.
  now apply (Hd x).
Qed.

Lemma lub_principal{P:Poset} : forall (x:P),
is_lub (principal x) x.
Proof.
split.
-
 intros  y Hm.
 now rewrite member_principal_iff in Hm.
-
 intros y Hu.
 apply Hu.
 apply member_principal.
Qed.   

Definition is_principal{P:Poset} (S : Setof P) := exists x, S = principal x.

Lemma principal_is_principal{P:Poset} : forall (x:P),
is_principal (principal x).
Proof.
intro x ; now exists x.
Qed.

Definition is_monotonic{P1 P2: Poset} (f : P1 -> P2) :=
 forall x y, ord x y -> ord (f x) (f y).

 Lemma id_is_monotonic{P: Poset} :
 is_monotonic id(P1 := P)(P2 := P).
Proof.
 now intros x x' Heq.
Qed.

Lemma comp_is_monotonic{P1 P2 P3: Poset}:
 forall (f : P2 -> P3) (g : P1 -> P2),
   is_monotonic (P1 := P2) (P2 := P3) f
   -> is_monotonic (P1:= P1)(P2 := P2) g ->
   is_monotonic (f° g).
Proof.  
intros f g Hm1 Hm2 x z Hle.
now apply Hm2,Hm1 in Hle.
Qed.

Lemma cst_is_monotonic{P1 P2:Poset}: forall (a : P2),
is_monotonic (P1 := P1) (P2 := P2) (fun _ => a).
Proof.
intros a x y _.
apply refl.
Qed.


Definition is_rev_monotonic{P1 P2 : Poset}(f : P1 -> P2) :=
 forall x y, f x <= f y -> x <= y.


Lemma comp_is_rev_monotonic{P1 P2 P3: Poset}:
forall (f : P2 -> P3) (g : P1 -> P2),
 is_rev_monotonic (P1 := P2) (P2 := P3) f
 -> is_rev_monotonic (P1:= P1)(P2 := P2) g ->
 is_rev_monotonic (f° g).
Proof.  
intros f g Hm1 Hm2 x z Hle.
now apply Hm1,Hm2 in Hle.
Qed.

Definition is_bimonotonic {P1 P2 : Poset}(f : P1 -> P2) :=
 is_monotonic f /\is_rev_monotonic f.

Lemma comp_is_bimonotonic{P1 P2 P3: Poset}:
 forall (f : P2 -> P3) (g : P1 -> P2),
   is_bimonotonic (P1 := P2) (P2 := P3) f
   -> is_bimonotonic (P1:= P1)(P2 := P2) g ->
   is_bimonotonic (f° g).
 Proof.  
 intros f g (Hm1& Hr1) (Hm2& Hr2).
 split.
 - now apply comp_is_monotonic.
 - now apply comp_is_rev_monotonic.
 Qed.


Lemma bimono_injective{P1 P2 : Poset} :
 forall (f : P1 -> P2),
   is_bimonotonic f -> is_injective f.
Proof.  
intros f Hb x y Heq.
apply antisym;
 apply Hb; rewrite Heq; apply refl.
Qed.



Record Poset_ISOMORPHISM (P1 P2 : Poset)  : Type :=
{
  b :>  BIJECTION P1 P2;
  to_mono : is_monotonic  (to b) ;
  from_mono : is_monotonic (from b)             
}.

Definition Poset_ISOMORPHISM_refl (P: Poset) :
  Poset_ISOMORPHISM P P. 
unshelve econstructor.
-
 exact (BIJECTION_refl P).
-
 apply id_is_monotonic.
-
 apply id_is_monotonic.
Defined.

Definition Poset_ISOMORPHISM_sym (P1 P2 : Poset) (Hi :Poset_ISOMORPHISM P1 P2): Poset_ISOMORPHISM P2 P1.  
unshelve econstructor.
- 
  apply BIJECTION_sym.
  exact (b _ _ Hi).
-
  intros x y Heq.
  now apply from_mono.
-  
  intros x y Heq.
  now apply to_mono.
Defined.

Definition Poset_ISOMORPHISM_trans  (P1 P2 P3: Poset) 
  (Hi1: Poset_ISOMORPHISM P1 P2)(Hi2:Poset_ISOMORPHISM P2 P3):
  Poset_ISOMORPHISM P1 P3.
unshelve econstructor.
-
  apply BIJECTION_trans with (Y := P2).
  +
    exact (b _  _ Hi1).
  +  
    exact (b _ _ Hi2).
-
  intros x y Heq.
  apply comp_is_monotonic ; auto; apply to_mono.
-
  intros x y Heq.
  apply comp_is_monotonic ; auto; apply from_mono.
Defined.

  
Lemma to_rev_mono{P1 P2 : Poset} :
  forall (Iso :Poset_ISOMORPHISM P1 P2) (x x' : P1),
    to Iso x <= to Iso x' -> x <= x'.
Proof.  
intros Iso x x' Hle.
destruct (from_surjective Iso x) as (y & Heq).
destruct (from_surjective Iso x') as (y' & Heq').
subst. 
do 2 rewrite to_from in Hle.
now apply from_mono.
Qed.


Lemma from_rev_mono{P1 P2 : Poset} :
  forall (Iso :Poset_ISOMORPHISM P1 P2) (y y' : P2),
    from Iso y <= from Iso y' -> y <= y'.
Proof.  
intros Iso y y' Hle.
destruct (to_surjective Iso y) as (x & Heq).
destruct (to_surjective Iso y') as (x' & Heq').
subst. 
do 2 rewrite from_to in Hle.
now apply to_mono.
Qed.


Lemma from_bimono{P1 P2 : Poset} :
  forall (Iso :Poset_ISOMORPHISM P1 P2),
  is_bimonotonic (from Iso).
Proof.  
intro Iso; split.
- apply from_mono.
- intros x y Hle; eapply from_rev_mono; eauto.
Qed.


Lemma to_bimono{P1 P2 : Poset} :
  forall (Iso :Poset_ISOMORPHISM P1 P2),
  is_bimonotonic (to Iso).
Proof.  
intro Iso; split.
- apply to_mono.
- intros x y Hle; eapply to_rev_mono; eauto.
Qed.

Lemma monotonic_directed{P1 P2 : Poset} :
  forall (S: Setof P1) (f : P1 -> P2), is_monotonic f ->
     is_directed  (P:=P1) S -> is_directed (P := P2) (fmap S  f).   
Proof.
intros S f Hmono Hd ; split.
-   
  intro Hne ; destruct Hd as (Hne' & _); apply Hne'.
  now rewrite <- is_empty_fmap in Hne.
-
  intros y y' Hmy Hmy'.
  apply inv_member_fmap in Hmy,Hmy'.
  destruct Hmy as (x & Heq & Hm).
  destruct Hmy' as (x' & Heq' & Hm'); subst.   
  destruct Hd as (_ & Hex).
  destruct (Hex _ _ Hm Hm') as (z' & Hmz' & Hlex & Hlex').
  exists (f  z'); repeat split.
  +
    now apply member_fmap.
  +
    now apply Hmono.
  +
    now apply Hmono.
Qed.

Lemma rev_monotonic_directed{P1 P2 : Poset} :
  forall (S: Setof P1) (f : P1 -> P2), is_rev_monotonic f ->
     is_directed  (P:=P2) (fmap S  f) -> is_directed (P := P1) S.
Proof.
intros S f Hrm Hd.
split.
- 
  destruct Hd as (Hne & _).
  rewrite not_empty_member in *.
  rewrite not_empty_member in Hne.
  destruct Hne as (y & (z & Hmz & Heq)).
  now exists z.
-             
  intros x y Hmx Hmy.
  destruct Hd as (_ &  Hd).
  apply member_fmap with (f :=f) in Hmx,Hmy.
  specialize (Hd _ _ Hmx Hmy).
  destruct Hd as (z & Hmz & Hle1 & Hle2).
  destruct Hmz as (x' & Hmx' & Heq); subst.
  exists x'; split; auto.
Qed.


Lemma isomorphic_directed{P1 P2 : Poset} :
  forall (Iso :Poset_ISOMORPHISM P1 P2) (S: Setof P1),
     is_directed  (P:=P1) S -> is_directed (P := P2) (fmap S  (to Iso) ).   
Proof.  
intros Iso S  Hd.
apply monotonic_directed; auto.
now destruct Iso.
Defined.


Lemma isomorphic_directed_rev{P1 P2 : Poset} :
  forall (Iso :Poset_ISOMORPHISM P1 P2) (S: Setof P1),
     is_directed (P := P2) (fmap S  (to Iso) ) -> is_directed  (P:=P1) S.   
Proof.
intros Iso S  Hd ; split.
-    
  intro Hne ; destruct Hd as (Hne' & _); apply Hne'.
  now rewrite <- is_empty_fmap.
-
   intros y y' Hmy Hmy'.
   destruct Hd as (_ & Hex).
   assert (Hm : member (fmap S (to Iso))
                   (to Iso y)) by now apply member_fmap.
   assert (Hm' : member (fmap S (to Iso))
                   (to Iso y')) by now apply member_fmap.
   destruct (Hex _ _ Hm Hm') as (z' & Hmz & Hlex' & Hley').
   destruct Hmz as (z & Hmz & Heq); subst.
   exists z; repeat split; auto;
     eapply to_rev_mono; eauto.
Qed.

Lemma Poset_isomorphism_lub_from_to{P P' : Poset}:
  forall (Iso :  Poset_ISOMORPHISM P P') (S' : Setof P') l,
  is_lub (fmap S' (from Iso)) l ->  is_lub S' (to Iso l).
Proof.
intros Iso S' l Hl.
destruct Hl as (Hu & Hmin).  
split.
-
  intros y' Hm.
  apply member_fmap with (f := from Iso) in Hm.
  specialize (Hu _ Hm).
  destruct (from_surjective Iso l) as (y & Hy).
  subst.
  rewrite to_from.
  eapply from_rev_mono; eauto.
-
  intros y' Hu'.
  specialize (Hmin (from Iso y')).
  destruct (from_surjective Iso l) as (y & Hy).
  subst.
  rewrite to_from.
  assert (Hle : from Iso y <= from Iso y');
    [|  eapply from_rev_mono; eauto].
  apply Hmin.
  intros x Hmx.
  apply  inv_member_fmap in Hmx.
  destruct Hmx as (z & Heq & Hmz).
  subst.
  apply from_mono.
  now apply (Hu' z).
Qed.


Lemma Poset_isomorphism_lub_to_from{P P' : Poset}: forall (Iso :  Poset_ISOMORPHISM P P') (S : Setof P) l,
  is_lub (fmap S (to Iso)) l ->  is_lub S (from Iso l).
Proof.
intros Iso S l Hl.
destruct Hl as (Hu & Hmin).  
split.
-
  intros y' Hm.
  apply member_fmap with (f := to Iso) in Hm.
  specialize (Hu _ Hm).
  destruct (to_surjective Iso l) as (y & Hy).
  subst.
  rewrite from_to.
  eapply to_rev_mono; eauto.
-
  intros y' Hu'.
  specialize (Hmin (to Iso y')).
  destruct (to_surjective Iso l) as (y & Hy).
  subst.
  rewrite from_to.
  assert (Hle : to Iso y <= to Iso y');
    [|  eapply to_rev_mono; eauto].
  apply Hmin.
  intros x Hmx.
  apply  inv_member_fmap in Hmx.
  destruct Hmx as (z & Heq & Hmz).
  subst.
  apply to_mono.
  now apply (Hu' z).
Qed.




Definition commutes_with_lub{P P' : Poset}
  (f: P -> P') (S: Setof P) (l: P) : Prop:=
  is_lub S l -> is_lub (fmap S f) (f l).



Lemma  to_commutes_with_lub{P P' : Poset}:
  forall (Iso :  Poset_ISOMORPHISM P P') (S : Setof P) l,
    is_directed S ->commutes_with_lub (to Iso) S l.
Proof.
intros i S l Hd (Hu & Hmin).
split.
-
  intros y Hmy.
  apply inv_member_fmap in Hmy.
  destruct Hmy as (x & Heq & Hmx); subst.
  now apply to_mono, (Hu x).
-
  intros y Hu'.
  replace y with (to i (from i y)); [| apply to_from].
  apply to_mono.
  apply Hmin.
  intros x Hmx.
  replace x with (from i (to i x)); [| apply from_to].
  apply from_mono.
  apply Hu'.
  now exists x.
Qed.


Lemma  from_commutes_with_lub{P P' : Poset}:
  forall (Iso :  Poset_ISOMORPHISM P P') (S' : Setof P') l,
    is_directed S' ->commutes_with_lub (from Iso) S' l.
Proof.
intros i S' l Hd (Hu & Hmin).
split.
-
  intros y Hmy.
  apply inv_member_fmap in Hmy.
  destruct Hmy as (x & Heq & Hmx); subst.
  now apply from_mono, (Hu x).
-
  intros y Hu'.
  replace y with (from i (to i y)); [| apply from_to].
  apply from_mono.
  apply Hmin.
  intros x Hmx.
  replace x with (to i (from i x)); [| apply to_from].
  apply to_mono.
  apply Hu'.
  now exists x.
Qed.

Lemma is_lub_fmap_rev{P1 P2 : Poset}:
  forall (S : Setof P1) (f : P1 -> P2)(l : P1),
  is_bimonotonic f ->
  is_lub (fmap S f) (f l) ->  is_lub S l.
Proof.  
intros S f l (Hm & Hrm)  (Hu,Hmin).
split.
- 
  intros x Hmx.
  apply Hrm,Hu.
  now apply member_fmap.
-
  intros y Huy.
  apply Hrm,Hmin.
  intros x Hux.
  destruct Hux as (z & Hmz & Heq); subst.
  now apply Hm,Huy.
Qed.
  
Lemma lub_fmap_iso{P P': Poset}:
forall (i:Poset_ISOMORPHISM P' P) (S:Setof P) (c:P),
is_lub S c-> is_lub (fmap S (from i)) (from i c).
Proof.
intros i S c Hl.
split.
-
 intros x Hm.
 destruct Hm as (y & Hmy & Heqy).
 destruct Hl as (Hu & _).
 unfold is_upper in Hu.
 specialize (Hu _ Hmy).
 subst.
 now apply from_mono.
- 
 intros x Hu'.
 destruct Hl as (Hu & Hmin).
 unfold is_upper in Hu'.
 replace x with (from i (to i x)); [| apply from_to].
 apply from_mono.
 apply Hmin.
 intros z Hu''.
 replace z with (to i (from i z)); [|apply to_from].
 apply to_mono.
 apply Hu'.
 now apply member_fmap.
 Qed.


 Definition is_monotonic_on{P1 P2:Poset}(f : P1 -> P2)
 (S: Setof P1) : Prop := 
   forall x y,  member S x -> member S y -> x <= y -> f x <= f y.
 

 Lemma lem50part1{D:Poset}{C:Poset}: forall (f : D -> C),
 forall d,
 is_monotonic_on f (fun d' =>  ord d' d) ->
    dclosure (fmap (fun d' =>  ord d' d) f) = 
    principal (f d).
Proof.
intros f d Hm.
apply set_equal; intro x; split; intro Hm'.
-
 rewrite member_principal_iff.
 destruct Hm' as (y & Hmy & Hle).
 destruct Hmy as (d' & Hle' & Heq); subst.
 eapply trans; eauto.
 apply Hm; auto.
 apply refl.
 -
rewrite member_principal_iff in Hm'.
exists (f d); split; auto.
exists d; split; auto; apply refl.
Qed.

Lemma lem50part2{D:Poset}{C:Poset}: forall (f : D -> C),
forall d,
 is_monotonic_on f (fun d' =>  ord d' d) ->
is_lub (fmap  (fun d' =>  ord d' d) f) (f d).
Proof.
intros f Hm d.
rewrite  is_lub_dclosure.
rewrite lem50part1; auto.
apply lub_principal.
Qed.

Lemma comp_is_monotonic_on{P1 P2 P3:Poset}:
forall (f : P2 -> P3)(g : P1 -> P2) (S: Setof P1),
is_monotonic f  -> is_monotonic_on g S -> 
is_monotonic_on (f ° g) S.
Proof.
intros f g S Hmf Hmog x y Hmx Hmy Hle.
unfold "°".
apply Hmf.
now apply Hmog.
Qed.

Lemma monotonic_on_directed{P1 P2:Poset}: 
forall (S : Setof P1) (f : P1 -> P2), is_monotonic_on f S -> 
  is_directed S -> is_directed (fmap S f).
  intros S f Hmono Hd ; split.
  -   
    intro Hne ; destruct Hd as (Hne' & _); apply Hne'.
    now rewrite <- is_empty_fmap in Hne.
  -
    intros y y' Hmy Hmy'.
    apply inv_member_fmap in Hmy,Hmy'.
    destruct Hmy as (x & Heq & Hm).
    destruct Hmy' as (x' & Heq' & Hm'); subst.   
    destruct Hd as (_ & Hex).
    destruct (Hex _ _ Hm Hm') as (z' & Hmz' & Hlex & Hlex').
    exists (f  z'); repeat split.
    +
      now apply member_fmap.
    +
      now apply Hmono.
    +
      now apply Hmono.
  Qed.



  Definition is_compact{D : Poset} (cc : D) :=
    forall S (Hd : is_directed S) l,
    is_lub S l -> 
      cc <= l ->  exists c, member S c /\ cc <= c.
  
  Lemma is_compact_alt{D: Poset} :
    forall (cc:D), is_compact  cc <->
           forall S (Hd : is_directed S)(Hc: is_dclosed S) l,
           is_lub S l ->
            cc  <= l ->  exists c, member S c /\ cc <= c.
  Proof.                   
  split; intro Hc.
  -
    intros S Hd Hdc k.
    now apply Hc.
  -   
    intros S Hd l Hdc Hlup.
    specialize (is_lub_dclosure S) as Hil.
    apply (Hil l) in Hdc; clear Hil.
    specialize (Hc _ (dclosure_is_directed _ Hd)
                  (dclosure_is_dclosed S) _ Hdc Hlup).
    destruct Hc as (x & Hmx & Hle).
    destruct Hmx as (y & Hly & Hley).
    exists y; split; auto.
    clear Hlup.
    eapply trans; eauto.
  Qed.              

  

Definition is_post_fixpoint {P: Poset}(f : P -> P)(x: P) :=
    ord x (f x).

Definition is_fixpoint{P: Poset}(f : P -> P)(x: P) :=
    x = f x.

Lemma fixpoint_is_post_fixpoint{P: Poset}(f : P -> P) :
forall (x:P), is_fixpoint f x -> is_post_fixpoint f x.
Proof.
intros x Hf.
unfold is_fixpoint,is_post_fixpoint in *.
rewrite <- Hf.
apply refl.
Qed. 



Lemma list_directed_has_upper{P:Poset} :
forall (l: list P)  (T: Setof P), is_directed T -> 
 (forall i, i < length l -> member T (nth  i l default) ) ->
  exists q, member T q /\  
   forall j, j < length l -> nth j l default <= q.
Proof.
induction l; intros T Hd Ha.
-
 destruct Hd as (Hne & _).
 rewrite not_empty_member in Hne.
 destruct Hne as (x & Hm).
 exists x; split; auto.
 intros j Hlt; cbn in Hlt; lia.
-
 cbn [length] in *.
 destruct l.
 +
  exists a; split ; auto.
  *
   cbn [length] in *.
   specialize (Ha 0); cbn in Ha; apply Ha; lia.
  *
   cbn [length]. 
   intros i Hi.
   assert (Heq : i = 0) by lia; subst.
   apply refl.
 +
  cbn [length] in *.
  specialize (IHl _ Hd).
  assert (Hal : (forall i : nat,
    i < S (length l) -> member T (nth i (c :: l) default))).
  { 
   intros i Hlt.
   apply (Ha (S i)); lia.
  }
  specialize (IHl Hal).
  clear Hal.
  destruct IHl as (q & Hmq & Hal).
  specialize Ha as Ha'.
  specialize (Ha' 0); cbn in Ha'.
  assert (Hma : member T a) by (apply Ha'; lia).
  clear Ha'.
  destruct Hd as (Hne & Hd).
  specialize (Hd _ _ Hmq Hma).
  destruct Hd as (z &  Hmz & Hleqz & Hleaz).
  exists z; split; auto.
  intros j Hlt.
  destruct j; auto.
  replace (nth (S j) (a :: c :: l) default) with
  (  nth j (c :: l) default); [|reflexivity].
   apply @trans with (y :=q); auto.
   apply Hal;lia.
Qed.  


Lemma list_directed_has_upper_alt{P:Poset} :
forall (T: Setof P), is_directed T -> 
forall (l: list P),  (forall x, In x l ->  member T x ) ->
  exists q, member T q /\  
   forall x, In x l  -> x <= q.
Proof.   
intros T Hd l Ha.
assert (Ha' :(forall i, i < length l -> member T (nth  i l default))) by
  (intros i Hlt; now apply Ha, nth_In).
clear Ha.
apply list_directed_has_upper in Ha'; auto.
destruct Ha' as (q & Hmq & Ha).
exists q; split; auto.
intros x Hin.
specialize (In_nth l x default Hin) as Hin'.  
destruct Hin' as (n & Hlt & Heq).
rewrite <- Heq.
now apply Ha.
Qed.
