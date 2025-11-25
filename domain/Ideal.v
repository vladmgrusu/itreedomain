From Stdlib Require Import ProofIrrelevance FunctionalExtensionality
 PropExtensionality IndefiniteDescription.
From Domain Require Export DCPO.


Record IDEAL (P: Poset) : Type :=
{
  ideal :> Setof P;
  ideal_is_ideal : is_ideal ideal;
}.    




Lemma ideal_equal{P : Poset} : forall (I J : IDEAL P),
    ideal _ I = ideal _ J -> I = J.
Proof.
intros I J Heq.
destruct I, J.
cbn in *; subst.
f_equal.
apply proof_irrelevance.
Qed.


Lemma ideals_subset_antisym{P : Poset} :
  forall (I J : IDEAL P),
    subset I J -> subset J I -> I = J.
Proof.
intros (I, (Hd, Hc)) (J, (Hd',Hc')); cbn; intros Hs1 Hs2.
apply subset_antisym in Hs1; auto;subst.
f_equal; apply proof_irrelevance.
Qed.


Definition ideals_Poset (P : Poset) :Poset :=
{|
  carrier := IDEAL P ;
  default := {|ideal := principal (@default P); 
            ideal_is_ideal := principal_is_ideal _|};
  ord :=  subset ;
  refl := subset_refl ;
  trans := subset_trans ;
  antisym := ideals_subset_antisym 
|}.




Lemma union_ideals_is_ideal{P:Poset} :
  forall (SS: (Setof (Setof P))),
    is_directed (P := ideals_Poset P) SS ->
    (forall S, member SS S -> is_ideal S) -> 
    is_ideal (union SS).
Proof.
intros SS (Hne & Hmax)  Hall.
repeat split.
-
  rewrite not_empty_member.
  rewrite not_empty_member in Hne.
  destruct Hne as (S & Hm).
  unfold member in Hm.
  unfold ideals_Poset in S; subst; cbn in *.
  destruct  S as (S , ((Hn , HmaxS) , Hd)); subst; cbn in *.
  rewrite not_empty_member in Hn.
  destruct Hn as (x & Hmx).
  now exists x, S.
-  
  intros x y Hm1 Hm2.
  destruct Hm1 as (S1 & HmS1 & HmS1').
  destruct Hm2 as (S2 & HmS2 & HmS2').
  specialize (Hall _ HmS1) as Hi1. 
  specialize (Hall _ HmS2) as Hi2.
  remember
    {| ideal := S1 ;
      ideal_is_ideal := Hi1
    |} as I1.
   remember
    {| ideal := S2 ;
      ideal_is_ideal := Hi2
    |} as I2.
  
   specialize (Hmax I1 I2).
   unfold member in Hmax.
   cbn in Hmax.
   subst.
   cbn in Hmax.
   specialize (Hmax HmS1 HmS2).
   destruct Hmax as (S & Hm & Hsub1 & Hsub2).
   eapply member_subset in Hsub1; eauto.
   eapply member_subset in Hsub2; eauto.
   destruct S as (S , ((HneS & HddS) , HdS)).
   cbn in *.
   specialize (HddS _ _ Hsub1 Hsub2).
   destruct HddS as (z & Hmz & Hlexz & Hleyz).
   exists z ; repeat split; auto.
   now apply member_union with (S := S).
-
  intros x Hmx y Hle.
  apply member_union_member_one in Hmx.
  destruct Hmx as (S & HmS & Hmx).
  apply member_union with (S := S); auto.
  destruct (Hall _ HmS) as (_ & Hd).
  now apply (Hd x).
Qed.


Lemma union_ideals_is_lub{P:Poset} :
  forall (SS: (Setof (Setof P)))
   (HD: is_directed (P := ideals_Poset P) SS)
    (Hall : (forall S, member SS S -> is_ideal S)), 
    is_lub  (P := ideals_Poset P)  SS (Build_IDEAL _ (union SS) 
    (union_ideals_is_ideal SS HD Hall)).
Proof.
intros SS HD Hall.
unfold ideals_Poset in * ; cbn in *.
split.
-
  unfold is_upper.
  cbn in *.
  intros y Hm.
  unfold member in Hm.
  apply member_union_subset; auto.  
-
  cbn.
  intros y Hu.
  unfold is_upper in Hu.
  cbn in Hu.
  apply union_lub.
  intros S  Hm.
  specialize (Hu  (Build_IDEAL _ S (Hall _ Hm))).
  apply Hu,Hm.
Qed.

                                 
Lemma member_ideals_set_is_ideal{P : Poset} :
  forall
    (SS : Setof (ideals_Poset P)), (forall  (S: Setof P),
    member (fmap  SS (fun (I:ideals_Poset P) => (ideal _ I))) S
     -> is_ideal S).
Proof.
intros SS S Hm.
destruct Hm as (x & HSS & Heq).
rewrite Heq.
now destruct x. 
Qed.

Definition ideal_lub_sig{P:Poset}
(S:Setof (IDEAL P)) (HD :is_directed (P:= ideals_Poset P) S) : 
{I : IDEAL P | is_lub (P := ideals_Poset P)S I}.
remember (fmap  S (fun (I:ideals_Poset P) => (ideal _ I))) as SS.
assert  (is_directed (P := ideals_Poset P) SS).
{
  rewrite HeqSS.
  split.
  -
   rewrite not_empty_member.
   destruct HD as (Hn & _).
   rewrite not_empty_member in Hn.
   destruct Hn as (x & Hm).
   exists x.
   now exists x.
  -
   cbn in *.
   intros x y Hmx Hmy.
   destruct Hmx as (v & Hv & Heq); rewrite Heq in *; clear Heq.
   destruct Hmy as (w & Hw & Heq); rewrite Heq in *; clear Heq.
   destruct HD as (_ & Hma).
   destruct (Hma _ _ Hv Hw) as (z &  Hmz & Hlev & Hlew); clear Hma.
   exists z; repeat split; auto.
   now exists z.
}
 specialize  (member_ideals_set_is_ideal S) as Haux.
 assert (HallI : forall I, member SS I -> is_ideal I).
 {
  intros I Hm.
  apply Haux.
  now subst.
 }
 (*Huai, HallI*)
  specialize (union_ideals_is_ideal SS H) as Huai.
  exists (Build_IDEAL _ (union SS) (Huai HallI)).
  cbn.
  specialize (union_ideals_is_lub SS H HallI) 
    as Huil.
  cbn in *.
  split.
  -
    intros x Hmx.
    destruct Huil as (Hu & _).
    apply (Hu x).
    unfold member.
    subst.
    now exists x.
  -
   intros y Huy.
   destruct Huil as (Hu & Hmin).
   apply Hmin.
   intros w Hmw.
   apply Huy.
   subst.
   destruct Hmw as (q & Hq & Heq); subst.
   cbn in *.
   assert (w = q)
     by now apply ideal_equal.
   now subst.
Defined.  

  


Program Definition ideals_DCPO (P : Poset): DCPO :=
{|
   dcpo_poset := ideals_Poset P;
   lub := _;
   lub_is_lub := _;
|}.

Next Obligation.
cbn in *.
destruct (oracle (is_directed (P:= ideals_Poset P) S)).
- 
 exact (proj1_sig (ideal_lub_sig S i)).
-  
 refine {|ideal := principal (@default P)|}.
 apply principal_is_ideal.
Defined. 

Next Obligation.
cbn in *.
unfold  ideals_DCPO_obligation_1.
destruct ( oracle(@is_directed
   (ideals_Poset P) S)); [ | contradiction].
cbn in *. 
exact  (proj2_sig (ideal_lub_sig S i)).
Qed.    


Lemma principal_is_compact{P: Poset} : forall (x :P),
    is_compact (D := (@ideals_DCPO P))
      (Build_IDEAL _ (principal  x)
         (principal_is_ideal x)).
Proof.
intros x S Hd l Hl Hle.
cbn in *.
(*Set Printing Coercions.*)
apply  (@is_lub_lub_eq1 (@ideals_DCPO P)) in Hl; auto; subst.
remember (fmap S (fun I : IDEAL P => (ideal _ I)))  as SS.
unfold subset in Hle.
cbn in *.
unfold ideals_DCPO_obligation_1 in Hle.
destruct (oracle (is_directed (P := ideals_Poset P)S)); [|contradiction].
cbn in *.
apply member_union_member_one  with (x := x)in Hle;[| apply member_principal].
destruct Hle as (S' & Hm & Hm').
subst.
destruct Hm as (I & HSI & HeqI).
exists I.
subst.
split; auto.
rewrite principal_subset; auto.
destruct I;now destruct ideal_is_ideal0.
Qed.


Definition all_principals{P: Poset} (I : IDEAL P) : Setof (Setof P) :=
  fmap (ideal P I) principal.

Lemma all_principals_are_ideals{P:DCPO} : forall I (S: Setof P),
  member (all_principals I) S -> is_ideal S.
Proof.
intros I S Hm.
destruct Hm as (x & HIx & Heq).
subst.
apply principal_is_ideal.
Qed.


Lemma all_principals_directed{P:Poset}:
forall (I: IDEAL P), @is_directed  (@ideals_Poset P)
     (all_principals   I).
Proof.
intros I.  
destruct I as (S & HI).
specialize HI as HI'.
destruct HI' as ((Hns &HdS) & HcS).
split.
-
  cbn.
  rewrite  not_empty_member in *.
  specialize (not_empty_member S) as HneS.
  assert (Hex : exists x, member S x) by tauto.
  clear HneS.
  destruct Hex as (x & Hmx).
  exists (Build_IDEAL _ (principal x) (principal_is_ideal x)).
  cbn.
  now exists x.
-
  cbn in *.
  intros I J HmI HmJ.
  destruct HmI as (x & Hmx & Heq).
  destruct HmJ as (y & Hmy & Heqy).  
  cbn in *.
  subst.
  destruct (HdS _ _  Hmx Hmy) as (z & Hmz & Hlexz& Hleyz).
  exists (Build_IDEAL _ (principal z) (principal_is_ideal z)).
  cbn.
  repeat split.
  +
    now exists z.
  +
    rewrite Heq.
    rewrite principal_subset.
    *
      now rewrite member_principal_iff.
    *
      now destruct (principal_is_ideal z).
  +
    rewrite Heqy.
    rewrite principal_subset.
    *
      now rewrite member_principal_iff.
    *
      now destruct (principal_is_ideal z).
Qed.      



Lemma reformulate_compact_in_ideals{P: Poset} :
  forall (cc : ideals_DCPO P),
    is_compact (D := ideals_DCPO P) cc
    -> forall (S : Setof(IDEAL P))  
    (HD : is_directed (P:= ideals_DCPO P) S),
      subset (ideal _  cc)  
        (union (fmap S (fun I : IDEAL P => ideal _ I)))
                    -> exists c, S c /\ subset (ideal _  cc) c.
Proof.     
intros cc Hc S HD Hsub.
cbn in *.
unfold is_compact in Hc.  
cbn in *.
apply   (Hc _ HD ) with (l := lub  (d := ideals_DCPO P) S); 
[apply (@lub_is_lub (ideals_DCPO P)); auto| ].
cbn in *.
unfold ideals_DCPO_obligation_1.
destruct 
(oracle (is_directed (P := ideals_Poset P )S));
 [|contradiction].
apply Hsub.
Qed.


Lemma subset_ideals_union{P: Poset}:
  forall (I : IDEAL P),
    subset (ideal P I)
          (union
             (fmap
                (fun J : IDEAL P =>
                 all_principals I
                   (ideal P J))
                (fun K : IDEAL P =>
                   ideal _ K)
             )
          ).
(* NB these are actually equal *)
Proof.
intros I x Hmem.
exists (principal x); split; auto.
-
  exists (Build_IDEAL _ (principal x) (principal_is_ideal x)).
  cbn; split; auto.
  now exists x.
-             
  apply member_principal.
Qed.




Lemma compact_is_principal{P: Poset} : forall (I : IDEAL P),
    is_compact (D := (@ideals_DCPO P)) I ->
    exists x, ideal _ I =(principal  x).
Proof.
intros I Hc.
specialize (reformulate_compact_in_ideals _ Hc
                (fun J => member (all_principals I) J)
                (all_principals_directed I)
              (subset_ideals_union I)
           ) as Hc'.
destruct Hc' as (J & Hm & Hs).
destruct Hm as (x & Sx & Heq).
replace J with I in *.
-
  now exists x.
-
  apply ideal_equal.
  apply subset_antisym; auto.           
  rewrite Heq in *.
  rewrite <- subset_principal_iff in *.
  intros y Hy.
  rewrite  member_principal_iff in Hy.
  destruct I as (SI & Hd & Hcc).
  now apply (Hcc x).
Qed.
    
