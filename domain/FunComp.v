From Stdlib Require Import IndefiniteDescription FunctionalExtensionality
 ProofIrrelevance.
From Domain Require Export Completion.



Lemma funcomp_dir{A1 A2 : ADCPO}:
forall (f : A1 -> A2),
(forall cc : A1, is_compact cc -> is_compact (f cc)) ->
is_monotonic_on f (fun cc : A1 => is_compact cc) ->
forall x : A1, is_directed (fmap (compacts_le x) f).
Proof.
intros f Hac Hmo x.
unshelve eapply monotonic_on_directed.
-
intros u v  (Hcu & _) (Hcv & _) Hle.
apply Hmo; auto.
-
 apply algebraic_dir.
Qed.   

Definition funcomp{A1 A2:ADCPO}(f : A1 -> A2)
(Hac : forall (cc:A1), is_compact cc -> is_compact (f cc)) 
(Hmo : is_monotonic_on f (fun cc => is_compact cc)) : A1 -> A2 :=
fun x => lub (fmap (compacts_le x) f) .

Lemma funcomp_ext{A1 A2:ADCPO} :
forall (f : A1 -> A2) 
(Hac : forall (cc:A1), is_compact cc -> is_compact (f cc)) 
(Hmo : is_monotonic_on f (fun cc => is_compact cc)),
forall cc, is_compact cc ->  
(funcomp f Hac Hmo) cc = f cc.
Proof.
intros f Hac Hmo cc Hcc.
unfold funcomp.
remember
(fun (xs : {x : A1  | is_compact x}) =>
exist  _ (f (proj1_sig xs)) (Hac _ (proj2_sig xs))) 
as fc.
remember (exist _ cc Hcc) as cc'.
specialize (lem50part2 
(D := compacts_Poset A1) (C := compacts_Poset A2) fc cc') as Hld.
assert (Hm' :      
is_monotonic_on (P1:=compacts_Poset A1)
 (P2 := compacts_Poset A2)fc (fun d' : compacts_Poset A1 =>
d' <= cc')).
{
 intros u v Hmu Hmv Hle.
 destruct u, v; cbn in *.
 subst.
 cbn.
 now apply Hmo.
}
specialize (Hld Hm').
clear Hm'.
assert (Hl : is_lub (fmap (compacts_le cc) f) (f cc)).
{
subst; cbn in *.
cbn in *.
split.
-
 intros x Hmx.
 destruct Hmx as (z & (Hcz & Hlez) & Heq);
 subst.
 apply Hmo; auto.
- 
 intros y Hu.
 destruct Hld as (Hu' & Hmin').
 cbn in *.
 apply Hu.
 exists cc; repeat split; auto.
 apply refl.
}
specialize 
(lub_is_lub _ (funcomp_dir f Hac Hmo cc)) as Hl'.
eapply is_lub_unique with (x := f cc) in Hl'; auto.
Qed.


Lemma funcomp_mono{A1 A2:ADCPO} :
forall (f : A1 -> A2) 
(Hac : forall (cc:A1), is_compact cc -> is_compact (f cc)) 
(Hmo : is_monotonic_on f (fun cc => is_compact cc)),
is_monotonic (funcomp f Hac Hmo).
Proof.
intros f Hac Hmo x y Hle.
unfold funcomp.
apply forallex_lelub.
{
  apply monotonic_on_directed; [| apply algebraic_dir].
  intros  u v (Hc & _) (Hc' & _) Hle'.
  now apply Hmo.
}
{
  apply monotonic_on_directed; [| apply algebraic_dir].
  intros  u v (Hc & _) (Hc' & _) Hle'.
  now apply Hmo.
}
intros u (v & (Hcv & Hlev)& Heq); subst.
exists (f v); split; [| apply refl].
exists v; repeat split; auto.
eapply trans; eauto.
Qed.


Lemma funcomp_ed_cont{A1 A2:ADCPO} :
forall (f : A1 -> A2) 
(Hac : forall (cc:A1), is_compact cc -> is_compact (f cc)) 
(Hmo : is_monotonic_on f (fun cc => is_compact cc)),
is_ed_continuous (funcomp f Hac Hmo).
Proof.
intros f Hac Hmo.
intros gc g Hc Hle.
assert (Hd : is_directed (fmap (compacts_le g) f) ).
{
  apply monotonic_on_directed; [| apply algebraic_dir].
  intros  u v (Hc1 & _) (Hc2 & _) Hle'.
  now apply Hmo. 
} 
specialize (Hc _ Hd _ (lub_is_lub _ Hd) Hle).
destruct Hc as (c & Hmc & Hlec).
destruct Hmc as (x & (Hcx & Hlex) & Heq); subst.
exists x; repeat split; auto.
eapply trans; [now apply Hlec| ].
rewrite funcomp_ext; auto; apply refl.
Qed.

Lemma funcomp_cont{A1 A2:ADCPO} :
forall (f : A1 -> A2) 
(Hac : forall (cc:A1), is_compact cc -> is_compact (f cc)) 
(Hmo : is_monotonic_on f (fun cc => is_compact cc)),
is_continuous (funcomp f Hac Hmo).
Proof.
intros f Hac Hmo.
rewrite continuous_iff_ed_continuous_mono.
split.
-
apply funcomp_mono.
-
apply funcomp_ed_cont.
Qed.   


Definition default_ext{P1 P2: Poset} (f: P1 -> P2)
(e1 : COMPLETION P1) (e2 : COMPLETION P2) : e1 -> e2 :=
 fun x => match (oracle (is_compact x)) with
 left _ =>  inject (f (rev_inj x))
 |right _ => inject (@default P2)
 end.

Program Definition funcomp_default_ext{P1 P2: Poset} (f: P1 -> P2)
(Hm: is_monotonic f) (e1 : COMPLETION P1) (e2 : COMPLETION P2)
(x : e1) : e2 := funcomp (default_ext f e1 e2) _ _ x.
Next Obligation.
intros.
unfold default_ext.
destruct (oracle (is_compact cc)) as [Hc | n];
[| exfalso; now apply n].
apply inject_compact.
Qed.

Next Obligation.
intros.
intros u v Hmu Hmv Hle.
unfold member in Hmu,Hmv.
unfold default_ext.
destruct (oracle (is_compact u)) as [_| n];
[|exfalso; now apply n].
destruct (oracle (is_compact v)) as [_| n];
[|exfalso; now apply n].
rewrite <- inject_bimono.
apply Hm.
rewrite <- rev_inj_bimono; auto.
Qed.
 

Lemma funcomp_default_ext_mono{P1 P2:Poset}:
forall (m : P1 -> P2) (Hm: is_monotonic m)
(e1 : COMPLETION P1) (e2 : COMPLETION P2),
    is_monotonic 
      (funcomp_default_ext m Hm e1 e2).
Proof.  
intros.  
unfold funcomp_default_ext.
apply funcomp_mono.
Qed.  
 


Lemma funcomp_default_ext_cont{P1 P2:Poset}:
forall (m : P1 -> P2) (Hm: is_monotonic m)
(e1 : COMPLETION P1) (e2 : COMPLETION P2),
    is_continuous 
      (funcomp_default_ext m Hm e1 e2).
Proof.  
intros.  
unfold funcomp_default_ext.
apply funcomp_cont.
Qed.  
 

Lemma funcomp_default_ext_ext{P1 P2:Poset}:
forall (m : P1 -> P2) (Hm: is_monotonic m)
(e1 : COMPLETION P1) (e2 : COMPLETION P2),
forall (cc: e1) (Hc : is_compact cc),
(funcomp_default_ext m Hm e1 e2) cc = inject (m (rev_inj cc)) . 
Proof.  
intros.  
unfold funcomp_default_ext.
rewrite funcomp_ext; auto.
unfold default_ext.
now destruct (oracle (is_compact cc)).
Qed.  




Lemma unique_continous_ext{P1 P2: Poset} 
  {e1 : COMPLETION P1}{e2 : COMPLETION P2}:
forall (f g : e1 -> e2),
is_continuous f -> 
is_continuous g -> (forall cc, is_compact cc ->f cc =  g cc) 
 -> f = g.
Proof.
intros f g Hcf Hcg Ha.
extensionality x.
replace x with (lub (compacts_le x)); 
[|now rewrite algebraic_lub].
unfold is_continuous in *.
destruct (Hcf _ (algebraic_dir x)) as (Hdf & Heq); 
rewrite Heq; clear Heq.
destruct (Hcg _ (algebraic_dir x)) as (Hdg & Heq); 
rewrite Heq; clear Heq.
apply lub_eq; auto.
apply set_equal ; intro y; split; intros (z & (Hc & Hle) & Heq); subst;
   exists z; repeat split; auto.
 now rewrite Ha.
Qed. 
  
   

Definition Ca2Cb{A B: Poset}(I: Poset_ISOMORPHISM A B)
(Ca:COMPLETION A)(Cb : COMPLETION B) := 
funcomp_default_ext (to I)(to_mono _ _ I) Ca Cb.




Definition Cb2Ca{A B: Poset}(I: Poset_ISOMORPHISM A B)
(Ca:COMPLETION A)(Cb : COMPLETION B) := 
funcomp_default_ext (from I)(from_mono _ _ I) Cb Ca.

Lemma Ca2Cb2Ca{A B: Poset}(I: Poset_ISOMORPHISM A B)
 (Ca:COMPLETION A)(Cb : COMPLETION B) : 
 Cb2Ca I Ca Cb °Ca2Cb I Ca Cb  = id.
Proof.
apply unique_continous_ext; 
[ apply comp_is_continuous; apply  funcomp_default_ext_cont| 
apply id_is_continuous | ].
intros a Hca.
unfold "°", id, Ca2Cb,Cb2Ca.
rewrite funcomp_default_ext_ext.
-
 rewrite funcomp_default_ext_ext; auto.
 rewrite rev_inj_inject.
 rewrite from_to.
 apply inject_rev_inj; assumption.
-
 rewrite funcomp_default_ext_ext; auto.
 apply inject_compact.
Qed. 


Lemma Cb2Ca2Cb{A B: Poset}(I: Poset_ISOMORPHISM A B)
 (Ca:COMPLETION A)(Cb : COMPLETION B) : 
 Ca2Cb I Ca Cb °Cb2Ca I Ca Cb  = id.
Proof.
apply unique_continous_ext; 
[ apply comp_is_continuous; apply  funcomp_default_ext_cont| 
apply id_is_continuous | ].
intros a Hca.
unfold "°", id, Ca2Cb,Cb2Ca.
rewrite funcomp_default_ext_ext.
-
 rewrite funcomp_default_ext_ext; auto.
 rewrite rev_inj_inject.
 rewrite to_from.
 apply inject_rev_inj; assumption.
-
 rewrite funcomp_default_ext_ext; auto.
 apply inject_compact.
Qed. 




Program Definition Ca2Cb_BIJ{A B: Poset}(I: Poset_ISOMORPHISM A B)
(Ca:COMPLETION A)(Cb : COMPLETION B) :
BIJECTION Ca Cb :=
{|
  to := Ca2Cb I Ca Cb;
  from := Cb2Ca I Ca Cb
|}.

Next Obligation.
replace (Ca2Cb I Ca Cb
(Cb2Ca I Ca Cb x)) with ((Ca2Cb I Ca Cb °Cb2Ca I Ca Cb) x) by auto.
now rewrite Cb2Ca2Cb.
Qed.

Next Obligation.
replace (Cb2Ca I Ca Cb
(Ca2Cb I Ca Cb y)) with ((Cb2Ca I Ca Cb °Ca2Cb I Ca Cb) y) by auto.
now rewrite Ca2Cb2Ca.
Qed.

Lemma Ca2Cb_mono{A B: Poset}(I: Poset_ISOMORPHISM A B)
(Ca:COMPLETION A)(Cb : COMPLETION B) : 
is_monotonic (Ca2Cb I Ca Cb).
Proof.
apply funcomp_default_ext_mono.
Qed.


Lemma Cb2Ca_mono{A B: Poset}(I: Poset_ISOMORPHISM A B)
(Ca:COMPLETION A)(Cb : COMPLETION B) : 
is_monotonic (Cb2Ca I Ca Cb).
Proof.
apply funcomp_default_ext_mono.
Qed.

Definition Ca2Cb_Poset_ISO{A B: Poset}(I: Poset_ISOMORPHISM A B)
(Ca:COMPLETION A)(Cb : COMPLETION B) :
Poset_ISOMORPHISM Ca Cb :=
{|
 b := Ca2Cb_BIJ I Ca Cb;
 to_mono := Ca2Cb_mono I Ca Cb;
 from_mono := Cb2Ca_mono I Ca Cb;
|}.


Definition Ca2Cb_DCPO_ISO{A B: Poset}(I: Poset_ISOMORPHISM A B)
(Ca:COMPLETION A)(Cb : COMPLETION B) :
DCPO_ISOMORPHISM Ca Cb := poset_iso_dcpo_iso 
(Ca2Cb_Poset_ISO I Ca Cb).
