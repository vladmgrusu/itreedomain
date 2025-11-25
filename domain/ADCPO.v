From Stdlib Require Import FunctionalExtensionality ProofIrrelevance 
 IndefiniteDescription. 
From Domain Require Export Ideal.

Definition compacts_le{P: DCPO}(c : P) := 
    fun cc => is_compact cc /\ cc <= c.

Record ADCPO : Type :=
{
  algebraic_dcpo :> DCPO;
  algebraic_dir : forall c,
    is_directed (compacts_le (P := algebraic_dcpo) c);
  algebraic_lub : forall c,
    c = lub (d:=algebraic_dcpo) (compacts_le c)
            
}.


Arguments algebraic_dcpo {_}.
Arguments algebraic_dir {_} _.
Arguments algebraic_lub {_} _.


Definition is_ed_continuous{X Y : ADCPO}(f: X -> Y):=
forall cy x, is_compact cy -> cy <= f x -> 
exists cx, is_compact cx /\ cx <= x  /\ cy <= f cx.

Lemma continuous_ed_continuous{X Y: ADCPO} :
forall (f: X -> Y), is_continuous f -> is_ed_continuous f.
Proof.
intros f Hc.
specialize Hc as Hm.
apply continuous_implies_monotonic in Hm.
intros  cy x Hcy Hle.
specialize (algebraic_lub x) as Hal.
destruct (Hc _ (algebraic_dir x)) as (Hdf & Heqf).
rewrite <- Hal in Heqf.
rewrite Heqf in Hle.
specialize (Hcy _ Hdf _ (lub_is_lub _ Hdf) Hle).
destruct Hcy as (c & (z & (Hcz & Hlez) & Heqz) & Hlec); subst.
exists z ;split; auto.
Qed.


Lemma ed_continuous_mono_continuous{X Y: ADCPO} :
forall (f: X -> Y), 
is_monotonic f ->is_ed_continuous f -> is_continuous f.
Proof.
intros f Hm Hc.
apply continuous_alt_implies_continuous;auto.
intros S Hd.
specialize (monotonic_directed _ _ Hm Hd) as Hd'.
split; auto.
specialize (algebraic_lub (f(lub S))) as Hl.
rewrite Hl.
apply  forallex_lelub; auto.
 -
  apply algebraic_dir.

 - intros cy (Hcy & Hlecy).
specialize (Hc _ _ Hcy Hlecy).
destruct Hc as (cx & Hcx & Hle1 & Hle2).
destruct (Hcx _ Hd  _ (lub_is_lub _ Hd) Hle1) as (y & Hmy & Hle).
exists (f y); split; auto.
+
  now exists y.
+
  eapply trans ; [now apply Hle2|].
  now apply Hm.
Qed.  


Lemma continuous_iff_ed_continuous_mono{X Y: ADCPO} :
forall (f: X -> Y), 
is_continuous f <-> (is_monotonic f /\ is_ed_continuous f).
Proof.
split.
-
 intro Hc ; split.
 + now apply continuous_implies_monotonic.
 + now apply continuous_ed_continuous.
 -
  intros (Hm & Hc).
  now apply ed_continuous_mono_continuous.
Qed.  




Lemma nonempty_compacts_le{C: ADCPO} :
  forall (c: C), ~ is_empty (compacts_le c).
Proof.  
intro c.
now destruct (algebraic_dir c).
Qed.

Lemma compacts_le_upper{C: ADCPO} :
  forall (c: C), is_upper  (compacts_le c) c.
Proof.  
now intros c x (y & Heq); subst.
Qed.



Lemma compacts_le_directed{P : Poset}:
forall (c :IDEAL P),
  is_directed (P := ideals_Poset P)
    (fun cc  =>
       is_compact  (D := ideals_DCPO P) cc /\ cc <= c).
Proof.  
intros c.
destruct c as (S & (Hne & Hd) & Hc).
cbn in *.
repeat split.
-
  rewrite not_empty_member in *.
  rewrite not_empty_member in Hne.
  destruct Hne as (x & Hm).
  cbn.
  exists (Build_IDEAL _ (principal x) (principal_is_ideal x)).
  repeat split; cbn.
  +
    apply principal_is_compact.
  +  
    now rewrite principal_subset.
-
  cbn.
  intros x y Hmx Hmy.
  destruct Hmx as (Hxc & Hsub).
  apply compact_is_principal in Hxc.
  destruct Hxc as (Maxx & Heq).
  rewrite Heq in Hsub.
  rewrite principal_subset in Hsub; auto.
  destruct Hmy as (Hyc & Hsub').
  apply compact_is_principal in Hyc.
  destruct Hyc as (Maxy & Heq').
  rewrite Heq' in Hsub'.
  rewrite principal_subset in Hsub'; auto.
  destruct (Hd _ _ Hsub Hsub') as (z & Hmz & Hlexz & Hleyz).
  exists (Build_IDEAL _ (principal z) (principal_is_ideal z)).
  repeat split; cbn.
  +
    apply principal_is_compact.
  +
    now rewrite principal_subset.
  +
    rewrite <- subset_principal_iff.
    intros w Hw.
    rewrite Heq in Hw.
    assert (Hmw :  (member (principal Maxx) w)) by exact Hw.
    rewrite member_principal_iff in Hmw.
    eapply trans; eauto.
  +
    rewrite <- subset_principal_iff.
    intros w Hw.
    rewrite Heq' in Hw.
    assert (Hmw :  (member (principal Maxy) w)) by exact Hw.
    rewrite member_principal_iff in Hmw.
    eapply trans; eauto.
Qed.


Lemma lub_le_compacts{P : Poset}: forall c : IDEAL P,
  c =
  lub (compacts_le (P:=  (ideals_DCPO P)) c).
     
Proof.
intro c.
specialize (compacts_le_directed (P:= P) c) as Hd.
cbn in *.
unfold Ideal.ideals_DCPO_obligation_1.
destruct (oracle
(is_directed (P:= ideals_Poset P)
   (compacts_le (P:= ideals_DCPO P) c))); [| contradiction].

apply ideal_equal.
apply set_equal.
split; intro Hm.
-
  exists (principal x); split; [ | apply member_principal].
  exists (Build_IDEAL _ (principal x) (principal_is_ideal x)).
  cbn; repeat split; auto.
  + 
    apply principal_is_compact.
  +
    cbn.
    rewrite  principal_subset; auto.
    now destruct c as (S & Hd' & Hc).
-
  destruct Hm as (S & Hm & HM).
  cbn in *.
  destruct Hm as (I & (HcI & Hsub)& HeqS).
  cbn in *.
  rewrite <- HeqS in Hsub.
  apply (Hsub _ HM).
Qed.
  
    
Definition ideals_ADCPO (P : Poset) : ADCPO :=
{|
  algebraic_dcpo := ideals_DCPO P;
  algebraic_dir := compacts_le_directed;
  algebraic_lub := lub_le_compacts
|}.


Lemma ppo_isomorphic_compact_le{P P' : DCPO}
    (i : Poset_ISOMORPHISM P P'):
    forall c, fmap (compacts_le (P := P') (to i c)) (from i) =
              compacts_le (P:= P) c.
Proof.
intro c; apply set_equal; split; intro Hm.
-
  destruct Hm as (y & (Hc & Hle) & Heq); subst.
  split.
  +
    replace y with (to i (from i y)) in Hc; [| apply to_from].
    now apply (@isomorphic_compact_inv) with (i := poset_iso_dcpo_iso i). 
  +  
     replace c with (from i (to i c)) ; [| apply from_to].
    now apply from_mono.
-      
  destruct Hm as (Hc & Hle).
  exists (to i x); split.
  + 
    split.
    *
      now apply (@isomorphic_compact) with (i := poset_iso_dcpo_iso i).
    *
      now apply to_mono.
  +
    symmetry.
    apply from_to.
 Qed.  

 Lemma is_lub_fmap_compacts_le{P1 P2: DCPO}: 
 forall (f : P1 -> P2) (x:P1),
 is_monotonic_on f (fun x => is_compact x) -> 
 is_compact x ->
 is_lub (fmap (compacts_le x) f) (f x).
 Proof.
 intros f x Hm Hc.
 split.
 - 
  intros y Hmy.
  destruct Hmy as (z & (Hmcz & Hlez) & Heq); subst.
  apply Hm; auto.
 -
  intros y Hu.
  apply Hu.
  exists x; repeat split; auto.
  apply refl.
 Qed.  
  


 Program Definition compacts_Poset (A : ADCPO) : Poset :=
   {|
   carrier := {x : A | is_compact x};
   ord := fun x y => proj1_sig x <= proj1_sig y
   |}.


Next Obligation.
specialize (@default (@algebraic_dcpo A)) as a.
specialize (nonempty_compacts_le a) as Hne.
rewrite not_empty_member in Hne.
apply constructive_indefinite_description.
destruct Hne as (x & Hc & _).
now exists x.
Qed.

Next Obligation.
cbn; intros.
apply refl.
Qed.

Next Obligation.
cbn.
intros.
eapply trans; eauto.
Qed.

Next Obligation.
cbn.
intros.
assert (Heq: x =y) by (apply antisym; auto); subst.
f_equal.
apply proof_irrelevance.
Qed.

Lemma compacts_le_iso{P Q:DCPO}(I:DCPO_ISOMORPHISM P Q)
: forall (c:Q), fmap (compacts_le (from I c)) (to I) =
compacts_le c.
Proof.
intro c.
apply set_equal; split.
 -
  intros (c' & (Hc &Hle) & Heq); subst.
  split.
  +
  now apply isomorphic_compact with (i := I).
  +
  replace c with ((to I) (from I  c))by 
  now rewrite  to_from.
  now apply to_mono.
-
 intros (Hc & Hle).
 exists (from I x); split; [| now rewrite to_from].
 split; [| now apply from_mono].
 replace x with (to I (from I x)) in * by
  (now rewrite to_from).
  rewrite from_to.
  now apply isomorphic_compact_inv with (i := I).
 Qed. 
 
  
Lemma dcpo_iso_alg_dir{P:ADCPO}{Q:DCPO}(I:DCPO_ISOMORPHISM P Q)
: forall (c:Q), is_directed (compacts_le c).
Proof.
intro c.
specialize (@algebraic_dir P) as Ha.
specialize (Ha (from (b _ _ I) c)).
apply isomorphic_directed with (Iso := (iso _ I)) in Ha.
now rewrite compacts_le_iso in Ha.
Qed.    
   
    

Lemma dcpo_iso_alg_lub{P:ADCPO}{Q:DCPO}(I:DCPO_ISOMORPHISM P Q)
: forall (c:Q), c = lub (compacts_le c).
Proof.
intros c.
specialize (@algebraic_lub P) as Ha.
specialize (Ha (from (b _ _ I) c)).
assert (Heqc : to I (from I c) = to I (lub
(compacts_le
   (from I c)))) by now f_equal.
rewrite to_from in Heqc.
rewrite Heqc at 1.
specialize (to_is_continuous I) as Hct.
eapply continuous_implies_commutes_with_lub with (S := (compacts_le
(from I c))) (l := (lub
(compacts_le
   (from I c)))) in Hct; [ | apply algebraic_dir].
unfold commutes_with_lub in Hct.   
assert (Hll : is_lub (compacts_le
(from I c))
(lub
(compacts_le
   (from I c))) ) by 
    apply lub_is_lub, algebraic_dir.
specialize (Hct Hll); clear Hll.  
apply  is_lub_lub_eq1 in Hct; [ | apply monotonic_directed;
[apply to_mono | apply algebraic_dir]].
rewrite Hct.
now rewrite compacts_le_iso.
Qed.


Definition adcpo_from_dcpo_sig{P:ADCPO}{Q:DCPO}(I:DCPO_ISOMORPHISM P Q)
: {D:ADCPO | @algebraic_dcpo D = Q}.
now exists {|algebraic_dcpo := Q; 
algebraic_dir := dcpo_iso_alg_dir I; algebraic_lub := 
dcpo_iso_alg_lub I|}.
Qed.

Definition adcpo_from_dcpo{P:ADCPO}{Q:DCPO}(I:DCPO_ISOMORPHISM P Q) :
ADCPO :=  (proj1_sig (adcpo_from_dcpo_sig I)).

Lemma adcpo_from_cpo_eq{P:ADCPO}{Q:DCPO}(I:DCPO_ISOMORPHISM P Q):
@algebraic_dcpo (adcpo_from_dcpo I) = Q.
Proof.
unfold adcpo_from_dcpo.
apply proj2_sig.
Qed.

Definition adcpo_from_dcpo'{P:ADCPO}{Q:DCPO}(I:Poset_ISOMORPHISM P Q) 
:= adcpo_from_dcpo  (poset_iso_dcpo_iso I).