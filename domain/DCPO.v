From Stdlib Require Import IndefiniteDescription ProofIrrelevance.
From Domain Require Export Poset.


Record DCPO : Type := {
    dcpo_poset :> Poset;
    lub : forall (S : Setof dcpo_poset), dcpo_poset;
    lub_is_lub : forall S,  is_directed S ->  is_lub  S (lub S);
}.

Arguments dcpo_poset {_}.
Arguments lub {_} _.
Arguments lub_is_lub {_} _ _.



Lemma is_lub_lub_eq1{D:DCPO}:
  forall (S: Setof D)(d: D), 
is_lub S d -> is_directed S -> d = lub S.
Proof.
intros S d Hl Hd.
specialize (lub_is_lub S Hd) as Hl'.
eapply is_lub_unique; eauto.
Qed.


Lemma is_lub_lub_eq2{D:DCPO}:
forall (S S': Setof D)
  (Hd : is_directed S) (Hd': is_directed S'),
 is_lub S' (lub S)
 ->
  lub S =
    lub S'.
Proof.
intros S S' Hd Hd' Hl.
specialize (lub_is_lub _ Hd') as Hl'.
eapply is_lub_unique; eauto.  
Qed.

Lemma lub_is_upper{D:DCPO}: forall (S: Setof D),
is_directed S -> forall x, member S x -> x <= lub S.
Proof.
intros S Hd x Hm.
specialize (lub_is_lub _ Hd) as Hl'.
destruct Hl' as (Hu & _).
now apply (Hu x).
Qed.


Lemma lub_is_minimal{D:DCPO}: forall (S: Setof D),
is_directed S -> forall x, is_upper S x ->   lub S <= x.
Proof.
intros S Hd x Hu.
specialize (lub_is_lub _ Hd) as Hl'.
destruct Hl' as (_ & Hm).
now apply Hm.
Qed.


Lemma forallex_lelub  {D : DCPO} :
      forall (S S' : Setof D) (Hd : is_directed S) (Hd' : is_directed S'),
      (forall x, member S x -> exists y, member S' y /\ x <= y) ->
      lub  S <= lub S'.
Proof.
intros S S' Hd Hd' Hsub.
apply  lub_is_minimal; [apply Hd |].
intros x Hm.
destruct (Hsub _ Hm) as (y & Hmy & Hle).
eapply trans; eauto.
now apply lub_is_upper.
Qed.

Lemma lub_mono{D:DCPO} : forall (S S' : Setof D),
subset S S' -> is_directed S -> is_directed S' ->
lub S <= lub S'.
Proof.
intros S S' Hs Hd Hd'.
eapply forallex_lelub; eauto.
intros x Hmx.
exists x; split; auto.
apply refl.
Qed.


Lemma lub_single{D: DCPO}:
  forall (x : D), lub (single x) = x.
Proof.
intros x.
specialize (single_is_directed x) as Hd.                    
specialize (lub_is_lub (single x) Hd) as Hp.
specialize (is_lub_single x) as Hs.
eapply is_lub_unique; eauto.
Qed.

Lemma forallex_iff_lelub  {D : DCPO} :
  forall (S S' : Setof D)  (Hd : is_directed S) (Hd' : is_directed S'),
      (forall x, member S x -> is_compact x) ->
      ((forall x, member S x -> exists y, member S' y /\ x <= y) <->
          lub S<= lub S').
Proof.
intros S S'  Hd Hd' Hc.
split.
-
  intros Hae.
  now apply forallex_lelub.
-
  intros Hle x Hm.
  specialize (Hc _ Hm).
  specialize (lub_is_upper _ Hd _ Hm) as Hlu.
  assert (Hlex: x <= lub S') by 
    (eapply trans; eauto).
  unfold is_compact in Hc.
  destruct (Hc _ Hd' _ (lub_is_lub _ Hd' ) Hlex) as (y & Hmy & Hley).
  now exists y.
Qed.


Definition is_continuous{P1 P2 : DCPO}
  (f : P1 -> P2) := forall (S: Setof P1),
  is_directed  S ->
  is_directed  (fmap S f) /\
  f(lub S) =  lub  (fmap S f). 

Lemma continuous_implies_monotonic{P1 P2 : DCPO} :
  forall (f : P1 -> P2), is_continuous f -> is_monotonic f.
Proof.
intros f Hc x y Hle.
specialize (Hc (fun z => z = x \/ z = y)
              (ordered_pair_is_directed  x y  Hle)).
destruct Hc as (Hd &  Heq). 
specialize (lub_is_lub _  (ordered_pair_is_directed x y Hle)) as Hcup.
specialize (lub_is_lub _ Hd) as Hcup'.
specialize (ordered_pair_has_lub _ _ Hle) as Hopl.
eapply is_lub_unique in Hcup; eauto.
rewrite <- Hcup in Heq; subst.
assert (Hisl:
         is_lub (fmap (fun z : P1 => z = x \/ z = y) f) (f y))
by
  (rewrite Heq;
  now apply lub_is_lub).
destruct Hisl as (Hu & _).
apply (Hu (f x)).
exists x ; split; auto.
Qed.

Lemma continuous_implies_commutes_with_lub  {P1 P2 : DCPO} :
    forall (f : P1 -> P2), is_continuous f ->
                           forall S l, is_directed S -> commutes_with_lub f S l.
Proof.
intros f Hc S l Hd Hi.
specialize (Hc _ Hd).
destruct Hc as (Hd' & Heq).
specialize (lub_is_lub S Hd) as His'.
eapply is_lub_unique in Hi; eauto.
rewrite Hi in *.
rewrite Heq.
now apply lub_is_lub.
Qed.


Lemma mono_commutes_implies_continuous{P1 P2 : DCPO} : 
    forall (f : P1 -> P2),
      is_monotonic f ->
       (forall S l, is_directed S -> commutes_with_lub f S l) ->
      is_continuous f.
Proof.
intros f Hm Hall S Hd.
split; [apply (monotonic_directed _ _ Hm Hd) |].
specialize (Hall _ (lub S) Hd (lub_is_lub S Hd)).
specialize (lub_is_lub (fmap S f) (monotonic_directed _ _ Hm Hd)) as His.
eapply is_lub_unique; eauto.
Qed.

Lemma continuous_iff_mono_commutes{P1 P2 : DCPO} :  forall (f : P1 -> P2),
    is_continuous f <->
      (is_monotonic f /\
       (forall S l, is_directed S -> commutes_with_lub f S l)).
Proof.
 split ; intro HH.
 -
   split.
   +
     now apply continuous_implies_monotonic.
   +
     now apply continuous_implies_commutes_with_lub.
 -
   now apply mono_commutes_implies_continuous.
Qed.


Record DCPO_ISOMORPHISM (P1 P2 : DCPO)  : Type :=
{
  iso :>  Poset_ISOMORPHISM P1 P2;
  to_comm : forall S l, is_directed S -> commutes_with_lub (to iso) S l;
  from_comm : forall S l, is_directed S -> commutes_with_lub (from iso) S l         
}.

Arguments iso {_}.
Arguments to_comm {_} _ _ _.
Arguments from_comm {_} _ _ _.

Definition poset_iso_dcpo_iso{P1 P2: DCPO}: Poset_ISOMORPHISM P1 P2 ->
DCPO_ISOMORPHISM P1 P2.
intro Hi.
unshelve econstructor.
-
  exact Hi.
-
  intros S l Hd.
  now apply  to_commutes_with_lub.
-
  intros S l Hd.
  now apply from_commutes_with_lub.
Defined.  


Definition DCPO_ISOMORPHISM_refl (P: DCPO) :  DCPO_ISOMORPHISM P P. 
unshelve econstructor.
-
 exact (Poset_ISOMORPHISM_refl P).
-
  cbn.
  intros S l Hd Hl.
  now rewrite fmap_id. 
-
  intros S l Hd Hl.
  cbn.
  now rewrite fmap_id. 
Defined.

Definition DCPO_ISOMORPHISM_sym  (P1 P2: DCPO) :
  DCPO_ISOMORPHISM P1 P2 -> DCPO_ISOMORPHISM P2 P1.
intros (iso , Hc1 , Hc2).  
unshelve econstructor.
-
  exact (Poset_ISOMORPHISM_sym _ _ iso).
-
  intros S l Hd.
  now apply Hc2.
-
  intros S l Hd.
  now apply Hc1.
Defined.

Definition DCPO_ISOMORPHISM_trans  (P1 P2 P3: DCPO) :
  DCPO_ISOMORPHISM P1 P2 -> DCPO_ISOMORPHISM P2 P3 -> 
  DCPO_ISOMORPHISM P1 P3.
intros (iso1 , Hc1, Hc'1) (iso2, Hc2, Hc'2).
unshelve econstructor.
-
  now apply Poset_ISOMORPHISM_trans with (P2 := P2).
-
  intros S l Hd Hl.
  cbn.
  rewrite fmap_comp.    
  apply Poset_isomorphism_lub_from_to.
  cbn.
  do 2 rewrite <- fmap_comp.
  apply Poset_isomorphism_lub_from_to.
  rewrite <- fmap_comp.
  rewrite bijection_from_to.
  rewrite comp_id_left.
  rewrite bijection_from_to.
  now rewrite fmap_id.
-
  intros S l Hd Hl.
  cbn.
  rewrite fmap_comp.
  apply Poset_isomorphism_lub_to_from.
  cbn.
  do 2 rewrite <- fmap_comp.
  apply Poset_isomorphism_lub_to_from.
  rewrite <- fmap_comp.
  rewrite bijection_to_from.
  rewrite comp_id_left.
  rewrite bijection_to_from.
  now rewrite fmap_id.
Defined.


Lemma from_is_continuous{P P' : DCPO}(i : DCPO_ISOMORPHISM P P'):
  is_continuous (from i).
Proof.  
rewrite continuous_iff_mono_commutes.
    split.
    -
      apply from_mono.
    -
      apply from_comm.
Qed.


Lemma to_is_continuous{P P' : DCPO}(i : DCPO_ISOMORPHISM P P'):
  is_continuous (to i).
Proof.  
rewrite continuous_iff_mono_commutes.
    split.
    -
      apply to_mono.
    -
      apply to_comm.
Qed.   
  



Lemma isomorphic_compact{P P' : DCPO}(i : DCPO_ISOMORPHISM P P'):
  forall cc, is_compact (D:= P) cc -> is_compact (D := P') (to i cc).
Proof.
intros cc Hc S' Hd' l' Hl'  Hle.
specialize (monotonic_directed _ _ (from_mono _  _ i) Hd') as Hd.
eapply from_mono with (P1 := P)(p:= i)  in Hle .
rewrite from_to in Hle.
specialize (from_is_continuous i) as Hcf.
specialize (Hcf   _ Hd').
destruct Hcf as (Hd'' & Heq).
assert (Heqp  : Hd = Hd'') by apply proof_irrelevance.
replace (lub S') with l' in * by
 (now apply is_lub_lub_eq1). 
subst.
rewrite Heq in *.
specialize (Hc _  Hd''  _ (lub_is_lub _ Hd'') Hle). 
destruct Hc as (c & Hl & Hle').
apply inv_member_fmap in Hl.
destruct Hl as (x & Heq' & Hm).
subst.
exists x; split; auto.
replace x with (to i (from i x)) in *; [| apply to_from].
rewrite from_to in Hle'.
now apply to_mono.
Qed.

  
Lemma isomorphic_compact_inv{P P' : DCPO}
  (i : DCPO_ISOMORPHISM P P'):
  forall cc, is_compact (D := P') (to i cc) ->
             is_compact (D:= P) cc.
Proof.
intros cc Hc.
remember (DCPO_ISOMORPHISM_sym _ _ i) as j.    
replace cc with (to j (from j cc)) in *; [| apply to_from].
apply isomorphic_compact.
replace (to j) with (from i) in *.
- 
  now rewrite to_from in Hc.
-  
  now subst.
Qed.

Lemma isomorphic_compact_iff{P P' : DCPO}
  (i : DCPO_ISOMORPHISM P P'):
  forall cc, is_compact (D := P') (to i cc)  <->
             is_compact (D:= P) cc.
Proof.
intros cc; split; intro Hc.
-
  eapply isomorphic_compact_inv; eauto.
-
  now apply isomorphic_compact.
Qed.  


Lemma isomorphic_compact_from{P P' : DCPO}(i : DCPO_ISOMORPHISM P P'):
forall cc, is_compact (D:= P') cc -> is_compact (D := P) (from i cc).
Proof.
intros cc Hc.
remember  (DCPO_ISOMORPHISM_sym _ _ i) as j.
replace (from i) with (to j).
-
 now apply isomorphic_compact.
-
 subst.
 reflexivity.
Qed.

  
Lemma isomorphic_compact_from_inv{P P' : DCPO}
  (i : DCPO_ISOMORPHISM P P'):
  forall cc, is_compact (D := P) (from i cc) ->
             is_compact (D:= P') cc.
Proof.
intros cc Hc.
remember (DCPO_ISOMORPHISM_sym _ _ i) as j.    
replace cc with (from j (to j cc)) in *; [| apply from_to].
apply isomorphic_compact_from.
replace (from j) with (to i) in *.
- 
  now rewrite from_to in Hc.
-  
  now subst.
Qed.

Lemma isomorphic_compact_from_iff{P P' : DCPO}
  (i : DCPO_ISOMORPHISM P P'):
  forall cc, is_compact (D := P) (from i cc)  <->
             is_compact (D:= P') cc.
Proof.
intros cc; split; intro Hc.
-
  eapply isomorphic_compact_from_inv; eauto.
-
  now apply isomorphic_compact_from.
Qed.  


Lemma lub_eq{P: DCPO} :
  forall (S S' : Setof P) (Hd : is_directed S) (Hd' : is_directed S'),
   S = S' ->   lub S = lub S'.
Proof.
intros S S' Hd Hd' Heq.
subst.
reflexivity.
Qed.


Lemma id_is_continuous{P:DCPO}: 
 is_continuous (P1:= P) (P2 := P) id.
Proof.
intros S Hd.
rewrite fmap_id.
split; auto.
Qed.

Lemma comp_is_continuous{P1 P2 P3: DCPO}:
  forall (f : P2 -> P3) (g : P1 -> P2),
    is_continuous (P1 := P2) (P2 := P3) f
    -> is_continuous (P1:= P1)(P2 := P2) g ->
    is_continuous (f° g).
Proof.  
intros f g Hc2 Hc1 S Hd1.
specialize Hc1 as Hc1'.
apply continuous_implies_monotonic in Hc1'.
specialize Hc2 as Hc2'.
apply continuous_implies_monotonic in Hc2'.
unfold is_continuous in *.
destruct (Hc1 _ Hd1) as (Hd2 & Heq2).
destruct (Hc2 _ Hd2) as (Hd2' & Heq').
unfold "°".
unshelve eexists.
-
 apply monotonic_directed; auto.
 apply comp_is_monotonic; now apply 
 continuous_implies_monotonic.
-
  rewrite Heq2, Heq'.
  +
   apply lub_eq; auto.
   *
     apply monotonic_directed; auto.  
     now apply comp_is_monotonic.
   *
   now rewrite <- fmap_comp.
Qed.



Lemma cst_is_continuous{P1 P2: DCPO}: forall (a:P2),
    is_continuous (P1 := P1) (P2 := P2) (fun _ => a).
Proof.
intro a.
rewrite continuous_iff_mono_commutes.
split; [apply cst_is_monotonic|].
intros T l Hd Hl.
split.
-
  intros x (z & Hmz & Heq); subst.
  apply refl.
-
 intros y Huy.
 apply Huy.
 destruct Hd as (Hne & _).
 rewrite not_empty_member in Hne.
 destruct Hne as (x & Hm).
 now exists x.
Qed.  

Lemma lub_iso_poset{P:DCPO}{Q:Poset}:  
  Poset_ISOMORPHISM P Q -> forall (S:Setof Q), is_directed S ->
  {l : Q | is_lub S l}.
Proof.
intros Hi S Hd.
apply Poset_ISOMORPHISM_sym in Hi.
apply (isomorphic_directed Hi) in Hd.
remember (fmap S (to Hi)) as S'.
remember (lub S') as l'.
specialize (lub_is_lub S' Hd) as Hil.
remember (from Hi l') as l.
exists l.
subst.
now apply Poset_isomorphism_lub_to_from.
Qed.


Definition dcpo_from_poset_sig{P:DCPO}{Q:Poset}(I:Poset_ISOMORPHISM P Q)
: {D:DCPO & @dcpo_poset D = Q & DCPO_ISOMORPHISM P D}.
unshelve eexists {|dcpo_poset := Q; 
lub := fun S => 
  match (oracle (is_directed S)) with
  | left Hd => proj1_sig (lub_iso_poset I _ Hd)
  | right Hn => @default Q
  end|}.
-
 intros S Hd.
 cbn.
 destruct (oracle (is_directed S)); [| contradiction].
 apply proj2_sig.
-
 reflexivity.
-
 cbn.
 apply poset_iso_dcpo_iso;exact I.
Qed.



Definition dcpo_from_poset{P:DCPO}{Q:Poset}(I:Poset_ISOMORPHISM P Q)
: DCPO := (projT1 (sigT_of_sigT2 (dcpo_from_poset_sig I))).


Lemma dcpo_from_poset_eq{P:DCPO}{Q:Poset}(I:Poset_ISOMORPHISM P Q) :
@dcpo_poset(dcpo_from_poset I) = Q.
Proof.
exact (projT2 (sigT_of_sigT2 (dcpo_from_poset_sig I))).
Qed.


Definition dcpo_from_poset_iso{P:DCPO}{Q:Poset}(I:Poset_ISOMORPHISM P Q) :
DCPO_ISOMORPHISM P (dcpo_from_poset I) := 
 projT3 (dcpo_from_poset_sig I).



Lemma lem39part1{P:DCPO}: 
forall (S:Setof P) (comps : P -> Setof P),
is_directed S -> 
(forall x, member S x -> 
  (forall y, member (comps x) y -> is_compact y) /\ 
   is_directed (comps x)  /\ is_lub (comps x) x) ->
 is_directed (union (fun (V: Setof P) => exists x, 
 member S x /\ V = comps x)).
Proof.
intros S comps Hd Ha.
split.
- 
  rewrite not_empty_member.
  destruct Hd as (Hne & _).
  rewrite not_empty_member in Hne.
  destruct Hne as (x & Hmx).
  destruct (Ha _ Hmx) as (_  & Hdx & _).
  destruct Hdx as (Hnex & _).
  rewrite not_empty_member in Hnex.
  destruct Hnex as (y & Hmy).
  exists y, (comps x); split; auto.
  exists  x; split; auto.
-
  intros a b Hma Hmb.
  apply  member_union_member_one in Hma,Hmb.
  destruct Hma as (Sa  & Hma & Hma').
  destruct Hmb as (Sb  & Hmb & Hmb').
  destruct Hma as (ca & Hmca & Heqa); subst.
  destruct Hmb as (cb & Hmcb & Heqb); subst.
  destruct (Ha _ Hmca) as (Haca & Hda & Hla).
  destruct (Ha _ Hmcb) as (Hacb & Hdb & Hlb).
  specialize (Haca _ Hma').
  specialize (Hacb _ Hmb').
  destruct Hd as (_ & Hd).
  destruct (Hd _ _ Hmca Hmcb) as 
   (c & Hmc & Hleca & Hlecb).
  destruct Hla as (Hua & _).
  destruct Hlb as (Hub & _).
  specialize (Hua _ Hma').
  specialize (Hub _ Hmb').
  destruct (Ha _ Hmc) as (_ & Hdc & Hlc).
  specialize (lub_is_lub _ Hdc) as Hlc'.
  apply is_lub_unique with (x := c) in Hlc' ; auto.
  assert (Hac : a <= c) by (eapply trans; eauto).
  assert (Hbc: b <= c) by (eapply trans; eauto).
  rewrite Hlc' in *.
  rewrite <- Hlc' in Hmc.
  assert (Hdc' : is_directed (comps c)) by 
  now rewrite <- Hlc' in Hdc.
  specialize (Haca _ Hdc'  _ (lub_is_lub _ Hdc') Hac).
  specialize (Hacb _ Hdc' _ (lub_is_lub _ Hdc') Hbc).
  clear Hac Hbc Hleca Hlecb Hua Hub.
  destruct Haca as (c'a & Hmc'a & Hac'a).
  destruct Hacb as (c'b & Hmc'b & Hbc'b).
  destruct Hdc as (Hnec  & Hdc).
  rewrite <- Hlc' in Hdc.
  destruct (Hdc _ _ Hmc'a Hmc'b) as 
    (z  & Hmz & Hlea1 & Hlea2).
  exists z; repeat split; try 
    (eapply trans; eauto).
  exists (comps c); split; auto.
  exists c ; split; auto.
  Qed.


Definition continuous_alt{P1 P2:DCPO}(f : P1 -> P2) :=
forall (S : Setof P1) (Hd1 : is_directed S),
is_directed (fmap S f) /\
  f (lub S) <= lub (fmap S f).

Lemma continuous_alt_implies_continuous{P1 P2:DCPO} :
forall (f :  P1 -> P2), is_monotonic f ->
continuous_alt f -> is_continuous f.
Proof.
intros f Hm Hc S Hd.
specialize (Hc _ Hd).
destruct Hc as (Hd' & Hle).
split ; auto.
apply antisym;auto.
specialize (lub_is_lub _ Hd') as Hc.
destruct Hc as (_ & Hu).
apply Hu.
intros y (z & Hmz & Heq); subst.
apply Hm.
specialize (lub_is_lub _ Hd) as Hc.
destruct Hc as (Hm' & _).
now apply Hm'.
Qed.