From Stdlib Require Import IndefiniteDescription ProofIrrelevance.
From Domain Require Export ADCPO CPO.

Record COMPLETION (P : Poset) : Type :=
{
  alg :> ADCPO;
  inject : P -> alg;
  inject_bimono : forall p p', p <= p' <-> inject p <= inject p';
  inject_compact : forall p, is_compact (inject p);
  rev_inj : alg -> P;
  rev_inj_iff : forall cc p, is_compact cc -> 
  (rev_inj cc = p <-> inject p = cc)
}.    


Arguments alg {_} _.
Arguments inject {_ _}   _.
Arguments inject_bimono {_}. 
Arguments inject_compact {_ _} _.
Arguments rev_inj {_ _} _.
Arguments rev_inj_iff {_} _ _ _ _.


Lemma inject_injective{P:Poset}: forall (A : COMPLETION P),
    is_injective  (inject (c := A)).
Proof.
intro A.
apply bimono_injective.
unfold is_bimonotonic, is_monotonic,is_rev_monotonic; split; intros.
-  now rewrite <- inject_bimono.
-  now rewrite <- inject_bimono in H.
Qed.

Lemma inject_compacts{P:Poset} :
  forall (A : COMPLETION P) (cc : A),
    is_compact  cc <-> exists p, cc = inject  p.
Proof.
intros A cc.
split ; intro Hs.
-
  exists (rev_inj cc).
  symmetry.
  now rewrite <-rev_inj_iff.
-
  destruct Hs as (p & Heq).
  subst.
  apply inject_compact.
Qed.

Lemma rev_inj_bimono{P:Poset} :
   forall (A : COMPLETION P) (cc cc': A),
    is_compact cc -> is_compact cc' ->
      (cc <= cc' <-> rev_inj cc <= rev_inj cc').         
Proof.
intros A cc cc' Hc Hc'.  
remember  (rev_inj cc) as p.
remember  (rev_inj cc') as p'.
symmetry in Heqp,Heqp'.
rewrite rev_inj_iff in Heqp,Heqp'; auto.
rewrite <- Heqp, <-Heqp'.
split ; apply inject_bimono.
Qed.

Lemma rev_inj_injective{P:Poset}{A : COMPLETION P} :
forall (cc cc': A),
is_compact cc -> is_compact cc' -> rev_inj cc = rev_inj cc' -> 
cc = cc'.
Proof.
intros cc cc' Hc Hc' Heq.
apply antisym.
-  
  rewrite rev_inj_bimono; auto.
  rewrite Heq; apply refl.
-  
  rewrite rev_inj_bimono; auto.
  rewrite Heq; apply refl.
Qed.  


Lemma inject_rev_inj{P:Poset}: forall (M:COMPLETION P),
forall cc, is_compact cc ->
inject (c := M)  (rev_inj cc) = cc.
Proof.
intros M cc Hc.
now rewrite <- rev_inj_iff.
Qed.


Lemma rev_inj_inject{P:Poset}: forall (M:COMPLETION P),
forall cc, 
 rev_inj (c := M) (inject  cc) = cc.
Proof.
intros M cc.
rewrite rev_inj_iff; auto.
apply inject_compact.
Qed.


Definition ideal_completion (P : Poset) : COMPLETION P.
unshelve econstructor.
-
  exact (ideals_ADCPO P).
-
  intro p.
  cbn.
  exact (Build_IDEAL _ (principal p) (principal_is_ideal p)).
-
  cbn.
  intro I.
  destruct (oracle (is_principal I)).
  +
    apply constructive_indefinite_description in i.
    destruct i as (x & Hx).
    exact x.
  +  
   exact (@default P).
-
  split.
  +
    intros Hle.
    cbn.
    rewrite <- subset_principal_iff.
    intros y Hm.
    apply member_principal_iff in Hm.
    eapply trans; eauto.
  +
    intro Hle.
    cbn in Hle.
    rewrite <- subset_principal_iff in Hle.
    apply Hle,member_principal.
-
  intros p S Hd Hle.
  specialize (principal_is_compact p) as Hc.  
  apply  (Hc _ Hd Hle).

-
  cbn.
  intros cc p Hc.
  destruct (oracle (is_compact  (D := ideals_DCPO P) cc));
  [| exfalso; now apply n].
  remember ( constructive_indefinite_description
     _
     (compact_is_principal cc i)) as ci.
  destruct ci.
  clear Heqci.
  rewrite e.
  specialize (principal_is_principal x).
    destruct ( oracle
  (is_principal
     (principal x))); [ | contradiction].
 intros _.
 destruct (constructive_indefinite_description _ i0).
 apply principal_injective in e0;subst.
 split; intro Hs ; subst; clear i i0; cbn in e.
 +
   destruct cc.
   now apply ideal_equal.
 +
  now apply principal_injective in e;subst.
Qed.  



Program Definition self_completion (A:ADCPO) : COMPLETION (compacts_Poset A):=
{|
 alg := A;
 inject :=  fun (Hc : compacts_Poset A) => proj1_sig Hc;
 rev_inj := 
   fun a => 
     match (oracle (is_compact a)) with
      left H => (exist _ a H)
      | right _ => _
     end
|}.

Next Obligation.
reflexivity.
Qed.

Next Obligation.
apply constructive_indefinite_description.
specialize (nonempty_compacts_le a) as Hne.
rewrite not_empty_member in Hne.
destruct Hne as (x & Hc & _).
now exists x.
Defined.

Next Obligation.
intros.
cbn.
destruct (oracle (is_compact cc)); [clear H | contradiction].
split; intro Hs.
+
 now injection Hs; intros; subst.
+
 revert H0.
 rewrite Hs.
 intro H0.
 f_equal.
 apply proof_irrelevance.
Qed.


Lemma eq_reduce_to_compacts{A:ADCPO}{B:CPO}(f g : A -> B)(x:A):
is_continuous (P1 := A)(P2 := B) f ->
is_continuous (P1 := A)(P2 := B) g ->
(forall y, member (compacts_le x) y -> f y = g y)
->
f x = g x.
Proof.
intros Hf Hg Ha.
rewrite (algebraic_lub x).
destruct (Hf (compacts_le x)) as (_ & Heqf); [apply algebraic_dir |];
rewrite Heqf;clear Heqf.
destruct (Hg (compacts_le x)) as (_ & Heqg); [apply algebraic_dir |];
rewrite Heqg;clear Heqg.
f_equal.
apply set_equal; intro w; split ;
intros (u & Hcu & Heq); subst.
-
 exists u; split; auto.
-
 exists u; split; auto.
 now rewrite Ha.
 Qed.

Lemma corr_eq_reduce_to_compacts{A:Poset}{B:CPO}
(c: COMPLETION A)
(f g : c -> B)(x:c):
is_continuous (P1 := c)(P2 := B) f ->
is_continuous (P1 := c)(P2 := B) g ->
(forall (y:A),   f (inject (P:= A) (c := c) y) = 
g (inject  (P:= A) (c := c)y)) ->
f x = g x.
Proof.
intros Hf Hg Ha.
apply eq_reduce_to_compacts; auto.
intros z (Hc & Hm).
remember (rev_inj z) as rz.
symmetry in Heqrz.
rewrite rev_inj_iff in Heqrz; auto.
specialize (Ha rz).
now rewrite Heqrz in Ha.
Qed.


Lemma strong_corr_eq_reduce_to_compacts{A:Poset}{B:CPO}
(c: COMPLETION A)
(f g : c -> B)(x:c):
is_continuous (P1 := c)(P2 := B) f ->
is_continuous (P1 := c)(P2 := B) g ->
(forall (y:A),  (inject (P:= A) (c := c) y) <= x -> f (inject (P:= A) (c := c) y) = 
g (inject  (P:= A) (c := c)y)) ->
f x = g x.
Proof.
intros Hf Hg Ha.
apply eq_reduce_to_compacts; auto.
intros z (Hc & Hm).
remember (rev_inj z) as rz.
symmetry in Heqrz.
rewrite rev_inj_iff in Heqrz; auto.
specialize (Ha rz).
rewrite Heqrz in Ha.
apply Ha,Hm.
Qed.

