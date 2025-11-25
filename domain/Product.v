From Stdlib Require Import FunctionalExtensionality Logic.Eqdep. 
(*PropExtensionality IndefiniteDescription  Classical.*)
From Domain Require Export Completion CPO.

Program Definition PROD_Poset(A B: Poset):= 
    {|
       carrier := A * B; 
       default := (@default A, @default B);
       ord := fun x y => fst x <= fst y /\ snd x <= snd y;
       refl := ltac: (split; apply refl);
       (*trans := ltac:(cbn in *; split; eapply trans; eauto);*)
    |}.

Next Obligation.    
cbn in *; split; eapply trans; eauto.
Qed.

Next Obligation.
cbn in *; f_equal; apply antisym; auto.
Qed.

Lemma fst_is_monotonic{A B : Poset}: 
is_monotonic (P1 := PROD_Poset A B) fst.
Proof.
now intros (x,y) (u,v) (Hle,Hle').
Qed.


Lemma snd_is_monotonic{A B : Poset}: 
is_monotonic (P1 := PROD_Poset A B) snd.
Proof.
now intros (x,y) (u,v) (Hle,Hle').
Qed.


Lemma is_directed_fst{A B : Poset}(S: Setof (A*B)):
is_directed (P := PROD_Poset A B) S -> is_directed (fmap S fst).
Proof.
intro Hd.
apply (@monotonic_directed (PROD_Poset A B)); 
[ apply fst_is_monotonic | assumption].
Qed. 


Lemma is_directed_snd{A B : Poset}(S: Setof (A*B)):
is_directed (P := PROD_Poset A B) S -> is_directed (fmap S snd).
Proof.
intro Hd.
apply (@monotonic_directed (PROD_Poset A B)); 
[ apply snd_is_monotonic | assumption].
Qed. 


Lemma is_directed_cprod{A B : Poset}(S1 : Setof A)(S2 : Setof B):
is_directed S1 -> is_directed S2 -> 
 is_directed (P := PROD_Poset A B)  (cprod S1 S2).
Proof.
intros (Hne1 & Hd1) (Hne2 & Hd2).
split.
- 
 repeat rewrite not_empty_member in *|-.
 rewrite not_empty_member.
 destruct Hne1 as (a & Hma).
 destruct Hne2 as (b & Hmb).
 now exists (a,b). 
-
 intros (x1,y1) (x2,y2) (Hmx1 & Hmx2) (Hmy1 & Hmy2); cbn in *.
 destruct (Hd1 _ _ Hmx1 Hmy1) as (z1 & Hmz1 & Hlex1z1 & Hley1z1).
 destruct (Hd2 _ _ Hmx2 Hmy2) as (z2 & Hmz2 & Hlex2z2 & Hley2z2).
 exists (z1,z2); repeat split; auto.
Qed. 



Lemma is_lub_prod_fst{A B: Poset}(S : Setof (A*B))(l : A* B):
is_lub (P := PROD_Poset A B) S l ->
is_lub (fmap S fst) (fst l).
Proof.
intros  (Hu & Hm).
split; cbn in *.
-
 intros x ((p,q) & Hmt & Heq); cbn in *; subst.
 destruct l as (l,r); cbn in *.
 specialize (Hu _ Hmt).
 now inversion Hu.
-
 intros y Hu'.
 destruct l as (l,r); cbn in *.
 assert (Hu'' : is_upper (P := PROD_Poset A B) S (y,r)).
 {
    intros (u,v) Hmz.
    constructor; cbn in *.
    -
     apply Hu'.
     now exists (u,v).
    -
     now destruct (Hu _ Hmz).
 }
 now destruct (Hm _ Hu'').
 Qed.
 

 Lemma is_lub_prod_snd{A B: Poset}(S : Setof (A*B))(l : A* B):
 is_lub (P := PROD_Poset A B) S l ->
 is_lub (fmap S snd) (snd l).
 Proof.
 intros (Hu & Hm).
 split; cbn in *.
 -
  intros x ((p,q) & Hmt & Heq); cbn in *; subst.
  destruct l as (l,r); cbn in *.
  specialize (Hu _ Hmt).
  now inversion Hu.
 -
  intros y Hu'.
  destruct l as (l,r); cbn in *.
  assert (Hu'' : is_upper (P := PROD_Poset A B) S (l,y)).
  {
     intros (u,v) Hmz.
     constructor; cbn in *.
     -
     now destruct (Hu _ Hmz).
     -
      apply Hu'.
      now exists (u,v).
  }
  now destruct (Hm _ Hu'').
Qed.

Lemma is_prod_lub{A B: Poset}(S : Setof (A*B))(l : A* B):
is_lub (fmap S fst) (fst l) ->
 is_lub (fmap S snd) (snd l) ->
  is_lub (P := PROD_Poset A B) S l.
Proof.
intros (Hu1 & Hm1) (Hu2 & Hm2).
destruct l as (l,r).
cbn in *.
split.
-
 intros (p,q) Hmpq.
 constructor;cbn.
 +
  apply Hu1.
  now exists (p,q).
 +
  apply Hu2.
  now exists (p,q).
-
 intros (u,v) Huv.
 constructor;cbn.
 +
  apply Hm1.
  intros x ((s,t) & Hmst & Heq); subst; cbn.
  specialize (Huv _ Hmst).
  now inversion Huv.
 +
  apply Hm2.
  intros x ((s,t) & Hmst & Heq); subst; cbn.
  specialize (Huv _ Hmst).
  now inversion Huv.
Qed.  


Program Definition PROD_DCPO (A B : DCPO) : DCPO :=
{|
  dcpo_poset := PROD_Poset A B;
  lub := fun S => 
    (lub (d:= A) (fmap S fst),lub (d := B)(fmap S snd)) 
|}.

Next Obligation.
destruct (oracle (is_directed (P := PROD_Poset A B)S)); 
[clear H | contradiction].
apply is_prod_lub; cbn; apply lub_is_lub; 
 [now apply is_directed_fst | now apply is_directed_snd].
Qed.

Program Definition PROD_CPO (A B : CPO) : CPO :=
{|
dcpo_cpo := PROD_DCPO A B;
bot := (@bot A, @bot B)
|}.

Next Obligation.
cbn; split; apply bot_least.
Qed.

Lemma prod_lub_dir{A B: DCPO}(S : Setof (A*B)):
is_directed (P := PROD_Poset A B) S ->
lub (d := PROD_DCPO A B) S =
(lub (d := A) (fmap S fst),lub (d := B)(fmap S snd)).
Proof.
intros Hd.
cbn.
destruct (oracle (is_directed (P := PROD_Poset A B)S)); 
[reflexivity | contradiction ].
Qed.


Lemma is_compact_fst{A B: DCPO}:
forall c, 
is_compact (D := PROD_DCPO A B) c -> is_compact (fst c).
Proof.
intros (l,r) Hc; cbn.
intros S Hd lu Hlu Hle.
apply is_lub_lub_eq1 in Hlu; auto; subst.
remember (fmap S (fun x => (x, r))) as S'.
assert (Hd' : is_directed (P := PROD_Poset A B) S').
{
  subst.
  apply @monotonic_directed; auto.
  intros x y Hle'.
  constructor;auto.
  apply refl.
}

assert (Hle' : 
 (lub S,r) = (lub (d := PROD_DCPO A B) S')).
{
  rewrite prod_lub_dir; auto.
  subst.
  f_equal.
  -
   rewrite <- fmap_comp.
   cbn.
   replace (fst ° (fun x : A => (x, r))) with (@id A); 
   [ | unfold comp; extensionality e; auto].
   now rewrite fmap_id.
  -
  rewrite <- fmap_comp.
  replace (snd ° (fun x : A => (x, r))) with (fun (_:A) => r);
  [ | unfold comp; extensionality e; auto].
  rewrite fmap_cst; [now rewrite lub_single| now destruct Hd].
}
assert (Ho :
ord (p := PROD_Poset A B) (l,r)  (lub  (d := PROD_DCPO A B) S')).
{ 
   rewrite <- Hle'. 
   constructor; auto.
  apply refl.
}
specialize (Hc _ Hd'  _ (@lub_is_lub  (PROD_DCPO A B) _ Hd') Ho).
destruct Hc as ((d,c) & Hm & Hlec).
rewrite HeqS' in Hm.
destruct Hm as (x & Hmx & Heq); injection Heq; intros; subst.
inversion Hlec ; subst; cbn in *.
now exists x.
Qed.


Lemma is_compact_snd{A B: DCPO}:
forall c, 
is_compact (D := PROD_DCPO A B) c -> is_compact (snd c).
Proof.
intros (l,r) Hc; cbn.
intros S Hd lu Hlu Hle.
apply is_lub_lub_eq1 in Hlu; auto; subst.
remember (fmap S (fun x => (l, x ))) as S'.
assert (Hd' : is_directed (P := PROD_Poset A B) S').
{
  subst.
  apply @monotonic_directed; auto.
  intros x y Hle'.
  constructor;auto.
  apply refl.
}

assert (Hle' : 
 (l,lub S) = (lub (d := PROD_DCPO A B) S')).
{
  rewrite prod_lub_dir; auto.
  subst.
  f_equal.
  -
  rewrite <- fmap_comp.
  replace (fst ° (fun x : B => (l, x))) with (fun (_:B) => l);
  [ | unfold comp; extensionality e; auto].
  rewrite fmap_cst; [now rewrite lub_single| now destruct Hd].
  -
   rewrite <- fmap_comp.
   cbn.
   replace (snd ° (fun x : B => (l, x))) with (@id B); 
   [ | unfold comp; extensionality e; auto].
   now rewrite fmap_id.

}
assert (Ho :
ord (p := PROD_Poset A B) (l,r)  (lub  (d := PROD_DCPO A B) S')).
{
   rewrite <- Hle'.
   constructor; auto; cbn.
   apply refl.
}
specialize (Hc _ Hd'  _ (@lub_is_lub (PROD_DCPO A B) _ Hd') Ho).
destruct Hc as ((d,c) & Hm & Hlec).
rewrite HeqS' in Hm.
destruct Hm as (x & Hmx & Heq); injection Heq; intros; subst.
inversion Hlec ; subst; cbn in *.
now exists x.
Qed.
  

Lemma is_compact_prod{A B: DCPO}:
forall c, is_compact (fst c) -> is_compact (snd c) ->
is_compact (D := PROD_DCPO A B) c.
Proof.
intros (l,r) Hcl Hcr; cbn in *.
intros S Hd lu Hlu   Hle; cbn in S.
specialize Hd as Hdl.
eapply (@is_lub_lub_eq1( PROD_DCPO A B)) with (d := lu) in Hdl;
auto; subst.
specialize Hd as Hdl.
apply is_directed_fst in Hdl.
specialize Hd as Hdr.
apply is_directed_snd in Hdr.
rewrite prod_lub_dir in Hle; auto.
inversion Hle; subst; clear Hle; cbn in *.
specialize (Hcl _ Hdl _ (lub_is_lub _ Hdl) H).
destruct Hcl as (a & Hma & Hlea).
specialize (Hcr _ Hdr _ (lub_is_lub _ Hdr) H0).
destruct Hcr as (b & Hmb & Hleb).
destruct Hma as (a' & Hma' & Heq); subst.
destruct Hmb as (b' & Hmb' & Heq); subst.
destruct a'; cbn in *.
destruct b'; cbn in *.
destruct Hd as (_ & Hd).
specialize (Hd _ _ Hma' Hmb').
destruct Hd as ((u,v) & Hmuv & Hle1 & Hle2).
inversion Hle1; inversion Hle2; cbn in *; subst.
exists (u,v); repeat split; cbn; auto.
- 
 apply trans with (y := c);auto.
- 
 apply trans with (y := c2); auto.
Qed.



 
Lemma is_compact_prod_iff{A B: DCPO}:
forall c, is_compact (D := PROD_DCPO A B) c <->
 (is_compact (fst c) /\ is_compact (snd c)).
Proof.
intro c ; split; intro Hc.
- 
 split; [now apply is_compact_fst | now apply is_compact_snd].
-
 apply is_compact_prod; tauto.
Qed.

Lemma compacts_le_prod{A B: DCPO}:
forall c, compacts_le (P := PROD_DCPO A B) c =
cprod (compacts_le (fst c)) (compacts_le (snd c)).
Proof.
intros c.
apply set_equal; split; intros Hmx.
-
 destruct Hmx as (Hcx & Hlex).
 rewrite is_compact_prod_iff in Hcx.
 inversion Hlex; subst.
 destruct Hcx as (Hcf & Hcs).
 repeat split; auto.
-
 destruct Hmx as  ((Hf & Hlef) & (Hs & Hles)).
 split; [| now constructor].
 now rewrite is_compact_prod_iff.
 Qed. 


 Lemma my_algebraic_dir{A B : ADCPO}:
 forall c,
   is_directed (compacts_le (P := PROD_DCPO A B)  c).
 Proof.
 intro c.
 cbn in *.
 rewrite compacts_le_prod.
 apply is_directed_cprod; apply  algebraic_dir.
Qed.

Lemma my_algebraic_lub{A B : ADCPO}:
forall c, c = lub (d := PROD_DCPO A B)(compacts_le c).
Proof.
intros c.
cbn in c.
rewrite compacts_le_prod.
rewrite prod_lub_dir;
  [| rewrite <- compacts_le_prod; apply my_algebraic_dir].
destruct c as (a,b); cbn ; f_equal.
-
 rewrite fmap_cprod_fst; [apply algebraic_lub |].
 now destruct (algebraic_dir b).
-
rewrite fmap_cprod_snd; [apply algebraic_lub |].
now destruct (algebraic_dir a).
Qed.



Definition PROD_ADCPO(A B : ADCPO): ADCPO :=
  {|
    algebraic_dcpo := PROD_DCPO A B;
    algebraic_dir := my_algebraic_dir;
    algebraic_lub := my_algebraic_lub
  |}.




Program Definition PROD_COMP{A B : Poset}
(Ca : COMPLETION A) (Cb: COMPLETION B) :
COMPLETION (PROD_Poset A B) :=
{|
  alg := PROD_ADCPO (alg Ca) (alg Cb);
  inject :=
   fun (x : A*B) =>
   ((inject (fst x)), (inject (snd x)));
  rev_inj :=  fun cc => ((rev_inj (fst cc)), (rev_inj (snd cc)))
|}.



Next Obligation.
cbn.
split; intros (Hle& Hle'); split.
- now apply inject_bimono.
- now apply inject_bimono.
- now apply inject_bimono in Hle.
- now apply inject_bimono in Hle'.
Qed.

Next Obligation.
cbn.
apply is_compact_prod_iff;split;cbn;
apply inject_compact.
Qed.

Next Obligation.
cbn ; split; intro Hinj;
injection Hinj; intros ; subst;f_equal;
try apply inject_rev_inj; try apply rev_inj_inject.
-
 now apply is_compact_fst in H.
-
now apply is_compact_snd in H.
Qed.

(* argument-wise monotonicity and continuity *)

Lemma is_monotonic_fst_arg{A B C: Poset}(f : A * B -> C):
is_monotonic (P1 := PROD_Poset A B) f -> 
forall b, is_monotonic (fun a => f (a, b)).
Proof.
intros Hm b a a' Hle.
apply Hm;  constructor; cbn; auto; apply refl.
Qed.

Lemma is_continuous_fst_arg{A B C: DCPO}(f : A * B -> C):
is_continuous (P1 := PROD_DCPO A B) f -> 
forall b, is_continuous (fun a => f (a, b)).
Proof.
intros Hc b.
rewrite continuous_iff_mono_commutes.
rewrite continuous_iff_mono_commutes in Hc.
destruct Hc as (Hm & Hc); split; [now apply is_monotonic_fst_arg |].
intros S l Hd Hlub.
rewrite <- fmap_cprod_single_right.
apply Hc.
- apply is_directed_cprod; auto.
  apply single_is_directed.
-
 apply is_prod_lub; cbn.
 +
  rewrite fmap_cprod_fst; auto.
  apply single_not_empty.
 +
 rewrite fmap_cprod_snd; [ | now destruct Hd].
 apply is_lub_single.
Qed. 
   

Lemma is_monotonic_snd_arg{A B C: Poset}(f : A * B -> C):
is_monotonic (P1 := PROD_Poset A B) f -> 
forall a, is_monotonic (fun b => f (a, b)).
Proof.
intros Hm a b b' Hle.
apply Hm;  constructor; cbn; auto; apply refl.
Qed.

Lemma is_continuous_snd_arg{A B C: DCPO}(f : A * B -> C):
is_continuous (P1 := PROD_DCPO A B) f -> 
forall a, is_continuous (fun b => f (a, b)).
Proof.
intros Hc a.
rewrite continuous_iff_mono_commutes.
rewrite continuous_iff_mono_commutes in Hc.
destruct Hc as (Hm & Hc); split;
 [now apply is_monotonic_snd_arg |].
intros S l Hd Hlub.
rewrite <- fmap_cprod_single_left.
apply Hc.
- apply is_directed_cprod; auto.
  apply single_is_directed.
-
 apply is_prod_lub; cbn.
 +
  rewrite fmap_cprod_fst; [ | now destruct Hd].
  apply is_lub_single.
 +
  rewrite fmap_cprod_snd; auto. 
  apply single_not_empty.
Qed. 
   


Lemma argwise_monotonic{A B C: Poset}(f : A * B -> C):
(forall a, is_monotonic (fun b => f (a, b))) ->
(forall b, is_monotonic (fun a => f (a, b))) ->
is_monotonic (P1 := PROD_Poset A B) f.
Proof.
intros Hma Hmb (a,b) (a',b') (Ha,Hb); cbn in *.
apply trans with (y := f(a', b)).
-
 now apply Hmb.
-
now apply Hma.
Qed.


Lemma argwise_continuous_aux{A B C:DCPO}
(f : A * B -> C)(S: Setof (A*B)) :
is_monotonic (P1 := PROD_DCPO A B)f ->
is_directed (P := PROD_DCPO A B)  S ->
is_directed ((fmap (fmap S snd)
(fun y : B =>
 lub
   (fmap (fmap S fst)
      (fun x : A =>
       f (x, y)))))
).
Proof.
intros Hmon Hd.
apply monotonic_directed;
 [|apply (monotonic_directed (P1 :=  PROD_Poset A B)) ; auto;
 apply snd_is_monotonic].
intros x y Hle.
do 2 rewrite <- fmap_cprod_single_right.
apply forallex_lelub; 
try apply (monotonic_directed (P1 :=  PROD_Poset A B)); 
auto; try apply is_directed_cprod; try apply single_is_directed;
try apply (monotonic_directed (P1 :=  PROD_Poset A B));auto;
try apply fst_is_monotonic.
intros u ((v,w) & (Hmv,Hmw) & Heq); subst; cbn in *.
rewrite member_single_iff in Hmw; subst.
destruct Hmv as (z & Hmz & Heq);subst.
destruct z as (l,r); cbn in *.
exists (f (l,y)); split.
-
  exists (l,y); split; auto.
  split; cbn; [ | apply member_single].
  now exists (l,r).
-
  apply Hmon; split; auto; apply refl.  
Qed.

Lemma argwise_continuous{A B C: DCPO}(f : A * B -> C):
(forall a, is_continuous (fun b => f (a, b))) ->
(forall b, is_continuous (fun a => f (a, b))) ->
is_continuous (P1 := PROD_DCPO A B) f.
Proof.
intros Hca Hcb.
assert (Hfm : is_monotonic (P1 := PROD_Poset A B)f).
{
  apply argwise_monotonic; intro; 
  apply continuous_implies_monotonic; auto.
}
apply continuous_alt_implies_continuous; auto.
intros S Hd.
assert (Hfd : is_directed (fmap S f)) by
(apply monotonic_directed; auto).
assert (Hdf : is_directed (fmap S fst)) by
   (apply (monotonic_directed ( P1 := PROD_DCPO A B)); 
    auto; apply fst_is_monotonic).
assert (Hds : is_directed (fmap S snd)) by
   (apply (monotonic_directed ( P1 := PROD_DCPO A B)); 
    auto; apply snd_is_monotonic).
split; auto.
remember (lub S) as l.
specialize ( argwise_continuous_aux _  _ Hfm Hd) as Haux0.
assert (Hl1 : f l = lub (fmap (fmap S snd) (fun y : B => f (fst l, y)))).
{
  subst.
  specialize (Hca (fst (lub S))).
  rewrite continuous_iff_mono_commutes in Hca.
  destruct Hca as (Hma & Hca); cbn in *.
  destruct (oracle (is_directed (P := PROD_Poset A B)S)); [ | contradiction].
  unfold commutes_with_lub in Hca.
  cbn in *.
  specialize (Hca _  (lub (fmap S snd)) Hds (lub_is_lub _ Hds)).
  apply is_lub_lub_eq1 in Hca; auto.
  apply monotonic_directed; auto.
}
assert (Hl2 : forall y:B, member (fmap S snd ) y -> 
f (fst l, y) = lub (fmap (fmap S fst) (fun x => f (x,y)))
).
{
  intros y ((v,w) & Hvw & Heq); cbn in *; subst.
  destruct (oracle (is_directed (P := PROD_Poset A B)S)); 
  [ | contradiction].
  cbn in *.
  specialize (Hcb w).
  rewrite continuous_iff_mono_commutes in Hcb.
  destruct Hcb as (Hmb & Hcb); cbn in *.
  unfold commutes_with_lub in Hcb.
  cbn in *.
  specialize (Hcb _ _ Hdf (lub_is_lub _ Hdf)).
  apply is_lub_lub_eq1 in Hcb; auto.
  apply monotonic_directed; auto.
}
assert (Hl3 : f l = lub (fmap (fmap S snd)
(fun y : B =>
 lub
   (fmap (fmap S fst)
      (fun x : A => f (x, y)))))
).
{
  rewrite Hl1.
  f_equal.
  apply set_equal; split; intro Hmx.
  -
    destruct Hmx as (y & Hmy & Heq); subst.
    rewrite Hl2; auto.
    now exists y.
  -
   destruct Hmx as (y & Hmy & Heq); subst.
   exists y; split; auto.
   rewrite Hl2;auto.
}
clear Hl1 Hl2.
assert (Hl1 : forall x y,
member (fmap S fst) x -> member (fmap S snd) y -> exists u v,
member S (u,v) /\ x <= u /\ y <= v).
{
intros x y ((u,v) & Hmuv & Heq) ((a,b) & Hmab & Heq'); subst.
cbn.
destruct Hd as (_ & Hd).
specialize (Hd _ _ Hmuv Hmab).
destruct Hd as 
((l,r) &Hmlr & (Hel1 & Hler1) &
(Hlel2 & Hler2)); cbn in *.
exists l,r; split; auto.
}
assert(Hl2 : forall x y,
member (fmap S fst) x -> member (fmap S snd) y -> 
f (x,y) <= lub (fmap S f)).
{
  intros x y Hmx Hmy; cbn in *; subst.
  specialize (Hl1 _ _ Hmx Hmy).
  destruct Hl1 as (u & v & Hmuv & Hle1 & Hle2).
  apply trans with (y := f (u,v)).
  -
   now apply Hfm.
  -
   apply lub_is_upper; auto.
   now exists (u,v).  
}
rewrite Hl3.
apply lub_is_minimal; [apply Haux0 |].
intros x (y & ((z,w) & Hmz & Heq')  & Heq); cbn; subst.
cbn.
apply lub_is_minimal;
[apply monotonic_directed; auto; now apply is_monotonic_fst_arg | ].
intros x (u & ((v,k) & Hmv & Heq') & Heq); subst;
cbn.
apply Hl2; eexists; eauto.
Qed.


(* n-ary product *)
Fixpoint Prodn(A:Type) (n:nat) : Type :=
match n with
0 => unit
| S n' =>  A *(Prodn A n')
end.

Global Obligation Tactic := idtac.
Program Definition unit_Poset : Poset :=
{|
  carrier := unit;
  default := tt;
  ord := eq;
  refl := @eq_refl unit;
  trans := @eq_trans unit;
|}.

Next Obligation.
intros x y H _; exact H.
Qed.

Fixpoint Prodn_Poset(A:Poset) (n:nat) : Poset :=
match n with
0 => unit_Poset
| S n' =>  PROD_Poset A (Prodn_Poset A n') 
end.

(**
Definition Prodn_ord(A:Poset) (n:nat) :
 Prodn A n -> Prodn A n -> Prop :=
  (Prodn_Poset A n).(ord).
*)

Lemma unit_directed: forall (S: Setof unit),
is_directed (P := unit_Poset) S <-> S = single tt.
Proof.
split; intro Hd.
-
 destruct Hd as (Hne & _).
 rewrite not_empty_member in Hne.
 destruct Hne as (x & Hmx).
 destruct x; subst.
 apply set_equal; split; intros Hm.
 +
  destruct x; subst;apply member_single.
 +
  rewrite member_single_iff in Hm; now subst.
-
 subst.
 apply @single_is_directed.
Qed.    

Program Definition unit_DCPO : DCPO :=
{|
dcpo_poset := unit_Poset;
lub := fun (_:Setof unit) => tt;
|}.

Next Obligation.
intros S Hd.
rewrite unit_directed in Hd;subst.
apply @is_lub_single.
Qed.



Fixpoint Prodn_DCPO(A:DCPO) (n:nat) : DCPO :=
match n with
0 => unit_DCPO
| S n' =>  PROD_DCPO A (Prodn_DCPO A n') 
end.


Lemma unit_compact : forall (x:unit),
is_compact  (D := unit_DCPO) x <-> x = tt.
Proof.
intros x; destruct x; subst; auto;split; intros; auto.
intros S Hd Hle.
rewrite unit_directed in Hd; subst.
now exists tt.
Qed.

Lemma unit_compacts_le : forall (x:unit),
compacts_le (P := unit_DCPO) x = single tt.
Proof.
intro x; destruct x; apply set_equal; split; intro Hm.
-
  destruct Hm as (Hc & _).
  rewrite unit_compact in Hc;now subst.
-
  rewrite member_single_iff in Hm; subst; split.
  + now rewrite unit_compact.
  + now apply refl.
Qed.

Lemma unit_algebraic_dir : 
forall (x:unit), is_directed (compacts_le (P := unit_DCPO) x ).
Proof.
intro x; destruct x; subst.
rewrite unit_compacts_le.
now apply unit_directed.
Qed.

Lemma unit_algebraic_lub :
forall (x:unit), x = lub (compacts_le (P := unit_DCPO) x).
Proof.
intros x; destruct x; reflexivity.
Qed.

Definition unit_ADCPO : ADCPO :=
{|
  algebraic_dcpo := unit_DCPO;
  algebraic_dir := unit_algebraic_dir;
  algebraic_lub := unit_algebraic_lub
|}.



Fixpoint Prodn_ADCPO(A:ADCPO) (n:nat) : ADCPO :=
match n with
0 => unit_ADCPO
| S n' =>  PROD_ADCPO A (Prodn_ADCPO A n')
end.


Program Definition unit_COMP : COMPLETION unit_Poset :=
{|
  alg := unit_ADCPO;
  inject := id;
  rev_inj := id  
|}.

Next Obligation.
intros p p'; destruct p ; destruct p'; subst; split; auto.
Qed.

Next Obligation.
intro p; destruct p; cbn.
now apply unit_compact.
Qed.

Next Obligation.
intros x y Hc; destruct x; destruct y ; subst; cbn;
 tauto.
Qed.

Fixpoint Prodn_COMP(A:Poset) (C:COMPLETION A) (n:nat) : 
COMPLETION (Prodn_Poset A n):=
match n with
0 => unit_COMP
| S n' =>  PROD_COMP C (Prodn_COMP A C n')
end.

(*Alternative order definition for finite product, together with an isomorphism 
with the above definiotion, convenient for technical reasons *)

Inductive Prodn_le{A:Poset}: forall n, Prodn A n -> Prodn A n -> Prop :=
|tt_le : Prodn_le 0 tt tt
|star_le : forall n (a a':A) p p', 
ord a a' -> Prodn_le n p p' -> Prodn_le (S n) (a,p) (a',p').



Lemma Prodn_le_refl{A:Poset}: forall n (p:Prodn A n), Prodn_le n p p.
Proof.
induction n; intro p; destruct p ; constructor; 
 [apply refl | now apply IHn].
Qed.


Lemma Prodn_le_trans{A:Poset}: forall n (p1 p2 p3:Prodn A n),
 Prodn_le n p1 p2 -> Prodn_le n p2 p3 -> Prodn_le n p1 p3.
Proof.
induction n; intros p1 p2 p3 Hle1 Hle2; 
inversion Hle1; subst; inversion Hle2; subst.
-
 apply inj_pair2 in H0,H1,H2,H3;subst;auto.
-
 apply inj_pair2 in H2,H3,H6,H7;subst.
 injection H6; intros;  subst.
 constructor.
 + 
  eapply trans; eauto.
 + 
  eapply IHn; eauto.
Qed.


Lemma Prodn_le_antisym{A:Poset}: forall n (p1 p2:Prodn A n),
 Prodn_le n p1 p2 -> Prodn_le n p2 p1 -> p1 = p2.
Proof.
induction n; intros p1 p2 Hle1 Hle2; 
inversion Hle1; subst; inversion Hle2; subst.
-
 apply inj_pair2 in H0,H1,H2,H3;subst;auto.
-
 apply inj_pair2 in H2,H3,H6,H7;subst.
 injection H6 ; intros; subst.
 injection H7 ; intros; subst.
 f_equal.
+ now apply antisym.
+ now apply IHn.
Qed.

Fixpoint Prodn_default{A:Poset}(n:nat)(d:A) : Prodn A n :=
match n with
| 0 => tt
| S n' => (d,Prodn_default n' d)
end.


Definition Prodn_expl_Poset(A:Poset)(n:nat) : Poset :=
{|
  carrier := Prodn A n;
  default := Prodn_default n (@default A);
  ord := Prodn_le n;
  refl := Prodn_le_refl n;
  trans := Prodn_le_trans n;
  antisym := Prodn_le_antisym n
|}.
 

 
Fixpoint P2C{A:Poset}(n:nat)(d:A)(p:Prodn A n) : 
 @carrier (Prodn_Poset A n) :=
 match n return (Prodn A n -> Prodn_Poset A n) with
   | 0 => fun _  => tt
   | S n' =>
       fun (p' : Prodn A (S n')) =>
        let (a, p1) := p' in  (a, P2C n' d p1) 
   end p.


Fixpoint C2P{A:Poset}(n:nat)(d:A)(c :@carrier (Prodn_Poset A n)) {struct n}: 
Prodn A n :=
match n return (Prodn_Poset A n -> Prodn A n) with
   | 0 => fun _  => tt
   | S n' =>
      fun (c' : Prodn_Poset A (S n')) =>
        let (a, p) := c' in
         (a, C2P  n' d p)
   end c.


Lemma C2P2C{A:Poset}: forall n (d:A) c,
P2C n d (C2P n d c) = c.
Proof.
induction n ; intros d c; destruct c ; cbn ; auto.
now rewrite IHn.
Qed.


Lemma P2C2P{A:Poset}: forall n (d:A) p,
C2P n d (P2C n d p) = p.
Proof.
induction n ; intros d p; destruct p ; cbn ; auto.
now rewrite IHn.
Qed.

Definition P2C_BIJ{A:Poset}(n:nat) : 
BIJECTION (Prodn A n)(@carrier (Prodn_Poset A n)) :=
{|
    to := P2C n (@default A);
    from := C2P n (@default A);
    to_from := C2P2C n (@default A);
    from_to := P2C2P n (@default A)
|}.


Lemma P2C_mono{A:Poset}(d:A): forall n (p p': Prodn A n),
Prodn_le n p p' -> 
(Prodn_Poset A n).(ord) (P2C n d p)(P2C n d p').
Proof.
induction n; intros p p' Hp; inversion Hp; subst; clear Hp; cbn;auto.
apply inj_pair2 in H2,H3; subst; cbn; split;auto.
Qed.


Lemma C2P_mono{A:Poset}(d:A): forall n (c c': Prodn_Poset A n),
(Prodn_Poset A n).(ord) c c' -> 
Prodn_le n (C2P n d c) (C2P n d c').
Proof.
induction n; intros c c' Hc; inversion Hc; subst; clear Hc; cbn;auto.
-
constructor.
-
 destruct c; destruct c' ; cbn in *.
 constructor; auto.
Qed.

Program Definition P2C_Iso{A:Poset}(n:nat) : 
 Poset_ISOMORPHISM (Prodn_expl_Poset A n)  (Prodn_Poset A n) :=
 {|
   b := P2C_BIJ n; 
 |}.

Next Obligation.
intros A n x y Hle.
now apply P2C_mono.
Qed.

Next Obligation.
intros A n x y Hle.
now apply C2P_mono.
Qed.


Definition diagonal {A : Type}:=
  fun (x:A) => (x,x).

Lemma diagonal_is_monotonic {A : Poset}:
  is_monotonic (P2 := PROD_Poset A _) diagonal.
Proof.
unfold diagonal.
intros u v Hle.
constructor; apply Hle.
Qed.

Lemma diagonal_is_continuous{A : DCPO}:
is_continuous (P2 := PROD_DCPO A _) diagonal.
Proof.
intros K Hd.
assert (Hd' : is_directed (P := PROD_Poset _ _)(fmap K diagonal) ).
{
  apply (monotonic_directed (P2 := PROD_Poset _ _));auto;
  apply diagonal_is_monotonic.
}
split;auto.
unfold diagonal.
cbn.
repeat rewrite <- fmap_comp.
unfold comp.
cbn.
now repeat rewrite fmap_id.
Qed.
