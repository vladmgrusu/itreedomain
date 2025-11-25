From Stdlib Require Import FunctionalExtensionality PropExtensionality
 IndefiniteDescription Classical List Lia.
From Domain Require Export Completion ACPO Setof  Finite.
Import ListNotations.

Definition EXP (D C: Type) : Type := D -> C.

Definition EXP_Poset (D: Type) (C: Poset):  Poset :=
  {|
    carrier := EXP D C;
    default := fun _:D => @default C;
    ord := fun f f' => forall d, ord (f d) (f' d);
    refl := ltac:(cbn;intros; apply refl);
    trans := ltac:(cbn;intros; eapply trans; eauto);
    antisym :=
      ltac:(cbn;intros;extensionality w ;apply antisym; auto)
  |}.

Program Definition EXP_PPO (D: Type) (C: PPO):  PPO :=
{| poset_ppo := EXP_Poset D C;
	pbot := fun _ => pbot
|}.

Next Obligation.
apply pbot_least.
Qed.


Definition proj{D : Type} {C : Poset} (S : Setof (EXP_Poset D C))(d : D) :=
fmap S (fun f => f d). 

  
Lemma directed_proj{D: Type} {C: Poset} :
  forall  (S: Setof (EXP_Poset D C)) (d:D),
    is_directed S -> is_directed (proj S d).
Proof.
intros S d (Hne & Hd).
split.
-   
  apply not_empty_member.
  apply not_empty_member in Hne.
  destruct Hne as (f & Hm).
  now exists (f d), f.
-
  intros x y Hm1 Hm2.
  destruct Hm1 as (f1 & Hm1 & Heq1).
  destruct Hm2 as (f2 & Hm2 & Heq2).
  destruct (Hd _ _ Hm1 Hm2) as (f & Hm & Hle1 & Hle2).
  subst.
  exists (f d); split; auto.
  now exists f.
Qed.


Lemma lub_proj{D : Type}{C : DCPO}: forall S,
is_directed S -> 
is_lub S
  (fun d : D =>
   lub (d:= C) (proj S d)).
Proof.
intros  S Hd.
split.
- 
  intros f Hm d.
  cbn in *.
  specialize (lub_is_lub  _ (directed_proj S d Hd)) as (Hu & _).
  apply (Hu (f d)).
  now  exists f.
-
  intros g Hu d.
  specialize (lub_is_lub  _ (directed_proj S d Hd)) as (_ &Hmm).
  apply Hmm; clear Hmm.
  intros x Hmx.
  destruct Hmx as (f & Hf & Heq).
  subst.
  specialize (Hu _ Hf).
  cbn in Hu.
  apply Hu.
Qed.


Program Definition EXP_DCPO (D: Type) (C: DCPO):  DCPO :=
{|
  dcpo_poset := EXP_Poset D C;
  lub := fun  S =>  (fun d =>  lub (proj S d))
|}.

Next Obligation.
intros.
cbn in *.
destruct (oracle (is_directed (P := EXP_Poset D C) S)); [| contradiction].
now apply lub_proj.
Qed.



Lemma is_directed_lub{D:Type}{C:DCPO}(S:Setof (EXP D C)):
is_directed (P := EXP_Poset D C) S -> 
lub (d := EXP_DCPO D C) S = (fun d =>  lub (proj S d)).
Proof.
intro Hd.
cbn in *.
destruct (oracle (is_directed (P := EXP_Poset D C) S)); [| contradiction].
reflexivity.
Qed.

Program Definition EXP_CPO (D: Type) (C: CPO):  CPO :=
{|
  dcpo_cpo := EXP_DCPO D C;
  bot := fun _ => bot;
|}.

Next Obligation.
intros.
cbn in *.
intros.
apply bot_least.
Qed.


Definition support{A B:Type}(f: A -> B)(b:B) : Setof A :=
  fun a => f a <> b.

Lemma finite_support_with_compact_values_is_compact{A:Type}{B:CPO}:
forall (f : A -> B), is_finite (support f bot) -> 
(forall a, is_compact  (f a))  -> 
is_compact (D := EXP_Poset A B) f.
Proof.
intros f Hf Hac.
rewrite is_compact_alt.
intros F Hd Hcl lu Hlu Hle.
apply (is_lub_lub_eq1 (D := EXP_DCPO A B) ) in Hlu; auto; subst.
assert(Hfunc:
  forall (a:A), exists (b : B), member (proj F a) b /\ f a <= b).
{  
  intros a.
  assert (Hds : is_directed (proj F a))
    by now apply directed_proj.
  rewrite is_directed_lub in Hle; auto.
  now specialize (Hac a _ Hds _ (lub_is_lub _ Hds )(Hle a)).
}  
apply functional_choice in Hfunc.
destruct Hfunc as (g & Hag).
assert (Hma: forall a, member (support f bot) a -> member (proj F a)
(g a) /\
f a <= g a) by (intros a _ ; now destruct (Hag a)).
clear Hag.
apply is_finite_iff in Hf.
destruct Hf as (l & _ & Himp).
assert (Hma' : forall a : A,
   In a l ->
     member (proj F a) (g a) /\ f a <= g a)
 by (intros a Hin; apply Hma;now rewrite Himp ).
clear Hma Hle.
assert (Hma : forall a, In a l -> exists h, member F h /\ f a <= h a).
{ 
  intros a Hin.
  destruct (Hma' _ Hin) as (Hm & Hle).
  destruct Hm as (h & Hmh & Heq).
  rewrite Heq in Hle.
  now exists h.
}
clear Hma'.
assert (Hma' : forall (a: {a: A | In a l}), exists h,
  member F h /\ f (proj1_sig a) <= h (proj1_sig a)) by
  (intros (a & Hin); now apply Hma).
clear Hma.
apply functional_choice in Hma'.
assert (Hnsig : exists ff: A -> EXP_DCPO A B,
  forall a, In a l -> member F (ff a) /\ f a <= ff a a).
{
  destruct Hma' as (fsig & Hasig).
  cbn in *.
  eexists (fun x => 
    match (oracle (In x l)) with
     | left Hl => fsig (exist _ x Hl)
     | right _ => @bot (EXP_CPO A B)
    end
  ).
 intros a Hin.
 destruct (oracle (In a l)); [| now contradict n].
 apply Hasig.
 Unshelve. 
}
clear Hma'.
destruct Hnsig as (ff & Haff).
assert (Haff1 : forall a : A,
In a l ->
member F (ff a)) by (intros a Hin;  now destruct (Haff _ Hin)).
assert (Haff2 : forall a : A,
In a l -> f a <= ff a a) by (intros a Hin;  now destruct (Haff _ Hin)).
clear Haff.
specialize (list_directed_has_upper_alt _ Hd (map ff l)) as Hex.
assert (HH : forall x : EXP_DCPO A B, 
In x (map ff l) -> member F x).
{
  intros x Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as (a & Heq & Hin).
  rewrite <- Heq.
  now apply Haff1.
}
specialize  (Hex HH).
destruct Hex as (q & Hmq & Ha).
clear HH.
cbn.
exists (fun a => 
    match (oracle (In a l)) with
     | left Hl => ff a a
     | right _ =>  @bot B
    end
  ).
 split.
 -
   apply Hcl with (x := q); auto.
   intro a.
   destruct (oracle (In a l)); [| apply bot_least].
   assert (Hin : In (ff a) (map ff l)) by
   (rewrite  in_map_iff; now exists a).
   specialize (Ha _ Hin).
   cbn in Ha.
   apply Ha.
 -
   intro a.
   destruct (oracle (In a l)).
   +
    now apply Haff2.
   +
    assert (Hnm : ~member (support f bot) a)  by (now rewrite Himp).
    unfold member, support in Hnm.
    unfold not in Hnm.
    apply NNPP in Hnm.
    rewrite Hnm.
    apply refl.
Qed.    


Definition cp_func{D : Type}{C : DCPO} 
(S : D -> Setof C)   (Hall : forall j : D, is_directed (S j))
  (f1 f2 : EXP D C)
  (Hmf1 : forall d : D, S d (f1 d))
  (Hmf2 : forall d : D, S d (f2 d)) : forall (d:D), C.
  intro d.
  specialize (Hmf1 d).
  specialize (Hmf2 d).
  specialize (Hall d ) as (_ & Hall').
  specialize (Hall' _ _ Hmf1 Hmf2).
  remember (constructive_indefinite_description _ Hall') as Hall''.
  destruct Hall'' as (z & Hmz & Hle1 & Hle2).
  exact z.
Defined.


Lemma  cp_func_prop_1{D : Type}{C : DCPO} :
 forall  (S : D -> Setof C)
  (Hall : forall j : D, is_directed (S j))
  (f1 f2 : EXP D C)
  (Hmf1 : forall d : D, S d (f1 d))
  (Hmf2 : forall d : D, S d (f2 d)) (d : D),
   S d
     (cp_func S Hall f1 f2 Hmf1
        Hmf2 d).
intros.
unfold cp_func.
destruct (Hall d).
remember (constructive_indefinite_description _
          (e (f1 d) (f2 d) (Hmf1 d) (Hmf2 d))) as ci.
clear Heqci.
now destruct ci as (x & Hmx & Hle1 & Hle2).
Qed.

Lemma  cp_func_prop_2{D : Type}{C : DCPO} :
 forall  (S : D -> Setof C)
  (Hall : forall j : D, is_directed (S j))
  (f1 f2 : EXP D C)
  (Hmf1 : forall d : D, S d (f1 d))
  (Hmf2 : forall d : D, S d (f2 d)) (d : D),
 f1 d <=
 cp_func S Hall f1 f2 Hmf1 Hmf2 d.
Proof.
intros.
unfold cp_func.
destruct (Hall d).
remember (constructive_indefinite_description _
          (e (f1 d) (f2 d) (Hmf1 d) (Hmf2 d))) as ci.
now destruct ci as (x & Hmx & Hle1 & Hle2).
Qed.

Lemma  cp_func_prop_3{D : Type}{C : DCPO} :
 forall  (S : D -> Setof C)
  (Hall : forall j : D, is_directed (S j))
  (f1 f2 : EXP D C)
  (Hmf1 : forall d : D, S d (f1 d))
  (Hmf2 : forall d : D, S d (f2 d)) (d : D),
 f2 d <=
 cp_func S Hall f1 f2 Hmf1 Hmf2 d. 
Proof.
intros. 
unfold cp_func.
destruct (Hall  d); cbn.
remember ( constructive_indefinite_description _
       (e (f1 d) (f2 d) (Hmf1 d) (Hmf2 d))) as ci.
now  destruct ci as (x & Hmx & Hle1 & Hle2).
Qed.



Definition choose{C : Poset} (S : Setof C): is_directed S ->  C. 
intro Hd.
destruct Hd as (Hne & _).
apply not_empty_member in Hne.
remember (constructive_indefinite_description _  Hne) as x.
clear Heqx.
destruct x as (x & Hm).
exact x.
Defined.

Lemma choose_chooses{C : Poset} : forall (S : Setof C)Hd, member S  (choose  S Hd).
Proof.
intros S (Hne & Hx).
unfold choose.
remember (constructive_indefinite_description
         (member S)
         (match not_empty_member S with
          | conj H _ => H
          end Hne)) as ci.
now destruct ci as (x & Hm).
Qed.

Lemma cartesian_product_is_directed{D : Type}{C : DCPO}
  (S : D -> Setof C)
  (Hall: forall j, is_directed (S j)):
  is_directed (P := EXP_DCPO D C)
    (fun f =>  forall  d,  member (S d) (f d)).
Proof.  
cbn.
split.
-
  apply not_empty_member.
  exists (fun d => choose (S d) (Hall d)).
  unfold member; cbn.
  intro d.
  apply choose_chooses.
-
  cbn.
  intros f1 f2 Hmf1 Hmf2.
  unfold member in *.
  exists (cp_func S Hall f1 f2 Hmf1 Hmf2).
  repeat split.
  *
    apply  cp_func_prop_1.
  *
    apply cp_func_prop_2.
  *
    apply cp_func_prop_3.
Qed.


Lemma lub_of_cartesian_product{D : Type}{C : DCPO}
  (S : D -> Setof C)
  (Hall: forall j, is_directed (S j)):
    lub  (d := EXP_DCPO D C)
     (fun f =>  forall  d,  member (S d) (f d))=
    fun d => lub (S d).
Proof.
specialize (cartesian_product_is_directed S Hall) as Hcd.
extensionality d.  
cbn in *.
destruct (oracle
(is_directed (P := EXP_Poset D C)
   (fun f : EXP D C
    =>
    forall d0 : D,
    member (S d0)
      (f d0)))); [| contradiction].
cbn.      
set (F :=  (fun f : EXP D C =>
        forall d : D,
          member (S d) (f d))).
specialize (lub_is_lub _  (directed_proj F d  Hcd) ) as Hl.
remember (lub (proj F d)) as c.
specialize (lub_is_lub _  (Hall d) ) as Hl'.
remember  (lub (S d)) as c'.
clear Heqc Heqc'.
cbn in *.
replace  (proj F d) with
            (S d) in *; [eapply is_lub_unique; eauto|].
apply set_equal.
intro x; split; intro Hm.
-
  exists (fun j =>
              match (oracle (j = d)) with
                left  => x
               | right  => choose (S j) (Hall j)        
              end).
  unfold member; cbn.
  split.
  +
    intros d'.
    remember  (oracle (d' = d) ) as o.
    destruct o; try (now subst).
    apply choose_chooses.
  +
    remember (oracle (d = d)) as o.
    destruct o; auto.
    clear Heqo.
    now contradict n.
-    
  destruct Hm as (f & Hf & Heq); subst.
  apply Hf.
Qed.    


Lemma compacts_have_compact_values{D: Type}: 
forall {A:ADCPO} f, 
    is_compact (D:= (EXP_DCPO D A)) f -> 
      forall d, is_compact (f d).
Proof.
intros  A f Hc d.
rewrite is_compact_alt.
intros Sd Hd Hcl lu Hlu Hle.
apply is_lub_lub_eq1 in Hlu; subst; auto.
remember (fun d => (compacts_le (f d))) as F.
assert (Hall : forall d, is_directed (F d)) by
  (intros;   subst; apply algebraic_dir).
specialize (lub_of_cartesian_product  _ Hall) as Hlem.
subst.
specialize  (cartesian_product_is_directed
(fun d : D =>
 compacts_le (f d))
Hall) as Hcd.
specialize (Hc  _ Hcd _ (lub_is_lub _ Hcd)).
(**
specialize (Hc (fun d : D => lub (compacts_le (f d)))).*)
cbn [compacts_le] in Hc.
rewrite Hlem in Hc.
assert (Hlef : 
 f <= (fun d : D => lub (compacts_le (f d)))).
{
  intro d'.
  rewrite (algebraic_lub (f d')) at 1.
  apply refl.
}  
specialize (Hc Hlef).
clear Hlef.
destruct Hc as (f'& Hm & Hlef).
unfold member in Hm; cbn in Hm.
exists (f' d); split; auto.
specialize (Hm d) as Hmd.
unfold compacts_le in Hmd.
destruct Hmd as (Hc' & Hle').
assert (Hlef' : f' d <= lub Sd)
  by (eapply trans; eauto).
unfold is_compact in Hc'.
specialize (Hc' _ Hd  _ (lub_is_lub _ Hd) Hlef').
destruct Hc' as (c & Hmc & Hlec).
now apply  (Hcl _ Hmc).
Qed.

Definition is_restriction{A:Type}{B: CPO} (f g : A -> B) : Prop :=
subset (support f bot) (support g bot) /\ 
    forall a, member (support f bot) a -> f a = g a.


Definition is_mixture{A:Type}{B: Type} (f g h : A -> B):= forall x,
h x = f x \/ h x = g x.



Lemma mixture_finite_is_finite {A:Type}{B: CPO} (f g h : A -> B):
is_mixture f g h ->  is_finite (support f bot) ->
 is_finite (support g bot) ->
is_finite (support h bot).
intros Hm Hff Hfg.
destruct Hff as (lf & Hf).
destruct Hfg as (lg & Hg).
exists (lf ++ lg).
intros x Hmx.
apply in_or_app.
destruct (Hm x) as [Hl | Hr].
-
 left.
 apply Hf.
 unfold member, support in *.
 now rewrite <- Hl.
-
 right.
 apply Hg. 
 unfold member, support in *.
 now rewrite <- Hr.
Qed. 


Definition finite_restrictions{A:Type}{B: CPO}
(g: A -> B):Setof(EXP A B):=
fun f => is_restriction f g /\ is_finite (support f bot).

Lemma finite_restriction_directed{A:Type}{B: CPO}(g: A -> B) :
  is_directed (P := EXP_Poset A B)(finite_restrictions g).
Proof.
split.
- 
 apply not_empty_member.
 exists (fun _ => bot).
 repeat split.
+ 
  now intro x.
+
  intros x Hm.
  now contradict Hm.
+
  exists (nil:list A).
  intros x Hm.
  now contradict Hm.
-
  intros f' g' Hmf' Hmg'.
  exists (fun a => 
    match (oracle (f' a = bot)), (oracle (g' a = bot)) with 
    |right _, right _  => f' a 
    |left _, right _ => g' a
    |right _, left _ => f' a
    |left _, left _ => bot
    end).
  repeat split.
  +       
   intros x Hmx Heq.
   apply Hmx; clear Hmx.
   destruct (oracle (f' x = bot)); 
     destruct (oracle (g' x = bot)); auto.
   *
    exfalso; apply n.
    destruct Hmg' as ((Hs & Heq') & _).
    rewrite Heq'; auto.
   *
   exfalso; apply n.
   destruct Hmf' as ((Hs & Heq') & _).
   rewrite Heq'; auto.
   *
   exfalso; apply n.
   destruct Hmf' as ((Hs & Heq') & _).
   rewrite Heq'; auto.
 +
  intros x Hmx.
  unfold member, support in Hmx.
  destruct (oracle (f' x = bot)); 
     destruct (oracle (g' x = bot)).
  *
   now contradict Hmx.
  *
  destruct Hmg' as ((Hs & Heq') & _).
  rewrite Heq'; auto.
  *
  destruct Hmf' as ((Hs & Heq') & _).
  rewrite Heq'; auto.
  *
  destruct Hmf' as ((Hs & Heq') & _).
  rewrite Heq'; auto.
 + 
   apply mixture_finite_is_finite with (f := f') (g := g').
   *
   intros x.
   destruct (oracle (f' x = bot)); 
      destruct (oracle (g' x = bot)); auto.
   *
    now destruct Hmf'.
   *
    now destruct Hmg'.
  +
    intros x.
    destruct (oracle (f' x =  bot)); 
      destruct (oracle (g' x = bot)); try (rewrite e) ;
      try (rewrite e0); try (apply refl).
    apply bot_least.
+    
  intros x.
  destruct (oracle (f' x = bot)); 
   destruct (oracle (g' x = bot)); try (rewrite e) ;
   try (rewrite e0); try (apply refl); try (apply bot_least).
  destruct Hmg' as ((_ & Heq') & _).
  destruct Hmf' as ((_ & Heq'') & _).
  rewrite Heq',Heq''; auto.
  apply refl.
Qed.   

Lemma single_support_finite{A: Type}{B: PPO}(a : A)(b:B):
is_finite
  (support
     (fun x : A =>
      if oracle (x = a)
      then b
      else pbot) pbot).
Proof.
exists [a].
intros x Hmx.
unfold member, support in Hmx.
destruct (oracle (x = a)); subst; try constructor; auto.
now contradict Hmx.
Qed.   


Lemma single_support_finite_restriction{A:Type}{B: CPO}:
forall (f: A -> B) a,
member(finite_restrictions f)
(fun x : A => if oracle (x = a) then f a else bot).
Proof.
intros f a.
repeat split.
 -
   intros x Hmx.
   unfold member, support in Hmx.
   destruct (oracle (x = a)); subst; auto.
   now contradict Hmx.
-
  intros x Hmx.
  unfold member, support in Hmx.
  destruct (oracle (x = a)); subst; auto.
  now contradict Hmx.
-
 apply (single_support_finite (B := CPO2PPO B)).
Qed.


Lemma function_is_lub_of_finite_restrictions{A:Type}{B: CPO}:
forall (f: A -> B),
 is_lub (P := EXP_Poset A B)(finite_restrictions f) f.
Proof.
intros f.
split.
-
  intros g Hmg a.
  destruct Hmg as ((Hq & Heq') & _).
  destruct (oracle (g a = bot)); [rewrite e; apply bot_least |].
  rewrite Heq'; auto.
  apply refl.
-
 intros g Hug a.
 unfold is_upper in Hug.
 specialize (Hug _ (single_support_finite_restriction f a) a).
 cbn in Hug.
 destruct (oracle (a = a)); auto.
 now contradict n.
 Qed.


Lemma function_le_lub_of_finite_restrictions{A:Type}{B: CPO}:
forall (f: A -> B),
ord (p := EXP_Poset A B )f  
(lub (d := EXP_DCPO A B)(finite_restrictions f)).
Proof.
intro f.
specialize (function_is_lub_of_finite_restrictions f) as Hlf.
specialize (finite_restriction_directed f) as Hdf.
specialize (@ is_lub_lub_eq1  (EXP_CPO A B) _ _ Hlf Hdf) as Hf.

(*specialize (@is_lub_cpo_lub_eq  (EXP_CPO A B) _ _ Hlf Hdf) as Hf
replace (finite_restriction_directed f) with Hdf by
 (now apply proof_irrelevance).*)
rewrite  Hf at 1.
apply refl.
Qed.



Lemma compacts_have_finite_support{D: Type} {A:CPO} : forall f, 
     is_compact (D:= (EXP_DCPO D A)) f -> 
     is_finite (support f bot).
Proof.
intros f Hc.
specialize (function_le_lub_of_finite_restrictions f) as Hle.
specialize (finite_restriction_directed f) as Hdf.
specialize (Hc _ Hdf _ (@lub_is_lub (EXP_DCPO D A)_ Hdf) Hle); clear Hle.
destruct Hc as (h & (Hr & Hf) & Hle).
destruct Hf as (l & Hin).
exists l.
intros x Hm.
apply Hin.
cbn in Hle.
intro Heq; apply Hm.
specialize (Hle x).
rewrite Heq in Hle.
now apply  le_bot_eq.
Qed.


Lemma compacts_are_functions_with_finite_support_and_compact_values
{A: Type}{B:ACPO} : forall f,
    is_compact (D:= (EXP_Poset A B)) f <-> 
    (is_finite (support f (@bot(ACPO2CPO B))) /\ 
     forall a, is_compact (f a)).
Proof.
split.
-
  intro Hc.
  split.
  +
   apply  (@compacts_have_finite_support A (ACPO2CPO B) _ Hc).
  + 
   now apply compacts_have_compact_values.
-
 intros (Hf & Ha).
now apply 
 (finite_support_with_compact_values_is_compact (B := ACPO2CPO B)).
Qed. 



Lemma my_algebraic_dir{A:Type}{B:ACPO}:
forall (f : A -> B), is_directed (compacts_le (P := EXP_DCPO A B)f).
Proof.
intros f.
split.
-
 apply not_empty_member.
 exists (fun _ => abot).
 split; [| intro x; apply  abot_least].
 rewrite (@compacts_are_functions_with_finite_support_and_compact_values A (ACPO2CPO B)).
 split.
 + exists [].
   intros x Hm.
   now contradict Hm.
 +
  intros _.
  apply (@pbot_is_compact (CPO2PPO ((ACPO2CPO B)))).
-
  intros u v (Hcu & Hleu) (Hcv & Hlev).
  rewrite
  (@compacts_are_functions_with_finite_support_and_compact_values A (ACPO2CPO B))
    in Hcu, Hcv.
  destruct Hcu as (Hfu & Hau).
  destruct Hcv as (Hfv & Hav).
  cbn in Hleu, Hlev.
  assert (Hkey : forall d, 
    exists w, u d <= w /\ w <= f d/\ v d <= w  /\ is_compact w 
     /\ (~member (support u (@bot(ACPO2CPO B))) d /\ 
     ~member (support  v (@bot(ACPO2CPO B))) d -> 
     w = abot)).
  {
     intro a.
     specialize (Hau a).
     specialize (Hav a).
     specialize (Hleu a).
     specialize (Hlev a).
     specialize (algebraic_lub (f a)) as Heq.
     rewrite Heq in Hleu,Hlev.
     (*specialize (compacts_le_directed (f a)) as Hd.*)
     assert (Hd : is_directed (compacts_le (f a))) by
        apply algebraic_dir.
     specialize (Hau _ Hd _ (lub_is_lub _ Hd ) Hleu).
     specialize (Hav _ Hd _ (lub_is_lub _ Hd) Hlev).
     clear Hleu Hlev.
     destruct Hau as (wu & Hcwu & Hleu).
     destruct Hav as (wv & Hcwv & Hlev).
     destruct Hd as (_ & Hd).
     specialize (Hd _ _ Hcwu Hcwv).
     destruct Hd as (z & (Hcz & Hmz) & Hleuz & Hlevz).
     destruct (oracle (member (support u (@bot(ACPO2CPO B))) a));
       destruct (oracle (member (support  v (@bot(ACPO2CPO B))) a)).
    -   
     exists z; repeat split; auto.
     +
     eapply trans; eauto.
     +
     eapply trans; eauto.
     +
      intros (Hnmu & Hnmv).
      now contradict Hnmu.
   -    
    exists z; repeat split; auto.
    +
    eapply trans; eauto.
    +
    eapply trans; eauto.
    +
    intros (Hnmu & Hnmv).
    now contradict Hnmu.
  -   
    exists z; repeat split; auto.
    +
    eapply trans; eauto.
    +
    eapply trans; eauto.
    +
    intros (Hnmu & Hnmv).
    now contradict Hnmv.
 -  
  exists abot; repeat split; auto.
  + 
   apply NNPP in n.
   rewrite n.
   apply refl.
  +
    apply abot_least.
  +
  apply NNPP in n0.
  rewrite n0.
  apply refl.
  +
  apply (@pbot_is_compact (CPO2PPO ((ACPO2CPO B)))).
  } 
  apply functional_choice in Hkey.
  destruct Hkey as (g & Hag).
  exists g; repeat split.
  +
  rewrite (@compacts_are_functions_with_finite_support_and_compact_values A (ACPO2CPO B)).
   split.
   *
     destruct Hfu as (lu & Hlu).
     destruct Hfv as (lv & Hlv).
     exists (lu ++ lv).
     intros x Hmx.
     destruct (Hag x) as (_ &_ & _ & _ & Himp).
     unfold member, support in *.
     assert (u x <> abot \/ v x <> abot); try tauto.
     clear Himp.
     apply in_or_app.
     destruct H as [Hl | Hr]; 
      [left; now apply Hlu| right; now apply Hlv].
   *
      intro a.
      now destruct (Hag a) as (_& _ & _ & Hc & _).
  +
    intros a.
    now destruct (Hag a) as (_& Hle & _ & _ & _).
  +
    intros a.  
    now destruct (Hag a) as (Hle & _ & _ & _ & _).
  +
    intros a.
    now destruct (Hag a) as (_ & _ & Hle & _ & _).
Qed.    


Lemma my_algebraic_lub{A:Type}{B:ACPO}:
forall (f : A -> B), 
f = lub (compacts_le (P:= EXP_DCPO A B)f).
Proof.
intro f.
remember  (my_algebraic_dir f) as Hd. 
extensionality a.
rewrite (algebraic_lub  (f a)).
apply antisym.
-
 specialize  (@forallex_lelub B ) as Hel.
 cbn in *.
 destruct (oracle
 (@is_directed (EXP_Poset A B)
    (@compacts_le (EXP_DCPO A B)
       f))); [|  contradict n; apply my_algebraic_dir].
   
 apply Hel; auto; try  apply refl.
 +
   apply algebraic_dir.
 + now apply directed_proj.
 +

 intros b (Hcb & Hleb).
 exists b; split; try apply refl.
 exists 
  (fun x => 
    match (oracle (x = a) ) with
    left _ => b
    |right _ => abot
    end).
 repeat split.
  *
  rewrite (@compacts_are_functions_with_finite_support_and_compact_values A (ACPO2CPO B)).
  split.
  --
     exists[a].
     intros x Hmx.
     unfold member, support in Hmx.
     destruct (oracle (x =a)); subst; try constructor; auto.
     now contradict Hmx.
  --
   intro x.
   destruct (oracle (x =a)); subst; auto.
   apply (@pbot_is_compact (CPO2PPO ((ACPO2CPO B)))).
  *
   intro x.
   destruct (oracle (x =a)); subst; auto.
   apply abot_least.
 *
  destruct (oracle (a  =a)); subst; auto.
  now contradict n.
 -
 specialize  (@forallex_lelub B ) as Hel.
 cbn in *.
 destruct (oracle
 (@is_directed (EXP_Poset A B)
    (@compacts_le (EXP_DCPO A B)
       f))); [|  contradict n; apply my_algebraic_dir].
   
 apply Hel; auto; try  apply refl.
  
  + now apply directed_proj.
  + apply algebraic_dir.
  + intros b (g & (Hcg & Hleg) & Heqb).
  exists b.
  rewrite (@compacts_are_functions_with_finite_support_and_compact_values A (ACPO2CPO B)) in Hcg.
  destruct Hcg as (Hf & Hac). 
  repeat split; try apply refl.
  *
    rewrite Heqb.
    apply Hac.
  *
   rewrite Heqb.
   apply (Hleg a).
Qed.     


Definition EXP_ADCPO (A: Type) (B: ACPO): ADCPO :=
{|
  algebraic_dcpo := EXP_DCPO A B;
  algebraic_dir := my_algebraic_dir;
  algebraic_lub := my_algebraic_lub
|}.



Program Definition EXP_ACPO (A: Type)(B:ACPO) : ACPO :=
  {| adcpo_acpo := EXP_ADCPO A B;
	abot := fun _ => (@abot B);
|}.

Next Obligation.
intros; cbn in *.
intros.
apply (@bot_least (ACPO2CPO B)).
Qed.



Record finitely_supported(A B:Type)(b:B) :=
{
  func :> EXP A B;
  fsup : is_finite (support func b)
}.


Arguments func { _ _} _ _.
Arguments fsup { _ _} _ _.

Lemma fin_sup_equal{A B:Type}(b:B) :
forall (f f': finitely_supported A B b),
func b f = func b f' -> f = f'.
Proof.
intros (f & Hf) (f' & Hf') Heq; cbn in *.
subst.
f_equal.
apply proof_irrelevance.
Qed.

Lemma cst_bot_finite_support{A B:Type}(b:B) :
is_finite (support (fun _: A => b) b).
Proof.
exists [].
intros x Hmx; now apply Hmx.
Qed.

Definition def{A B:Type}(b:B) :=
  {|
    func := fun _:A => b;
    fsup := @cst_bot_finite_support A B b;
  |}.


Program Definition finitely_supported_Poset(A:Type)(B : PPO) : Poset:=
{|
  carrier := finitely_supported A B (@pbot B);
  ord := fun  x y => @ord (EXP_Poset A B) (func _ x) 
  (func _  y);
  default := @def A B (@pbot B);
|}.

Next Obligation.
cbn.
intros.
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
apply fin_sup_equal.
extensionality u.
apply @antisym; auto.
Qed.

Lemma inject_pbot_least_compact{P:PPO}(c: COMPLETION P):  
forall (cc:c), is_compact cc -> inject pbot <= cc.
Proof.
intros cc Hc.
rewrite <- inject_rev_inj; auto.
apply inject_bimono.
apply pbot_least.
Qed.


Lemma inject_pbot_least{P:PPO}(c: COMPLETION P):  
forall (y:c),  inject pbot <= y.
Proof.
intros y.
replace y with (lub (compacts_le y)); [| now rewrite algebraic_lub].
destruct (algebraic_dir y) as (Hne & _).
rewrite not_empty_member in Hne.
destruct Hne as (x & Hcx & Hle).
apply trans with (y := x); [now apply inject_pbot_least_compact |].
apply lub_is_upper; [apply algebraic_dir|].
now split.
Qed.


Program Definition EXP_COMP{A:Type}{P:PPO}(c: COMPLETION P) :
 COMPLETION (finitely_supported_Poset A P) :=
 {|
   alg := EXP_ADCPO A 
    {| adcpo_acpo := (alg c); 
     abot :=  inject pbot;
      abot_least := inject_pbot_least c
    |};
   inject :=  fun f x => inject (func _ f x);
   rev_inj :=  fun f => {| func := fun x =>
     if (oracle (is_compact (D:= EXP_Poset A c) f)) then
     rev_inj (f x) else pbot |}
 |}.


Next Obligation.
cbn.
destruct p as (f & Hf) ; destruct p' as (f' & Hf'); cbn in *.
split; intros Hle d.
-
 now  apply inject_bimono.
-
 specialize (Hle d).
 now apply inject_bimono in Hle.
Qed.

Next Obligation.
destruct p as (f & Hf); cbn in *.
specialize 
(@compacts_are_functions_with_finite_support_and_compact_values A
{| adcpo_acpo := (alg c); 
   abot :=  inject pbot;
   abot_least := inject_pbot_least c|}
 )
as Hc.
cbn in Hc.
specialize (Hc (fun x : A =>
inject (f x) )).
rewrite Hc; clear Hc.
split; [| intros; apply inject_compact].
destruct Hf as (l & Ha).
exists l.
intros x Hmx.
apply Ha; clear Ha.
unfold member, support in *.
intro Heq.
apply Hmx.
now rewrite Heq.
Qed.

Next Obligation.
cbn.
destruct (oracle (is_compact (D := EXP_Poset A c) f));
[|
  exists [];intros x Hmx ; now apply Hmx
].
apply 
(@compacts_are_functions_with_finite_support_and_compact_values A
{| adcpo_acpo := (alg c); 
   abot :=  inject pbot;
   abot_least := inject_pbot_least c|})
in i.
destruct i as (Hf & Hc).
destruct Hf as (l & Hml).
exists l.
intros x Hmx.
apply Hml.
unfold member, support in *.
intro Heq.
apply Hmx.
rewrite Heq.
rewrite rev_inj_iff;auto.
apply inject_compact.
Qed.

Next Obligation.
cbn.
destruct p as (f & Hf).
cbn.
split; intro Hex.
-
 injection Hex; intros.
 clear Hex.
 destruct (oracle (is_compact (D := EXP_Poset A c) cc)); [|contradiction].
 extensionality x.
 rewrite <- rev_inj_iff; [now rewrite <- H0 |].
 apply (@compacts_are_functions_with_finite_support_and_compact_values A
 {| adcpo_acpo := (alg c); 
    abot :=  inject pbot;
    abot_least := inject_pbot_least c|})
 in i.
 now destruct i as (_ & Ha).
-
remember (EXP_COMP_obligation_3 A P c cc) as Hx.
clear HeqHx.
destruct  (oracle (@is_compact (EXP_Poset A c) cc)); [| contradiction].
cbn in *.
subst.
assert (Heq' :  (fun x : A => @rev_inj P c 
(@inject P c (f x))) = f ) by 
 ( extensionality z;now rewrite rev_inj_inject).
now apply fin_sup_equal.
Qed.


Lemma apply_exp_cont
{A:Type}{B:DCPO}(a:A):
is_continuous (P1 := EXP_DCPO _ _) (fun f : EXP A B => f a).
intros T HdT.
assert  (Hd: is_directed (P := B)
(fmap T
   (fun x : EXP A B =>
    x a))).
 {
 apply monotonic_directed; auto.
 intros u v Hle.
 cbn in Hle.
 apply Hle.
 }
 split; auto.
Qed.