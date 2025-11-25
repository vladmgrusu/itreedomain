From Stdlib Require Import FunctionalExtensionality PropExtensionality
 IndefiniteDescription Classical List Lia JMeq.

 From Domain Require Export Cont ADCPO.
 From Itree Require Export Itree.

(* fold on interaction trees : definition and continuity in 2nd argument
(not counting implicits) *)

Definition ffold_functional{F : Type -> Type}{X : Type}{Y : CPO}
  (f : X -> Y)(g : forall Z, F Z -> (Z -> Y) -> Y)
    (Hc : forall T ft, 
    is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft))
  (ff : itree F X-> Y) 
  (m : itree F X)
    : Y :=
    match (fcases m) with
    inleft s  => 
      match s with
        inl (exist _ x _ )=>  f x
        | inr (existT _ Z (existT _ fz (exist _ k _))) => 
           g _ fz (fun z => 
            ff (k z))
      end
    | inright _ => @bot Y
    end.

Lemma ffold_functional_mono{F : Type -> Type}{X : Type}{Y : CPO}
{f : X -> Y}{g : forall Z, F Z -> (Z -> Y) -> Y}
  {Hc : forall T ft, 
  is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft)} :
  is_monotonic 
  (P1 := EXP_Poset (itree F X) Y)
  (P2 := EXP_Poset (itree F X) Y)
  (ffold_functional f g Hc).
 Proof. 
 intros m m' Hle n.
 cbn in Hle.
 unfold ffold_functional.
 destruct (fcases n) as 
 [ [(x & He) | (W & fw & k & He)]| He]; subst.
 -
  apply refl.
 -
   specialize (Hc W fw).
   rewrite continuous_iff_mono_commutes 
    in Hc.
   destruct Hc as (Hm &  _ ).
   apply Hm.
   intro d.
   apply Hle.
-
  apply refl.
Qed.     
  
Lemma ffold_mono_aux{F : Type -> Type}{X}{Y: CPO}:
forall W (g : forall Z,   F Z -> (Z -> Y) -> Y) k,
@is_monotonic (EXP_Poset (itree F X) Y) (EXP_Poset W Y)
  (fun (f0 : EXP (itree F X) Y) (z : W) => f0 (k z)).
intros W g k x y Hle.
intro w.
apply Hle.
Qed.

Lemma ffold_cont_aux{F : Type -> Type}{X}{Y: CPO}:
forall W (g : forall Z,   F Z -> (Z -> Y) -> Y) 
(Hc : forall (T : Type)
(ft : F T),
@is_continuous
(EXP_DCPO T Y) Y 
(g T ft))
fw k,
@is_continuous
  (EXP_DCPO (itree F X) Y) Y
  (fun f0 : EXP (itree F X) Y =>
   g W fw
     (fun z : W => f0 (k z))).
Proof.
intros W g Hc fw k.
remember ((fun (f0 : EXP (itree F X) Y) =>
  (fun z : W => f0 (k z)))) as h.
replace (fun f0 : EXP (itree F X) Y =>
g W fw
  (fun z : W => f0 (k z))) with (comp (g W fw) h) by
  now subst.
apply 
(comp_is_continuous 
  (P1 := (EXP_DCPO (itree F X) Y))
  (P2 := EXP_DCPO W Y ) 
  (P3 := Y)); [apply Hc | ].
rewrite continuous_iff_mono_commutes; split; cbn;
  [subst; now apply ffold_mono_aux | ].
cbn.    
intros S l Hd Hl.
specialize (lub_proj _ Hd) as Hll.
apply is_lub_unique with (x := l) in Hll; auto.
replace l with 
(lub (d := (EXP_DCPO (itree F X) Y)) S)
in *.
rewrite Hll.
assert (Hd' : @is_directed (EXP_DCPO W Y)
(@fmap (EXP_Poset (itree F X) Y)
(EXP_Poset W Y) S h)).
{
 apply (monotonic_directed 
 (P1 := 
    (EXP_Poset 
    (itree F X) Y))
 (P2 := (EXP_Poset W Y))); auto.
 subst.
 now apply ffold_mono_aux.
}        
subst.
cbn.
cbn in Hd'.
remember ((@fmap (EXP (itree F X) Y) 
(EXP W Y) S
(fun (f0 : EXP (itree F X) Y) (z : W) =>
 f0 (k z)))) as S'.
assert
(Hk :(lub 
    (d := (EXP_DCPO W Y))
    (@fmap
    (EXP (itree F X) Y)
    (EXP W Y) S
    (fun
       (f0 : EXP
               (itree F X)
               Y) 
       (z : W) => 
     f0 (k z))) =
    ((fun z : W =>
    @lub Y
      (@proj (itree F X) Y S
         (k z)))))).
{
 rewrite <- HeqS'.
 specialize (lub_proj _ Hd') as Hl'.
 replace (lub (d:= EXP_DCPO W Y )S') 
  with  ( (fun d : W =>
  lub (proj S' d))) by 
    (now apply (is_lub_lub_eq1 (D :=EXP_DCPO W Y))).
 extensionality d.
 f_equal.
 subst.
 apply set_equal; split ; intro Hm.
 -
  destruct Hm as (f0 & Hm & Heq); subst.
  destruct Hm as (g' & Hm & Heq); subst.
  now exists g'.
 -
   destruct Hm as (g' & Hm & Heq); subst.
   exists (fun d => g' (k d)); split; auto.
   now exists g'.  
}
rewrite <- Hk in *.
subst.
now apply (@lub_is_lub (EXP_DCPO W Y)).
Qed.   

Lemma ffold_functional_H_cont{F : Type -> Type}{X : Type}{Y : CPO}
{f : X -> Y}{g : forall Z, F Z -> (Z -> Y) -> Y}
  {Hc : forall T ft, 
  is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft)} :
  is_H_continuous 
  (A :=  (itree F X))
  (B := Y)
  (ffold_functional f g Hc).
 Proof.
 split; [apply ffold_functional_mono|].
 intros S Hd.
 extensionality t.
 unfold ffold_functional.
 destruct (fcases t) as 
 [ [(x & He) | (W & fw & k & He)]| He]; subst;
 [ rewrite fmap_cst; [ | now destruct Hd];
 now rewrite lub_single | |  rewrite fmap_cst; [ | now destruct Hd];
 now rewrite lub_single].
cbn in S.
remember ((fun f0 : 
EXP (itree F X) Y => g W fw (fun z : W => f0 (k z))))
as h.
assert (Hcont : 
is_continuous 
(P1 := (EXP_DCPO (itree F X) Y))
(P2 := Y) h) by
  (rewrite Heqh;
  now apply ffold_cont_aux).
rewrite continuous_iff_mono_commutes in Hcont.
destruct Hcont as (Hmo & Hcont).
specialize (Hcont S _ Hd (lub_is_lub (d := (EXP_DCPO
(itree F X) Y)) _ Hd)).
specialize (lub_proj _ Hd) as Hlp.
assert (Heqh' : h (lub (d := (EXP_DCPO
(itree F X) Y)) S) =  g W fw
(fun z : W =>
 lub (proj S (k z)))).
{
  rewrite Heqh.
  f_equal.
}
rewrite Heqh' in Hcont.
apply is_lub_lub_eq1; auto.
apply (monotonic_directed (P1 := (EXP_Poset
 (itree F X) Y)) (P2 := Y)); auto.
Qed.

Definition ffold{F : Type -> Type}{X: Type}{Y:CPO}
(f : X -> Y)(g : forall Z, F Z -> (Z -> Y) -> Y)
  (Hc : forall T ft, 
  is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft)) :
  itree F X -> Y
 := 
   pointwise_fix 
(A := (itree F  X)) 
(B := Y) 
(ffold_functional f g Hc).

Lemma ffold_least_fixpoint{F : Type -> Type}{X: Type}{Y:CPO}
{f : X -> Y}{g : forall Z, F Z -> (Z -> Y) -> Y}
  {Hc : forall T ft, 
  is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft)} : 
is_least_fixpoint 
   (X := EXP_Poset ((itree F  X)) Y)
   (ffold_functional f g Hc)
(ffold f g Hc).
Proof.
intros.
apply Haddock_pointwise,
ffold_functional_H_cont.
Qed.

Lemma ffold_fixpoint_eq{F : Type -> Type}{X: Type}{Y:CPO}
{f : X -> Y}{g : forall Z, F Z -> (Z -> Y) -> Y}
  {Hc : forall T ft, 
  is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft)} : 
ffold_functional f g Hc
(ffold f g Hc) =
ffold f g Hc.
Proof.
intros.
destruct  (@ffold_least_fixpoint F X Y f g Hc) as (Hf & _).
apply Hf.
Qed.

Lemma ffold_fbot{F : Type -> Type}{X: Type}{Y:CPO}
{f : X -> Y}{g : forall Z, F Z -> (Z -> Y) -> Y}
  {Hc : forall T ft, 
  is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft)}:
ffold f g  Hc fbot = bot.
Proof.
rewrite <- ffold_fixpoint_eq.
unfold ffold_functional.
(destruct (fcases fbot)); auto.
repeat destruct s.
-
 specialize (pure_not_fbot (F := F) x) as Hneq.
 now contradict Hneq.
-
 specialize (impure_not_fbot x0 x1) as Hneq.
 now contradict Hneq.
Qed.
  
Lemma ffold_pure{F : Type -> Type}{X: Type}{Y:CPO}
{f : X -> Y}{g : forall Z, F Z -> (Z -> Y) -> Y}
  {Hc : forall T ft, 
  is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft)}
(x:X)  :
ffold f g Hc (pure (F:=F) x)  = f x.
Proof.
rewrite <- ffold_fixpoint_eq.
unfold ffold_functional.
(destruct (fcases (pure (F:=F) x))); auto; repeat destruct s.
-
 apply pure_is_injective in e; now subst.
-
 specialize (pure_not_impure x x1 x2) as Hneq.
 now contradict Hneq.
-
 specialize (pure_not_fbot (F:=F) x) as Hneq.
 now contradict Hneq.
Qed. 

Lemma ffold_impure{F : Type -> Type}{X W: Type}{Y:CPO}
{f : X -> Y}{g : forall Z, F Z -> (Z -> Y) -> Y}
  {Hc : forall T ft, 
  is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft)}
(fw: F W) (k:W -> itree F X ):
ffold f g Hc (impure fw k) = 
g _ fw (fun w =>  ffold f g Hc (k w)).
Proof.
 remember (fun w : W =>
 ffold f g Hc (k w)) as r.
 rewrite <- ffold_fixpoint_eq; subst.
 unfold ffold_functional.
 (destruct (fcases (impure fw k))); auto; repeat destruct s.
 -
 specialize (pure_not_impure x fw k) as Hneq.
 now contradict Hneq.
 -
  apply impure_is_injective in e.
  destruct e as (He & Hj & Hj'); now subst.
 -
  specialize (impure_not_fbot fw k) as Hne.
  now contradict Hne.
  Qed.



Lemma ffold_functional_pres_mono{F:Type -> Type}{X:Type}{Y:CPO}
(f : X -> Y)(g : forall Z, F Z -> (Z -> Y) -> Y)
(Hc : forall T ft, 
is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft))
(ff : itree F X -> Y):
is_monotonic (P1 := itree F X) (P2 := Y) ff ->
is_monotonic (P1 := itree F X) (P2 := Y)
(ffold_functional f g Hc ff).
Proof.
intros Hff x y Hle.
apply itree_ord_inv in Hle.
destruct Hle as [Heq | [(w & Heq1 & Heq2) | 
(Z & fz & k & k' & Heq1 & Heq2 & Ha)]]; subst;
unfold ffold_functional.
-
 rewrite fcases_fbot.
 apply bot_least.
-
 rewrite fcases_pure.
 apply refl.
-
 repeat rewrite fcases_impure.
 specialize (Hc _ fz).
 rewrite continuous_iff_mono_commutes in Hc.
 destruct Hc as (Hc & _).
 apply Hc.
 intro z.
 apply Hff,Ha.
Qed. 


Lemma ffold_functional_pres_cont_aux{F:Type -> Type}{X:Type}{Y:CPO}:
forall ff : (itree F X -> Y),
 @is_continuous
      (itree F X) Y ff ->
   forall(Z:Type) (fz : F Z) (g: forall W : Type,
   F W -> (W -> Y) -> Y),
   (forall (T : Type) (ft : F T),
   @is_continuous  (EXP_DCPO T Y) Y (g T ft)) ->
@is_continuous (EXP_DCPO Z (itree F X)) Y
(fun x : Z -> itree F X =>
g Z fz (fun z : Z => ff (x z))).
Proof.
intros f Hc Z fz g Ha.
remember (fun x : Z -> itree F X => 
g Z fz (fun z : Z => f (x z))) as i.
(* (Z -> itree F X) -> itree F Y*)
remember (fun (g: itree F X -> Y) => (fun x : Z -> itree F X =>
  (fun z : Z =>  g ( x z)))) as h.
replace i with (( g Z fz) ° (h f)) in * by now subst.
apply (comp_is_continuous
(P1 := EXP_DCPO Z (itree F X))
(P2 :=  EXP_DCPO Z Y)
(P3 := Y)); [apply Ha |].
clear i Heqi.
subst.
replace ((fun (x : Z -> itree F X) (z : Z) => f (x z))) with
(fun (x :  Z -> itree F X ) => (f° x) ) by reflexivity.
now apply comp_cont_snd.
Qed.

Lemma ffold_functional_pres_cont{F:Type -> Type}{X:Type}{Y:CPO}
(f : X -> Y)(g : forall Z, F Z -> (Z -> Y) -> Y)
(Hc : forall T ft, 
is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft))
(ff : itree F X -> Y):
is_continuous (P1 := itree F X) (P2 := Y) ff ->
is_continuous (P1 := itree F X) (P2 := Y)
(ffold_functional f g Hc ff).
Proof.
intro Hff.
rewrite continuous_iff_mono_commutes.
split; [rewrite continuous_iff_mono_commutes in Hff;
apply ffold_functional_pres_mono; now destruct Hff |].
intros S l Hd Hl.
remember ((fmap S(ffold_functional f g Hc ff))) as S'.
assert (Hd': is_directed (P := Y) S').
{
 subst.
 apply (monotonic_directed (P1 := itree F X) (P2 := Y));
 auto.
 apply  ffold_functional_pres_mono.
 rewrite continuous_iff_mono_commutes in Hff;
 now destruct Hff.
}
destruct (fcases l) as 
[ [(x & Heq) | (Z & fz & k & Heq)]| Heq]; subst.
-
 remember (ffold_functional f g Hc ff (pure x)) as l'.
 unfold ffold_functional in Heql'.
 rewrite fcases_pure in Heql'.
 subst.
 apply is_lub_pure in Hl; auto.
 destruct Hl as [Heq | Heq].
 +
  rewrite Heq in *.
  rewrite fmap_single in *.
  unfold ffold_functional.
  cbn.
  rewrite fcases_pure.
  apply is_lub_single.
 +
  cbn.
  replace 
  (fmap S
     (ffold_functional f g
        Hc ff)) with (fun m => m = bot \/ m = f x).
   {
    apply ordered_pair_has_lub.
    apply bot_least.
   }
  subst.
  unfold ffold_functional.
  cbn.
  apply set_equal;
  intro w ; split; intro Hm.
  *
    destruct Hm as [Heq | Heq];
    subst.
    --
     exists fbot.
     rewrite fcases_fbot; tauto.
   --
    exists (pure x).
    rewrite fcases_pure; tauto.
 *
   destruct Hm as (n & [Heq | Heq] & Heq'); subst.
   --
   rewrite fcases_fbot.
   now left.
   -- 
   rewrite fcases_pure.
   now right.
-
assert (Hn: S <> single fbot).
{
 intro Heq;subst.
 destruct Hl as (Hu & Hm).
 specialize (@single_pbot_upper_pbot (CPO2PPO(itree_CPO(F:=F)(X := X)))) as Hp.
 specialize (Hm _ Hp).
 apply (itree_ord_inv) in Hm.
 destruct Hm as [Heq | [(w & Heq1 & Heq2) | 
(W & fw &  c & c' & Heq1 & Heq2 & Ha)]]; subst.
-
 now apply impure_not_fbot in Heq.
-
 symmetry in Heq1; now apply pure_not_impure in Heq1.
-
symmetry in Heq2;
now apply impure_not_fbot in Heq2.
}
assert (Hil : is_lub (P :=  Y)
(fmap (remove S fbot) (ffold_functional f g Hc ff))
(ffold_functional f g Hc ff (impure fz k))).
{
 specialize (ffucp_aux3_aux _ Hd _ _ _ Hl) as Hex.
 destruct Hex as (K & HdK & HeqS & HlK).
 rewrite HeqS.
 rewrite <- fmap_comp.
 remember (((ffold_functional f g Hc ff)
° impure fz)) as G.
unfold ffold_functional in *.
cbn in *.
unfold comp in *.
rewrite fcases_impure in *.
assert (HG : G = fun x =>   g Z fz (fun z : Z => ff (x z))).
{
 extensionality l.
 rewrite HeqG.
 now rewrite fcases_impure.
}
clear HeqG.
subst.
remember 
((fun x : Z -> itree F X =>
g Z fz (fun z : Z => ff (x z)))) as h.
cbn.
remember ((g Z fz (fun z : Z => ff (k z)))) as hk.
assert (Heq : h k = hk)
by now subst.
rewrite <- Heq.
clear hk Heqhk Heq.
assert (Hch : is_continuous
 (P1 := EXP_DCPO Z (itree F X)) 
 (P2 := Y)
h) by (subst;
  now apply ffold_functional_pres_cont_aux).
rewrite continuous_iff_mono_commutes in Hch.
destruct Hch as (Hmh & Hch).
specialize (Hch K (lub (d := EXP_DCPO Z (itree F X))  K) HdK (lub_is_lub (d := EXP_DCPO Z (itree F X)) _ HdK)).
unfold commutes_with_lub in Hch.
specialize (is_lub_lub_eq1 (D := EXP_DCPO Z (itree F X)) K _ HlK).
intro Himp.
now rewrite (Himp HdK).
}
{
destruct Hil as (Hu & Hm).
split.
-
 intros x (y & Hmy & Heq); subst.
 apply ffold_functional_pres_mono;
 [rewrite continuous_iff_mono_commutes in Hff; 
 now destruct Hff |].
 destruct (oracle (y = fbot)); subst; 
 [apply lnbot_least |].
destruct Hl as (Hu' & _).
now apply Hu'.
-
intros y Huy.
remember (ffold_functional f g Hc ff
(impure fz k)) as w.
unfold ffold_functional in Heqw.
cbn in Heqw.
rewrite fcases_impure in Heqw.
subst.
apply Hm.
intros x (z & Hmz & Heq); subst.
apply Huy.
exists z; split; auto.
now destruct Hmz.
}
-
 cbn.
 destruct Hd as (Hne & _).
 destruct Hl as (Hu & _).
 rewrite (@is_upper_pbot_empty_single_iff
 (CPO2PPO(itree_CPO(F:=F)(X := X)))) in Hu.
 destruct Hu as [He | Hs]; [contradiction |];
 subst.
 rewrite fmap_single.
 unfold ffold_functional.
 rewrite fcases_fbot.
 unfold pbot.
 cbn.
 rewrite fcases_fbot.
 apply is_lub_single.
 Qed.


 Definition ffold_fuel{F : Type -> Type}{X : Type}{Y : CPO}
 (f : X -> Y)(g : forall Z, F Z -> (Z -> Y) -> Y)
   (Hc : forall T ft, 
   is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft))
   (n:nat)
   : itree F X -> Y := 
   iterate n (fun _ => bot) 
   (ffold_functional f g Hc).


 Lemma ffold_fuel_is_continuous{F : Type -> Type}{X:Type} 
 {Y: CPO} (f : X -> Y)(g : forall Z, F Z -> (Z -> Y) -> Y)
 (Hc : forall T ft, 
 is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft)):
forall n,
  is_continuous 
  (P1 := itree F X)
  (P2 :=  Y)
  (ffold_fuel f g Hc n).
 Proof.
 induction n.
 - 
  cbn.
  apply cst_is_continuous.
 -
  cbn.
  now apply ffold_functional_pres_cont.
 Qed.


Lemma ffold_lub_ffold_fuel{F : Type -> Type}{X: Type}{Y:CPO}
{f : X -> Y}{g : forall Z, F Z -> (Z -> Y) -> Y}
  {Hc : forall T ft, 
  is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft)}:
ffold f g Hc =
 lub (d := EXP_DCPO (itree F X)Y)(fun x =>  exists n, x = ffold_fuel f g Hc n ).
Proof.
extensionality m.
specialize (@ffold_least_fixpoint F X Y f g Hc) as Hlp.
specialize (@Kleene ((EXP_CPO (itree F X) Y)) (ffold_functional f g
Hc)) as Hk.
assert (Hc': is_continuous (P1 := (EXP_CPO (itree F X) Y))
(P2 := (EXP_CPO (itree F X) Y))
 (ffold_functional f g Hc)).
 {
  rewrite cont_iff_H_cont.
  apply ffold_functional_H_cont.
 }
 specialize (Hk Hc').
 rewrite continuous_iff_mono_commutes in Hc'.
 destruct Hc' as (Hm & _).
 apply iterate_directed in Hm.
 replace  (ffold f g Hc) with
 (ffix (X :=  (EXP_CPO (itree F X) Y)) (ffold_functional f g Hc)).
- 
unfold ffix.
cbn in *. 
unfold EXP.
destruct (oracle (@is_directed
(EXP_Poset (itree F X) Y)
(fun x : itree F X -> Y
 =>
 exists n : nat,
   x =
   @iterate
     (itree F X -> Y) n
     (fun _ : itree F X
      => @bot Y)
     (@ffold_functional F
        X Y f g Hc))));
         [auto| contradiction].
-  
  unfold is_least_fixpoint in *.
  destruct Hlp as (Hp & Hl).
  destruct Hk as (Hp' & Hl').
 apply antisym.
 +
   now apply Hl'.
 +
  now apply Hl.
Qed.         


Lemma ffold_is_continuous{F:Type -> Type}{X:Type}{Y:CPO}
(f : X -> Y)(g : forall Z, F Z -> (Z -> Y) -> Y)
(Hc : forall T ft, 
is_continuous (P1 := EXP_DCPO T Y) (P2 := Y) (g T ft)):
is_continuous (P1 := itree F X) (P2 := Y) (ffold f g Hc).
Proof.
rewrite ffold_lub_ffold_fuel.
apply lub_cont.
-
 unfold ffold_fuel.
 cbn.
 apply (iterate_directed   (X :=  (EXP_CPO (@itree_CPO F X) Y))).
 apply ffold_functional_mono.
-
 cbn.
 intros h (n & Hmq);subst.
 apply ffold_fuel_is_continuous.
Qed. 
