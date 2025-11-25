From Stdlib Require Import FunctionalExtensionality PropExtensionality
 IndefiniteDescription Classical List Lia JMeq.

 From Domain Require Export Cont ADCPO.
 From Itree Require Export Itree.

 (* bind on interaction trees: definition, monadic laws,
  and proof of continuity in both arguments*)

Definition fbind_functional_uncurried{F:Type -> Type}{X Y:Type} 
    (ff : (itree F  X) * (X -> itree F Y ) -> itree F Y )
     (p: itree F X * (X -> itree F Y )) : 
     itree F Y  :=
        match (fcases (fst p)) with
        inleft s  => 
          match s with
            inl (exist _ x _ )=>  (snd p) x
            | inr (existT _ _ (existT _ fz (exist _ k _))) => 
               impure fz (fun c => ff ((k c), (snd p)))
          end
        | inright _ => fbot
        end.

 
 Lemma fbind_functional_uncurried_is_monotonic{F:Type -> Type}{X Y:Type} 
 : is_monotonic 
  (P1 := EXP_Poset  ((itree F  X) * (X -> itree F Y )) (itree F Y))
  (P2 := EXP_Poset ((itree F  X) * (X -> itree F Y )) (itree F Y))
fbind_functional_uncurried.      
Proof.
intros px py Hle.
cbn in px, py, Hle.
intros (fx & x2fx).
unfold fbind_functional_uncurried.
cbn.
destruct (fcases fx) as [ [(x & Heq) | (Z & fz & k & Heq) ] | Heq];subst.
-
 apply refl.
-
 apply impure_is_monotonic.
 intro d.
 apply Hle.
-
 apply refl. 
Qed.

Lemma impure_is_continuous{F : Type -> Type}{X Y : Type} (fy : F Y):
is_continuous 
(P1 := (EXP_DCPO _ _))
(P2 := itree F X)
(impure fy).
Proof.
rewrite continuous_iff_mono_commutes; split; 
[apply impure_is_monotonic|].
intros S l Hd Hl.
apply is_lub_lub_eq1 in Hl; auto.
remember (fmap S (impure fy)) as S'.
assert (Hd' : is_directed S').
{
  subst.
  apply monotonic_directed; auto.
  apply impure_is_monotonic.
} 
unfold impure in *.
rewrite Hl.
specialize (@lnode_is_continuous (unit+Type)
(fun x : unit + Type =>
match x with
| @inl _ _ _ => Empty_set
| @inr _ _ Y0 => Y0
end)
(fun x : unit + Type =>
      match x with
      | @inl _ _ _ => X
      | @inr _ _ Y0 => F Y0
      end) (@inr unit Type Y) fy
) as Hc.
rewrite continuous_iff_mono_commutes in Hc.
destruct Hc as (Hm & Hc).
unfold commutes_with_lub in Hc.
specialize (Hc S (lub S) Hd (lub_is_lub _ Hd)).
now  subst.
Qed.

Lemma mono_aux{F : Type -> Type}{X Y: Type}:
forall Z k f,
is_monotonic 
 (P1 := (EXP_Poset ((itree F X *
 (X -> itree F Y))) (itree F Y)))
(P2 := (EXP_Poset Z (itree F Y)))
(fun
  g : EXP
         (itree F X *
          (X -> itree F Y))
         (itree F Y) =>
  (fun c : Z => g (k c, f))).
Proof.
intros Z k f x y Hle.
intro w.
apply Hle.
Qed.

Lemma cont_aux{F : Type -> Type}{X Y: Type}:
forall Z fz k f,
is_continuous 
 (P1 := (EXP_DCPO ((itree F X *
 (X -> itree F Y))) (itree F Y)))
(P2 := itree F Y)
(fun g : EXP
         (itree F X *
          (X -> itree F Y))
         (itree F Y) =>
@impure F Y Z fz
  (fun c : Z => g (k c, f))).
Proof.
intros Z fz k f.
remember (fun
       (ff : EXP
               (itree F X *
                (X -> itree F Y))
               (itree F Y)) 
       (c : Z) => ff (k c, f)) as h.
replace (fun g : EXP
      (itree F X *
       (X ->
        itree F Y))
      (itree F Y) => impure fz
(fun c : Z =>
 g (k c, f))) with (comp (impure fz) h) by
  now subst.
apply 
(comp_is_continuous 
  (P1 :=(EXP_DCPO
  (itree F X * (X -> itree F Y))
  (itree F Y)))(P2 := EXP_DCPO Z (itree F Y)) 
  (P3 := itree F Y)); [apply impure_is_continuous |].
rewrite continuous_iff_mono_commutes; split;
  [subst; apply mono_aux |].
cbn.    
intros S l Hd Hl.
specialize (lub_proj _ Hd) as Hll.
apply is_lub_unique with (x := l) in Hll; auto.
replace l with 
(lub (d := (EXP_DCPO (itree F X * (X -> itree F Y)) (itree F Y))) S)
in *.
clear Hl.
rewrite Hll.
assert (Hd' : @is_directed (EXP_DCPO Z (itree F Y))
  (@fmap
     (EXP (itree F X * (X -> itree F Y))
        (itree F Y)) (Z -> itree F Y) S
     (fun
        (ff : EXP
                (itree F X *
                 (X -> itree F Y))
                (itree F Y)) 
        (c : Z) => ff (k c, f)))).
{
 apply (monotonic_directed 
 (P1 := 
    (EXP_Poset 
    (itree F X * (X -> itree F Y)) 
    (itree F Y)))
 (P2 := (EXP_Poset  Z  (itree F Y)))); auto.
 apply mono_aux.
}        
subst.
remember ((fmap S
(fun
   (ff : EXP
           (itree F X *
            (X -> itree F Y))
           (itree F Y)) 
   (c : Z) => ff (k c, f))) ) as S'.
assert
(Hk :(lub 
    (d := (EXP_DCPO Z
    (itree F Y)))
    (fmap S   (fun ff => (fun c : Z => ff (k c,f))))) =
    (fun c : Z => lub (proj S (k c, f)))).
{
 rewrite <- HeqS'.
 specialize (lub_proj _ Hd') as Hl'.
 replace (lub (d:= EXP_DCPO Z (itree F Y))S') 
  with  (fun d : Z => lub (proj S' d)) by 
    (now apply (is_lub_lub_eq1 (D :=EXP_DCPO Z (itree F Y)))).
 extensionality d.
 f_equal.
 subst.
 apply set_equal; split ; intro Hm.
 -
  destruct Hm as (f0 & Hm & Heq); subst.
  destruct Hm as (g & Hm & Heq); subst.
  now exists g.
 -
   destruct Hm as (g & Hm & Heq); subst.
   exists (fun d => g (k d, f)); split; auto.
   now exists g.  
}
rewrite <- Hk in *.
subst.
now apply lub_is_lub in Hd'.
Qed.



Lemma fbind_functional_uncurried_is_H_continuous
{F : Type -> Type}{X Y: Type} :
is_H_continuous 
(A := ((itree F  X) * (X -> itree F Y )))
(B := itree_CPO)
fbind_functional_uncurried.
Proof.
split; [apply fbind_functional_uncurried_is_monotonic|].
intros S Hd.
extensionality t.
unfold fbind_functional_uncurried.
destruct t as (m & f); cbn.
destruct (fcases m) eqn:Hm.
-
 destruct s.
 +
  destruct s.
  rewrite fmap_cst; [ | now destruct Hd].
  now rewrite lub_single.
 +
  destruct s.
  destruct s.
  destruct s.
  clear Hm; subst.
  cbn in S.
  remember (fun
  f0 : EXP
         (itree F X *
          (X -> itree F Y))
         (itree F Y) => impure x0
  (fun c : x => f0 (x1 c, f))) as h.
 assert (Hcont : 
 is_continuous 
 (P1 := (EXP_DCPO ((itree F X *
 (X -> itree F Y))) (itree F Y)))
 (P2 := itree F Y) h) by (
  rewrite Heqh;
  apply cont_aux).
 rewrite continuous_iff_mono_commutes in Hcont.
 destruct Hcont as (Hmo & Hcont).
 specialize (Hcont S _ Hd (lub_is_lub (d := (EXP_DCPO
 (itree F X *
  (X -> itree F Y))
 (itree F Y))) _ Hd)).
 specialize (lub_proj _ Hd) as Hlp.
 assert (Heqh' : h (lub (d := (EXP_DCPO
 (itree F X *
  (X -> itree F Y))
 (itree F Y))) S) = impure x0
 (fun c : x =>
  lub (proj S (x1 c, f)))).
  {
   rewrite Heqh.
   f_equal.
  }
rewrite Heqh' in Hcont.
apply is_lub_lub_eq1; auto.
apply (monotonic_directed (P1 := (EXP_Poset
  (itree F X *
   (X -> itree F Y))
  (itree F Y))) (P2 := itree F Y)); auto.
-
  rewrite fmap_cst; [ | now destruct Hd].
  now rewrite lub_single.
Qed.
 

Definition fbind_uncurried{F : Type -> Type}{X Y: Type} 
: (itree F  X) * (X -> itree F Y ) -> itree F Y 
 := pointwise_fix 
(A := (itree F  X) * (X -> itree F Y )) 
(B := itree_CPO) 
fbind_functional_uncurried.

Lemma fbind_uncurried_least_fixpoint{F : Type -> Type}{X Y: Type} : 
is_least_fixpoint 
   (X := EXP_Poset ((itree F  X) * (X -> itree F Y )) itree_CPO)
fbind_functional_uncurried 
fbind_uncurried.
Proof.
intros.
apply Haddock_pointwise,
fbind_functional_uncurried_is_H_continuous.
Qed.

Lemma fbind_uncurried_fixpoint_eq{F : Type -> Type}{X Y: Type} : 
(@fbind_functional_uncurried F X Y)
fbind_uncurried =
fbind_uncurried.
Proof.
intros.
destruct  (@fbind_uncurried_least_fixpoint F X Y) as (Hf & _).
apply Hf.
Qed.

Definition fbind_uncurried_fuel{F : Type -> Type}{X Y: Type} (n:nat)  :
(itree F X * (X -> itree F Y)) -> itree F Y:=
  @iterate ((itree F X * (X -> itree F Y)) -> itree F Y) n (fun _ => fbot) (@fbind_functional_uncurried F X Y).

Lemma fbind_uncurried_lub_fuel{F : Type -> Type}{X Y: Type}:
  @fbind_uncurried F X Y= 
  lub (d := EXP_DCPO (PROD_DCPO _ (EXP_DCPO _ _)) _)
  (fun x => exists n, x = fbind_uncurried_fuel n).
  Proof.
  unfold fbind_uncurried,pointwise_fix.
  cbn.
  unfold proj.
  extensionality p.
  f_equal.
  apply set_equal;intro x; split; intro Hmx.
  -
   destruct Hmx as (m & Heq); subst.
   exists (fbind_uncurried_fuel m); split; auto.
   now exists m.
  -    
   destruct Hmx as (m & (n &Hn) & Heq); subst.
   now exists n.
Qed.   

Lemma fbind_uncurried_lub_fuel_pointwise{F : Type -> Type}{X Y: Type}(m : itree F X)
(f: X -> itree F Y) :
fbind_uncurried (m,f)= 
lub
(fun (x: (itree F Y)) => exists n, x = fbind_uncurried_fuel n (m,f)).
Proof.
reflexivity.
Defined.

Definition fbind_functional{F:Type -> Type}{X Y:Type} 
    (ff : (itree F  X) -> (X -> itree F Y ) -> itree F Y )
     (m: itree F X) (f:(X -> itree F Y )) : 
     itree F Y  :=
        match (fcases m) with
        inleft s  => 
          match s with
            inl (exist _ x _ )=>  f x
            | inr (existT _ Z (existT _ fz (exist _ k _))) => 
               @impure F Y Z fz (fun c => ff (k c) f)
          end
        | inright _ => fbot
        end.


Lemma func_eq{F:Type -> Type}{X Y:Type}:
forall (ff : (itree F  X) -> (X -> itree F Y ) -> itree F Y)
(m: itree F X) (f:X -> itree F Y ),
fbind_functional ff m f = 
fbind_functional_uncurried (fun p => ff (fst p) (snd p)) (m,f).
Proof.
intros ff m f.
reflexivity.
Qed.

Definition  fbind{F : Type -> Type}{X Y: Type} 
(m: itree F X) (f:X -> itree F Y ) :=
fbind_uncurried (m,f).

Lemma fbind_fixpoint_eq{F : Type -> Type}{X Y: Type} : 
(@fbind_functional F X Y)
fbind =
fbind.
Proof.
extensionality m.
extensionality f.
rewrite func_eq.
unfold fbind.
cbn.
rewrite <-fbind_uncurried_fixpoint_eq.
f_equal.
extensionality p.
rewrite fbind_uncurried_fixpoint_eq.
now destruct p.
Qed.

Lemma fbind_fbot{F : Type -> Type}{X Y: Type}
 (f:X -> itree F Y ) :
fbind fbot f = fbot.
Proof.
rewrite <- fbind_fixpoint_eq.
unfold fbind_functional.
(destruct (fcases fbot)); auto.
repeat destruct s.
-
 specialize (pure_not_fbot (F := F) x) as Hneq.
 now contradict Hneq.
-
 specialize (impure_not_fbot x0 x1) as Hneq.
 now contradict Hneq.
Qed.

Lemma fbind_impure{F : Type -> Type}{X Y Z: Type}
(fz: F Z) (k:Z -> itree F X ) (f : X -> itree F Y):
@fbind F X Y (@impure F X Z fz k) f = 
 @impure F Y Z fz (fun c => @fbind F X Y (k c) f).
 Proof.
 remember (@impure F Y Z fz
 (fun c : Z =>
  @fbind F X Y (k c) f)) as r.
 rewrite <- fbind_fixpoint_eq; subst.
 unfold fbind_functional.
 (destruct (fcases (impure fz k))); auto; repeat destruct s.
 -
 specialize (pure_not_impure x fz k) as Hneq.
 now contradict Hneq.
 -
  apply impure_is_injective in e.
  destruct e as (He & Hj & Hj'); now subst.
 -
  specialize (impure_not_fbot fz k) as Hne.
  now contradict Hne.
  Qed.
 

Definition fret{F : Type -> Type}{X: Type}(x:X) :=
  pure (F:=F) x.

(* monadic laws*)
 Lemma fbind_fret_left{F : Type -> Type}{X Y: Type}
 (x:X) (f:X -> itree F Y ) :
 fbind (fret x) f = f x.
 Proof.
 rewrite <- fbind_fixpoint_eq.
 unfold fbind_functional.
 (destruct (fcases (fret x))); auto; repeat destruct s.
 -
  apply pure_is_injective in e; now subst.
 -
  specialize (pure_not_impure x x1 x2) as Hneq.
  now contradict Hneq.
 -
  specialize (pure_not_fbot (F:=F) x) as Hneq.
  now contradict Hneq.
 Qed. 

Lemma fbind_fret_right{F: Type -> Type}{X: Type}:
forall (m: itree F X ), fbind m fret = m.
Proof.
intro m.
rewrite <-fbisim_iff_eq.
apply fbisim_coind with 
(R := fun x y => exists m, x = fbind m fret /\ y = m);
 [ | now exists m].
clear.
intros m m' (n & Heq & Heq'); subst.
destruct (fcases n) as 
[ [(x & Heq) | (Y & fy & k & Heq)]| Heq]; subst.
-
 right; left.
 exists x;split;auto.
 replace (pure x) with (@fret F X x) by reflexivity.
 now rewrite fbind_fret_left.
-
 right;right.
 rewrite fbind_impure.
 exists Y, fy,((fun c : Y => fbind (k c) fret)), k;
 repeat split; auto.
 intros x.
 now exists (k x).
-
left; split; auto.
now rewrite fbind_fbot.
Qed.    

Lemma fbind_assoc{F : Type -> Type}{X Y Z: Type}
(m :itree F X) (f : X -> itree F Y) (g : Y -> itree F Z):
fbind (fbind m f) g = fbind m (fun x => fbind (f x) g).
Proof.
rewrite <- fbisim_iff_eq.
apply fbisim_strong_coind with 
(R := fun u v =>  
exists m,
  u = (fbind (fbind m f) g) /\
  v = fbind m (fun x => fbind (f x) g)); [ | now exists m].
clear.
intros m1 m2 (n & Ha & Hb); subst.
destruct (fcases n) as 
[ [(x & He) | (W & fw & k & He)]| He]; subst.
- 
 right.
 replace (pure x) with (@fret F X x) in * by reflexivity.
 repeat rewrite fbind_fret_left.
 now rewrite fbisim_iff_eq.
-
 left; right;right.
 repeat rewrite fbind_impure.
 exists W, fw,   (fun c : W => fbind (fbind (k c) f) g),
  (fun c : W =>fbind (k c)(fun x : X => fbind (f x) g)); repeat split;auto.
 intro w.
 now exists (k w).
-
 right.
 repeat rewrite fbind_fbot.
 now rewrite fbisim_iff_eq.
Qed. 

Lemma fbind_functional_pointwise_fix{F:Type -> Type}{X Y:Type}
(m:itree F X):
  @fbind_functional F X Y fbind m = fbind m.
Proof.
remember (fbind_functional fbind m) as temp.
now rewrite <-fbind_fixpoint_eq.
Qed.

(* continuity in both argument*)

Lemma fbind_functional_uncurried_mono_pres{F:Type -> Type}{X Y:Type}
(f : (itree F X)*(X -> itree F Y) -> itree F Y ) :
is_monotonic (P1 := PROD_Poset (itree F X)(EXP_Poset X (itree F Y))) 
(P2:= itree F Y)  f ->
is_monotonic (P1 := PROD_Poset (itree F X)(EXP_Poset X (itree F Y))) 
(P2:= itree F Y)  (fbind_functional_uncurried f).
Proof.
intros Hm.
unfold fbind_functional_uncurried.
intros (u,v)  (u',v') Hle.
inversion Hle; subst; clear Hle.
cbn in  *.
apply itree_ord_inv in H.
destruct H as [Heq | [(x & Heq1 & Heq2) | 
(Z & fz & k & k' & Heq1 & Heq2 & Ha)]]; subst.
-
 rewrite fcases_fbot.
 apply lnbot_least.
-
 rewrite fcases_pure.
 apply H0.
-
 do 2 rewrite fcases_impure.
 apply impure_is_monotonic.
 intro z.
 apply Hm.
 split; auto.
 cbn.
 apply Ha.
Qed.  

Lemma ffucp_mono_aux1{F: Type -> Type}{X Y: Type}(x:X):
is_monotonic (P1 :=  EXP_Poset X (itree F Y) )
(P2 :=(itree F Y) )
(fun b : EXP X (itree F Y) => b x).
Proof.
intros u v Hle.
apply Hle.
Qed.

Lemma ffucp_aux1{F: Type -> Type}{X Y: Type}(x:X):
is_continuous (P1 :=  EXP_DCPO X (itree F Y) )
(P2 :=(itree F Y) )
(fun b : EXP X (itree F Y) => b x).
Proof.
rewrite continuous_iff_mono_commutes.
split; [apply ffucp_mono_aux1 | ].
intros S k Hd Hl.
cbn in S, k.
assert (Hd' : is_directed (P := itree F Y)
(fmap S
     (fun b : EXP X (itree F Y) => b x))).
{
   apply (monotonic_directed  (P1 :=  EXP_Poset X (itree F Y) )
   (P2 :=(itree F Y) )); auto.
   apply ffucp_mono_aux1.
}
specialize Hd as Hll.
apply lub_proj in Hll.
apply is_lub_unique with (x := k) in Hll;auto.
subst.
cbn.
replace (fmap S
(fun b : EXP X (itree F Y) => b x)) with (proj S x) in *
 by reflexivity.
now apply lub_is_lub.
Qed.

Lemma ffucp_mono_aux2{F: Type -> Type}{X Y: Type}
(f: itree F X * (X -> itree F Y) ->
    itree F Y) :
is_monotonic
    (P1 := PROD_DCPO (itree F X)
       (EXP_DCPO X (itree F Y))) 
    (P2 :=(itree F Y)) f   ->
forall (Z: Type) (fz: F Z)
(k: Z -> itree F X),
is_monotonic
(P1 :=  EXP_Poset X (itree F Y) )
(P2 := EXP_Poset Z (itree F Y) )
  ((fun
  b : EXP X
       (itree F
       Y) =>
(fun
   (g : 
    itree F X *
    EXP X
      (itree F
       Y) ->
    itree F Y)
   (c : Z) =>
 g (k c, b)) f)).
Proof.
intros Hm Z kz l u v Hle z.
apply Hm.
split; auto.
apply refl.
Qed.   

Lemma ffucp_aux2{F: Type -> Type}{X Y: Type}
(f: itree F X * (X -> itree F Y) ->
    itree F Y) :
is_continuous 
(P1 :=  (PROD_DCPO ( itree F X) (EXP_DCPO X (itree F Y))))
(P2 :=(itree F Y) )
f -> 
forall (Z: Type) (fz: F Z)
(k: Z -> itree F X),
is_continuous 
(P1 :=  EXP_DCPO X (itree F Y) )
(P2 :=(itree F Y) )
  (fun b : EXP X (itree F Y) =>
   impure fz (fun c : Z => f (k c, b))).
Proof.
intros Hc Z fz k.   
remember (fun b : EXP X (itree F Y) =>
  (fun g (c : Z) =>  g(k c, b)) f) as h.
replace (fun b : EXP X (itree F Y) =>
impure fz (fun c : Z => f (k c, b))) with (fun b =>  
((impure fz) (h b))) by now subst.
replace
((fun b : EXP X (itree F Y) =>
impure fz (h b))) with 
 (comp (@impure F Y Z fz) h) by now subst.
apply 
(comp_is_continuous (P1 := EXP_DCPO X (itree F Y)) 
(P2 := EXP_DCPO Z (itree F Y))
(P3 := itree F Y));
  [ apply (impure_is_continuous (Y := Z)) |].
subst.
rewrite continuous_iff_mono_commutes.
split.
{
  apply ffucp_mono_aux2; auto.
  rewrite continuous_iff_mono_commutes in Hc; 
  now destruct Hc.
}
intros S l Hd Hl.
cbn in S,l.
cbn.
remember (@fmap (EXP X (itree F Y))
(EXP Z (itree F Y)) S
(fun
   (b : EXP X (itree F Y))
   (c : Z) => f (k c, b))) as S'.
assert (Hd' : 
is_directed (P := (EXP_Poset  Z(itree F Y))) S').
{
subst.
 apply (monotonic_directed  (P1 :=  EXP_Poset X (itree F Y) )
    (P2 :=(EXP_Poset Z (itree F Y) ))); auto.
 apply ffucp_mono_aux2; auto.
 rewrite continuous_iff_mono_commutes in Hc; 
 now destruct Hc.
}
specialize Hd' as Hll.
apply lub_proj in Hll.
replace (fun c : Z => f (k c, l)) with (fun d : Z =>
lub (proj S' d)); auto.
extensionality d.
rewrite HeqS'.
rewrite proj_fmap.
rewrite <-fmap_comp.
unfold comp.
remember (fun x : EXP X (itree F Y) => (k d, x)) as h.
replace ((fun x : EXP X (itree F Y) =>
f (h x))) with (comp f h); auto.
assert (Hcont : 
 is_continuous 
 (P1 := EXP_DCPO X (itree F Y))
 (P2 := (itree F Y)) (f° h)).
 {
    apply (comp_is_continuous
    (P1 := EXP_DCPO X (itree F Y))
    (P2 :=  PROD_DCPO (itree F X) (EXP_DCPO X (itree F Y)) )
    (P3 := itree F Y)); auto.
    subst.
    apply (is_continuous_pair_snd
    (P1 := EXP_DCPO X (itree F Y))
    (P2 :=  (itree F X))).
 }
rewrite continuous_iff_mono_commutes in Hcont.
destruct Hcont as (Hm & Hcont).
cbn in Hcont.
specialize (Hcont S (lub (d := EXP_DCPO X (itree F Y)) S) Hd (lub_is_lub  _ Hd)).
specialize (lub_is_lub  _ Hd) as Hl3.
replace (f (h l)) with ((f°h) l) by auto.
eapply is_lub_unique with (x := l) in Hl3;
auto.
subst l.
erewrite is_lub_lub_eq1; eauto.
eapply @monotonic_directed in Hm; eauto.
Qed.

Lemma ffucp_mono_aux3{F:Type -> Type}{X Y:Type}
(f : (itree F X)*(X -> itree F Y) -> itree F Y ) :
 is_monotonic 
 (P1 := PROD_Poset (itree F X)(EXP_Poset X (itree F Y))) 
 (P2:= itree F Y)  f  ->
 forall(b: EXP X (itree F Y)),
is_monotonic 
(P1 := (itree F X))
(P2 := (itree F Y))
  (fun a : itree F X =>
   fbind_functional_uncurried
    f (a, b)).
Proof.
intros Hm b u v Hle.
unfold fbind_functional_uncurried.
apply itree_ord_inv in Hle.
destruct Hle as [Heq | [(x & Heq1 & Heq2) | 
(Z & fz & k & k' & Heq1 & Heq2 & Ha)]]; subst;
cbn [fst].
- 
  rewrite fcases_fbot.
  apply lnbot_least.
-
 rewrite fcases_pure.
 apply refl.
-
 do 2 rewrite fcases_impure.
 apply impure_is_monotonic.
 intro z.
 apply Hm.
 split; [|apply refl].
 cbn.
 apply Ha.
 Qed.
  


 Lemma ffucp_aux3_aux2{F:Type -> Type}{X Y:Type}:
 forall f : (itree F X * (X -> itree F Y) ->itree F Y), @is_continuous
    (PROD_DCPO (itree F X)
       (EXP_DCPO X (itree F Y)))
    (itree F Y) f ->
    forall(Z:Type) (fz : F Z)(b:  EXP X (itree F Y)),
 @is_continuous (EXP_DCPO Z (itree F X))
 (itree F Y)
 (fun x : Z -> itree F X =>
  @impure F Y Z fz
    (fun c : Z => f (x c, b))).
 Proof.
 intros f Hc Z fz b.
 remember ((fun x : Z -> itree F X =>
 impure fz
   (fun c : Z => f (x c, b)))) as i.
 (* (Z -> itree F X) -> itree F Y*)
 remember (fun g : (itree F X * (X -> itree F Y) ->
 itree F Y) => (fun x : Z -> itree F X =>
   (fun c : Z =>  g (x c, b)))) as h.
replace i with ((impure fz) ° (h f)) in * by now subst.
apply (comp_is_continuous
(P1 := EXP_DCPO Z (itree F X))
(P2 := EXP_DCPO Z (itree F Y))
(P3 := (itree F Y))); 
[apply  (impure_is_continuous (X := Y) fz) |].
clear i Heqi.
subst.
replace ((fun (x : Z -> itree F X) (c : Z) => f (x c, b))) with
(fun (x :  Z -> itree F X )  =>(f °  
(fun w => (pair w b))) ° x) by reflexivity.
remember  (f ° (fun w : itree F X => (w, b))) as g.
apply comp_cont_snd.
subst.
apply 
(comp_is_continuous
(P1 := itree F X)
(P2 := PROD_DCPO (itree F X)(EXP_DCPO X (itree F Y)))
(P3 := itree F Y)
); auto.
apply 
(is_continuous_pair_fst
(P1 := itree F X)
(P2 := EXP_DCPO X (itree F Y))
).
Qed.

Lemma ffucp_aux3{F:Type -> Type}{X Y:Type}
(f : (itree F X)*(X -> itree F Y) -> itree F Y ) :
 is_continuous (P1 := PROD_DCPO (itree F X)(EXP_DCPO X (itree F Y))) 
 (P2:= itree F Y)  f  ->
 forall(b: EXP X (itree F Y)),
is_continuous 
(P1 := (itree F X))
(P2 := (itree F Y))
  (fun a : itree F X =>
   fbind_functional_uncurried
    f (a, b)).
Proof.
intros Hc b.
rewrite continuous_iff_mono_commutes.
split; [apply ffucp_mono_aux3; rewrite continuous_iff_mono_commutes in Hc;
 now destruct Hc|].
 intros S l Hd Hl.
 remember (fmap S(fun a : itree F X =>
  fbind_functional_uncurried f (a, b))) as S'.
assert (Hd': is_directed (P := itree F Y) S').
{
 subst.
 apply (monotonic_directed (P1 := itree F X) (P2 := itree F Y));
 auto.
 apply ffucp_mono_aux3.
 rewrite continuous_iff_mono_commutes in Hc;
 now destruct Hc.
}
 destruct (fcases l) as 
[ [(x & Heq) | (Z & fz & k & Heq)]| Heq]; subst; cbn [fst snd].
-
 apply is_lub_pure in Hl; auto.
 destruct Hl as [Heq | Heq].
 +
  rewrite Heq in *.
  rewrite fmap_single in *.
  unfold fbind_functional_uncurried.
  cbn.
  rewrite fcases_pure.
  apply is_lub_single.
 +
  cbn.
  replace 
  ((fmap S
  (fun a : itree F X =>
   fbind_functional_uncurried f (a, b)))) with (fun m => m = fbot \/ m = b x).
   {
    unfold fbind_functional_uncurried.
    cbn.
    rewrite fcases_pure.
    apply ordered_pair_has_lub.
    apply lnbot_least.
   }
  rewrite Heq. 
  subst.
  unfold fbind_functional_uncurried.
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
assert (Hil : is_lub (P := itree F Y)
(fmap (remove S fbot)
   (fun a : itree F X =>
    fbind_functional_uncurried f (a, b)))
(fbind_functional_uncurried f
   (impure fz k, b))).
{
 specialize (ffucp_aux3_aux _ Hd _ _ _ Hl) as Hex.
 destruct Hex as (K & HdK & HeqS & HlK).
 rewrite HeqS.
 rewrite <- fmap_comp.
 remember (((fun a : itree F X =>
 fbind_functional_uncurried f (a, b))
° impure fz)) as G.
unfold fbind_functional_uncurried in *.
cbn in *.
unfold comp in *.
rewrite fcases_impure in *.
assert (HG : G = fun x => impure fz (fun c : Z => f (x c, b))).
{
 extensionality l.
 rewrite HeqG.
 now rewrite fcases_impure.
}
clear HeqG.
subst.
remember 
((fun x : Z -> itree F X =>
@impure F Y Z fz (fun c : Z => f (x c, b)))) as h.
cbn.
match goal with
| |- context[@impure ?F ?X ?Y ?fy ?k] => remember (@impure F X Y fy k) as hk
end.
assert (Heq : h k = hk)
by now subst.
rewrite <- Heq.
clear hk Heqhk Heq.
assert (Hch : is_continuous
 (P1 := EXP_DCPO Z (itree F X)) 
 (P2 := itree F Y)
h) by (subst;  now apply ffucp_aux3_aux2).
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
 apply fbind_functional_uncurried_mono_pres; 
 [rewrite continuous_iff_mono_commutes in Hc; 
 now destruct Hc |].
 split; [cbn | apply refl].
 destruct (oracle (y = fbot)); subst; 
 [apply lnbot_least |].
destruct Hl as (Hu' & _).
now apply Hu'.
-
intros y Huy.
remember (fbind_functional_uncurried f
 (impure fz k, b)) as w.
unfold fbind_functional_uncurried in Heqw.
cbn in Heqw.
rewrite fcases_impure in Heqw.
subst.
unfold fbind_functional_uncurried.
apply Hm.
intros x (z & Hmz & Heq); subst.
apply Huy.
exists z; split; auto.
now destruct Hmz.
}
-
 unfold fbind_functional_uncurried.
 cbn.
 destruct Hd as (Hne & _).
 destruct Hl as (Hu & _).
 rewrite (@is_upper_pbot_empty_single_iff
 (CPO2PPO(itree_CPO(F:=F)(X := X)))) in Hu.
 destruct Hu as [He | Hs]; [contradiction |];
 subst.
 rewrite fmap_single.
 rewrite fcases_fbot.
 unfold pbot.
 cbn.
 rewrite fcases_fbot.
 apply is_lub_single.
 Qed.


Lemma fbind_functional_uncurried_cont_pres{F:Type -> Type}{X Y:Type}
(f : (itree F X)*(X -> itree F Y) -> itree F Y ) :
is_continuous 
(P1 := PROD_DCPO (itree F X)(EXP_DCPO X (itree F Y))) 
(P2:= itree F Y) 
 f ->
is_continuous 
(P1 := PROD_DCPO (itree F X)(EXP_DCPO X (itree F Y))) 
(P2:= itree F Y) 
(fbind_functional_uncurried f).
Proof.
intro Hc.
apply argwise_continuous.
-
 intro m.
 unfold fbind_functional_uncurried.
 cbn.
 destruct (fcases m) as 
[ [(x & Heq) | (Z & fz & k & Heq)]| Heq]; subst. 
+
 now apply ffucp_aux1.
+
 now apply ffucp_aux2.
+
 apply (cst_is_continuous (P1 := (EXP_DCPO X (itree F Y)))).
- 
  intro b.
  now apply ffucp_aux3.
Qed.  

Lemma fbind_uncurried_fuel_is_continuous{F : Type -> Type}{X Y: Type}:
forall n,
 is_continuous 
 (P1 := (PROD_DCPO(itree F X) (EXP_DCPO X (itree F Y))))
 (P2 :=  (itree F Y))
 (fbind_uncurried_fuel n).
Proof.
induction n.
- apply cst_is_continuous.
-
 now apply fbind_functional_uncurried_cont_pres.
Qed. 


Lemma fbind_lub_fbind_fuel{F : Type -> Type}{X Y: Type}:
fbind_uncurried  =
lub
(d := EXP_CPO (PROD_CPO (@itree_CPO F X)(EXP_CPO X (@itree_CPO F Y)))
(@itree_CPO F Y)) (fun f =>  exists n, f = fbind_uncurried_fuel n).
Proof.
specialize (@fbind_uncurried_least_fixpoint F X Y) as Hlp.
specialize (Kleene 
(A := EXP_CPO (PROD_CPO (@itree_CPO F X)(EXP_CPO X (@itree_CPO F Y)))
(@itree_CPO F Y))
(@fbind_functional_uncurried F X Y)) as Hk.
assert (Hc': is_continuous 
(P1 :=
 EXP_CPO (PROD_CPO (@itree_CPO F X)(EXP_CPO X (@itree_CPO F Y)))(@itree_CPO F Y ))
(P2 := 
EXP_CPO (PROD_CPO (@itree_CPO F X)(EXP_CPO X (@itree_CPO F Y))) (@itree_CPO F Y))
 (@fbind_functional_uncurried F X Y)).
 {
  rewrite cont_iff_H_cont.
  apply fbind_functional_uncurried_is_H_continuous.
 }
specialize (Hk Hc').
rewrite continuous_iff_mono_commutes in Hc'.
destruct Hc' as (Hm & _).
cbn -[lub].
apply iterate_directed in Hm.
cbn - [lub] in Hm.
replace (@fbind_uncurried F X Y) with
(@ffix
         (EXP_CPO
            (PROD_CPO (@itree_CPO F X)
               (EXP_CPO X (@itree_CPO F Y)))
            (@itree_CPO F Y))
         (@fbind_functional_uncurried F X Y)).
-
 unfold ffix.
 cbn -[lub].
 f_equal.
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

Lemma fbind_uncurried_is_continuous
 {F : Type -> Type}{X Y: Type}:
 is_continuous 
 (P1 := (PROD_DCPO(itree F X) (EXP_DCPO X (itree F Y))))
 (P2 :=  (itree F Y))
 fbind_uncurried.
Proof.
rewrite fbind_lub_fbind_fuel.
apply lub_cont.
-
 unfold fbind_uncurried_fuel.
 cbn.
 apply (iterate_directed  (X :=  (EXP_CPO (PROD_CPO (@itree_CPO F X)(EXP_CPO X (@itree_CPO F Y)))
 (@itree_CPO F Y)))).
 apply fbind_functional_uncurried_is_monotonic.
-
 cbn.
 intros f (n & Hmq);subst.
 apply fbind_uncurried_fuel_is_continuous.
Qed. 


Lemma fbind_is_continuous_fst
 {F : Type -> Type}{X Y: Type}:
 forall (f : X -> itree F Y),
 is_continuous 
 (P1 := itree F X)
 (P2 :=  (itree F Y))
 (fun m => fbind m f).
 intro f.
 specialize (@fbind_uncurried_is_continuous F X Y) as Hc.
 now apply is_continuous_fst_arg with (b := f) in Hc.
 Qed.

Lemma fbind_is_continuous_snd
 {F : Type -> Type}{X Y: Type}:
 forall (m : itree F X),
 is_continuous 
 (P1 := (EXP_DCPO X (itree F Y)))
 (P2 :=  (itree F Y))
 (fun k => (fbind m k)).
 intro m.
 specialize (@fbind_uncurried_is_continuous F X Y) as Hc.
 now apply is_continuous_snd_arg with (a := m) in Hc.
 Qed.


Lemma fbind_ignore_is_monotonic_snd{F : Type -> Type}{X Y: Type}:
forall (m : itree F X),
is_monotonic
(P1 := ((itree F Y)))
(P2 :=  (itree F Y))
(fun k:(itree F Y) => (fbind m (fun _:X => k))).
Proof.
intros m u v Hle.
specialize (@fbind_is_continuous_snd  F X Y m) as Hcs.
apply continuous_implies_monotonic in Hcs.
apply Hcs.
now intros _.
Qed.

Lemma fbind_ignore_is_continuous_snd{F : Type -> Type}{X Y: Type}:
forall (m : itree F X),
is_continuous
(P1 := ((itree F Y)))
(P2 :=  (itree F Y))
(fun k:(itree F Y) => (fbind m (fun _:X => k))).
Proof.
intros m S Hd.
specialize (@fbind_is_continuous_snd F X Y m) as Hcs.
split.
{
  apply monotonic_directed; auto.
  apply fbind_ignore_is_monotonic_snd.
}
remember (fmap S (fun x  => (fun _:X => x))) as S'.
assert (HS': is_directed (P := EXP_Poset _ _) S').
{
  subst.
  apply 
   (monotonic_directed (P2 := EXP_Poset _ _)); auto.
  now intros u v Hle _.
}
specialize (Hcs _ HS').
clear HS'.
destruct Hcs as (_ & Heq).
subst.
rewrite <- fmap_comp in Heq.
unfold comp in Heq.
cbn in *.
rewrite <- Heq.
unfold proj.
f_equal.
extensionality x.
rewrite <- fmap_comp.
unfold comp.
now rewrite fmap_id.
Qed.
