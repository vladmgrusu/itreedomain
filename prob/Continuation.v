From Stdlib Require Import FunctionalExtensionality.
From Domain Require Export Cont.
From Monad Require Export Monad.


Section Continuation.

Variable Res : CPO.

Definition cont_functor (X : Type) : CPO :=
CONT_CPO (EXP_CPO X Res) Res.


Lemma cont_ret_cont{X:Type}{Y:DCPO}(x:X):
is_continuous (P1 := EXP_DCPO _ _)
  (fun (f: EXP X Y)  =>   f x).
Proof.  
intros S Hd.
assert (Hd' : is_directed
  (fmap S
     (fun f : EXP_DCPO X Y =>
      f x)) ).
  {
    apply monotonic_directed;auto.
    intros u v Hle.
    apply (Hle x).
  }
split; auto.
Qed.

Program Definition cont_ret (X : Type) (x : X) : cont_functor X :=
{|
  fonc := fun f => f x; cont := cont_ret_cont x
|}.

Lemma cont_bind_mono_aux{X Y : Type}
  (m : cont_functor X)
  (f : X -> cont_functor Y):
is_monotonic
(P1 := EXP_Poset Y Res)
    (P2 := EXP_Poset X Res)
(fun g x
      => fonc (f x) g).
Proof.
intros g g' Hle.     
intro x.
remember (f x) as fx.
destruct fx as (fx & Hfxc).
cbn.
clear Heqfx.
rewrite continuous_iff_mono_commutes in Hfxc.
destruct Hfxc as (Hfxm & _).
now apply Hfxm.
Qed. 


Lemma cont_bind_mono{X Y : Type}
  (m : cont_functor X)
  (f : X -> cont_functor Y):
is_monotonic
  (fun g 
   =>
   fonc m (fun x : X => fonc (f x) g)).
Proof.
change (is_monotonic ((fonc m) ° (fun g x => fonc (f x) g))).
apply comp_is_monotonic; [ | now apply cont_bind_mono_aux].
destruct m as (m & Hmc).
cbn.
rewrite continuous_iff_mono_commutes in Hmc.
now destruct Hmc as (Hmc & _).
Qed.



Lemma cont_bind_cont_aux{X Y : Type}
  (m : cont_functor X)
  (f : X -> cont_functor Y):
is_continuous (P1 := EXP_DCPO _ _) (P2 :=  EXP_DCPO _ _)
  (fun g  x  => fonc (f x) g).
Proof.
intros S Hd.
assert (Hd' : is_directed (P := EXP_Poset _ _)
(fmap S
   (fun (g : EXP Y Res)
      (x : X) => 
    fonc (f x) g))).
{
  apply (monotonic_directed
  (P1 := EXP_Poset _ _)
  (P2 := EXP_Poset _ _)); auto.
  now apply cont_bind_mono_aux.
}
split; auto.
cbn.
unfold proj.
extensionality x.
rewrite <- fmap_comp.
unfold comp.
cbn.
remember (f x) as fx.
destruct fx as (fx & Hfxc).
cbn.
clear Heqfx.
specialize (Hfxc _ Hd).
destruct Hfxc as (Hd''  & Heqfx).
replace ((fun d : Y =>
@lub Res
  (@fmap (EXP Y Res) Res S
     (fun f0 : EXP Y Res => f0 d)))) with (lub S).
{
 cbn in *.
 rewrite Heqfx.
 f_equal.
}
apply lub_fonc_fmap in Hd.
symmetry.
apply is_lub_unique with
 (x := lub (d := EXP_CPO _ _)  S) in Hd;
  auto.
Qed.  

Lemma cont_bind_cont{X Y : Type}
  (m : cont_functor X)
  (f : X -> cont_functor Y):
is_continuous 
  (fun g 
   =>
   fonc m (fun x : X => fonc (f x) g)).
Proof.
change (is_continuous ((fonc m) ° (fun g x => fonc (f x) g))).
apply comp_is_continuous; [now destruct m |  now apply cont_bind_cont_aux].
Qed.





Definition cont_bind
  (X Y : Type) (d : cont_functor X) (f : X -> cont_functor Y) :
cont_functor Y := {|
  fonc := fun g => fonc d (fun x => fonc (f x) g);
  cont := cont_bind_cont d f
|}.

Lemma cont_bind_is_monotonic_fst (X Y : Type) (f : X -> cont_functor Y) :
is_monotonic (fun d => cont_bind d f).
Proof.
intros m m' Hle.
unfold cont_bind.
cbn.
intro d.
cbn in Hle.
apply Hle.
Qed.

Lemma cont_bind_is_continuous_fst (X Y : Type) (f : X -> cont_functor Y) :
is_continuous (fun d => cont_bind d f).
Proof.
intros S Hd.
assert (Hd' : is_directed (fmap S (fun d : cont_functor X => cont_bind d f))).
{
 apply monotonic_directed; auto.
 apply cont_bind_is_monotonic_fst.
}
split ; auto.
unfold cont_bind.
cbn.
destruct (oracle
(@is_directed
   (CONT_Poset (EXP_DCPO _ _)_)
   (@fmap (CONT (EXP_DCPO _ _) _)
          (CONT(EXP_DCPO _ _) _) S
      (fun d  =>
       Build_CONT
         (EXP_DCPO _ _) _
         (fun g : EXP  _ _ =>
          fonc d (fun x  =>
             fonc  (f x) g))
         (cont_bind_cont d f))))).
{
  apply CONT_equal.
   cbn.
   extensionality h.
   cbn.
   destruct (oracle (
   (@is_directed
      (CONT_Poset (EXP_DCPO X (@dcpo_cpo Res)) (@dcpo_cpo Res)) S)));
   [ | contradiction].
  cbn.
  unfold proj.
  now repeat rewrite <- fmap_comp.
}
contradict n.
apply (monotonic_directed
(P1 := CONT_Poset _ _)
(P2 := CONT_Poset _ _)); auto.
intros h h' Hl k.
cbn.
cbn in Hl.
apply Hl.
Qed.       



Lemma cont_bind_is_monotonic_snd (X Y : Type) (m : cont_functor X) :
@is_monotonic (EXP_DCPO X (cont_functor Y)) (cont_functor Y) (cont_bind m).
Proof.
destruct m as (m & Hc).
specialize Hc as  Hm.
rewrite continuous_iff_mono_commutes in Hm.
destruct Hm as (Hm & _).
unfold cont_bind.
intros u v Hle.
cbn.
intro h.
apply Hm.
intro x.
cbn in Hle.
apply Hle.
Qed.



Lemma cont_bind_is_monotonic_snd_aux(X Y : Type)
(h : Y -> Res):
@is_monotonic (EXP_DCPO X (CONT_DCPO (EXP_DCPO Y Res) Res))
(EXP_CPO X Res)
  (fun (x : EXP X (CONT (EXP_DCPO Y Res) Res))
     (x0 : X) => fonc (x x0) h).
 Proof.
 intros u v Hle x.
 cbn in Hle.
 apply Hle.
 Qed.


Lemma cont_bind_is_continuous_snd_aux(X Y : Type)
(h : Y -> Res):
@is_continuous (EXP_DCPO _ (CONT_DCPO _ _))
(EXP_CPO _ _)
  (fun (f : EXP X (CONT (EXP_DCPO _ _) Res))
      x => fonc (f x) h).
intros S Hd.
assert (@is_directed (EXP_CPO X Res)
(@fmap (EXP_DCPO X (CONT_DCPO (EXP_DCPO Y Res) Res)) 
   (EXP_CPO X Res) S
   (fun (x : EXP X (CONT (EXP_DCPO Y Res) Res)) (x0 : X) => fonc (x x0) h))).
{
  apply monotonic_directed; auto.
  apply cont_bind_is_monotonic_snd_aux.
}
split; auto.   
extensionality x.
cbn.
destruct oracle ; [ | contradict n; now apply directed_proj].
cbn.
unfold proj.
now repeat rewrite <- fmap_comp.
Qed.
    

Lemma cont_bind_is_continuous_snd (X Y : Type) (m : cont_functor X) :
@is_continuous (EXP_DCPO X (cont_functor Y)) (cont_functor Y) (cont_bind m).
Proof.
specialize m as m'.
destruct m as (m & Hc).
specialize Hc as  Hm.
rewrite continuous_iff_mono_commutes in Hm.
destruct Hm as (Hm & Hco).
intros S Hd.
assert (Hd' : is_directed (P := cont_functor Y) 
(fmap S
     (cont_bind
        {|
          fonc := m;
          cont := Hc
        |}))).
 { 
   apply monotonic_directed; auto.
   apply cont_bind_is_monotonic_snd.
 }
 split; auto.
 cbn.       
 destruct oracle;
  [ | contradiction].
cbn.
unfold cont_bind.
apply CONT_equal.
cbn.
extensionality h.
unfold proj.
etransitivity.
  {
    apply f_equal.
    extensionality x.
    destruct oracle.
    -
     cbn.
     repeat rewrite <- fmap_comp in *.
     unfold comp in *.
     change (@lub Res
     (fmap S (fun  x0  => fonc (x0 x) h) ))
      with
      ((fun x => (@lub Res
           (fmap S (fun x0  => fonc (x0 x) h) ))) x).
     reflexivity.
    -
     contradict n.
     cbn in *.
     apply (monotonic_directed
      (P1 := EXP_Poset _ ( CONT_Poset _ _))
      (P2 := CONT_Poset _ _)); auto.
   intros u v Hle.
   apply Hle.   
  }
cbn.
repeat rewrite <- fmap_comp in *.
unfold comp in *.
cbn.
remember ( (fun x : EXP X (CONT (EXP_DCPO Y Res) Res) =>
m (fun x0 : X => fonc (x x0) h))) as k.
replace (@lub Res (@fmap (EXP X (CONT (EXP_DCPO Y Res) Res)) Res S k)) with 
(k (lub S)).
{
  subst.
  cbn.
  f_equal.
  extensionality x.
  destruct oracle.
  {
    cbn.
    unfold proj.
    now repeat rewrite <- fmap_comp in *.
  }
   contradict n.
   now apply directed_proj.
}
assert (Hk : is_continuous
 (P1 := 
 EXP_DCPO _ (CONT_DCPO _ _))  k).
 {
 subst.
 change  ((fun
 x : EXP X
       (CONT
          (EXP_DCPO Y
            Res) Res) => m(fun x0 : X => fonc (x x0) h))) with 
  (m ° (fun (x : EXP X (CONT
    (EXP_DCPO Y  Res) Res)) (x0:X) => fonc (x x0) h)).
apply comp_is_continuous; auto.
apply cont_bind_is_continuous_snd_aux.
 }
subst.
specialize (Hk _ Hd).
now destruct Hk.
Qed.


Program Definition cont_monad : MONAD := {|
  functor := cont_functor;
  ret := cont_ret;
  bind := cont_bind;
  bind_continuous_fst := cont_bind_is_continuous_fst;
  bind_continuous_snd := cont_bind_is_continuous_snd;
|}.

Solve Obligations with intros; apply CONT_equal; reflexivity.

End Continuation.
