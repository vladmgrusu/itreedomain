From Stdlib Require Export FunctionalExtensionality Classical.
From Domain Require Export Product Discrete.
From Monad Require Export Monad.

Local Close Scope nat_scope.

Section State.

Variable S : Type.

Variable M : MONAD.

Definition stateT_functor (X : Type) : CPO :=
EXP_CPO S (M (X * S)).

Definition stateT_ret (X : Type) (x : X) : stateT_functor X :=
fun s => ret M (x, s).

Definition stateT_bind
  (X Y : Type) (m : stateT_functor X) (f : X -> stateT_functor Y) :
stateT_functor Y :=
fun s => do xs' <- m s; f (fst xs') (snd xs').

Definition swap (X Y : Type) (xy : X * Y) : Y * X := (snd xy, fst xy).


Lemma swap_is_continuous(X Y:DCPO):
is_continuous (P1 := PROD_DCPO _ _) (P2 := PROD_DCPO _ _) (@swap X Y).
unfold swap.
apply argwise_continuous.
-
  cbn.
  intro x.
  apply is_continuous_pair_fst.
-
  intro y.
  cbn.
  apply is_continuous_pair_snd.
Qed.


Definition prod_fun
  (X1 X2 Y1 Y2 : Type) (f : X1 -> Y1) (g : X2 -> Y2) : X1*X2 -> Y1*Y2 :=
fun x => (f (fst x), g (snd x)).

Lemma prod_fun_uncurry_is_continuous
(X Y: Type)
(m: S -> M (X * S))
(s: S):
@is_continuous
  (PROD_DCPO (EXP_DCPO _ (EXP_DCPO _ _)) (discrete_DCPO _ s))
  (PROD_DCPO (EXP_DCPO _ _)  _)
  (prod_fun  (@uncurry X S (M (Y * S))) m).
Proof.    
apply argwise_continuous; cbn.
{
  intro f.
  unfold prod_fun.
  cbn.
  intros T Hd.
  split. 
  { 
    apply monotonic_directed;auto.
    intros v w Hle.
    split; [apply refl |].
    cbn.
    inversion Hle.
    apply refl.
  }
  {
     cbn.
     destruct oracle;
     [| contradiction].
     unfold proj.
     repeat rewrite <- fmap_comp.
     unfold comp.
     cbn.
     remember (discrete_lub s T i) as dl.
     destruct dl as (x & Hl).
     cbn.
     clear Heqdl.
     unfold uncurry.
     f_equal.
     -
       extensionality xs.
       destruct xs as (x',s').
       repeat rewrite <- fmap_comp.
       unfold comp.
       rewrite fmap_cst; [| now destruct Hd].
       now rewrite lub_single.
     -
       apply discrete_directed in Hd.
       destruct Hd as (y & Hy); subst.
       rewrite fmap_single.
       rewrite lub_single.
       apply is_lub_unique with (x := y) in Hl;
       [now subst | apply @is_lub_single].
  }
}
{
  intro s'.
  unfold prod_fun.
  cbn.
  intros T Hd.
  split.
  {
    apply monotonic_directed;auto.
    intros v w Hle.
    split; [| apply refl].
    cbn.
    intros (x' & s'').
    unfold uncurry.
    cbn in Hle.
    apply Hle.
  }
  cbn in T.
  cbn.
  unfold proj.
  repeat rewrite <- fmap_comp.
  unfold comp.
  cbn.
  f_equal.
  -
   unfold uncurry.
   extensionality xs.
   destruct xs as (x',s'').
   now repeat rewrite <- fmap_comp.
 -
  rewrite fmap_cst; 
  [ | now destruct Hd].
  now rewrite lub_single.
}
Qed.

Lemma state_bind_as_comp
  (X Y : Type) (m : stateT_functor X) :
@stateT_bind X Y m =
curry (uncurry (bind M (Y * S)) ° @swap _ _ ° prod_fun uncurry m).
Proof.
extensionality f.
extensionality s.
compute.
f_equal.
extensionality xs'.
destruct xs' as [x s'].
reflexivity.
Qed.


Lemma stateT_bind_monotonic_fst (X Y : Type) (f : X -> S -> M (Y * S)) :
is_monotonic (fun m => @stateT_bind X Y m f).
Proof.
cbn.
intros h h' Hle x.
unfold stateT_bind.
destruct M as (fct,fret,fbind,fc1,fc2,fb,fr1,fr2, fbb).
specialize fc1 as Hm.
specialize (Hm (X*S) (Y*S) (fun xs' : X * S =>
f (fst xs') (snd xs'))).
cbn.
cbn in *.
apply continuous_implies_monotonic in Hm.
apply Hm,Hle.
Qed.

Lemma stateT_bind_continuous_fst (X Y : Type) (f : X -> S -> M (Y * S)) :
is_continuous (fun m => @stateT_bind X Y m f).
Proof.
specialize (@bind_continuous_fst M) as Hc.
intros T Hd.

split.
{
  apply monotonic_directed;auto.
  apply stateT_bind_monotonic_fst.
}
cbn in *.
cbn.

unfold proj.
extensionality s.
rewrite <- fmap_comp.
unfold comp.
cbn.
specialize (Hc (X*S) (Y*S) (fun xs' : X * S =>
f (fst xs') (snd xs'))).
cbn in *.
remember (fmap T (fun f => f s)) as T'.
assert (Hd' : is_directed T').
{
subst.
apply (monotonic_directed
(P1 := EXP_Poset _ _)); auto.
intros u v Hle; apply Hle.
}
specialize (Hc _ Hd').
destruct Hc as (_ & Heq).
subst.
rewrite <- fmap_comp in *.
unfold comp in *.
unfold stateT_bind at 2.
now rewrite <- Heq.
Qed.



Lemma stateT_bind_continuous_snd_default (X Y : Type) (m : S -> M (X * S))(s:S) :
@is_continuous (EXP_DCPO _ _) _ (@stateT_bind X Y m).
Proof.
rewrite state_bind_as_comp.
remember ((uncurry (bind M (Y * S)) ° swap (Y:=M (X * S))) ° prod_fun uncurry m) as 
 h.
 apply (curry_preserves_cont
 (A := (EXP_DCPO X (EXP_DCPO S (M(Y*S)))))
 (B := (@discrete_DCPO _ s))).
subst. 
remember (prod_fun uncurry m) as g.
remember ((uncurry (bind M (Y * S)) ° swap (Y:=M (X * S)))) as f.
apply (comp_is_continuous
   (P1 := PROD_DCPO (EXP_DCPO X (EXP_DCPO S (M(Y*S)))) (@discrete_DCPO _ s))
   (P2 := PROD_DCPO (EXP_DCPO (X*S) (M(Y*S)) ) (M (X*S)))
   (P3 := M(Y*S))).
- 
   subst.
   remember (uncurry (@bind M (X * S) (Y * S))) as f.
   remember (@swap (X * S -> M (Y * S)) (M (X * S)))  as g.
   apply (comp_is_continuous 
   (P1 :=  PROD_DCPO (EXP_DCPO (X*S) (M(Y*S)) ) (M (X*S)))
   (P2 := PROD_DCPO (M (X*S)) (EXP_DCPO (X*S) (M(Y*S)) ) )
   (P3 := M(Y*S))).
   +
    subst.
    remember ((bind M (Y * S))) as h.
    apply (uncurry_preserves_cont
    (A := M (X*S))
    (B := EXP_DCPO(X*S) (M(Y*S)))
    (C := M (Y*S))).
    *
     intro mxs.
     subst.
     apply bind_continuous_snd.
    *
     intro k.
     subst.
     apply bind_continuous_fst.
   +
    subst.
    apply swap_is_continuous.
 -
  subst.
  apply prod_fun_uncurry_is_continuous.
Qed.      


Lemma empty_continuous_2 (X : DCPO) (Y : Type) (Z : DCPO) (f : X -> Y -> Z) :
~inhabited Y -> @is_continuous X (EXP_DCPO Y Z) f.
Proof.
intro Hempty.
replace f with (fun (_ : X) (_ : Y) => @default Z).
- apply cst_is_continuous.
- extensionality x.
  extensionality y.
    contradict Hempty.
  constructor.
  exact y.
Qed.


Lemma stateT_bind_continuous_snd (X Y : Type) (m : S -> M (X * S)) :
@is_continuous (EXP_DCPO _ _) _ (@stateT_bind X Y m).
Proof.
assert (H := classic (inhabited S)).
destruct H as [[dS] | Hempty];
 [apply (stateT_bind_continuous_snd_default _ dS) | ].
now apply empty_continuous_2.
Qed.


Program Definition stateT_monad : MONAD := {|
  functor := stateT_functor;
  ret := stateT_ret;
  bind := stateT_bind;
  bind_continuous_fst := stateT_bind_continuous_fst;
  bind_continuous_snd := stateT_bind_continuous_snd;
|}.

Next Obligation.
compute.
intros X Y f.
extensionality s.
apply bind_strict.
Qed.

Next Obligation.
compute.
intros X m.
extensionality s.
etransitivity.
{
  apply f_equal.
  extensionality xs'.
  destruct xs'.
  reflexivity.
}
apply ret_right.
Qed.

Next Obligation.
compute.
intros X Y x f.
extensionality s.
apply ret_left.
Qed.

Next Obligation.
compute.
intros X Y Z m f g.
extensionality s.
apply bind_assoc.
Qed.

Definition stateT_lift (X : Type) (m : M X) : stateT_monad X :=
fun s => do x <- m; ret M (x, s).

Lemma stateT_lift_is_monotonic (X : Type) : 
 is_monotonic (stateT_lift X).
Proof.
intros u v Hle s.
specialize (@bind_continuous_fst M) as Hc.
unfold stateT_lift.
specialize (Hc _ _ (fun (x:X) => ret M (x,s)) ).
apply continuous_implies_monotonic in Hc.
now apply Hc.
Qed.



Lemma stateT_lift_is_continuous (X : Type) : is_continuous (stateT_lift X).
Proof.
apply continuous_alt_implies_continuous; 
[apply stateT_lift_is_monotonic |].
intros T Hd.
split.
{
  apply monotonic_directed; auto.
  apply stateT_lift_is_monotonic.
}
specialize (@bind_continuous_fst M) as Hc.
unfold stateT_lift.
intro s.
specialize Hc as Hc'.
specialize (Hc' _ _ (fun (x:X) => ret M (x,s)) ).
specialize (Hc' _ Hd).
destruct Hc' as (_ & Hc').
rewrite Hc'.
clear Hc'.
apply lub_is_minimal.
{
  apply monotonic_directed; auto.
  intros u v Hle; auto.
  specialize (Hc _ _ (fun (x:X) => ret M (x,s)) ).
  apply continuous_implies_monotonic in Hc.
  now apply Hc.
}
intros u (v & Hv & Heq);subst.
(*Check (( (fun (m : M X) (s0 : S) => do x <- m; ret M (x, s0)))).*)
assert (Ho :ord (p := EXP_Poset _ _ )
(fun s => do x <- v; ret M (x, s)) 
(lub (d :=  (stateT_monad X))
(fmap T
   (fun (m : M X)
      (s0 : S) =>
    do x <- m;
    ret M (x, s0)))
)).
{
 apply (lub_is_upper (D := EXP_DCPO _ _)).
 -
  apply (monotonic_directed (P2 := EXP_DCPO _ _)); auto.
  intros y z Hle s'.
  specialize (Hc _ _ (fun (x:X) => ret M (x,s')) ).
  apply continuous_implies_monotonic in Hc.
  now apply Hc.
 -
  now exists v. 
}
apply Ho.
Qed.

Program Definition stateT_lift_mmor : MONAD_MORPHISM M stateT_monad := {|
  mmor := stateT_lift;
  mmor_continuous := stateT_lift_is_continuous
|}.

Next Obligation.
intro X.
compute.
extensionality s.
apply bind_strict.
Qed.

Next Obligation.
intros X x.
compute.
extensionality s.
apply ret_left.
Qed.

Next Obligation.
intros X Y m f.
compute.
extensionality s.
rewrite bind_assoc, bind_assoc.
apply f_equal.
extensionality x.
rewrite ret_left.
reflexivity.
Qed.

Definition get : stateT_monad S :=
fun s => ret M (s, s).

Definition put (s : S) : stateT_monad unit :=
fun _ => ret M (tt, s).

Lemma put_put (s s' : S) : put s;; put s' = put s'.
Proof.
compute.
rewrite ret_left.
reflexivity.
Qed.

Lemma put_get (s : S) : put s;; get = put s;; ret stateT_monad s.
Proof.
compute.
rewrite ret_left, ret_left.
reflexivity.
Qed.

Lemma get_put : do s <- get; put s = ret stateT_monad tt.
Proof.
compute.
extensionality s.
rewrite ret_left.
reflexivity.
Qed.

Lemma get_get (X : Type) (f : S -> S -> stateT_monad X) :
do x <- get; do y <- get; f x y = do x <- get; f x x.
Proof.
compute.
extensionality s.
rewrite ret_left, ret_left, ret_left.
reflexivity.
Qed.

End State.

Arguments stateT_lift [_ _ _] _.
Arguments get {_ _}.
Arguments put [_] {_} _.
