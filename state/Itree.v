From StateT Require Export StateT.
From Itree Require Export Denote.

Local Close Scope nat_scope.

Section State.

Variable S : Type.

Inductive stateT_effect : Type -> Type :=
| Get : stateT_effect S
| Put : S -> stateT_effect unit.



Definition fget : itree_monad stateT_effect S :=
trigger Get.

Definition fput (s : S) : itree_monad stateT_effect unit :=
trigger (Put s).

Variable M : MONAD.

Definition denote_stateT_effect
  (X Y : Type) (fy : stateT_effect Y) (k : Y -> stateT_functor S M X) :
stateT_monad S M X :=
fun s =>
  match fy in stateT_effect Y
   return (Y -> stateT_functor S M X) -> M (X * S) with
  | Get    => fun k => k s s
  | Put s' => fun k => k tt s'
  end k.

Lemma denote_stateT_effect_bind
  (X Y Z : Type) (fx : stateT_effect X)
  (f : X -> stateT_monad S M Y) (g : Y -> stateT_monad S M Z) :
denote_stateT_effect fx (fun x => do y <- f x; g y) =
do y <- denote_stateT_effect fx f; g y.
Proof.
destruct fx; reflexivity.
Qed.

Lemma denote_stateT_effect_is_continuous_1_mono{X: Type}:
is_monotonic
  (P1 := EXP_Poset S(EXP_Poset S  (M (X * S))))
  (P2 := EXP_Poset S (M (X * S)))
  (fun
     (k : S -> EXP S (M (X * S))) (s:S)
   => k s s).
Proof.
intros x y Hle s.
apply Hle.
Qed.

Lemma denote_stateT_effect_is_continuous_1 {X: Type}:
is_continuous
 (P1 := EXP_DCPO S
    (EXP_DCPO S
       (M (X * S))))
 (P2 := EXP_DCPO S (M (X * S)))
 (fun
    (k : S -> EXP S (M (X * S))) (s:S)
  => k s s).
Proof.
rewrite continuous_iff_mono_commutes.
split; [apply denote_stateT_effect_is_continuous_1_mono |].
cbn.
intros T l Hd Hl.
specialize Hd as Hd'.
apply 
(lub_fonc_fmap 
(A := S)
(B := (EXP_DCPO S (M (X * S)))))
in Hd.
apply is_lub_unique with (x := l) in Hd; auto.
subst l.
cbn - [lub].
remember (fun s' : S =>
lub (d := (EXP_DCPO S (M (X * S))))
 (fmap T
    (fun
       f : EXP S
             (EXP S
                (M (X * S)))
     => f s')) s') as l'.
assert (Ha : forall s', l' s' = 
(fun _ : S =>
@lub (EXP_DCPO S (M (X * S)))
 (@fmap (EXP S (EXP S (M (X * S))))
    (EXP S (M(X * S))) T
    (fun f : EXP S (EXP S (M (X * S))) => f s')) s') s'
) by now subst.
cbn -[lub] in Ha.
assert (Had : forall (s':S), 
is_directed 
(P := (EXP_Poset S (M (X * S))))(fmap T
(fun
  f : EXP S (EXP S (M (X * S)))
=> f s'))).
{
 intro s.
 apply (@monotonic_directed
 (EXP_Poset S (EXP_Poset S (M (X * S))))
 );auto.
 intros x y Hle.
 now apply Hle.
}
assert (Hal: forall s',@is_lub
(EXP_Poset S (M (X * S)))
(@fmap (EXP S (EXP S (M (X * S))))
   (EXP S (M (X * S))) T
   (fun
      f : EXP S (EXP S (M (X * S)))
    => f s'))
(fun x : S =>
 @lub (M (X * S))
   (@fmap (EXP S (M (X * S)))
      (M (X * S))
      (@fmap
         (EXP S (EXP S (M (X * S))))
         (EXP S (M (X * S))) T
         (fun
            f : EXP S
                  (EXP S
                     (M (X * S)))
          => f s'))
      (fun f : EXP S (M (X * S)) =>
       f x)))).
{
intro s'.
specialize (Had s').
apply 
(lub_fonc_fmap 
(A := S)
(B :=  (M (X * S))))
in Had;auto.
}
cbn - [lub] in Hal.
assert (Hal'' : forall s' : S,
@is_lub
 (EXP_Poset S (M (X * S)))
 (@fmap (EXP S (EXP S (M (X * S))))
    (EXP S (M (X * S))) T
    (fun
       f : EXP S (EXP S (M (X * S)))
     => f s'))
 (fun x : S =>
  @lub (M (X * S))
       (@fmap
          (EXP S (EXP S (M (X * S))))
          (M (X * S)) T
          ((fun f : EXP S (M (X * S)) =>
          f x)°
          (fun
             f : EXP S
                   (EXP S
                      (M (X * S)))
           => f s'))))).
{
intros s'.
specialize (Hal s').  
replace ((fun x : S =>
@lub (M (X * S))
 (@fmap (EXP S (EXP S (M (X * S))))
    (M (X * S)) T
    ((fun f : EXP S (M (X * S)) => f x)
     ° (fun f : EXP S (EXP S (M (X * S)))
        => f s'))))) with
        (fun x : S =>
        @lub (M (X * S))
          (@fmap (EXP S (M (X * S)))
             (M (X * S))
             (@fmap
                (EXP S (EXP S (M (X * S))))
                (EXP S (M (X * S))) T
                (fun
                   f : EXP S
                         (EXP S (M (X * S)))
                 => f s'))
             (fun f : EXP S (M (X * S)) => f x)));
auto.
extensionality s.
now rewrite fmap_comp.
}
unfold comp in Hal''.
cbn - [lub] in Hal''.
clear Hal.
cbn  - [lub] in  Heql'.
assert (Hal' : forall s', @lub
(EXP_DCPO S (M (X * S)))
(@fmap
  (EXP S (EXP S (M (X * S))))
  (EXP S (M (X * S))) T
  (fun
     f : EXP S
           (EXP S (M (X * S)))
   => f s'))=
(fun x => @lub (M (X * S))
 (@fmap
    (EXP S (EXP S (M (X * S))))
    (M (X * S)) T
    (fun
       x0 : EXP S
              (EXP S
                 (M (X * S)))
     => x0 s' x)))).
{
 intro s.
 specialize (Hal'' s).
 symmetry.
 apply is_lub_lub_eq1; auto.
}      
assert (Hel' : l' =
     (fun s  => @lub (M (X * S))
       (@fmap
          (EXP S (EXP S (M (X * S))))
          (M (X * S)) T
          (fun
             k : S ->
                    (EXP S
                       (M (X * S)))
           => k s s)))).
{
extensionality s'.
rewrite  Ha.
specialize (Hal' s').
now rewrite Hal'.
}
rewrite Hel'.
assert (Hd1 : @is_directed
(EXP_DCPO S
  (M (X * S))) 
  (fmap T
  (fun (k : S -> EXP S (M (X * S))) (s : S) =>
   k s s))).
{
  apply (@monotonic_directed 
  (EXP_Poset S(EXP_Poset S (M (X * S)))));
  auto;apply @denote_stateT_effect_is_continuous_1_mono.
}
assert (Hd2 : forall s,
is_directed 
(P := (M (X * S)))
 (fmap T
    (fun
       k : S ->
           EXP S
             (M (X * S))
     => k s s))).
{
intro s.
apply (@monotonic_directed 
(EXP_Poset S(EXP_Poset S (M(X * S)))));auto.
intros u v Hle.
apply Hle.
}      
assert (Heql : 
@lub (EXP_DCPO S (M (X * S)))
(@fmap (EXP S (EXP S (M (X * S))))
  (EXP S (M (X * S))) T
  (fun (k : S -> EXP S (M (X * S))) (s : S)
   => k s s)) =
(fun s : S =>
@lub (M (X * S))
  (@fmap (EXP S (EXP S (M (X * S))))
     (M (X * S)) T
     (fun k : S -> EXP S (M (X * S)) =>
      k s s)))).
{
apply antisym.
-
apply lub_is_minimal;auto.
intros x (y & Hmy & Heq);subst.
intro s.
apply lub_is_upper;auto. 
 now exists y.
-
intro s.
apply lub_is_minimal; auto.
intros x (y & Hmy & Heq);subst.
assert (Ho : ord (p := EXP_Poset S (M (X*S)))
(fun s => y s s) 
(@lub (EXP_DCPO S (M (X * S)))
  (@fmap
     (EXP S
        (EXP S (M (X * S))))
     (EXP S (M (X * S))) T
     (fun
        (k : S ->
             EXP S
               (M (X * S)))
        (s0 : S) => k s0 s0)))).
{
 apply (@lub_is_upper (EXP_DCPO S
 (M (X * S))));auto.
 now exists y.
}
apply Ho.
}
rewrite <- Heql.
apply (@lub_is_lub  (EXP_DCPO S (M (X * S)))).
apply (@monotonic_directed
(EXP_DCPO S (EXP_DCPO S (M (X * S)))));
auto.
apply denote_stateT_effect_is_continuous_1_mono.
Qed.

Lemma denote_stateT_effect_is_continuous_2_mono{X: Type}
(s:S):
is_monotonic
 (P1 := EXP_Poset unit
    (EXP_Poset S
       (M (X * S))))
 (P2 := EXP_Poset S (M (X * S)))
 (fun
    (k : unit -> EXP S (M (X * S))) (_:S)
  => k tt s).
Proof.
intros x y Hle s'.
apply Hle.
Qed.

Lemma denote_stateT_effect_is_continuous_2{X: Type}
(s:S):
is_continuous
 (P1 := EXP_DCPO unit
    (EXP_DCPO S
       (M (X * S))))
 (P2 := EXP_DCPO S (M (X * S)))
 (fun
    (k : unit -> EXP S (M (X * S))) (_:S)
  => k tt s).
Proof.
remember ((fun (k : unit -> EXP S (M (X * S))) (_ : S)
=> k tt s)) as h.
rewrite continuous_iff_mono_commutes.
split; [subst; apply denote_stateT_effect_is_continuous_2_mono | ].
cbn.
intros T l Hd Hl.
specialize Hd as Hd'.
apply (@lub_fonc_fmap unit (EXP_DCPO S (M (X*S))))
  in Hd.
apply is_lub_unique with (x := l) in Hd; auto; subst l h.
cbn - [lub]. 
remember ((fmap T (fun
  f : EXP unit
        (EXP S
           (M (X * S)))
=> f tt))) as K.
assert (HdK : is_directed
(P := (EXP_Poset S (M (X * S))))K).
{
subst.
apply (@monotonic_directed
(EXP_Poset unit (EXP_Poset S (M (X * S))))
    (EXP_Poset S (M (X * S)))
);auto.
intros x y Hle.
now apply Hle. 
}
assert (Hd2 : @is_directed
(M (X * S))
(fmap T
   (fun
      x : EXP unit
            (EXP S (M (X * S)))
    => x tt s))).
{
 apply (@monotonic_directed
 ( EXP_Poset unit (EXP_Poset S (M (X * S))))
 (M (X * S))); auto.
 intros x y Hle.
 now apply Hle.
}     
assert (Hd3 : 
is_directed (P := EXP_Poset S (M (X * S)))
 (fmap T
    (fun
       (k : unit ->
            EXP S (M (X * S)))
       (_ : S) => k tt s))
).
{
 apply (@monotonic_directed
 ( EXP_Poset unit (EXP_Poset S (M (X * S))))
 (EXP_Poset S (M (X * S)))); auto.
 intros x y Hle _.
 apply Hle.
}
specialize HdK as HdK'.
apply (@lub_fonc_fmap S 
(M (X * S))) in HdK.
apply is_lub_unique with
 (x := lub (d := EXP_DCPO S (M (X * S))) K) in HdK; auto.
 (*[| apply (lub_is_lub  (d := EXP_DCPO S (M (X * S))))];auto.*)
subst.
cbn  - [lub].
rewrite HdK.
rewrite <- fmap_comp.
unfold comp.
cbn - [lub]. 
clear HdK Hl.
assert (Heql : 
lub (d:= (EXP_DCPO S (M (X * S))))
 (fmap T
    (fun  (k : unit ->
            EXP S (M (X * S)))
       (_ : S) => k tt s)) = 
  (fun _ : S =>
       lub (d:= M (X * S))
         (fmap T
            (fun x : EXP unit (EXP S (M (X * S)))
             => x tt s)))).
{
cbn -[lub].
apply (@antisym (EXP_Poset S (M (X * S)))).
-
 apply (@lub_is_minimal (EXP_DCPO S(M (X * S))));
 auto.
 intros y (z & Hmz & Heq); subst.
 intro s'.
 apply (@lub_is_upper ((M (X * S))));auto.
 now exists z.
-
intro s'.
apply (@lub_is_minimal ((M (X * S)))); auto.
intros y (z & Hmz & Heq); subst.
assert (Hle' :
@ord (EXP_Poset S (M (prod X S)))
(fun (s':S) => (z tt s))
(lub
(d :=  (EXP_DCPO S (M (X * S))))
(fmap T (fun (k : unit -> EXP S (M (X * S)))
     (_ : S) => k tt s)))).
{
 apply (@lub_is_upper (EXP_DCPO S (M (X * S))));
 auto.
 now exists z.
}      
apply (Hle' s').
}
rewrite <- Heql.
now apply (@lub_is_lub (EXP_DCPO S
(M (X * S)))).
Qed.

Lemma denote_stateT_effect_is_continuous (X Y : Type) (fy : stateT_effect Y) :
@is_continuous (EXP_DCPO _ _) _ (@denote_stateT_effect X _ fy).
Proof.
unfold denote_stateT_effect.
destruct fy; cbn.
-
apply denote_stateT_effect_is_continuous_1.
-
apply denote_stateT_effect_is_continuous_2.
Qed.
 

Definition denote_stateT [X : Type] (m : itree stateT_effect X) :
stateT_monad S M X :=
denote_monad
  stateT_effect (stateT_monad S M) denote_stateT_effect
  denote_stateT_effect_is_continuous X m.

Definition denote_stateT_mmor :
MONAD_MORPHISM (itree_monad stateT_effect) (stateT_monad S M) :=
denote_monad_mmor _ _ _
  (fun X Y Z => @denote_stateT_effect_bind Z X Y)
  denote_stateT_effect_is_continuous.

Lemma denote_stateT_fret (X : Type) (x : X) :
denote_stateT (fret x) = ret (stateT_monad S M) x.
Proof.
apply denote_monad_fret.
Qed.

Lemma denote_stateT_impure
  (X Y : Type) (fx : stateT_effect X) (k : X -> itree stateT_effect Y) :
denote_stateT (impure fx k) =
denote_stateT_effect fx (fun x => denote_stateT (k x)).
Proof.
apply denote_monad_impure.
Qed.

Lemma denote_stateT_fbind
  (X Y : Type) (m : itree stateT_effect X) (f : X -> itree stateT_effect Y) :
denote_stateT (fbind m f) = do x <- denote_stateT m; denote_stateT (f x).
Proof.
apply denote_monad_fbind; intros; apply denote_stateT_effect_bind.
Qed.

Lemma denote_stateT_while
  (cond : itree_monad stateT_effect bool) (body : itree stateT_effect unit) :
denote_stateT (While cond {{ body }}) =
While denote_stateT cond {{ denote_stateT body }}.
Proof.
apply denote_monad_while; intros; apply denote_stateT_effect_bind.
Qed.

Lemma denote_fget :
denote_stateT fget = get.
Proof.
unfold fget, trigger.
rewrite denote_stateT_impure.
etransitivity.
{
  apply f_equal.
  extensionality s.
  apply denote_stateT_fret.
}
reflexivity.
Qed.

Lemma denote_fput (s : S) :
denote_stateT (fput s) = put s.
Proof.
unfold fput, trigger.
rewrite denote_stateT_impure.
etransitivity.
{
  apply f_equal.
  extensionality t.
  apply denote_stateT_fret.
}
reflexivity.
Qed.

End State.

Arguments fget {_}.
