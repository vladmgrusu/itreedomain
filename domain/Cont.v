From Stdlib Require Import FunctionalExtensionality ProofIrrelevance Lia.
From Domain Require Export CPO Exp Product Kleene Unit.


Lemma lub_fonc_fmap{A:Type}{B: DCPO}
(S: Setof (EXP A B)):
is_directed (P := EXP_Poset A B) 
S ->
 is_lub (P := EXP_Poset A B) S (fun x : A => 
 lub (d := B) (fmap S (fun f => f x))).
 Proof.
 intros Hd.
 apply lub_proj in Hd.
 replace (fun x : A =>
 lub (fmap S (fun f : EXP A B => f x))) with (fun d : A => lub (proj S d)); auto.
 Qed.


Lemma lub_mono{A B : DCPO}(K : Setof (EXP A B)):
is_directed (P := (EXP_Poset A B)) K ->
(forall f, member K f -> is_monotonic f) ->
is_monotonic (lub (d := EXP_DCPO A B) K).
Proof.
intros Hd Ha x y Hle.
rewrite <- (is_lub_lub_eq1 (D := EXP_DCPO A B)_ _ (lub_fonc_fmap _ Hd) Hd).
apply forallex_lelub.
-
apply (monotonic_directed
     (P1 := (EXP_Poset A B)) (P2 := B));
     auto.
intros u v Hleuv.
now apply Hleuv.
-     
apply (monotonic_directed
(P1 := (EXP_Poset A B)) (P2 := B));
auto.
intros u v Hleuv.
now apply Hleuv.
-
 intros b (g & Hmg & Heq); subst.
 exists (g y); split; [| now apply (Ha _ Hmg)].
 now exists g.
Qed.



Lemma proj_fmap{D}{C :Poset}
 (S : Setof (EXP_Poset D C)) (d:D):
    proj S d = fmap S (fun f => f d).
Proof.
reflexivity.
Qed.

Lemma lub_cont{A B : DCPO}(K : Setof (EXP A B)):
is_directed (P := (EXP_Poset A B)) K ->
(forall f, member K f -> is_continuous f) ->
is_continuous (lub (d := EXP_DCPO A B) K).
Proof.
intros Hd Ha.
apply continuous_alt_implies_continuous.
{
 apply lub_mono; auto.
 intros f Hf.
 apply continuous_implies_monotonic.
 now apply Ha.
}
intros S HdS.
assert (Hdf: is_directed (fmap S (lub (d := EXP_DCPO A B) K))).
 {
    apply monotonic_directed; auto.
    apply lub_mono; auto.
    intros f Hf.
    apply continuous_implies_monotonic.
    now apply Ha.
 }
 split; auto.
 specialize (directed_proj K (lub S) Hd) as Hdp.
rewrite proj_fmap in Hdp.
cbn in Hdp.
 rewrite <- (is_lub_lub_eq1 (D := EXP_DCPO A B)_ _ (lub_fonc_fmap _ Hd) Hd) in *.

 replace ((fmap K
 (fun f : EXP A B => f (lub S)))) with
 (fmap K (fun f => (lub (d := B) (fmap S f)))) in *.
{
apply lub_is_minimal; auto.
intros k (w & Hmw & Heq);subst.
apply forallex_lelub; auto.
-
 apply (monotonic_directed
 (P1 := A)(P2 :=B) );auto.
 intros x y Hle.
 specialize (Ha _ Hmw).
 rewrite continuous_iff_mono_commutes in Ha.
 destruct Ha as (Ha & _).
 now apply Ha.
 -
 intros b (a & Hmga & Heq); subst.
 exists ((lub (d := EXP_DCPO A B) K) a).
 split.
 +
  exists a; split; auto.
 +
  assert (Hle : 
  ord (p := EXP_Poset A B) w (lub  (d := EXP_DCPO A B) K)); 
  [ | now apply Hle].
  now apply (lub_is_upper (D := EXP_DCPO A B) K).
}
{
 apply set_equal; intro f ; split; intro Hmf.
 +
 destruct Hmf as (g & Hmg & Heq);subst.
 exists g; split; auto.
 now destruct  (Ha _ Hmg _ HdS) as (_ & Heq).
 +
 destruct Hmf as (g & Hmg & Heq);subst.
 exists g; split; auto.
 now destruct  (Ha _ Hmg _ HdS) as (_ & Heq).
}
Qed.    

Record CONT (A B : DCPO)  : Type := 
{
 fonc :> EXP A B;
 cont : is_continuous fonc
}.

Arguments fonc {_} {_} _.
Arguments cont {_} {_} _.

Lemma CONT_equal{A B : DCPO}(c1 c2 : CONT A B):
 c1.(fonc) = c2.(fonc) -> c1 = c2.
 intros Heq.
 destruct c1; destruct c2.
 cbn in Heq; subst.
 f_equal.
 apply proof_irrelevance.
Qed.


Program Definition CONT_Poset (A B : DCPO) : Poset :=
{|
 carrier := CONT A B;
 default := {|fonc := fun _ => @default B |};
 ord := fun x y =>
  ord (p := EXP_Poset A B) (fonc x) (fonc y)
|}.

Next Obligation.
intros A B.
apply cst_is_continuous.
Qed.

Next Obligation.
intros.
apply refl.
Qed.

Next Obligation.
intros.
cbn in *.
intro a .
eapply trans; eauto.
Qed.

Next Obligation.
intros.
apply CONT_equal.
apply (antisym (p := EXP_Poset A B)); auto.
Qed.

Lemma fonc_is_monotonic{A B : DCPO}:
is_monotonic (P1 := CONT_Poset A B) (P2 := EXP_Poset A B) fonc.
Proof.
intros x y Hle;auto.
Qed.


Lemma fonc_is_rev_monotonic{A B : DCPO}:
is_rev_monotonic (P1 := CONT_Poset A B) (P2 := EXP_Poset A B) fonc.
Proof.
intros x y Hle;auto.
Qed.

Lemma directed_iff{A B : DCPO}(S: Setof (CONT A B)):
is_directed (P := CONT_Poset A B) S <-> 
is_directed (P := EXP_Poset A B) (fmap S fonc).
Proof.
split; intro Hd.
-
 apply (monotonic_directed (P1 := CONT_Poset A B) (P2 := EXP_Poset A B));
 auto; apply fonc_is_monotonic.
-
apply (rev_monotonic_directed (P1 := CONT_Poset A B) (P2 := EXP_Poset A B))
 with (f := fonc); auto; apply fonc_is_rev_monotonic.
Qed.


Lemma lub_proj_cont{A B : DCPO}(S: Setof (CONT A B)):
is_directed (P := CONT_Poset A B) S ->
@is_continuous A B
  (fun d : A =>
   @lub B
     (@proj A B
        (@fmap (CONT A B) (EXP A B) S (@fonc A B))
        d)).
Proof.
intro Hd.
cbn.

replace (fun (i:A) =>
lub (d := B)(proj (D := A) (fmap S fonc) i)) 
with (lub (d := EXP_DCPO A B) (fmap S fonc)).
+
 apply lub_cont;
 [now rewrite directed_iff in Hd | ].
 intros f (g & Hmf & Heq); subst.
 now destruct g.
+
specialize Hd as i.
apply directed_iff in Hd.
apply lub_proj in Hd.
apply directed_iff in i.
now rewrite (is_lub_lub_eq1 (D := EXP_DCPO A B) _ _ Hd i).
Qed.


Lemma aux{A B : DCPO}
(S : Setof (CONT A B)):
is_directed (P := CONT_Poset A B) S ->
exists (Hc:is_continuous (P1:= A) (P2 := B) 
(lub (d:= EXP_DCPO A B )((fmap S fonc)))), 
is_lub (P := CONT_Poset A B) S 
({|fonc := (lub (d:= EXP_DCPO A B ) ((fmap S fonc))); cont := Hc|}).
Proof.
intro Hd.
assert (Hc : @is_continuous A B
(@lub (EXP_DCPO A B)
   (@fmap (CONT A B)
      (EXP A B) S
      (@fonc A B)))); [ | exists Hc].
-
 apply lub_cont.
 +
 apply (monotonic_directed (P1 := CONT_Poset A B) (P2 := EXP_Poset A B));
 auto.
 apply fonc_is_monotonic.
 +
 intros f (g & Hmf & Heq); subst.
 now destruct g.
-
 apply (is_lub_fmap_rev
  (P1 := CONT_Poset A B) (P2 := EXP_Poset A B)) with (f := fonc).
 + 
  split; [apply fonc_is_monotonic | apply fonc_is_rev_monotonic].
 +
  cbn.
  destruct (oracle
  (@is_directed (EXP_Poset A B)
     (@fmap (CONT A B) (EXP A B) S
        (@fonc A B)))).
   *
   replace ((fun d : A =>
   @lub B
     (@proj A B
        (@fmap (CONT A B) (EXP A B) S
           (@fonc A B)) d))) with (lub (d:= EXP_DCPO A B) (fmap S fonc));
           [now apply (lub_is_lub (d:= EXP_DCPO A B)) |].
    specialize i as j.
    apply lub_proj in i.
    symmetry.
    now apply is_lub_lub_eq1.
    *
      contradict n; now rewrite directed_iff in Hd.
Qed.      

  


Program Definition CONT_DCPO (A B : DCPO) : DCPO :=
{|
dcpo_poset := CONT_Poset A B;
lub := fun (S : Setof (CONT A B)) =>
if (oracle (is_directed (P := CONT_Poset A B) S))
then
{| fonc := lub (d := EXP_DCPO A B) (fmap S fonc) |}
else {|fonc := fun _ => default|}
|}.

Next Obligation.
intros.
now apply lub_proj_cont.
Qed.

 
Next Obligation.
intros.
apply cst_is_continuous.
Qed.

Next Obligation.
intros.
cbn.
destruct oracle; [| contradiction].
unfold proj.
specialize H as Hd.
apply aux in H.
destruct H as (Hc & Hl).
replace ({|
   fonc :=
     @lub (EXP_DCPO A B)
       (@fmap (CONT A B) 
          (EXP A B) S 
          (@fonc A B));
   cont := Hc
 |}) with 
 ({|
   fonc :=
     fun d : A =>
     @lub B
       (@proj A B
          (@fmap (CONT A B)
             (EXP A B) S
             (@fonc A B)) d);
   cont :=
     CONT_DCPO_obligation_1 A
       B S i
 |}) in Hl;auto.
 apply CONT_equal; auto.
 Qed.




Program Definition CONT_CPO (A B : CPO) :=
{| dcpo_cpo := CONT_DCPO A B;
   bot := {| fonc := fun _ => bot|}
|}.

Next Obligation.
intros.
apply cst_is_continuous.
Qed.

Next Obligation.
intros.
cbn.
intro d.
apply bot_least.
Qed.

Lemma comp_mono_snd{A:Type}{B C : Poset}
(f : B -> C):
is_monotonic f ->
is_monotonic
(P1 := EXP_Poset A B)
(P2 := EXP_Poset A C)
(fun (g : A -> B) => f ° g).
Proof.
intros Hm h h' Hle x.
apply Hm,Hle.
Qed.


Lemma comp_cont_snd{A:Type}{B C : DCPO}
(f : B -> C):
is_continuous f ->
is_continuous
(P1 := EXP_DCPO A B)
(P2 := EXP_DCPO A C)
(fun (g : A -> B) => f ° g).
Proof.
intro Hc.
rewrite continuous_iff_mono_commutes.
specialize Hc as Hcl.
rewrite continuous_iff_mono_commutes in Hcl.
destruct Hcl as (Hm & Hcl).
split; [now apply comp_mono_snd |].
cbn.
intros S l Hd Hl.
assert (Hd' : is_directed (P := EXP_Poset A C)
(fmap S (fun g : A -> B => f ° g))).
{
   apply (monotonic_directed (P1 := EXP_DCPO A B)
   (P2 := EXP_DCPO A C)); auto.
   now apply comp_mono_snd.
}
unfold comp in *.
split.
{
 intros x (y & Hmy & Heq);subst.
 unfold comp.
 intros x.
 destruct Hl as (Hu & _).
 apply Hm.
 now apply Hu.
}
cbn.
intros z Huz a.
specialize Hl as Hl'.
destruct Hl as (Hu & Hmin).
unfold is_upper in Huz.
cbn in *.
specialize Hd as HdS.
apply lub_fonc_fmap in Hd.
apply is_lub_unique with (x := l) in Hd; 
auto.
subst.
remember  (fmap S (fun f0 : EXP A B => f0 a)) as S'.
assert (HdS' : is_directed S').
{
 subst.
 apply (monotonic_directed (P1 := EXP_DCPO A B)
 (P2 := B)); auto.
 intros x y Hle.
 cbn in *.
 apply Hle.
}
assert (HdS'f : is_directed
(fmap S' f)) by now apply monotonic_directed. 
specialize (Hcl _ (lub S') HdS' (lub_is_lub _ HdS')).
apply is_lub_lub_eq1 with (d :=(f (lub S'))) in HdS'f;auto.
rewrite HdS'f.
clear HdS'f.
rewrite HeqS'.
rewrite <- fmap_comp.
remember (f ° (fun f0 : EXP A B => f0 a)) as g.
unfold comp in Heqg.
apply lub_is_minimal.
-
 apply (monotonic_directed
 (P1 := EXP_DCPO A B)
 (P2 := C)); auto.
 intros x y Hle.
 cbn in *.
 subst.
 apply Hm, Hle.
-
 intros x (w & Hmw & Heq); subst.

specialize ( Huz (f° w) ).
apply Huz.
unfold comp.
now exists w.
Qed.

Lemma if_monotonic
  (X Y : Poset) (f g : X -> Y) (Hf : is_monotonic f) (Hg : is_monotonic g) : 
@is_monotonic _ (EXP_Poset _ _) (fun x (b : bool) => if b then f x else g x).
Proof.
intros u v Hle [ | ] ; [now apply Hf | now apply Hg].
Qed.


Lemma seq_monotonic_snd_gen (X : Type) (Y : DCPO) (f : (X -> Y) -> Y) :
@is_monotonic (EXP_Poset _ _) _ (fun g : X -> Y => f g) ->
is_monotonic (fun y => f (fun _ => y)).
Proof.
intros Hm u v Hle.
apply Hm.
now intros _.
Qed.

Lemma if_continuous
  (X Y : DCPO) (f g : X -> Y) (Hf : is_continuous f) (Hg : is_continuous g) : 
@is_continuous _ (EXP_DCPO _ _) (fun x (b : bool) => if b then f x else g x).
Proof.
apply continuous_alt_implies_continuous; 
[apply if_monotonic;rewrite continuous_iff_mono_commutes in Hf,Hg;
destruct Hf; destruct Hg;auto | ].
split.
{
 apply (monotonic_directed (P1 := X) (P2 := (EXP_DCPO bool Y)));
 auto.
 apply if_monotonic; rewrite continuous_iff_mono_commutes in Hf,Hg;
 destruct Hf; destruct Hg;auto.
}
assert 
 (Hle : 
 forall z, S z ->
 ord (p := EXP_Poset bool Y) (fun b: bool => if b then f z else g z)
 (lub (d := EXP_DCPO bool Y)
(fmap S
   (fun (x : X)
      (b : bool) =>
    if b
    then f x
    else g x)) )).
 {
  intros z Hmz.
  apply (lub_is_upper (D := EXP_DCPO bool Y));
  [apply (monotonic_directed (P1 := X) (P2 := (EXP_DCPO bool Y)));
  auto;
  apply if_monotonic; rewrite continuous_iff_mono_commutes in Hf,Hg;
  destruct Hf; destruct Hg;auto | ].
  now exists z.
 }
intros [ | ].
-
apply trans with (y := lub (fmap S f )).
  +
  destruct (Hf S); auto.
  rewrite H0;apply refl.
  +
  apply lub_is_minimal;
   [apply monotonic_directed; auto; 
   rewrite continuous_iff_mono_commutes in Hf;
   destruct Hf;auto |].
  intros y (z & Hmz & Heq); subst.
  apply (Hle _ Hmz true).
-   
apply trans with (y := lub (fmap S g )).
 +
 destruct (Hg S); auto.
 rewrite H0;apply refl.
+
 apply lub_is_minimal;
 [apply monotonic_directed; auto; 
 rewrite continuous_iff_mono_commutes in Hg;
 destruct Hg;auto |].
 intros y (z & Hmz & Heq); subst.
 apply (Hle _ Hmz false).
Qed.


Lemma seq_continuous_snd_gen (X : Type) (Y : DCPO) (f : (X -> Y) -> Y) :
@is_continuous (EXP_DCPO _ _) _ (fun g : X -> Y => f g) ->
is_continuous (fun y => f (fun _ => y)).
Proof.
intros  Hc.
assert (Hda:
forall (S:Setof Y), 
 is_directed S -> 
  is_directed (fmap S (fun y : Y => f (fun _ : X => y)))).
{
intros S Hd.
apply monotonic_directed;auto;apply seq_monotonic_snd_gen;
rewrite continuous_iff_mono_commutes in Hc; now destruct Hc.
}  
apply continuous_alt_implies_continuous;
[apply seq_monotonic_snd_gen;rewrite continuous_iff_mono_commutes in Hc;
now destruct Hc | ].
split; auto.
specialize (Hda _ Hd1).
assert (Hd2 :  is_directed
(P := EXP_Poset X Y)
(fmap S (fun (y : Y) (_ : X) => y))).
{
 apply 
 (monotonic_directed
  (P1 := Y)
  (P2 := EXP_Poset X Y)); auto.
now intros x y Hlu u.  
}
destruct (Hc  _ Hd2) as (Hd3 & Heql).
rewrite <- fmap_comp in *.
unfold comp in *.
cbn - [lub] in *.
rewrite <- Heql.

apply lub_fonc_fmap in Hd2.
eapply is_lub_unique 
 with (x := 
 lub (d := EXP_DCPO X Y) (fmap S (fun (y : Y) (_ : X) => y)))
 in Hd2;[ | apply (lub_is_lub(d := EXP_DCPO X Y))].
-
 rewrite  Hd2.
 replace (fun _ : X => lub S) with 
 (fun x : X =>
 lub
   (fmap
      (fmap S
         (fun (y : Y)
            (_ : X) => y))
      (fun f0 : EXP X Y
       => f0 x))); [apply refl |].
 extensionality x.      
 rewrite  <- fmap_comp.
 unfold comp.
 cbn - [lub].
 now rewrite fmap_id.
-
  apply (monotonic_directed
  (P1 := Y)(P2 := EXP_Poset X Y)); auto.
  now intros x y Hle u.
Qed.



Lemma is_monotononic_pair_snd{P1 P2 : Poset}
(y:P2):
is_monotonic
(P1 := P1)
(P2 := PROD_Poset  P2 P1)
(fun x  => (y, x)).
Proof.
intros u v Hle.
now split; [apply refl |].
Qed.


Lemma is_continuous_pair_snd{P1 P2 : DCPO}
(y:P2):
is_continuous 
(P1 := P1)
(P2 := PROD_DCPO  P2 P1)
(fun x  => (y, x)).
Proof.
specialize (id_is_continuous (P := PROD_DCPO P2 P1)) as Hc.
apply (is_continuous_snd_arg  _ Hc y).
Qed.


Lemma is_continuous_pair_fst{P1 P2 : DCPO}
(y:P2):
is_continuous 
(P1 := P1)
(P2 := PROD_DCPO  P1 P2)
(fun x  => (x, y)).
Proof.
specialize (id_is_continuous (P := PROD_DCPO P1 P2)) as Hc.
apply (is_continuous_fst_arg  _ Hc y).
Qed.



Lemma curry_mono{A B C:Poset}
(f: A * B -> C):
is_monotonic(P1 := PROD_Poset A B) (P2 := C) f ->
is_monotonic (P1 := A) (P2 := EXP_Poset B C)(curry f).
Proof.
intros Hm u v Hle y.
unfold curry.
apply Hm.
split; auto.
apply refl.
Qed.



Lemma curry_preserves_cont{A B C:DCPO}
(f: A * B -> C):
is_continuous(P1 := PROD_DCPO A B) (P2 := C) f ->
is_continuous (P1 := A) (P2 := EXP_DCPO B C)(curry f).
intros Hc S Hd.
assert (Hd' : is_directed  (P := EXP_Poset B C) (fmap S (curry f))).
{
  apply @monotonic_directed; auto.
  apply curry_mono.
  now apply continuous_implies_monotonic in Hc.
}
split; auto.
unfold curry in *.
cbn.
extensionality y.
unfold proj.
rewrite <- fmap_comp.
unfold comp.
apply is_continuous_fst_arg with (b := y) in Hc.
specialize (Hc _ Hd).
now destruct Hc.
Qed.



Lemma uncurry_preserves_cont{A B C: DCPO} (f : A -> B -> C):
(forall a, is_continuous (f a)) ->
(forall b, is_continuous (fun a => f a b)) ->
is_continuous (P1 := PROD_DCPO A B) (P2 := C)(uncurry f).
Proof.
intros Hc1 Hc2.
now apply argwise_continuous.
Qed.




Definition eval{A B: DCPO}(p:  (CONT A B)* A) :=
fonc (fst p) (snd p).

Lemma eval_is_monotonic_snd{A B: DCPO}:
forall (a:A),
is_monotonic (P1 := CONT_Poset _  _)(fun f : CONT A B => eval (f,a)).
Proof.
intros a f g Hle.
apply Hle.
Qed.

Lemma eval_is_continuous_snd{A B: DCPO}:
forall (a:A),
is_continuous (P1 := CONT_DCPO _  _)(fun f : CONT A B => eval (f,a)).
Proof.
intro b.
intros K Hd.
assert (Hd' : is_directed
(fmap K
   (fun a : CONT_DCPO A B => eval (a, b)))).
{
  apply monotonic_directed;auto;
  apply eval_is_monotonic_snd.
}
split; auto.
unfold eval.
cbn.
destruct oracle; [ cbn | contradiction].
unfold proj.
now rewrite <- fmap_comp.
Qed.

Lemma eval_is_continuous{A B: DCPO}:
is_continuous (P1 := PROD_DCPO (CONT_DCPO A B) A) eval.
Proof.
apply argwise_continuous;[now intros (f & Hc) | ].
intro b.
apply eval_is_continuous_snd.
Qed.


Lemma ffix_is_monotonic (X : CPO) :
@is_monotonic (CONT_DCPO _ _) _ (fun f : CONT X X => ffix (fonc f)).
Proof.
intros u v Hle.
unfold ffix.
apply forallex_lelub.
-
 apply iterate_directed.
 destruct u.
 cbn.
 now apply continuous_implies_monotonic.
-
 apply iterate_directed.
 destruct v.
 cbn.
 now apply continuous_implies_monotonic.
- 
intros x (n & Hmn); subst.
exists  (iterate n bot (fonc v)).
split; [eexists; reflexivity | ].
apply iterate_mono_func; auto.
+ apply continuous_implies_monotonic.
  now destruct u.
+ apply continuous_implies_monotonic.
  now destruct v.
Qed.    




Lemma duplicate_arg_cont_aux{F0 F1 D0 D1: DCPO}
(h0 : F0 -> D0)(h1 : F1 -> D1):
is_continuous h0 -> is_continuous h1 ->
is_continuous (P1 := PROD_DCPO _ _)
(P2 := PROD_DCPO _ _)
 (fun xy: F0*F1 => (h0 (fst xy), h1 (snd xy))).
Proof.
intros Hh0 Hh1.
change (is_continuous (P1 := PROD_DCPO _ _)
(P2 := PROD_DCPO _ _) (fun xy:F0*F1 => ((h0°(@fst F0 F1)) xy, (h1°(@snd F0 F1)) xy))).
apply argwise_continuous; unfold comp; intro x ; cbn.
-
  remember (h0 x) as k.
  change (is_continuous (P2 := PROD_DCPO _ _) ((pair k)°h1)).
  apply comp_is_continuous; auto.
  apply is_continuous_pair_snd.
-
  remember (h1 x) as k.
  change (is_continuous (P2 := PROD_DCPO _ _) ((fun x => (x,k))°h0)).
  apply comp_is_continuous; auto.
  apply is_continuous_pair_fst.
Qed.



Lemma duplicate_arg_cont{D0 D1 E F: DCPO}
(g : D0 * D1 -> E)(h0 : F -> D0)(h1 : F -> D1):
is_continuous (P1 := PROD_DCPO _ _) g ->
is_continuous h0 -> is_continuous h1 -> 
is_continuous (fun x => g (h0 x, h1 x)).
Proof.
intros Hg Hh0 Hh1.
remember   (fun x : F => (h0 x, h1 x)) as f.
replace ((fun x : F => g (h0 x, h1 x)))  with (g ° f)
by (subst; reflexivity).
apply (comp_is_continuous (P2 := PROD_DCPO _ _)); auto.
clear g Hg E.
subst.
remember ((fun xy: F*F => (h0 (fst xy), h1 (snd xy)))) as h.
remember (fun x : F => (h0 x, h1 x)) as f.
replace f with (h°diagonal) by (subst; reflexivity).
apply (comp_is_continuous (P2 := PROD_DCPO _ _)).
-
  subst.
  now apply duplicate_arg_cont_aux.
-  
  apply diagonal_is_continuous.
Qed.  


Lemma eval_is_continuous_snd_dep{A B: DCPO}:
forall (F: CONT A  B ->A),
is_continuous (P1 := CONT_DCPO _  _) F ->
is_continuous (P1 := CONT_DCPO _  _)
(fun f : CONT A B => eval (f, F (fonc f))).
Proof.
intros F HcF.
apply (duplicate_arg_cont
(D0 := CONT_DCPO A B)
(D1 := A)
(E := B)
(F := CONT_DCPO A B) eval id F); auto.
- apply eval_is_continuous.
- apply id_is_continuous.
Qed.


Lemma iterate_is_continuous (X : CPO) :
forall n,
@is_continuous (CONT_DCPO _ _) _
(fun f : CONT_DCPO X X => iterate n bot (fonc f)).
Proof.
induction n as [ | n IH];
[cbn;apply (cst_is_continuous (P1 := CONT_DCPO _ _)) |].
cbn.
change
(fun f : CONT X X => (fonc f) (iterate n bot (fonc f))) with
(fun f : CONT X X => eval (f, (iterate n bot (fonc f)))).
cbn in *.
now apply (eval_is_continuous_snd_dep 
(fonc (Build_CONT (CONT_DCPO _ _) _ _ IH))).
Qed.



Lemma ffix_is_continuous (X : CPO) :
@is_continuous (CONT_DCPO _ _) _
(fun f : CONT X X => ffix (fonc f)).
Proof.
remember 
(fun F => exists n, F = fun (f : CONT X X) => iterate n bot (fonc f)) 
as K.
cbn in *.
assert (Heql : lub (d := (EXP_DCPO (CONT_DCPO X X) X)) K = (fun f : CONT X X =>
ffix (fonc f))).
{
  subst.
  cbn.
  extensionality d.
  unfold proj.
  cbn.
  unfold ffix.
  f_equal.
  apply set_equal; intro x; split; intro Hmx.
  {
    destruct Hmx as (f & ((n & Hn) & Heq)); subst.
    now exists n.
  }
  {
    destruct Hmx as (n & Hn); subst.
    eexists.
    split.
    -
     eexists.
     reflexivity.
    - reflexivity.
  }     
}
 rewrite <- Heql.
 clear Heql.
 apply lub_cont.
 -
  subst.
  split.
  {
    rewrite not_empty_member.
    exists (fun (f: CONT X X) => iterate 0 bot (fonc f)).
    now exists 0.
  }
  {
    cbn in *.
    intros x y (n & Hn) (m & Hm); subst.
    exists (fun (f: CONT X X) => iterate (max n m) bot (fonc f));
    repeat split.
    -
    eexists.
    reflexivity.
    -
    intro d.
    apply iterate_mono; [| lia].
    destruct d; cbn.
    now apply continuous_implies_monotonic.
    -
    intro d.
    apply iterate_mono; [| lia].
    destruct d; cbn.
    now apply continuous_implies_monotonic.

  }
 -
  intros f Hmf; subst.
  destruct Hmf  as (n & Hn); subst.
  apply iterate_is_continuous.
Qed.



Lemma fonc_is_continuous{A B:DCPO}:
is_continuous (P1 := CONT_DCPO A B)(P2 := EXP_DCPO A B) fonc.
Proof.
intros K HdK.
assert (Hd' : is_directed (P := EXP_Poset _ _)(fmap K fonc)).
{
  apply (monotonic_directed
  (P1 := CONT_Poset  _ _)
  (P2 := EXP_Poset _ _));auto.
  apply fonc_is_monotonic.
}
split; auto.
cbn.
destruct oracle ; [ auto | contradiction].
Qed.


Definition swap{X Y Z: Type}(f : X -> Y -> Z):=
  fun y x => f x y.

Lemma swap_preserves_mono{A B C D: DCPO}
(k : A -> CONT B C -> D):
(forall x, is_monotonic (P1 := CONT_Poset _ _)(k x )) ->
@is_monotonic (CONT_DCPO _ _) (EXP_DCPO _ _)(swap k).
Proof.
intros Ha u v Hle x.
unfold swap.
now apply Ha.
Qed.




Lemma swap_preserves_cont{A B C D: DCPO}
(k : A -> CONT B C -> D):
(forall x, is_continuous (P1 := CONT_DCPO _ _)(k x )) ->
@is_continuous (CONT_DCPO _ _) (EXP_DCPO _ _)(swap k).
Proof.
intros Ha K HdK.
assert (Hd' : is_directed (P := EXP_Poset _ _) (fmap K (swap k)) ).
{
   apply (monotonic_directed
   (P1 := CONT_Poset _ _)
   (P2 := EXP_Poset _ _)); auto.
   apply swap_preserves_mono.
   intro x.
   specialize (Ha x).
   now apply continuous_implies_monotonic in Ha.
}
split; auto.
unfold swap.
extensionality x.
cbn -[lub].
destruct (Ha x _ HdK) as (Hdk' & Heq).
rewrite Heq.
cbn.
unfold proj.
now rewrite <- fmap_comp.
Qed.




Lemma fonc_enough_for_mono
{A B C D:DCPO} (f : CONT A B -> CONT C D):
is_monotonic (P1 := CONT_Poset _ _ )(P2 := EXP_Poset _ _) (fonc ° f)
 -> is_monotonic (P1 := CONT_Poset _ _ )(P2 := CONT_Poset _ _) f.
Proof.
intros Hm u v Hle.
unfold comp in Hm.
cbn in *.
intro c.
now apply Hm.
Qed.


Lemma fonc_enough_for_cont
{A B C:DCPO} (f : A-> CONT B C):
is_continuous (P2 := EXP_DCPO _ _) (fonc ° f)
 -> is_continuous (P2 := CONT_DCPO _ _) f.
Proof.
unfold comp.
intros Hc K HdK.
assert (is_directed (P := CONT_Poset _ _) (fmap K f) ).
{
  apply (monotonic_directed
   (P2 := CONT_Poset _ _)); auto.
   apply continuous_implies_monotonic in Hc.
   apply Hc.
}
split; auto.
cbn -[lub].
unfold is_continuous in Hc.
cbn -[lub] in *.
destruct (Hc _ HdK) as (Hd'' & Heq).
apply CONT_equal.
cbn -[lub] in *.
replace (fonc  (f (lub   K))) with
(lub (d := EXP_DCPO _ _) (fmap K (fun x : A => fonc (f x)))).
destruct (@fonc_is_continuous B C _ H) as (Hd''' & Heq').
now rewrite <- fmap_comp in Heq'.
Qed.



Lemma apply_cont_is_mono[X Y:DCPO]: 
is_monotonic (P2 := EXP_Poset _ _)
(fun (x:X) => (fun (k:CONT X Y) => fonc k x)).
Proof.
intros u v Hle x.
destruct x.
cbn.
apply continuous_implies_monotonic in cont0.
now apply cont0.
Qed.

Lemma apply_cont_is_cont[X Y:DCPO]: 
is_continuous (P2 := EXP_DCPO _ _)
(fun (x:X) => (fun (k:CONT X Y) => fonc k x)).
Proof.
intros K HdK.
assert (Hd' :
is_directed (P := EXP_Poset _ _) (fmap K (fun (x : X) (k : CONT X Y) => fonc k x))).
{
 apply (monotonic_directed (P2 := EXP_Poset _ _));auto.
 apply apply_cont_is_mono.
}
split ; auto.
extensionality k.
cbn.
unfold proj.
rewrite <- fmap_comp.
unfold comp.
destruct k as (k & Hk).
cbn.
destruct (Hk _ HdK) as (_ & Heq).
now rewrite Heq.
Qed.


Lemma mono_cont2
{A B C D: Poset}
(f : C -> D)
(h : A -> B -> C):
is_monotonic f ->
is_monotonic (P2 := EXP_Poset _ _) h ->
is_monotonic (P2 := EXP_Poset _ _) (fun (x:A) => (f ° (h x))).
Proof.
intros Hf Hh u v Hle x.
unfold comp.
apply Hf.
now apply Hh.
Qed.

Lemma comp_cont2
{A B C D: DCPO}
(f : C -> D)
(h : A -> B -> C):
is_continuous f ->
is_continuous (P2 := EXP_DCPO _ _) h ->
is_continuous (P2 := EXP_DCPO _ _) (fun (x:A) => (f ° (h x))).
Proof.
intros Hf Hh K HdK.
unfold comp.
assert (Hd' : is_directed (P := EXP_Poset _ _)
(fmap K
   (fun (x : A)
      (x0 : B) =>
    f (h x x0)))).
{
  apply (monotonic_directed (P2 := EXP_Poset _ _)); auto.
  apply mono_cont2.
   - now apply continuous_implies_monotonic in Hf.
   - now apply continuous_implies_monotonic in Hh.
}
split ; auto.
cbn.
extensionality b.
unfold proj.
rewrite <- fmap_comp.
unfold comp.
destruct (Hh _ HdK) as (HdK' & Heqh).
rewrite Heqh.
unfold is_continuous in Hf.    
cbn.
unfold proj.
rewrite <- fmap_comp.
unfold comp.
assert (Hd'' : is_directed (fmap K (fun x : A => h x b))).
{
  apply monotonic_directed; auto.
  intros u v Hle.
  apply continuous_implies_monotonic in Hh.
  unfold is_monotonic in Hh.
  cbn in Hh.
  now apply Hh.
}
destruct (Hf _ Hd'')  as (Hd''' & Heqf).
rewrite Heqf.
now rewrite <- fmap_comp.
Qed.




Lemma comp_mono_fst{A B C:DCPO}
(g: A -> B):
is_monotonic
(P1 := CONT_DCPO B C)
(P2 := EXP_DCPO A C)
(fun (f:CONT B C) => (fonc f) ° g).
Proof.
intros h h' Hle x.
unfold comp.
destruct h as (h & Hch).
destruct h' as (h' & Hch').
cbn in *.
apply Hle.
Qed.

Lemma comp_cont_fst{A B C:DCPO}
(g: A -> B):
is_continuous
(P1 := CONT_DCPO B C)
(P2 := EXP_DCPO A C)
(fun (f:CONT B C) => (fonc f) ° g).
Proof.
apply continuous_alt_implies_continuous; 
[apply comp_mono_fst |].
intros K Hd.
assert (HdK : is_directed (P := EXP_DCPO _ _) (fmap K (fun f  => fonc f ° g))).
{
  apply (monotonic_directed
   (P1 := CONT_DCPO _ _)
   (P2 := EXP_DCPO _ _)); auto;
   apply comp_mono_fst.
}
split; auto.
unfold comp.
intro d.
cbn.
destruct oracle ; [ | contradiction].
cbn.
unfold proj.
repeat rewrite <- fmap_comp.
unfold comp; apply refl.
Qed.




Lemma comp_with_from_unit_is_monotonic
 [X Y : DCPO] (h : X -> Y):
 is_monotonic h ->
  is_monotonic (P1 := CONT_Poset _ _) (fun k => (h ° (fonc k)) (tt:UNIT_CPO)).
Proof.
intros Hc x y Hle.
unfold comp.
apply Hc, (Hle tt).
Qed. 


Lemma comp_with_from_unit_is_continuous
[X Y : DCPO] (h : X -> Y):
is_continuous h ->
 is_continuous (P1 := CONT_DCPO _ _) (fun k => (h ° (fonc k)) (tt:UNIT_CPO)).
 Proof.
 cbn.
 intros Hc K Hd.
 assert (Hd' : is_directed (fmap K (fun k : CONT UNIT_DCPO X => (h ° (fonc k)) (tt:UNIT_CPO)))).
 {
   apply monotonic_directed;auto.
   apply comp_with_from_unit_is_monotonic.
   now apply continuous_implies_monotonic in Hc.
 }
 split; auto.
 unfold comp.
 cbn.
 unfold proj.
 cbn in *.
 destruct oracle; [ | contradiction].
 cbn.
 remember (fmap K (fun k : CONT UNIT_CPO X => (fonc k tt))) as T.
 assert (Hd'' : is_directed T).
 {
    subst.
    apply (monotonic_directed (P1 := CONT_Poset _ _));
    auto.
    intros u v Hle.
    apply (Hle tt).
 }
 destruct  (Hc _ Hd'') as (_ & Heq).
 subst.
 repeat rewrite <- fmap_comp in *.
 now unfold comp in *.
 Qed.



 Lemma apply_cont_to_cst_is_cont{A B : DCPO}
 (a:A): is_continuous (P1 := CONT_DCPO _ _) 
 (fun (f:CONT A B) => fonc f a).
 Proof.
 intros K HdK.
    assert (Hk': is_directed
    (fmap K
       (fun f : CONT A B =>
        fonc f a)) ).
    {
     apply monotonic_directed; auto.
     intros (u & Hu) (v & Hv) Hle.
     cbn in *.
     now apply Hle.
    }
    split ; auto.
    cbn.
    destruct oracle ; [ | contradiction].
    cbn.
    unfold proj.
    now rewrite <- fmap_comp.
 Qed.
 
 Lemma diag_fonc_is_cont
 {A B: DCPO}
 (f: A -> CONT A B):
  is_continuous (P2 := CONT_DCPO _ _) f
 -> is_continuous
   (fun x : A => fonc (f x) x).
 Proof.
 intro Hc.
 change (is_continuous ((uncurry (fonc ° f)) °diagonal)).
 apply (comp_is_continuous (P2 := PROD_DCPO _ _)); 
  [| apply diagonal_is_continuous].
 apply uncurry_preserves_cont.
 -
  intro a; unfold comp ; now destruct (f a).
 -
  intro b.
  unfold comp.
  change (is_continuous (fun x : A => uncurry fonc (f x, b))).
  apply (@duplicate_arg_cont (CONT_DCPO _ _) _ _ _
  (uncurry fonc) f (fun _ => b)); auto; [ | apply cst_is_continuous].
   apply (uncurry_preserves_cont (A := CONT_DCPO _ _)).
   +
    now intros (h & Hh).
   +
    clear f Hc b.
    intro a.
    cbn.
    apply apply_cont_to_cst_is_cont.
  Qed.  
 
  Lemma double_diag_fonc_is_cont{A B: DCPO}:
  is_continuous
  (P1 := CONT_DCPO _ (CONT_DCPO _ _))
  (P2 := EXP_DCPO _ _)
    (fun (f : CONT A(CONT_DCPO A B))
       (a : A) =>
     fonc (fonc f a) a).
 Proof.
 change (is_continuous (P1 := CONT_DCPO _ _)
 (P2 := EXP_DCPO _ _)
 (fun (f : CONT A( CONT_DCPO A B)) => (uncurry fonc) ° (fun s => (fonc f s, id s)))).
 apply  (@comp_cont2 (CONT_DCPO _ (CONT_DCPO _ _)) _
 (PROD_DCPO (CONT_DCPO _ _) _) _ (uncurry fonc)).
 -
  apply argwise_continuous.
 +
  cbn.
  intro h.
  now destruct h.
 +
  intro b.
  cbn.
  apply apply_cont_to_cst_is_cont.
 -
  cbn.
  match goal with
  | |- is_continuous ?ff =>
  change ff with (curry (uncurry ff))
  end.
  apply (curry_preserves_cont 
  (A := CONT_DCPO _ (CONT_DCPO _ _))(C := PROD_DCPO (CONT_DCPO _ _) _)).
  apply (uncurry_preserves_cont
   (A := CONT_DCPO _ (CONT_DCPO _ _))(C := PROD_DCPO (CONT_DCPO _ _) _)).
   +
    intros (f & Hcf).
    cbn.
    apply (@duplicate_arg_cont (CONT_DCPO _ _) _
    (PROD_DCPO _ _) _ id);auto;
    apply id_is_continuous.
   +
    intro a.
    cbn.
    unfold id.
    apply (@duplicate_arg_cont
    (CONT_DCPO _ _) _ (PROD_DCPO _ _) (CONT_DCPO _ _)  id);
    [apply id_is_continuous | | apply cst_is_continuous].
    apply apply_cont_to_cst_is_cont.
 Qed.
 