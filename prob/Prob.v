From Stdlib Require Export FunctionalExtensionality Bool List Lra.
From Domain Require Export Bounded.
From Prob Require Export Continuation.

Export ListNotations.

Local Open Scope R_scope.

Program Definition pr_0 : Bounded 0 1 := {|
  bounded_val := 0
|}.

Next Obligation.
split; [apply Rle_refl | exact Rle_0_1].
Qed.

Program Definition pr_1 : Bounded 0 1 := {|
  bounded_val := 1
|}.

Next Obligation.
split; [exact Rle_0_1 | apply Rle_refl].
Qed.

Program Definition pr_opp (p : Bounded 0 1) : Bounded 0 1 := {|
  bounded_val := 1 - p
|}.

Next Obligation.
intros [p Hp].
cbn.
lra.
Qed.

Lemma pr_opp_half (Hbounded : 0 <= / INR 2 <= 1) :
pr_opp {| bounded_val := / INR 2; bounded_prop := Hbounded |} =
{| bounded_val := / INR 2; bounded_prop := Hbounded |}.
Proof.
apply bounded_equal.
cbn.
lra.
Qed.

Program Definition pr_plus (p q r : Bounded 0 1) : Bounded 0 1 := {|
  bounded_val := p * q + (1 - p) * r
|}.

Next Obligation.
intros [p Hp] [q Hq] [r Hr].
cbn.
nra.
Qed.

Program Definition pr_mult (p q : Bounded 0 1) : Bounded 0 1 := {|
  bounded_val := p * q
|}.

Next Obligation.
intros [p Hp] [q Hq].
cbn.
nra.
Qed.

Lemma bounded_val_pr_mult (p q :  Bounded 0 1) :
bounded_val (pr_mult p q) = bounded_val p * bounded_val q.
Proof.
reflexivity.
Defined.

Program Definition pr_div (p q : Bounded 0 1) (Hle : p <= q) : Bounded 0 1 := {|
  bounded_val := p / q
|}.

Next Obligation.
intros [p Hp] [q Hq] Hle.
cbn in *.
destruct (Req_dec_T q 0) as [Heq | Hneq].
- rewrite Heq.
  rewrite Rdiv_0_r.
  lra.
- unfold Rdiv.
  split.
  + apply (Rmult_le_reg_r q); [lra | ].
    rewrite Rmult_assoc, Rinv_l by exact Hneq.
    lra.
  + apply (Rmult_le_reg_r q); [lra | ].
    rewrite Rmult_assoc, Rinv_l by exact Hneq.
    lra.
Qed.

Program Definition pr_or (p q : Bounded 0 1) : Bounded 0 1 := {|
  bounded_val := p + q - p * q
|}.

Next Obligation.
intros [p Hp] [q Hq].
cbn.
nra.
Qed.

Definition prob_monad : MONAD := {|
  functor := cont_functor (Bounded_CPO Rle_0_1);
  ret := @cont_ret (Bounded_CPO Rle_0_1);
  bind := @cont_bind (Bounded_CPO Rle_0_1);
  bind_continuous_fst := @cont_bind_is_continuous_fst (Bounded_CPO Rle_0_1);
  bind_continuous_snd := @cont_bind_is_continuous_snd (Bounded_CPO Rle_0_1);
  bind_strict := bind_strict (cont_monad (Bounded_CPO Rle_0_1));
  ret_right := ret_right (cont_monad (Bounded_CPO Rle_0_1));
  ret_left := ret_left (cont_monad (Bounded_CPO Rle_0_1));
  bind_assoc := bind_assoc (cont_monad (Bounded_CPO Rle_0_1))
|}.

Lemma choice_is_monotonic (p : Bounded 0 1) (X : Type) (m1 m2 : prob_monad X) :
@is_monotonic _ (Bounded_Poset Rle_0_1)
  (fun f : EXP_Poset X (Bounded_Poset Rle_0_1) =>
    pr_plus p (fonc m1 f) (fonc m2 f)).
Proof.
intros u v Hle.
destruct p as [p [Hp0 Hp1]].
destruct m1; destruct m2.
cbn in *.
apply continuous_implies_monotonic in cont,cont0.
specialize (cont _ _ Hle).
specialize (cont0 _ _ Hle).
cbn in *.
clear - cont cont0 Hp0 Hp1.
remember (fonc u) as fu.
remember (fonc v) as fv.
remember (fonc0 u) as gu.
remember (fonc0 v) as gv.
clear - cont cont0 Hp0 Hp1.
destruct fu,fv,gu,gv;cbn in *.
destruct bounded_prop,bounded_prop0,bounded_prop1,bounded_prop2.
nra.
Qed.

Lemma pair_preserves_continuity {X Y:DCPO}
(f1 f2: X -> Y ):
is_continuous  f1 ->
is_continuous  f2 ->
is_continuous 
(P2 := PROD_DCPO _ _ )
 (fun x => (f1 x, f2 x)).
Proof.
intros Hc1 Hc2 S Hd.
split.
{
  apply monotonic_directed;auto.
  intros u v Hle; split;cbn.
  -
   apply continuous_implies_monotonic in Hc1.
   now apply Hc1.
  - 
   apply continuous_implies_monotonic in Hc2.
   now apply Hc2.
}
 cbn.
 repeat rewrite <-fmap_comp.
 unfold comp.
 cbn.
 f_equal.
 -
  now destruct (Hc1 _ Hd).
 -
  now destruct (Hc2 _ Hd).
Qed.

Lemma pr_plus_mono_left(p a:Bounded 0 1):
is_monotonic (P1 :=  Bounded_Poset Rle_0_1) (P2 :=  Bounded_Poset Rle_0_1)
(pr_plus p a).
Proof.
intros x y Hle.
cbn in *.
destruct p,a,x,y; cbn in *.
destruct bounded_prop, bounded_prop0,
bounded_prop1, bounded_prop2.
nra.
Qed.

Program Definition embed (a a' b b':R) (Hab : a <= b)
(Ha'b' : a' <= b')(Haa': a <= a')(Hb'b : b' <= b) (x : Bounded a' b') :
Bounded a b := {| bounded_val := bounded_val x|}.

Next Obligation.
intros a a' b b' Hab Ha'b' Haa' Hb'b (v & (Hl & Hh)).
cbn.
split;lra.
Qed.

Lemma embed_is_monotonic (a a' b b':R) (Hab : a <= b)
(Ha'b' : a' <= b')(Haa': a <= a')(Hb'b : b' <= b):
is_monotonic 
(P1 := Bounded_Poset Ha'b')
(P2 := Bounded_Poset Hab)
(embed  Hab Ha'b' Haa' Hb'b).
Proof.
now intros u v Hle.
Qed.

Lemma embed_is_continuous (a a' b b':R) (Hab : a <= b)
(Ha'b' : a' <= b')(Haa': a <= a')(Hb'b : b' <= b):
is_continuous
(P1 := Bounded_DCPO Ha'b')
(P2 := Bounded_DCPO Hab)
(embed  Hab Ha'b' Haa' Hb'b).
Proof.
intros S Hd.
split.
{
  apply monotonic_directed;auto.
  apply embed_is_monotonic.
}
 unfold embed;cbn.
 unfold bounded_lub.
 apply bounded_equal.
 cbn.
 unfold bounded_lub_val.

  destruct oracle; 
  [destruct Hd; contradiction | ].
  destruct oracle.
  - contradict i.
    rewrite not_empty_member.
    rewrite not_empty_member in n.
    destruct n as (x & Hmx).
    exists (embed  Hab Ha'b' Haa' Hb'b x).
    exists x; split; auto.
-
  unfold bounded_lub_nonempty.
  repeat (destruct completeness;cbn).
  rewrite <-fmap_comp in *.
  unfold comp in *.
  cbn in *.
  replace (bounded_val (b:=b')) with
  (fun x : Bounded a' b' => bounded_val x) in i by reflexivity.
  eapply is_lub_u; eauto.
Qed.

Program Definition restrict_func(a b c d: R)(Hab : a <= b)(Hcd : c <= d)
(f : Bounded a b -> Bounded c d) (a' b' c' d': R)
(Ha'b' : a' <= b')(Haa': a <= a')(Hb'b : b' <= b) (Hc'd' : c' <= d')
(Hf: forall (x : Bounded a' b' ),
 c' <= bounded_val (f (embed Hab Ha'b' Haa' Hb'b x)) <= d') (x:Bounded a' b') : 
Bounded c' d' := 
 {|bounded_val := bounded_val (f (embed Hab Ha'b' Haa' Hb'b x))|}.

Next Obligation.
intros a b c d Hab Hcd f a' b' c' d' Ha'b' Haa' Hb'b Hc'd' Ha (v & (Hl & Hh)).
apply Ha.
Qed.

Definition restrict_val(c d c' d':R) (x : Bounded c d) (Hle : c' <= x <= d'):
Bounded c' d' := 
{| bounded_val := x;
bounded_prop := Hle|}.

Definition restrict_set(c d c' d':R) (S : Setof(Bounded c d)) 
(Hle : forall x, member S x ->  c' <= x <= d'):
Setof (Bounded c' d') := 
fun x => exists y (Hm: member S y), 
x = restrict_val  y (Hle _ Hm ).

Lemma restrict_set_preserves_dir(c d c' d':R) (Hcd : c <= d)
(Hc'd' : c' <= d') (S : Setof(Bounded c d)) 
(Hle : forall x, member S x ->  c' <= x <= d')
(Hd : is_directed (P := Bounded_Poset Hcd) S):
is_directed (P := Bounded_Poset Hc'd') (restrict_set S Hle).
Proof.
destruct Hd as (Hn & Hd).
split.
{
  rewrite not_empty_member.
  rewrite not_empty_member in Hn.
  destruct Hn as (x & Hmx).
  exists (restrict_val x (Hle _ Hmx)).
  now exists x, Hmx.
}
intros x y Hmx Hmy.
destruct Hmx as (x' & Hmx' & Heq);subst.
destruct Hmy as (y' & Hmy' & Heq);subst.
specialize (Hd _ _ Hmx' Hmy').
destruct Hd as (z & Hmz & Ho1 & Ho2).
exists (restrict_val z (Hle _ Hmz)); repeat split; auto.
now exists z, Hmz.
Qed.
 

Lemma restrict_set_preserves_lub(c d c' d':R) (Hcd : c <= d)
(Hc'd' : c' <= d') (S : Setof(Bounded c d)) 
(Hle : forall x, member S x ->  c' <= x <= d')
(Hd : is_directed (P := Bounded_Poset Hcd) S):
bounded_val (lub (d := Bounded_DCPO Hcd) S) =
bounded_val (lub (d :=  Bounded_DCPO Hc'd') (restrict_set S Hle)).
Proof.
cbn.
unfold bounded_lub_val; cbn.
destruct oracle; [destruct Hd ; contradiction |].
destruct oracle.
-
 contradict i.
 eapply restrict_set_preserves_dir in Hd; 
 eauto.
 destruct Hd.
 exact H.
- 
unfold bounded_lub_nonempty.
repeat destruct completeness; cbn.
replace (fmap (restrict_set S Hle) (bounded_val (b:=d')))
with (fmap S (bounded_val (b:=d))) in i0;
 [eapply is_lub_u; eauto |].
apply set_equal; intro y; split; intro Hmy.
{
  destruct Hmy as (z & Hmz & Heq); subst.
  unfold restrict_set,restrict_val.
  eexists.
  split.
  -
   exists z, Hmz.
   reflexivity.
  - 
   reflexivity.
}
{
  unfold restrict_set,restrict_val in Hmy.
  destruct Hmy as ((z & (Hloz & Hhz) ) & Hmz & Heq); subst.
  destruct Hmz as ((y & (Hloy & Hhy)) & Hmy & Heq).
  cbn in *.
  injection Heq; intros ; subst.
  exists ({|
    bounded_val := y;
    bounded_prop := conj Hloy Hhy
  |}); split; auto.
}
Unshelve.
assumption.
Qed.

Lemma continuous_restriction(a a' b b' c c' d d' :R)
 (Hab : a <= b)(Hcd : c <= d)
(Ha'b' : a' <= b')(Haa': a <= a')(Hb'b : b' <= b)
(Hc'd' : c' <= d')
(f : Bounded a b -> Bounded c d)
(Hf: forall (x : Bounded a' b' ),
 c' <= bounded_val (f (embed Hab Ha'b' Haa' Hb'b x)) <= d'):
is_continuous (P1 := Bounded_DCPO Hab)(P2 := Bounded_DCPO Hcd) f->
is_continuous (P1 := Bounded_DCPO Ha'b')(P2 := Bounded_DCPO Hc'd') 
(restrict_func Hab Hcd f Ha'b' Haa' Hb'b  Hc'd' Hf ).
Proof.
intros Hcf S Hd.
split.
{
  apply monotonic_directed; auto.
  apply continuous_implies_monotonic in Hcf.
  unfold restrict_func.
  intros u v Hle.
  cbn.
  now apply Hcf.
}
{
  remember (fmap S (embed Hab Ha'b' Haa' Hb'b)) as S'.
  assert (Hd' : is_directed (P := Bounded_Poset Hab )S').
  {
    subst.
    apply (monotonic_directed
    (P1 := Bounded_Poset Ha'b')
    (P2 := Bounded_Poset Hab)); auto.
    apply embed_is_monotonic.
  }
  specialize (Hcf _ Hd').
  destruct Hcf as (Hd'' & Hcf).
  unfold restrict_func; cbn -[lub].
  subst.
  rewrite <-fmap_comp in *.
  unfold comp in *.
  specialize (@embed_is_continuous _ _ _ _ Hab Ha'b' Haa' Hb'b _ Hd) as Hec.
  destruct Hec as (_ & Hec).
  cbn -[lub] in *.
  apply bounded_equal.
  cbn -[lub].
  rewrite Hec,Hcf.
   remember  
   (fmap S 
   (fun x : Bounded a' b' => 
   f (embed Hab Ha'b' Haa' Hb'b x))) as S'.
   assert (Hle: forall x,
   member S' x -> c' <= x <= d').
   {
    subst.
    intros (x & (Hlox & Hhx)) ((y & (Hloy & Hhy)) & Hmy & Heq);
    subst.
    rewrite Heq.
    apply Hf.
   }
   remember (restrict_set S' Hle) as S''.
   replace (bounded_val (lub (d := Bounded_DCPO  Hcd) S')) with
   (bounded_val (lub (d := Bounded_DCPO  Hc'd') S'')).
   {
    apply f_equal.
    cbn - [lub] in *.
    subst.
    cbn -[lub].
    apply f_equal.
    apply set_equal; intro w; split;
    intro Hmw.
    {
      destruct Hmw as (x & Hmx & Heq);subst.
      destruct Hmx as (y & Hmy & Heq); subst.
      unfold restrict_val.
      exists y; split ; auto.
      now apply bounded_equal.
    }
    {
      destruct Hmw as (x & Hmx & Heq);subst.
      eexists.
      eexists.
      unfold restrict_val.
      apply bounded_equal.
      reflexivity.
      Unshelve.
      now exists x.
    }
   }
subst.   
erewrite <- restrict_set_preserves_lub; eauto.
}
Qed.


Lemma Rprop0 (p :Bounded 0 1) : p < 1 ->  1 <= 1/ (1-  p).
intro Hp.
destruct p as (p & Hp0 & Hp1); cbn in *.
replace 1 with (1/1) at 1 by nra.
do 2 rewrite Rdiv_1_l.
apply Rinv_le_contravar; lra.
Qed.

Lemma Rprop1 (p :Bounded 0 1) :  p <1 -> 0 <= 1/ (1- p).
Proof.
intro Hp.
eapply Rle_trans with(r2 := 1); [lra |  ].
now apply Rprop0.
Qed.

Lemma Rprop2(p a : Bounded 0 1) : 0 <= p*a + 1.
Proof.
destruct p as (p & Hp0 & Hp1); cbn in *.
destruct a as (a & Ha0 & Ha1); cbn in *.
nra.
Qed.

Lemma Rprop3(p a : Bounded 0 1):
p < 1 ->
forall x : Bounded 0 (1 / (1 - p)),
 0 <= p * a + (1 - p) * x <= p * a + 1.
Proof.
destruct p as (p & (Hlp & Hhp)); cbn in *.
destruct a as (a & (Hla & Hha)); cbn in *.
intros Hlt (x & (Hlx & Hhx)); cbn in *.
split; [nra | ].
apply Rplus_le_compat_l.
rewrite Rdiv_1_l in Hhx.
eapply Rmult_le_reg_l with (r := /(1-p)).
-
 rewrite <-Rdiv_1_l.
 specialize (Rprop0 {| bounded_val := p; 
 bounded_prop := (conj Hlp Hhp)|} Hlt).
 intro Hh.
 cbn in *.
 lra.
- 
 replace (/ (1 - p) * 1) with (/(1-p)) by lra.
 rewrite <- Rmult_assoc.
 rewrite Rinv_l; lra.
 Qed.

 Lemma Rprop4 (w x p :R):
 0 < p <=1 ->
 x <= w <= x + 1 ->
 0 <= (w - x) / p <= 1 / p.
 Proof.
 intros (Hpl & Hph) (Hxl & Hxh).
 split.
 -
  assert (Hh1 : 0 <= w -x) by lra.
  rewrite <- Rdiv_0_l with (r := p).
  eapply Rmult_le_reg_r with (r := p); auto.
  do 2 rewrite <- Rmult_div_swap.
  rewrite Rmult_div_l; [| lra].
  now rewrite Rmult_div_l; [| lra].
-
assert (Hh1 : w -x <= 1) by lra.
eapply Rmult_le_reg_r with (r := p); auto.
do 2 rewrite <- Rmult_div_swap.
rewrite Rmult_div_l; [| lra].
now rewrite Rmult_div_l; [| lra].
Qed.

Lemma Rprop5
 (p a z w : R):
  0 <= p < 1 ->
  0 <= a <= 1 ->
  0 <= z <= 1/(1 -p) ->
  0 <= w <= p*a + 1 ->
  p * a + (1 - p) * z <= w
  -> z <= (w - p*a) / (1-p).
Proof.
intros (Hlp & Hhp) (Hla & Hha)  (Hlz & Hhz) (Hlw & Hhw ) Hle.
assert (Hle' : (1-p) * z <= w - p *a) by lra.
eapply Rmult_le_reg_r with (r := 1-p); [lra |].
rewrite Rmult_comm.
rewrite <- Rmult_div_swap.
now rewrite Rmult_div_l; [| lra].
Qed.

Lemma Rprop6
 (p a z w : R):
  0 <= p < 1 ->
  0 <= a <= 1 ->
  0 <= z <= 1/(1 -p) ->
  0 <= w <= p*a + 1 ->
  z <= (w - p*a) / (1-p) ->
  p * a + (1 - p) * z <= w.
Proof.
intros (Hlp & Hhp) (Hla & Hha)  (Hlz & Hhz) (Hlw & Hhw ) Hle.
assert (Hle' : (1-p)*z <= w - p*a); [ | lra].
eapply Rmult_le_reg_l with (r :=  1/ (1- p)).
- 
assert (Hp1 :p <= 1) by lra.
specialize (Rprop0 {| bounded_val := p; 
bounded_prop := (conj Hlp Hp1)|} Hhp); cbn.
intro Hh.
lra.
-
  rewrite <- Rmult_assoc.
  rewrite <- Rmult_div_swap.
  replace (1 *(1 - p) / (1 - p)) with 1.
  +
   replace (1*z) with z by lra.
   rewrite Rmult_comm.
   rewrite Rmult_div_assoc.
   now replace ((w - p * a) * 1) with  (w - p * a) by lra.
  +
  replace (1 * (1 - p)) with (1-p) by lra.
  rewrite Rdiv_diag; auto; lra.
Qed.

Program Definition 
pr_plus' (p a: Bounded 0 1)(Hp1 : p < 1) (x: Bounded 0 (1/ (1-p))): 
Bounded 0 (p*a + 1) :=
{| bounded_val := bounded_val p * bounded_val a + (1 -  bounded_val p) * bounded_val x |}.

Next Obligation.
intros; now apply Rprop3.
Qed.

Lemma pr'_plus_mono_left(p a:Bounded 0 1)
 (Hp1 :p < 1):
is_monotonic(P1 :=  Bounded_Poset (Rprop1 _ Hp1)) 
(P2 :=  Bounded_Poset (Rprop2 p a))
(pr_plus' p a Hp1).
Proof.
intros (u & (Hul & Huh)) (v & (Hvl & Hvh)) Hle.
cbn in *.
destruct a as (a & (Hal & Hah)).
destruct p as (p & (Hpl & Hoh)).
cbn in *.
nra.
Qed.

Lemma pr_plus'_cont_left_lt(p a:Bounded 0 1)
 (Hp1 :p < 1):
is_continuous (P1 :=  Bounded_DCPO (Rprop1 _ Hp1)) 
(P2 :=  Bounded_DCPO (Rprop2 p a))
(pr_plus' p a Hp1).
rewrite continuous_iff_mono_commutes; split;
[apply pr'_plus_mono_left |].
intros S l Hd (Hu & Hm).
split.
{
 intros x (y & Hmy & Heq);subst.
 now apply pr'_plus_mono_left,Hu.
}
intros (w & (Hlw & Hhw)) Huw.
cbn in *.
assert (Hord: 0 <= (w - p* a)/(1-p) <= 1/(1-p)).
{
  remember p as p'.
  destruct p' as (p' & (Hlp & Hhp)).
  remember a as a'.
  destruct a' as (a' & (Hla & Hha)); cbn in *.
  apply Rprop4; [split ; lra | split; auto].
  destruct Hd as (Hn &  _).
  rewrite not_empty_member in Hn.
  destruct Hn as (z & Hmz).
  assert (Hmz' : member (fmap S (pr_plus' {|
    bounded_val := p';
    bounded_prop :=
      conj Hlp Hhp
  |} {|
  bounded_val := a';
  bounded_prop :=
    conj Hla Hha
  |}  Hp1))
 (pr_plus' {|
  bounded_val := p';
  bounded_prop :=
    conj Hlp Hhp
|} {|
bounded_val := a';
bounded_prop :=
  conj Hla Hha
|}  Hp1 z)) by now exists z.
 specialize (Huw _ Hmz').
cbn in Huw.
destruct z as (z & (Hlz & Hhz)).
cbn in *.
nra.
}
assert (Hex :  
is_upper (P := Bounded_Poset (Rprop1 p Hp1)) S
{| bounded_val :=  (w - p* a)/(1-p);
bounded_prop := Hord|} ).
{
 intros z Hmz.
 cbn in z.
 assert (Hmz' : member (fmap S (pr_plus' p a Hp1))
 (pr_plus' p a Hp1 z)) by now exists z.
 specialize (Huw _ Hmz').
 cbn in Huw.
 cbn.
 destruct p as (p & (Hlp & Hhp)).
 destruct a as (a & (Hla & Hha)).
 destruct z as (z & (Hlz & Hhz)).
 cbn in *.
 destruct Hord.
 apply Rprop5; try split; auto.
}
specialize (Hm _ Hex).
cbn in Hm.
destruct Hord.
destruct l as (l & (Hll & Hhl)).
destruct p as (p & (Hlp & Hhp)).
destruct a as (a & (Hla & Hha)).
cbn in *.
apply Rprop6; try split;auto.
Qed.

Lemma pr_plus'_cont_left_lt_aux2(p a:Bounded 0 1)(Hp : p <1):
forall x : Bounded 0 1,
         0 <=
         pr_plus' p a Hp
           (embed (Rprop1 p Hp) Rle_0_1 
              (Rle_refl 0) (Rprop0 p Hp) x) <=
         1.
Proof.
intros x.
unfold pr_plus',embed.
cbn.
destruct x as (x & (Hlx & Hhx)).
destruct p as (p & (Hlp & Hhp)).
destruct a as (a & (Hla & Hha)).
cbn in *.
nra.
Qed.

Lemma pr_plus_cont_left_lt(p a:Bounded 0 1):
 p < 1 ->
is_continuous (P1 :=  Bounded_DCPO Rle_0_1) 
(P2 :=  Bounded_DCPO Rle_0_1)
(pr_plus p a).
Proof.
intros Hlt.
specialize (pr_plus'_cont_left_lt (p:= p) (Hp1 := Hlt) a ) as Hc.
specialize (@continuous_restriction 0 0 (1/(1-p)) 
1 0 0 (p*a+1) 1 (Rprop1 _ Hlt) (Rprop2 p a) Rle_0_1
 (Rle_refl _) (Rprop0 _ Hlt ) (Rle_0_1) (pr_plus' p a Hlt)
 (pr_plus'_cont_left_lt_aux2 p a Hlt) Hc
 ) as Hcr.
 unfold pr_plus,pr_plus',restrict_func,restrict_val in *.
 cbn in *.
replace  (fun x : Bounded 0 1 =>
{|
  bounded_val := p * a + (1 - p) * x;
  bounded_prop :=
    restrict_func_obligation_1 (Rprop1 p Hlt)
      (fun x0 : Bounded 0 (1 / (1 - p)) =>
       {|
         bounded_val := p * a + (1 - p) * x0;
         bounded_prop := pr_plus'_obligation_1 p a Hlt x0
       |})
      Rle_0_1 (Rle_refl 0) (Rprop0 p Hlt)
      (pr_plus'_cont_left_lt_aux2 p a Hlt) x
|}) with 
(fun r : Bounded 0 1 =>
{|
  bounded_val := p * a + (1 - p) * r;
  bounded_prop := pr_plus_obligation_1 p a r
|}) in Hcr; auto.
extensionality x.
now apply bounded_equal.
Qed.

Lemma pr_plus_cont_left(p a:Bounded 0 1):
is_continuous (P1 :=  Bounded_DCPO Rle_0_1) 
(P2 :=  Bounded_DCPO Rle_0_1)
(pr_plus p a).
Proof.
destruct (Rge_lt_dec p 1).
-
  assert (Heqp : bounded_val p =1).
  {
   destruct p as (p & (Hl & Hh)); cbn in *.
   lra. 
  }
  clear r.
  unfold pr_plus.
  subst.
  destruct p as (p & (Hl & Hh)); cbn in *.
  destruct a as (a & (Hla & Hha)); cbn in *.
  subst.
  replace (fun r : Bounded 0 1 =>
  {|
    bounded_val := 1 * a + (1 - 1) * r;
    bounded_prop :=
      pr_plus_obligation_1
        {| bounded_val := 1; bounded_prop := conj Hl Hh |}
        {| bounded_val := a; bounded_prop := conj Hla Hha |} r
  |})
  with 
  (fun _ : Bounded 0 1  =>
   {|
     bounded_val :=  a ;
     bounded_prop :=
     (conj Hla Hha)
   |}).
  +
   apply (cst_is_continuous
    (P1 := Bounded_DCPO Rle_0_1)).
  +
   extensionality r.
   apply bounded_equal.
   cbn.
   lra.  
- 
 now apply pr_plus_cont_left_lt.
Qed.

Lemma  uncurry_pr_plus_is_continuous(p:Bounded 0 1):
is_continuous
(P1 := PROD_DCPO (Bounded_DCPO Rle_0_1) (Bounded_DCPO Rle_0_1)) 
(P2 := Bounded_DCPO Rle_0_1 )
(uncurry (pr_plus p)).
Proof.
apply (uncurry_preserves_cont
(A := (Bounded_DCPO Rle_0_1) )
(B := (Bounded_DCPO Rle_0_1))
(C := (Bounded_DCPO Rle_0_1))).
- 
 intro a.
 apply pr_plus_cont_left.
- 
 intro b.
 cbn in *.
 replace 
 (fun a => pr_plus p a b) with
 (pr_plus (pr_opp p) b).
 +
  apply pr_plus_cont_left.
 +
 unfold pr_plus,pr_opp. 
 extensionality r.
 apply bounded_equal.
 cbn.
 destruct p as (p & (Hl & Hh)); cbn in *.
 destruct b as (b& (Hlb & Hhb)); cbn in *.
 destruct r as (r& (Hlr & Hhr)); cbn in *.
 lra.
Qed.

Lemma choice_is_continuous (p : Bounded 0 1) (X : Type) (m1 m2 : prob_monad X) :
@is_continuous _ (Bounded_DCPO Rle_0_1)
  (fun f : EXP_DCPO X (Bounded_DCPO Rle_0_1) =>
    pr_plus p (fonc m1 f) (fonc m2 f)).
Proof.
intros T Hd.
assert (Hd' : is_directed (P := Bounded_Poset Rle_0_1)
(fmap T
   (fun f : EXP_CPO X (Bounded_CPO Rle_0_1) => pr_plus p (fonc m1 f) (fonc m2 f)))).
{
  apply (monotonic_directed
  (P2 := (Bounded_Poset Rle_0_1))
  )
  ;auto.
  apply choice_is_monotonic.
}
split; auto.
cbn in T.
cbn -[lub].
destruct m1 as (m1 & Hcm1).   
destruct m2 as (m2 & Hcm2).
cbn -[lub] in *.
remember (pr_plus p) as prp.
change (fmap T (fun f : EXP X (Bounded 0 1) => prp (m1 f) (m2 f)))
with ((fmap T (fun f : EXP X (Bounded 0 1) => (uncurry prp ((m1 f), (m2 f)))))).
change 
(prp
(m1 (@lub (EXP_DCPO X (@Bounded_DCPO 0 1 Rle_0_1)) T))
(m2 (@lub (EXP_DCPO X (@Bounded_DCPO 0 1 Rle_0_1)) T)))
 with 
 (uncurry prp
 ((m1 (@lub (EXP_DCPO X (@Bounded_DCPO 0 1 Rle_0_1)) T)),
 (m2 (@lub (EXP_DCPO X (@Bounded_DCPO 0 1 Rle_0_1)) T)))).
replace (lub (d := (Bounded_DCPO Rle_0_1))
(fmap T
   (fun f : EXP X (Bounded 0 1) =>
    uncurry prp (m1 f, m2 f)))) with
( (uncurry prp) (lub (d := PROD_DCPO(Bounded_DCPO Rle_0_1)  (Bounded_DCPO Rle_0_1))
(fmap T  (fun f => (m1 f, m2 f))) )).
-
 f_equal.
 cbn -[lub] in *.
 now destruct 
 (@pair_preserves_continuity
  (EXP_DCPO X (Bounded_DCPO Rle_0_1)) 
  (Bounded_DCPO Rle_0_1) _ _ Hcm1 Hcm2 _ Hd).
-

 assert (Hd'' : 
 is_directed (P := PROD_Poset(Bounded_Poset Rle_0_1)  (Bounded_Poset Rle_0_1))
 (fmap T
       (fun x : EXP X (Bounded 0 1) =>
         (m1 x, m2 x)))
 ).
 {
  apply (monotonic_directed
  (P1 := EXP_Poset _(Bounded_Poset Rle_0_1))
  (P2 := PROD_Poset(Bounded_Poset Rle_0_1)  (Bounded_Poset Rle_0_1)));auto.
  intros x y Hle.
  cbn; split.
  -
   apply continuous_implies_monotonic in Hcm1.
   now apply Hcm1.
  - 
   apply continuous_implies_monotonic in Hcm2.
   now apply Hcm2.
 }
 destruct (@uncurry_pr_plus_is_continuous p _ Hd'').
 rewrite <- fmap_comp in *.
 now subst.
Qed.

Lemma flip_fonc_is_continuous (p : Bounded 0 1) :
 @is_continuous (EXP_DCPO _ (Bounded_DCPO Rle_0_1)) (Bounded_DCPO Rle_0_1)
   (fun f => pr_plus p (f true) (f false)).
Proof.
 specialize (@choice_is_continuous p bool) as Hcc.
cbn in *.
remember ((fun (g:EXP bool (Bounded 0 1))  => g true): EXP (EXP_DCPO bool (Bounded_DCPO  Rle_0_1)) (( (Bounded_DCPO  Rle_0_1))))
 as fm1.
assert (fm1c : is_continuous (P1 :=EXP_DCPO _ (Bounded_DCPO
Rle_0_1) ) (P2 := (Bounded_DCPO Rle_0_1) )fm1) by 
(subst;cbn in *;  split; auto;
  now apply directed_proj).
remember ((fun (g:EXP bool (Bounded 0 1))  => g false):
EXP (EXP_DCPO bool (Bounded_DCPO  Rle_0_1)) (( (Bounded_DCPO  Rle_0_1))))
 as fm2.
assert (fm2c : is_continuous (P1 :=EXP_DCPO _ (Bounded_DCPO
Rle_0_1) ) (P2 := (Bounded_DCPO Rle_0_1) )fm2) 
by (subst;cbn in *;  split; auto;
now apply directed_proj).
specialize (Hcc {| fonc := fm1; cont := fm1c|} 
{| fonc := fm2; cont := fm2c|}).
subst.
apply Hcc.
Qed.

Program Definition flip (p : Bounded 0 1) : prob_monad bool := {|
  fonc := fun f => pr_plus p (f true) (f false);
  cont := flip_fonc_is_continuous p
|}.

Lemma flip_ignored (p : Bounded 0 1) [X : Type] (m : prob_monad X) :
flip p;; m = m.
Proof.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
lra.
Qed.

Lemma flip_0 : flip pr_0 = ret prob_monad false.
Proof.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
lra.
Qed.

Lemma flip_1 : flip pr_1 = ret prob_monad true.
Proof.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
lra.
Qed.

Lemma flip_opp (p : Bounded 0 1) :
flip (pr_opp p) = do b <- flip p; ret _ (negb b).
Proof.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
lra.
Qed.

Lemma flip_assoc
  (p q r s : Bounded 0 1) [X : Type] (m1 m2 m3 : prob_monad X) :
p = pr_mult r s -> pr_opp s = pr_mult (pr_opp p) (pr_opp q) ->
do b <- flip p; do b' <- flip q; (if b then m1 else if b' then m2 else m3) =
do b <- flip s; do b' <- flip r; (if b then if b' then m1 else m2 else m3).
Proof.
intros Hp Hs_.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
assert (Hp' := f_equal (@bounded_val _ _) Hp).
assert (Hs_' := f_equal (@bounded_val _ _) Hs_).
clear Hp Hs_.
cbn in Hp', Hs_'.
assert (Heq : (1 - p) * q = (1 - r) * s) by lra.
generalize (fonc m1 g), (fonc m2 g), (fonc m3 g).
cbn.
clear m1 m2 m3 g.
intros (x & Hx0 & Hx1) (y & Hy0 & Hy1) (z & Hz0 & Hz1).
cbn.
destruct
 p as (p & Hp0 & Hp1), q as (q & Hq0 & Hq1),
 r as (r & Hr0 & Hr1), s as (s & Hs0 & Hs1).
cbn in *.
nra.
Qed.

Lemma flip_flip_comm [X : Type] (p q : Bounded 0 1)
  (f : bool -> bool -> prob_monad X) :
do b  <- flip p; do b' <- flip q; f b b' =
do b' <- flip q; do b  <- flip p; f b b'.
Proof.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
nra.
Qed.

(*
Lemma flip_comm [X Y : Type] (p : Bounded 0 1)
  (m : prob_monad X) (f : X -> bool -> prob_monad Y) :
do x <- m; do b <- flip p; f x b = do b <- flip p; do x <- m; f x b.
Proof.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
Admtted.
*)

Lemma flip_and (p q : Bounded 0 1) :
do b1 <- flip p; do b2 <- flip q; ret _ (b1 && b2) = flip (pr_mult p q).
Proof.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
lra.
Qed.

Lemma flip_or (p q : Bounded 0 1) :
do b1 <- flip p; do b2 <- flip q; ret _ (b1 || b2) =
flip (pr_or p q).
Proof.
apply CONT_equal.
cbn.
extensionality g.
apply bounded_equal.
cbn.
lra.
Qed.

Definition probability (X : Type) (E : X -> bool) (m : prob_monad X) :
Bounded 0 1 :=
fonc m (fun x => if E x then pr_1 else pr_0).
