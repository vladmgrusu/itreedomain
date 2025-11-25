From Stdlib Require Import FunctionalExtensionality PropExtensionality
 IndefiniteDescription Classical List Lia JMeq.
 
From Domain Require Export Exp FunComp Coind.
Import ListNotations.

Inductive lcont (A : Type)(B L : A -> Type) : Type :=
|lcbot : lcont A B L
|lcnode : forall a, L a ->  (B a -> lcont A B L) -> lcont A B L.

  
Arguments lcbot {_ _ _}.
Arguments lcnode {_ _ _} _ _ _.


Inductive is_LFPC{A : Type}{B L : A -> Type} : lcont A B L-> Prop :=
   |lcbot_is_LFPC : is_LFPC lcbot
   |lcnode_is_LFPC : forall a l f,  is_finite (support f lcbot) ->
   (forall b, is_LFPC (f b)) -> is_LFPC (lcnode a l f).
   

Record LFPC (A : Type)(B L : A -> Type) :=
    {
      lfpc :> lcont A B L;
      lfinsup : is_LFPC lfpc
    }.
    
    
  Arguments lfpc {_ _ _} _.
  Arguments lfinsup {_ _ _} _.



Lemma finite_pos_is_LFPC{A : Type}{B L : A -> Type}(c: lcont A B L) : 
(forall a, is_finite_type (B a))-> is_LFPC c.
Proof.
induction c; intros Hf.
-
 constructor.
-
 constructor.
 +
  unfold is_finite, support, member; cbn.
  assert (IH : forall b, is_LFPC (l0 b)).
  {
    intro b.
    apply H.
    intro a'.
    now apply Hf.
  }
  specialize (Hf a) as Hfa.
  destruct Hfa as (l' & Hl).
  exists l'.
  intros x _.
  now apply Hl.
  +
   intro b.
   now apply H.
Qed. 

   
(*lcbot, seen as an LFPC*)
Definition Lcbot{A : Type}{B L: A -> Type} : LFPC A B L:=
{|
 lfpc := lcbot;   
 lfinsup := lcbot_is_LFPC
|}.


Lemma LFPC_equal{A : Type}{B L : A -> Type}(u v: LFPC A B L):
lfpc u = lfpc v -> u = v.
Proof.
intro Heq.
destruct u as (c & Hc).
destruct v as (c' & Hc').
cbn in *.
subst.
f_equal.
apply proof_irrelevance.
Qed.

(* proving that LFPCs form a PPO. Start with labelled containers.*)
Inductive le_lcont{A : Type}{B L: A -> Type} :
lcont A B L-> lcont A B L-> Prop :=
 |le_lcbot : forall c, le_lcont lcbot c
 |le_lcnode : forall a (l : L a) f f',
  (forall x, le_lcont (f x) (f' x)) -> 
  le_lcont (lcnode a  l f) (lcnode a l f').

Lemma le_lcont_refl{A : Type}{B L : A -> Type}(c: lcont A B L):
le_lcont c c.
Proof.
induction c; now constructor.
Qed.


Lemma le_lcont_trans{A : Type}{B L: A -> Type}:
forall (c c' c'': lcont A B L),
le_lcont c c' -> le_lcont c' c'' -> le_lcont c c''.
Proof.
induction c ; intros c' c'' Hle Hle' ; [constructor |].
inversion Hle; subst; clear Hle.
apply inj_pair2 in H2,H3; subst.
inversion Hle'; subst; clear Hle'.
apply inj_pair2 in H2,H3; subst.
constructor.
intro x.
eapply H;  eauto.
Qed.


Lemma le_lcont_antisym{A : Type}{B L : A -> Type}:
forall (c c': lcont A B L),
le_lcont c c' -> le_lcont c' c -> c = c'.
Proof.
induction c ; intros c' Hle Hle'.
-
 now inversion Hle'.
-
inversion Hle; subst; clear Hle.
apply inj_pair2 in H2,H3; subst.
inversion Hle'; subst; clear Hle'.
apply inj_pair2 in H2,H3,H5,H6; subst.
f_equal.
extensionality x.
now apply H.
Qed.

Definition lcont_Poset(A : Type)(B L : A -> Type) : Poset :=
{|
   carrier := lcont A B L;
   default := lcbot;
   ord := le_lcont;
   refl := le_lcont_refl;
   trans := le_lcont_trans;
   antisym :=  le_lcont_antisym
|}.


Definition cont_PPO (A : Type)(B L: A -> Type) : PPO :=
{| poset_ppo := lcont_Poset A B L;
	pbot := lcbot;
    pbot_least := le_lcbot 
|}.

(* onto LFPC, their order, Poset and PPI*)
Definition le_LFPC{A : Type}{B  L: A -> Type} (u v: LFPC A B L): Prop :=
le_lcont (lfpc u) (lfpc v). 

Program Definition LFPC_Poset(A : Type)(B L : A -> Type) : Poset :=
{|
  carrier := LFPC A B L;
  ord := le_LFPC;  
  default := Lcbot;
|}.


Next Obligation.
destruct x as (c & Hf).
apply le_lcont_refl.
Qed.

Next Obligation.
destruct x as (c & Hf).
destruct y as (c' & Hf').
destruct z as (c'' & Hf'').
 unfold le_LFPC in *;
 cbn in *.
eapply le_lcont_trans; eauto.
Qed.


Next Obligation.
destruct x as (c & Hf).
destruct y as (c' & Hf').
unfold le_LFPC in *;cbn in *.
apply LFPC_equal.
now apply le_lcont_antisym.
Qed.




Lemma Lcbot_least{A : Type}{B L : A -> Type}:
 forall x : LFPC A B L, le_LFPC Lcbot x.
Proof.
intros (c & Hc).
constructor.
Qed.



Program Definition LFPC_PPO (A : Type)(B L : A -> Type) : PPO :=
{| poset_ppo := LFPC_Poset A B L;
	pbot := Lcbot;
    pbot_least := Lcbot_least
|}.


Definition completed_ord{P:Poset}{c: COMPLETION P} : c -> c -> Prop :=
@ord (@dcpo_poset(@algebraic_dcpo (alg c))).

(* Now we take the ideal completion of LFCP_PPO and get Labelled Partial Containers*)
Definition LPC(A : Type)(B L : A -> Type) 
 := ideal_completion (LFPC_PPO A B L).

(* For all a: A, The finitely supported functions B a -> LFCP A B Lare
completed using completion of exponentials *)
 Definition fLPC{A : Type}{B L : A -> Type}:forall (a:A),
 COMPLETION (finitely_supported_Poset (B a) (LFPC_PPO A B L)).
Proof. 
 exact
   (fun a => EXP_COMP (A:= B a) (LPC A B L)).
Defined.


Lemma completed_ord_func{A : Type}{B L : A -> Type} (a:A) :
forall (f f' : fLPC (L := L) a),
completed_ord f f' <-> forall (b: B a), f b <= f' b.
Proof.
intros f f'.
split; intro Hc.
- 
 intro b.
 unfold completed_ord in Hc.
 replace f with (lub (compacts_le f)) in Hc; 
 [| symmetry; apply algebraic_lub].
 replace f' with (lub (compacts_le f')) in Hc; [| symmetry; apply algebraic_lub].
 rewrite <-  forallex_iff_lelub in Hc; 
 try apply algebraic_dir; 
 [ | intros x (Hx & _); auto].
 cbn in *.
 replace (f b) with (lub (compacts_le (f b))); 
 [| symmetry; apply algebraic_lub].
 replace (f' b) with (lub (compacts_le (f' b))); 
 [| symmetry; apply algebraic_lub].
 apply forallex_lelub;  
  try apply algebraic_dir.
 intros y Hmy.
 remember ((fun z : B a =>
  if oracle (z = b)
  then y
  else inject pbot)) as fy.
 specialize (Hc fy).
  
 assert (Hm : member (compacts_le (P := (fLPC a)) f) fy).
 {
    split.
    -
    apply @compacts_are_functions_with_finite_support_and_compact_values.
    split.
    +
     subst. 
     exists [b].
     intros x Hmx.
     subst.
     unfold member, support in Hmx.
     destruct (oracle (x = b)); subst; [now constructor | ].
     now contradict Hmx.
    +
     intro b'.
     subst.
     destruct Hmy as (Hcy & _).
     destruct (oracle (b' = b)); auto.
     apply inject_compact.
    -
     subst.
     cbn.
     intro d.
     destruct Hmy as (Hcy & Hley).
     destruct (oracle (d = b)); subst; auto.
     cbn.
     apply (inject_pbot_least (LPC A B L)).
 }
 specialize (Hc Hm).
 destruct Hc  as ( g & (Hcg & Hleg) & Ha).
 exists (g b); subst.
 repeat split.
 +
  now apply compacts_have_compact_values.
 +
  cbn in Hleg.
  apply Hleg.
 +
  specialize (Ha b).
  destruct (oracle (b= b)); [assumption| contradiction].
 -
  unfold completed_ord.
  replace f with (lub (compacts_le f)); 
  [| symmetry; apply algebraic_lub].
  replace f' with (lub (compacts_le f')); [| symmetry; apply algebraic_lub].
  apply forallex_lelub;  
  try apply algebraic_dir.
  intros g (Hcg & Hleg).
  exists g; repeat split; auto; [| apply refl].
  eapply trans; eauto.
Qed.  

(* Next, we restrict the lcnode constructor to finitely supported functions*)

Program Definition flcnode{A:Type}{B L: A -> Type}(a:A)(l: L a)
(f : finitely_supported (B a) (LFPC A B L) Lcbot) : LFPC A B L:=
{|
  lfpc := lcnode a l (func _ f);
|}.

Next Obligation.
destruct f; 
constructor; cbn.
-
 destruct fsup as (s  & Ha).
 exists s.
 intros x Hmx.
 apply Ha.
 intro Heq.
 apply Hmx.
 now rewrite Heq.
-
 intros b.
 now destruct func.
Qed.

(* proving that fcnode is monotonic*)
Lemma flcnode_mono{A:Type}{B L: A -> Type}(a:A)(l: L a):
forall (f f' : finitely_supported (B a) (LFPC A B L) Lcbot),
(forall b, le_LFPC (func _ f b) (func _ f' b)) ->
le_LFPC (flcnode a l f) (flcnode a l f').
Proof.
intros f f' Hle.
now constructor.
Qed.



(* completing lfcnode to a continuous function between 
the completions (fLPC a) of functions in (B a  -> LFPC A B L) and
LPC A B Lof LFPC A B L*)

Definition lnode{A:Type}{B L: A -> Type}(a:A)(l : L a) := 
funcomp_default_ext (P1 :=finitely_supported_Poset (B a) (LFPC_PPO A B L))
(P2 := LFPC_PPO A B L)(flcnode a l) (flcnode_mono a l) 
(fLPC a) (LPC A B L).

Lemma lnode_is_monotonic{A:Type}{B L: A -> Type}(a:A) (l : L a):
is_monotonic (P2 := LPC A B L) (lnode a l).
Proof.
apply funcomp_default_ext_mono.
Qed.

Lemma lnode_is_continuous{A:Type}{B L: A -> Type}(a:A) (l : L a):
is_continuous (P2 := LPC A B L) (lnode a l).
Proof.
apply funcomp_default_ext_cont.
Qed.

Lemma lnode_extends_flcnode{A:Type}{B L: A -> Type}(a:A)(l: L a)
(f : fLPC a):
is_compact f ->
 lnode a l f = 
  inject (c := LPC A B L) 
   (flcnode a l 
   (rev_inj f)).
Proof.
intro Hc.
now apply funcomp_default_ext_ext.
Qed.



Lemma lnode_ord_same_shape{A:Type}(B L : A -> Type)(a a':A) 
(l : L a)(l' : L a')
(f : fLPC a) (f' : fLPC a'):
completed_ord (c := LPC A B L) (lnode a l f) (lnode a' l' f') -> a = a'.
Proof.
unfold completed_ord.
intro  Hle.
replace f with (lub (compacts_le f)) in Hle; 
[|  now rewrite algebraic_lub].
replace f' with (lub (compacts_le f')) in Hle; 
[|  now rewrite algebraic_lub].
specialize (lnode_is_continuous (B := B) a l) as Hc.
specialize (lnode_is_continuous (B := B) a' l') as Hc'.
rewrite @continuous_iff_mono_commutes in Hc,Hc'.
destruct Hc as (Hm & Hc).
destruct Hc' as (Hm' & Hc').
specialize (Hc _ (lub  (compacts_le f)) (algebraic_dir f)).
specialize (Hc' _ (lub  (compacts_le f')) (algebraic_dir f')).
unfold commutes_with_lub in Hc,Hc'.
specialize (Hc (lub_is_lub _ (algebraic_dir f))).
specialize (Hc' (lub_is_lub _ (algebraic_dir f'))).
apply is_lub_lub_eq1 in Hc; [| now apply monotonic_directed,my_algebraic_dir].
rewrite Hc in Hle.
apply is_lub_lub_eq1 in Hc'; [| now apply monotonic_directed,my_algebraic_dir].
rewrite Hc' in Hle.
rewrite <- forallex_iff_lelub in Hle;
[| now apply monotonic_directed,my_algebraic_dir |
now apply monotonic_directed,my_algebraic_dir |  ].
-
destruct (algebraic_dir f) as (Hne & _).
rewrite not_empty_member in Hne.
destruct Hne as (y & Hmy).
assert (Hmy' :
member (fmap (compacts_le f) (lnode a l)) (lnode a l y)) by 
now exists y.
specialize (Hle _ Hmy') as Hley.
destruct Hley as (u & (z & Hmz & Heq) & Hlez); subst.
rewrite lnode_extends_flcnode in Hlez; [|now destruct Hmy].
rewrite lnode_extends_flcnode in Hlez; [|now destruct Hmz].
apply inject_bimono in Hlez.
inversion Hlez; subst.
now apply inj_pair2 in H1,H2,H4,H5; subst.
-
 intros x (y & Hmy & Heq); subst.
 rewrite lnode_extends_flcnode; [ | now destruct Hmy].
 apply inject_compact.
Qed.




Lemma lnode_ord_func_ord{A:Type}(B L: A -> Type)(a:A)
(l l' : L a)
(f f': fLPC a) :
completed_ord (c := LPC A B L) (lnode a l f) (lnode a l' f') -> 
completed_ord f f'.
Proof.
intro Hle.
unfold completed_ord in *.
replace f with (lub (compacts_le f)) in *; 
[|  now rewrite algebraic_lub].
replace f' with (lub (compacts_le f')) in *; 
[|  now rewrite algebraic_lub].
specialize (lnode_is_continuous (B := B) a l) as Hc.
specialize (lnode_is_continuous (B := B) a l') as Hc'.

rewrite @continuous_iff_mono_commutes in Hc,Hc'.
destruct Hc as (Hm & Hc).
destruct Hc' as (Hm' & Hc').

specialize (Hc _ (lub  (compacts_le f)) (algebraic_dir f))  as Hcf.
specialize (Hc' _ (lub  (compacts_le f')) (algebraic_dir f'))  as Hcf'.

unfold commutes_with_lub in Hcf,Hcf'.
specialize (Hcf (lub_is_lub _ (algebraic_dir f))).
specialize (Hcf' (lub_is_lub _ (algebraic_dir f'))).

apply is_lub_lub_eq1 in Hcf; [| now apply monotonic_directed,my_algebraic_dir].
rewrite Hcf in Hle.
apply is_lub_lub_eq1 in Hcf'; [| now apply monotonic_directed,my_algebraic_dir].
rewrite Hcf' in Hle.
unfold completed_ord in Hle.
clear Hcf Hcf' Hc.
apply forallex_lelub; try apply algebraic_dir.
cbn.
intros x (Hmc & Hlex).
rewrite <- forallex_iff_lelub in Hle;
[| now apply monotonic_directed,my_algebraic_dir |
now apply monotonic_directed,my_algebraic_dir |  ].
-
assert (Hmx' :
member (fmap (compacts_le f) (lnode a l)) (lnode a l x)) by 
now exists x.
specialize (Hle _ Hmx') as Hlex'.
clear Hmx'.
destruct Hlex' as (u & (z & Hmz & Heq) & Hlez); subst.
exists z; split; auto.
rewrite lnode_extends_flcnode in Hlez; auto.
rewrite lnode_extends_flcnode in Hlez; [|now destruct Hmz].
apply inject_bimono in Hlez.
inversion Hlez; subst; clear Hlez.
apply inj_pair2 in H1,H2,H3,H4; subst.
intro w.
specialize (H0 w).
destruct (oracle
(@is_compact
   (EXP_Poset (B a) (LPC A B L)) x)); 
[ | contradiction].
destruct (oracle
(@is_compact
   (EXP_Poset (B a) (LPC A B L)) z)); 
[ | destruct Hmz; contradiction].
apply rev_inj_bimono; auto;
 now apply compacts_have_compact_values.
-
 intros w (u & (Hvy & Hley) & Heq); subst.
 rewrite lnode_extends_flcnode; auto.
 apply inject_compact. 
Qed.

Lemma lnode_is_bimonotonic{A:Type}(B L: A -> Type)(a:A)(l : L a):
is_bimonotonic (P1 := fLPC (B:= B) a) (lnode a l).
Proof.
split; [apply lnode_is_monotonic |].
intros x y Hle.
eapply lnode_ord_func_ord; eauto.
Qed.


Lemma lnode_ord_labels_eq{A:Type}(B L: A -> Type)(a:A)
(l l' : L a)
(f f': fLPC a) :
completed_ord (c := LPC A B L) (lnode a l f) (lnode a l' f') -> 
l = l'.
Proof.
unfold completed_ord.
intro  Hle.
replace f with (lub (compacts_le f)) in Hle; 
[|  now rewrite algebraic_lub].
replace f' with (lub (compacts_le f')) in Hle; 
[|  now rewrite algebraic_lub].
specialize (lnode_is_continuous (B := B) a l) as Hc.
specialize (lnode_is_continuous (B := B) a l') as Hc'.
rewrite @continuous_iff_mono_commutes in Hc,Hc'.
destruct Hc as (Hm & Hc).
destruct Hc' as (Hm' & Hc').
specialize (Hc _ (lub  (compacts_le f)) (algebraic_dir f)).
specialize (Hc' _ (lub  (compacts_le f')) (algebraic_dir f')).
unfold commutes_with_lub in Hc,Hc'.
specialize (Hc (lub_is_lub _ (algebraic_dir f))).
specialize (Hc' (lub_is_lub _ (algebraic_dir f'))).
apply is_lub_lub_eq1 in Hc; [| now apply monotonic_directed,my_algebraic_dir].
rewrite Hc in Hle.
apply is_lub_lub_eq1 in Hc'; [| now apply monotonic_directed,my_algebraic_dir].
rewrite Hc' in Hle.
rewrite <- forallex_iff_lelub in Hle;
[| now apply monotonic_directed,my_algebraic_dir |
now apply monotonic_directed,my_algebraic_dir |  ].
-
destruct (algebraic_dir f) as (Hne & _).
rewrite not_empty_member in Hne.
destruct Hne as (y & Hmy).
assert (Hmy' :
member (fmap (compacts_le f) (lnode a l)) (lnode a l y)) by 
now exists y.
specialize (Hle _ Hmy') as Hley.
destruct Hley as (u & (z & Hmz & Heq) & Hlez); subst.
rewrite lnode_extends_flcnode in Hlez; [|now destruct Hmy].
rewrite lnode_extends_flcnode in Hlez; [|now destruct Hmz].
apply inject_bimono in Hlez.
inversion Hlez; subst.
apply inj_pair2 in H1,H2,H3,H4.
congruence.
-
 intros x (y & Hmy & Heq); subst.
 rewrite lnode_extends_flcnode; [ | now destruct Hmy].
 apply inject_compact.
Qed.




Lemma lnode_injective{A:Type}(B L : A -> Type)(a a':A)
(l : L a)(l' : L a')
(f: @fLPC A B L a) (f': fLPC a') :
lnode a l f = lnode a' l' f' -> a = a' /\ JMeq f  f'/\ JMeq l l'.
Proof.
intros Heq.
assert (Heqa : a = a') by (eapply lnode_ord_same_shape;
  rewrite Heq;
  apply refl).
subst; repeat split; auto.
-
replace f with f'; [apply JMeq_refl |].
apply antisym.
 + apply lnode_ord_func_ord with (l := l')(l' := l).
   rewrite Heq.
   apply refl.
 +
  apply lnode_ord_func_ord  with (l := l)(l' := l').
  rewrite Heq.
  apply refl.
-
  assert (Hle: lnode a' l f <=
  lnode a' l' f') by (rewrite Heq; apply refl).
  apply lnode_ord_labels_eq in Hle;subst.
  constructor.
Qed.


Lemma remove_bot_directed{A:ACPO} (S:Setof A):
lub S <> abot -> is_directed S -> 
is_directed (remove S abot) /\
 lub(remove S abot)  = lub S.
Proof.
intros Hne Hd.
specialize Hd as Hd'.
destruct Hd' as (Hn & Hd').
assert (Hns: S <> single abot).
{
intro Habs; subst.
apply Hne.
apply lub_single.
}
specialize (not_empty_not_single_2dif _ _ Hn Hns) as Hex.
destruct Hex as (y & Hmy & Hney).
assert (Hdr: is_directed (remove S abot)).
{
 split.
 -
 apply not_empty_member.
 exists y; repeat split; auto.
 -
  intros u v (Hmu & Hdu) (Hmv & Hdv).
  specialize (Hd' _ _ Hmu Hmv).
  destruct Hd' as (z & Hmz & Hle1 & Hle2).
  exists z; repeat split; auto.
  intro Habs; subst.
  specialize (le_bot_eq  (C := ACPO2CPO A) u) as Hleu.
  cbn in *.
  apply Hdu.
  now apply Hleu.
}
split; auto.
apply antisym.
-
 apply lub_mono; auto.
 apply remove_subset.
-
 apply forallex_lelub; auto.
 intros x Hmx.
 destruct (oracle (x = abot)); subst.
 +
  exists y; repeat split; auto.
  apply abot_least.
 +
  exists x; repeat split; auto.
  apply refl. 
 Qed.
  
Definition lnbot{A:Type}{B L:A -> Type} := 
  inject (c := LPC A B L) (@Lcbot A B L).

Lemma rev_inj_not_pbot{A:Type}{B L:A -> Type}:
forall (x: LPC A B L),
is_compact x -> 
x <> lnbot -> rev_inj x <> pbot.
Proof.
intros x Hc Hne Habs; apply Hne; clear Hne.
replace x with (inject (c:= LPC A B L) (rev_inj x)); 
[now rewrite Habs| now apply inject_rev_inj].
Qed.

Lemma not_Lcbot_lcnode{A:Type}{B L:A -> Type}
(fc: LFPC A B L):
fc <> Lcbot -> exists a l f p, fc = {| lfpc := lcnode a l f;
lfinsup := p |}.
Proof.
intro Hne.
destruct fc.
cbn in *.
destruct lfpc0.
-
 contradict Hne.
 unfold Lcbot.
 now apply LFPC_equal.
-
 now exists a,l, l0, lfinsup0.
Qed. 

Lemma is_LFPC_inv{A:Type}{B L:A -> Type}(a:A)(l : L a):
forall (f:B a -> lcont A B L),
is_LFPC (lcnode a l f) -> is_finite (support f lcbot) /\
forall b, is_LFPC (f b).
Proof.
intros f Hf.
remember (lcnode a l f) as c.
inversion Hf; subst; [discriminate |].
inversion H1; subst.
apply inj_pair2 in H4,H5; now subst.
Qed.

Lemma compact_lnode_surj{A:Type}{B L:A -> Type}
 (x: LPC A B L):
 is_compact x -> x <> lnbot ->
 exists a  l f, x = inject (c:= LPC A B L) (flcnode a l f).
Proof.
intros Hc Hne.
specialize Hc as Heqx.
apply rev_inj_not_pbot in Heqx; auto.
remember (rev_inj x) as fc.
cbn in *.
apply not_Lcbot_lcnode in Heqx.
destruct Heqx as (a & l & f & p & Heq).
exists a, l.
cbn in *.
specialize p as p'.
apply is_LFPC_inv in p'.
destruct p' as (Hfs & Hab).
remember
 (fun (b: (B a)) =>  {| lfpc := f b; lfinsup := (Hab b)|})
as g.
assert (Hfg : is_finite
(support (fun (b: (B a)) =>  {| lfpc := f b; lfinsup := (Hab b)|}) Lcbot)).
{
 destruct Hfs as (l' & Hm).
 exists l'.
 intros y Hmy.
 apply Hm.
 intro Heqy.
 apply Hmy.
 subst.
 unfold Lcbot.
 now apply LFPC_equal.
}
exists ({| func := (fun (b: (B a)) =>  {| lfpc := f b; lfinsup := (Hab b)|}); fsup := Hfg|}).
replace x with (inject (c := LPC A B L)(rev_inj x)); 
[| now rewrite inject_rev_inj].
f_equal.
rewrite <- Heqfc,Heq.
now apply LFPC_equal.
Qed.


Lemma lnode_flcnode_inject{A:Type}{B L:A -> Type}(a:A) l f:
lnode a l (inject (c:= fLPC a) f) = inject (c:= LPC A B L) (flcnode a l f).
Proof.
rewrite lnode_extends_flcnode; [| apply inject_compact].
now rewrite rev_inj_inject.
Qed.

Lemma lnode_surj_aux1{A:Type}{B L:A -> Type}
(c: LPC A B L):
let S' := (remove (compacts_le c) lnbot) in
is_directed S' -> forall x, member S' x -> 
exists a l f, x = (lnode a l f).
Proof.
intros S Hd x Hmx.
subst S.
destruct Hmx as ((Hc & _) & Hn).
apply compact_lnode_surj in Hc;auto.
destruct Hc as (a & l & f & Heq); subst.
exists a, l, (inject (c:= fLPC a) f).
now rewrite lnode_flcnode_inject.
Qed.


Lemma lnode_surj_aux2{A:Type}{B L:A -> Type}
(c: LPC A B L):
let S' := (remove (compacts_le c) lnbot) in
is_directed S' ->
forall a1 a2 l1 l2 f1 f2, 
member S' (lnode a1 l1 f1) -> member S' (lnode a2 l2 f2) ->
a1 = a2.
Proof.
intros S' Hd' a1 a2 l1 l2 f1 f2 Hm1 Hm2.
specialize (lnode_surj_aux1 _ Hd') as Ha.
replace (remove (compacts_le c) (inject pbot)) with S' in Ha by auto.
destruct Hd' as (_ & Hd').
specialize (Hd' _ _ Hm1 Hm2).
destruct Hd' as (f' & Hmf & Hle1 & Hle2).
destruct (Ha _ Hmf) as (a & l & f & Heq); subst.
apply lnode_ord_same_shape in Hle1,Hle2; congruence.
Qed.


Lemma node_surj_aux3{T T':Type}(S: Setof T)
(f : T' -> T):
(forall x, member S x -> exists y, x = f y)->
S = fmap (fun x => member S (f x)) f.
Proof.
intros Ha.
apply set_equal; intro x; split; intro Hmx.
-
 specialize (Ha _ Hmx).
 destruct Ha as (y & Heq); subst.
 now exists y.
-
 now destruct Hmx as (y & Hmy& Heq); subst.
Qed.

Lemma lnode_surj_aux4{A A': ADCPO}(S:Setof A)(f : A' -> A):
is_bimonotonic f ->
(forall x, member S x -> exists y, x = f y)->
is_directed S -> is_directed  (fun x => member S (f x)).
Proof.
intros Hm Ha  Hd.
split.
-
  rewrite not_empty_member.
  destruct Hd as (Hne & _).
  rewrite not_empty_member in Hne.
  destruct Hne as (x & Hmx).
  specialize (Ha _ Hmx).
  destruct Ha as (y & Heq); subst.
  now exists y.
-
  intros x y Hmx Hmy.
  destruct Hd as (_ & Hd).
  specialize (Hd _ _ Hmx Hmy).
  destruct Hd as (z & Hmz & Hle1 & Hle2).
  destruct (Ha _ Hmz) as (w & Heq); subst.
  apply Hm in Hle1, Hle2.
  exists w; split; auto.
Qed.


Lemma lnode_surj{A:Type}{B L:A -> Type}(c: LPC A B L):
c <> lnbot ->  exists a  l f, c = lnode a l f.
Proof.
intro Hc.
replace c with (lub (compacts_le c)) in Hc; 
[| now rewrite algebraic_lub].
remember (@abot {|adcpo_acpo := LPC A B L;abot := lnbot;
    abot_least :=inject_pbot_least (LPC A B L)|}) as b.
replace lnbot with b in Hc.
rewrite Heqb in Hc.
clear b Heqb.
specialize Hc as Hc'.
apply (remove_bot_directed (A := {|
    adcpo_acpo := LPC A B L;
    abot :=lnbot;
    abot_least := inject_pbot_least (LPC A B L)
  |})(compacts_le c)) in Hc'; [|apply algebraic_dir].
destruct Hc' as (Hd' & Hleq).
cbn in *.
remember (@remove (LPC A B L)
(@compacts_le (LPC A B L) c)
lnbot) as S'.
remember (compacts_le c) as S.
rewrite HeqS',HeqS in Hd'. 
specialize (lnode_surj_aux1 c Hd') as Ha.
cbn in Ha.
rewrite <- HeqS, <- HeqS' in Ha.
specialize Hd' as Hne.
destruct Hne as (Hne & _).
rewrite not_empty_member in Hne.
destruct Hne as (x & Hmx).
rewrite <- HeqS, <- HeqS' in Hmx.
specialize Ha as Ha_cp.
specialize (Ha _ Hmx).
destruct Ha as (a & l & f & Heq).
subst x.
exists a, l.
specialize (lnode_surj_aux2 c Hd') as Ha.
replace (remove (compacts_le c)
(inject pbot)) with S' in * by (subst; auto).
assert (Ha' : forall a' l f, member S' (lnode a' l f) -> a' = a).
{
 intros a' l' f' Hm'.
 rewrite <- HeqS, <-HeqS' in Ha.
 eapply Ha; eauto.
}
assert (Hl' : forall a' l' f, member S' (lnode a' l' f) -> JMeq l l').
{
 intros a' l' f' Hm'.
 rewrite <- HeqS, <-HeqS' in Ha.
 specialize (Ha' _ _ _ Hm'); subst.
 destruct Hd' as (_ & Hd').
 specialize (Hd' _ _ Hmx Hm').
 destruct Hd' as (z & Hmz & Hz & Hz').
 specialize (Ha_cp _ Hmz).
 destruct Ha_cp as (a' & l'' & f'' & Heq); subst.
 specialize Hz' as Hz''.
 apply lnode_ord_same_shape in Hz'; subst.
 apply lnode_ord_labels_eq in Hz,Hz''; subst.
 constructor.
}
clear Ha.
assert (Ha_cp' : forall x : LPC A B L,
member S' x -> exists (y: fLPC a),
  x = lnode a l y).
{
  intros u Hmu.
  destruct (Ha_cp _ Hmu) as (a' & l' & f' & Heq); subst.
  specialize (Ha' _ _ _ Hmu); subst.
  exists f'.
  f_equal.
  specialize (Hl' _ _ _ Hmu).
  inversion Hl'; subst; reflexivity.
}
clear Ha_cp.
remember  (fun x : fLPC a => member S' (lnode a l x))
 as Fa.
specialize (node_surj_aux3 S' (lnode a l) Ha_cp') as Heq'.
assert (Hda : is_directed Fa).
 {
 rewrite HeqFa.
 apply lnode_surj_aux4; auto; [| now subst].
 apply lnode_is_bimonotonic.
 }
 assert (Hec' : c = lub S') by (rewrite Hleq,HeqS;apply algebraic_lub).
 rewrite Heq' in Hec'.
 specialize (lnode_is_continuous (B:= B) a l) as Hca.
 rewrite continuous_iff_mono_commutes in Hca.
 destruct Hca as (Hma & Hca).
 unfold commutes_with_lub in Hca.
 specialize (Hca Fa (lub Fa) Hda (lub_is_lub _ Hda)).
 rewrite <- HeqFa in Hec'.
 apply is_lub_lub_eq1 in Hca; auto; 
 [ | apply monotonic_directed; auto; apply node_is_monotonic].
 rewrite Hec'.
 now exists (lub Fa).
 Qed.

Lemma lnode_lub_fmap_lnode{A:Type}{B L:A -> Type}(a:A)(l : L a)(f : fLPC a):
lnode (B:= B) a l f = lub (fmap (compacts_le f) (lnode a l)).
Proof.
specialize (lnode_is_continuous(B:= B) a l) as Hc.
rewrite continuous_iff_mono_commutes in Hc.
destruct Hc as (Hm & Hc).
unfold commutes_with_lub in Hc.
specialize (Hc (compacts_le f) (lub (compacts_le f)) (algebraic_dir f)
(lub_is_lub _ (algebraic_dir (a := fLPC a)f))).
replace (lub (compacts_le f)) with f in Hc; [| apply algebraic_lub].
apply is_lub_lub_eq1; auto.
apply monotonic_directed; [ apply lnode_is_monotonic | apply algebraic_dir].
Qed.


Lemma lnode_lub_fmap_flcnode{A:Type}{B L:A -> Type}(a:A)(l : L a)
(f : fLPC a):
lnode (B:= B) a l f = 
lub (fmap (compacts_le f)
 ((inject (c := LPC A B L))° (flcnode a l) ° (rev_inj(c := fLPC a)))).
Proof.
rewrite lnode_lub_fmap_lnode.
f_equal.
apply set_equal; split; intro Hmx.
- 
destruct Hmx as (y & Hmy & Heq); subst.
exists y; split; auto.
apply lnode_extends_flcnode; now destruct Hmy.
-
destruct Hmx as (y & Hmy & Heq); subst.
exists y ; split; auto.
symmetry.
apply lnode_extends_flcnode; now destruct Hmy.
Qed.

Lemma lnode_not_lnbot{A:Type}{B L:A -> Type}(a:A)(l : L a)(f : fLPC a):
lnbot <> lnode (B:= B) a l f.
Proof.
intros Habs.
assert (Hle: lnode a l f <= lnbot) by (rewrite Habs; apply refl).
clear Habs.
rewrite lnode_lub_fmap_lnode in Hle.
specialize (algebraic_dir f) as Hd.
specialize Hd as Hne.
destruct Hne as (Hne & _).
rewrite not_empty_member in Hne.
destruct Hne as (g & Hmx).
assert(Hd' : is_directed  (fmap (compacts_le f) (lnode a l))).
{
  apply monotonic_directed; auto.
  apply lnode_is_monotonic.
}
assert (Hm : member (fmap (compacts_le f) (lnode a l)) (lnode a l g)) by
now exists g.
specialize (lub_is_upper _ Hd' (lnode a l g) Hm) as Hu.
assert (Habs: lnode a l g <= lnbot).
{
  eapply trans; [exact Hu | assumption].
}
replace g with (inject (c := fLPC a)(rev_inj g)) in Habs;
[| rewrite inject_rev_inj; auto; now destruct Hmx].
rewrite lnode_flcnode_inject in Habs.
apply inject_bimono in Habs.
inversion Habs.
Qed.


Lemma lcases{A:Type}{B L:A -> Type}(c: LPC A B L):
{a: A & {l : L a & {f: B a -> LPC A B L | c = lnode a l f}}} + 
{c = lnbot}.
Proof.
destruct (oracle (c = lnbot));
 [now right |].
apply lnode_surj in n.
left.
apply constructive_indefinite_description in n.
destruct n as (a & Hex).
apply constructive_indefinite_description in Hex.
destruct Hex as (x & Hex).
apply constructive_indefinite_description in Hex.
destruct Hex as (f & Heq).
now exists a, x, f.
Qed.

Lemma lnbot_least{A:Type}{B L:A -> Type}: forall (c:LPC A B L), 
lnbot <= c.
Proof.
intro c.
destruct (lcases c) as [(a & (l & f & Heq)) | Heq]; subst; [| apply refl].
rewrite lnode_lub_fmap_lnode.
specialize (algebraic_dir (a := fLPC a)f) as Hd.
destruct Hd as (Hne & _).
rewrite not_empty_member in Hne.
destruct Hne as (x & Hmx).
specialize Hmx as Heq.
destruct Heq as (Heq & _).
apply inject_rev_inj in Heq.
apply trans with (y :=  lnode a l x).
-
  rewrite <- Heq.
  rewrite lnode_flcnode_inject.
  unfold lnbot.
  rewrite <- inject_bimono.
  constructor.
-
 apply lub_is_upper.
 +
   apply monotonic_directed; [apply lnode_is_monotonic |].
   apply algebraic_dir.
 +
  now exists x.
Qed.  


Lemma LFPC_ind{A:Type}{B L: A -> Type} 
(P:LFPC A B L -> Prop):
P Lcbot -> 
(forall a l f,
  (forall b, P ((func Lcbot f) b)) -> P (flcnode a l f)
) ->
forall c, P c.
Proof.
intros Hb Ha c.
destruct c as (c & Hfpc).
revert Ha Hfpc.
induction c; intros Ha Hfpc.
-
  replace 
  {| lfpc := lcbot; lfinsup := Hfpc |} 
    with (@Lcbot A B L); auto.
  now apply LFPC_equal.  
-
  specialize Hfpc as Hfpc'.
  inversion Hfpc'; subst; clear Hfpc'.
  apply inj_pair2 in H1,H3; subst.
  unfold flcnode in Ha; cbn in Ha.
  remember (fun b => {| lfpc := l0 b; lfinsup := H4 b |})  as c'.
  assert (Hf' : is_finite (support c' Lcbot)).
  {
   destruct H2 as (l' & Hl).
   exists l'.
   intros b Hm.
   apply Hl.
   intro Heq.
   apply Hm.    
   subst.
   now apply LFPC_equal.
  }
  specialize (Ha a l {| func := c'; fsup := Hf'|}) as Has.
  subst; cbn in Has.
  replace (flcnode_obligation_1 _ _ _ a l
    {|
      func :=
        fun b  =>
        {|
          lfpc := l0 b;
          lfinsup := H4 b
        |};
      fsup := Hf'
    |}) with Hfpc in Has by apply proof_irrelevance.
  apply Has;clear Has. 
  intro b.
  apply H; clear H.
  intros a' l' f Ha'.
  now apply Ha.
 Qed.
    

     

Lemma compact_lnode_compact_func{A:Type}(B L: A -> Type):
forall a l f, is_compact(D := LPC A B L) (lnode a l f) -> 
is_compact (D := fLPC a) f.
Proof.
intros a l f Hc.
apply compact_lnode_surj in Hc; [| intro Habs; symmetry in Habs;
contradict Habs; apply lnode_not_lnbot].
destruct Hc as (a' & l' & f' & Heq).
rewrite <- lnode_flcnode_inject in Heq.
apply lnode_injective in Heq; destruct Heq as (Heq & Hj & Hj').
subst.
apply inject_compact.
Qed.

Lemma compact_lnode_compact_succ{A:Type}(B L: A -> Type):
forall a l f, is_compact(D := LPC A B L) (lnode a l f) -> 
forall (b:B a), is_compact (D := LPC A B L) (f b).
Proof.
intros a l f Hc.
apply compact_lnode_compact_func in Hc.
apply compacts_are_functions_with_finite_support_and_compact_values 
in Hc.
now destruct Hc.
Qed.



Lemma compact_func_compact_lnode{A:Type}(B L: A -> Type):
forall a l f, 
is_compact (D := fLPC a) f -> is_compact(D := LPC A B L) (lnode a l f).
Proof.
intros a l f Hc.
rewrite lnode_extends_flcnode; auto.
apply inject_compact.
Qed. 


 (* coinductive totality = absence of nbot *)
 
Definition _total{A:Type}{B L: A -> Type}
(P : Setof (LPC A B L)): Setof (LPC A B L)  :=
fun c =>
exists a l f, c = lnode a l f /\ forall b, P (f b).

 
Lemma _total_mono{A:Type}{B L: A -> Type}: 
  is_monotonic 
  (P1 := @to_poset (LPC A B L) Prop_poset)
   (P2 := @to_poset (LPC A B L)  Prop_poset) 
  _total.
Proof.
  intros f g Hle c Hwf.
  cbn in *.
  destruct Hwf as (a & (l & (h & Hh & Heq))); subst.
  exists a, l, h; split; auto.
Qed.


Definition total{A:Type}{B L: A -> Type} (c: LPC A B L) :=
    gfp (L := Pred_semilattice) _ _total_mono c.


Lemma total_unfold{A:Type}{B L: A -> Type}: 
  forall (c: LPC A B L), total c <-> 
    exists a l f, c = lnode a l f /\ forall b, total (f b).
Proof. 
  intros t.
  specialize (@Pred_unfold _ _ (@_total_mono A B L)) as Hfu.
  assert (Hi : @gfp
        (@Pred_semilattice (LPC A B L))_ (@_total_mono A B L)t <->
        _total (@gfp (@Pred_semilattice _) _
           ((@_total_mono A B L))) t); auto.
  split ; intro Hx.
  - now rewrite <- Hfu.
  - now rewrite  Hfu.
Qed.    


Lemma total_coind{A:Type}{B L: A -> Type}: 
forall (S:Setof (LPC A B L)),
(forall t, 
 member S t -> 
 exists a l f, t = lnode a l f /\ forall b, member S (f b)) ->
(forall t, member S t -> total t).
Proof.
intros S Hall.
apply pred_coind.
intros x Hmx.
now apply Hall.
Qed.


(*coinductive version of order on PC*)

Inductive _cle{A:Type}{B L: A -> Type}
(R: LPC A B L-> LPC A B L -> Prop):  
    LPC A B L-> LPC A B L-> Prop :=
|_cle_lnbot : forall c, _cle R lnbot c
|_cle_lnode : forall a l f f', 
(forall b, R (f b) (f' b)) -> 
  _cle R (lnode a l f) (lnode a l f').


Lemma _cle_mono{A:Type}{B L: A -> Type}: 
  is_monotonic 
    (P1 := binary_poset) (P2 := binary_poset) 
  (@_cle A B L).
Proof.
intros R R' Hle x y Hsle.
inversion Hsle; subst.
-
  constructor.
-
   constructor; auto.
   intro b.
   cbn in Hle.
   apply Hle.
   inversion Hsle; subst; auto.
Qed.       


Definition cle{A:Type}{B L: A -> Type} (c c': LPC A B L) : Prop :=
gfp (L:= binary_semilattice) _cle _cle_mono c c'.


Lemma cle_unfold{A:Type}{B L: A -> Type} : 
forall (c c': LPC A B L), 
 cle  c c' <-> 
(c = lnbot \/ exists a l f f', c = lnode a l f /\ c' = lnode a l f' /\  
forall b, cle (f b) (f' b)).
Proof.
intros c c'.
specialize (@binary_unfold _ _ _ (@_cle_mono A B L)) as Hfu.
assert (Hi : @gfp (@binary_semilattice  (LPC A B L)
   (LPC A B L)) _cle _cle_mono  c c' <->
_cle (@gfp
   (@binary_semilattice (LPC A B L)  (LPC A B L))
   _cle _cle_mono) c c')
    by (now rewrite <- Hfu).
 split ; intro Hx.
 - 
  unfold cle in Hx.
  rewrite Hi in Hx.
  replace (@gfp (@binary_semilattice (LPC A B L) (LPC A B L))
  _cle _cle_mono) with (@cle A B L) in Hx; auto.
  inversion Hx; subst.
  +
    now left.
  +
    right.
    now exists a,l, f,f'.
 -
   unfold cle.
   rewrite Hi.
   replace (@gfp
  (@binary_semilattice
     (LPC A B L) (LPC A B L))
  _cle _cle_mono) with (@cle A B L); auto.
  destruct Hx as [Hb | (a & l &  f & f' & Heq1 & Heq2& Heq3 )];
   subst; now constructor.
Qed.


Lemma cle_coind{A:Type}{B L: A -> Type}: 
forall (R: binary (LPC A B L)(LPC A B L)),
(forall c c', 
 R c c' -> (c = lnbot \/ exists a l f f', 
 c = lnode a l f /\ c' = lnode a l f' /\  forall b, R (f b) (f' b))) ->
(forall c c', R c c' -> cle c c').
Proof.
intros S Hall.
apply binary_coind.
intros x y Hm.
specialize (Hall _ _ Hm).
destruct Hall as [Hb | (a & l & f & f' & Heq & Heq' & Ha)]; subst;
now constructor.
Qed.




Lemma le_cle{A:Type}{B L: A -> Type}: forall (c c' :LPC A B L),
c <= c' -> cle c c'.
Proof.
apply cle_coind.
intros c c' Hle.
destruct (lcases c) as [(a & l & f & Heq) | Heq]; subst;
destruct (lcases c') as [(a' & l' & f' & Heq') | Heq']; subst.
-
 right.
 specialize Hle as Hle'.
 apply lnode_ord_same_shape in Hle'; subst.
 specialize Hle as Hle'.
 apply lnode_ord_labels_eq in Hle'; subst.
 exists a',l', f,f'; repeat split; auto.
 now apply lnode_ord_func_ord in Hle.
-
 left.
 apply antisym; auto.
 unfold lnbot.
 specialize (inject_pbot_least (LPC A B L)); cbn; now intro Hl.
 -
  now left.
 -
  now left.
 Qed.  


 
Lemma cle_le{A:Type}{B L: A -> Type}: 
forall (c c' :LPC A B L), cle c c' -> c <= c'.
Proof.
intros  c c' Hcle.
 assert (Hd : is_directed ((compacts_le c))) by 
  now apply algebraic_dir.
assert (Hd' : is_directed ((compacts_le c'))) by 
  now apply algebraic_dir.
replace c with (lub (compacts_le c));
[|now rewrite algebraic_lub].
replace c' with (lub (compacts_le c'));
[|now rewrite algebraic_lub].
rewrite <- forallex_iff_lelub; auto ; [|now intros x (Hc & _)].
intros x (Hc & Hle).
replace x with 
  (inject ( c:= LPC A B L) (rev_inj x)) in Hle;
  [|now rewrite inject_rev_inj].
remember (rev_inj x) as c0.
clear Hd Hd'.
revert c c' Hcle x Hc Heqc0 Hle.
induction c0 using LFPC_ind;
 intros c c' Hcle x Hc Heqc0 Hle.
-
 exists lnbot.
 symmetry in Heqc0.
 rewrite (rev_inj_iff (LPC A B L)) in Heqc0; auto.
 rewrite <- Heqc0.
 split; [ |apply refl].
 split; [apply inject_compact|].
 unfold lnbot.
 apply (inject_pbot_least (LPC A B L)).
-
symmetry in Heqc0.
rewrite (rev_inj_iff (LPC A B L)) in Heqc0; auto.
rewrite <- Heqc0.
rewrite cle_unfold in Hcle.
destruct Hcle as [Heq | (a' & l' & g & g' & Heq & Heq' & Ha')].
+ 
rewrite <- lnode_flcnode_inject in Hle.
subst.
assert (Heq: lnode a l (inject (c := fLPC a) f ) = lnbot). 
{
  apply antisym; auto.
  apply (inject_pbot_least (LPC A B L)).
}
symmetry in Heq.
contradict Heq.
apply  lnode_not_lnbot.
+
 subst.
 assert (Heqa' : a' = a).
 {
  rewrite <- lnode_flcnode_inject in Hle.
  now apply lnode_ord_same_shape in Hle.
 }
 subst.
 assert (HI : forall (b: B a),
        exists y, member (compacts_le (g' b)) y /\
        inject (c:= LPC A B L) (func Lcbot f b) <=  y 
        ).
{
  cbn.
  intro b.
  specialize (H b _ _ (Ha' b) (inject (c:= LPC A B L)(func Lcbot f b))).
  assert (Hcl : is_compact ((inject (c:= LPC A B L)(func Lcbot f b)))) by apply inject_compact.
  specialize (H Hcl).
  rewrite rev_inj_inject in H.
  specialize (H (eq_refl _)).
  rewrite <- lnode_flcnode_inject in Hle.
  apply lnode_ord_func_ord in Hle.
  specialize (Hle b); auto.
}
 cbn in HI.
 clear H.
 apply functional_choice in HI.
 destruct HI as (h & Hah).
 remember (rev_inj (c := LPC A B L) ° h) as h'.
 cbn in h'.
 remember (fun (b:B a) => if (oracle
  (member (support (func Lcbot f) Lcbot) b) )
then h' b else Lcbot) as h''.
assert (Hfin : is_finite (support h'' Lcbot)).
{
   destruct f as (f & (l'' & Hl)); cbn in *.
   exists l''.
   intros x Hm.
   apply Hl.
   intro Heqf.
   apply Hm.
   subst.
   unfold support, member.
   destruct (oracle (f x <> Lcbot)); [contradiction | auto].
}
remember {| func := h''; fsup := Hfin|} as k.
exists (inject (c := LPC A B L)(flcnode a l' k)).
repeat split; [apply inject_compact  | |].
subst; cbn.
*
 rewrite <-lnode_flcnode_inject.
 apply lnode_is_monotonic.
 intro b.
 cbn.
 destruct ( oracle (@member (B a) (@support (B a)
 (LFPC A B L) (func Lcbot f) (@Lcbot A B L)) b)).
  {
   unfold "°".
   destruct  (Hah b) as ((Hcb & Hleb) & _).
   rewrite inject_rev_inj; auto.
  }
  apply (inject_pbot_least (LPC A B L)).
 *
  apply inject_bimono.
  rewrite <- lnode_flcnode_inject in Hle.
  apply lnode_ord_labels_eq in Hle; subst.
  apply flcnode_mono.
  intro b.
  subst.
  cbn.
  destruct (oracle(@member (B a)(@support (B a) 
  (LFPC A B L)  (func Lcbot f) (@Lcbot A B L)) b)).
  {
    destruct  (Hah b) as ((Hcw & Hlew) & Hi).
    cbn.
    replace (h b) with (inject (c := LPC A B L)(rev_inj (h b))) in Hi; [ | rewrite inject_rev_inj; auto].
    now apply inject_bimono in Hi.
  }
   unfold member, support in n.
   assert (func Lcbot f b = Lcbot)  by tauto.
   rewrite H.
   constructor.
Qed.   


Definition bisim{A:Type}{B L:A->Type}(c c' : LPC A B L) :=
  cle c c' /\ cle c' c.
  

  Lemma bisim_unfold{A:Type}{B L: A -> Type} : 
  forall (c c': LPC A B L), 
   bisim  c c' <-> 
  (c = lnbot  /\ c' = lnbot \/ 
  exists a l f f', c = lnode a l f /\ c' = lnode a l f' /\  
    forall b, bisim (f b) (f' b)).
  Proof.
  intros c c'.
  split.
  -
    intros (Hc & Hc').
    apply cle_unfold in Hc, Hc'.
    destruct Hc as [Heq | (a & l & f & f' & Heq1 & Heq2 & Ha)];
    subst;
    destruct Hc' as [Heq | (a1 & l1 & f1 & f'1 & Heq1 & Heq2 & Ha')];
    subst.
    + now left.
    + contradict Heq2;  apply lnode_not_lnbot.
    +  symmetry in Heq;  contradict Heq;  apply lnode_not_lnbot.
    +
     right.
     apply lnode_injective in Heq1,Heq2.
     destruct Heq1 as (Heq1 & Heq'1 & Heq''1); subst.
     destruct Heq2 as (Heq2 & Heq'2 & Heq''2); subst.
     exists a1,  l1, f'1, f1; repeat split; auto.
 -
  intros [(Heq1 & Heq2) | (a & l & f & f' & Heq1 & Heq2 & Ha)];subst.
  +
   split; apply le_cle; apply inject_bimono; apply Lcbot_least.
  +
   split; apply le_cle; apply lnode_is_monotonic; 
   intro b; destruct (Ha b) as (Hc & Hc'); 
   now apply cle_le in Hc, Hc'.
Qed.   
  
  
Lemma bisim_coind{A:Type}{B L: A -> Type}: 
  forall (R: binary (LPC A B L)(LPC A B L)),
  (forall c c', 
   R c c' -> (c = lnbot /\ c' =lnbot  \/ exists a l f f', 
   c = lnode a l f /\ c' = lnode a l f' /\  forall b, R (f b) (f' b))) ->
  (forall c c', R c c' -> bisim c c').
  Proof.
  intros R Ha c c' HR; split.
  - 
   apply cle_coind with (R := R); auto.
   intros u v Huv.
   specialize (Ha _ _ Huv).
   destruct Ha as [(Heq1 & Heq2) | (a & l & f & f' & Heq1 & Heq2 & Ha)];
   subst.
   + 
    now left.
   +
    right.
    exists a, l, f, f'; repeat split; auto.
 -  
 apply cle_coind with (R := fun x y => R y x); auto.
 intros u v Huv.
 specialize (Ha _ _ Huv).
 destruct Ha as [(Heq1 & Heq2) | (a & l & f & f' & Heq1 & Heq2 & Ha)];
 subst.
 + 
  now left.
 +
  right.
  exists a,l, f', f; repeat split; auto.
Qed.


Lemma bisim_iff_eq{A:Type}{B L: A -> Type}:
forall (c c':LPC A B L), 
   bisim c c' <-> c = c'.
Proof.
split; intro Hb.
-
 destruct Hb as (Hc & Hc').
 apply cle_le in Hc,Hc'.
 now apply antisym.
-
 subst.
 split; apply le_cle,refl.
Qed.  

