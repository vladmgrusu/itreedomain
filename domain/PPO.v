From Stdlib Require Import IndefiniteDescription ProofIrrelevance.
From Domain Require Export Poset.


Record PPO : Type := {
    poset_ppo :> Poset;
    pbot : poset_ppo;
    pbot_least: forall (x:poset_ppo), pbot <= x
}.


Arguments poset_ppo {_}.
Arguments pbot {_}.
Arguments pbot_least {_} _.

Lemma le_bot_eq{C:PPO} : forall (x:C),
x <= pbot -> x = pbot.
Proof.
intros x Hle.
apply antisym; auto.
apply pbot_least.
Qed.


Lemma pbot_is_compact{P:PPO}: is_compact (D := P) pbot.
Proof.
intros S (Hne & _) Hle.
rewrite not_empty_member in Hne.
destruct Hne as (x & Hmx).
exists x; split; auto.
apply pbot_least.
Qed.

Lemma empty_upper_pbot{P:PPO}: forall (S : Setof P),
is_empty S -> is_upper S pbot.
Proof.
intros S He x Hm.
unfold is_empty in He.
rewrite He in Hm.
inversion Hm.
Qed.


Lemma single_pbot_upper_pbot{P:PPO}: 
is_upper (single (@pbot P)) pbot.
Proof.
intros x Hm.
rewrite member_single_iff in Hm.
subst.
apply refl.
Qed.


Lemma is_upper_pbot_empty_single{P:PPO}: forall (S : Setof P),
is_upper S pbot -> is_empty S \/ S = single pbot.
Proof.
intros S Hu.
destruct (oracle (is_empty S)); [now left | right].
rewrite not_empty_member in n.
destruct n as (x & m).
apply set_equal; intro y ; split ; intro Hm.
-
 specialize (Hu _ Hm).
 apply le_bot_eq in Hu; subst.
 apply member_single.
-
 rewrite member_single_iff in Hm; subst.
 specialize (Hu _ m).
 apply le_bot_eq in Hu; now subst.
Qed.


Lemma is_upper_pbot_empty_single_iff{P:PPO}: forall (S : Setof P),
is_upper S pbot <-> is_empty S \/ S = single pbot.
Proof.
split.
- 
 apply is_upper_pbot_empty_single.
-
 intros [He | Hs].
 +
  now apply empty_upper_pbot.
 +
  subst.
  apply single_pbot_upper_pbot.
Qed.  
  

Lemma is_lub_remove_bot{P : PPO}:
  forall (S: Setof P) (l : P),
    ~ is_empty S ->
  S <> single (pbot) -> is_lub S l <-> is_lub (remove S pbot) l.
Proof.
intros S l Hne Hns.
rewrite not_empty_member in Hne.
destruct Hne as (a & Hma).
split; intro Hl ; auto.  
- 
  split.
  +
    intros x Hm.
    destruct Hm as (Hm & _).
    destruct Hl as (Hu & _).
    now apply Hu.
  +
    intros y Hu'.
    destruct Hl as (Hu & Hmin).
    apply Hmin.
    intros x Hmx.
    destruct (oracle (x= pbot)); subst; [ apply pbot_least |].
    apply Hu'.
    split; auto.
-    
  split.
  +
    intros y Hu'.
    destruct Hl as (Hu & Hmin).
    destruct (oracle (y= pbot)); subst; [ apply pbot_least |].
    apply Hu.
    split; auto.
  +
    intros y Hu'.
    destruct Hl as (Hu & Hmin).
    apply Hmin.
    intros x Hmx.
    apply (Hu' x).
    now destruct Hmx.
Qed.   


Lemma remove_pbot_directed{P : PPO}:
  forall (S: Setof P),
is_directed S -> S <> single pbot ->
is_directed (remove S pbot).
Proof.
intros S Hd Hns.
destruct Hd as (Hne & Hd).
split.
-
 eapply not_empty_not_single_2dif in Hne;
 eauto.
 destruct Hne as (y & Hmy & Hne).
 rewrite not_empty_member.
 now exists y.
-
intros x y (Hmx & Hdx) (Hmy & Hdy).
specialize (Hd _ _ Hmx Hmy).
destruct Hd as (z & Hmz & Hle1 & Hle2).
exists z ; repeat split; auto.
intro Habs; subst.
apply PPO.le_bot_eq in Hle2; subst.
contradiction.
Qed.
