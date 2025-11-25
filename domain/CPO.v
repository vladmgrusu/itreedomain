From Stdlib Require Import IndefiniteDescription ProofIrrelevance.
From Domain Require Export DCPO PPO.


Record CPO : Type := {
    dcpo_cpo :> DCPO;
    bot : dcpo_cpo;
    bot_least: forall (x:dcpo_cpo), bot <= x
}.


Arguments dcpo_cpo {_}.
Arguments bot {_}.
Arguments bot_least {_} _.

Lemma le_bot_eq{C:CPO} : forall (x:C),
x <= bot -> x = bot.
Proof.
intros x Hle.
apply antisym; auto.
apply bot_least.
Qed.


Definition CPO2PPO(C:CPO) : PPO :=
    {|
       poset_ppo := C.(dcpo_poset) ;
       pbot := bot;
       pbot_least := bot_least;
    |}. 


