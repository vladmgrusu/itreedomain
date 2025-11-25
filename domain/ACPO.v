From Stdlib Require Import IndefiniteDescription ProofIrrelevance.
From Domain Require Export ADCPO CPO.


Record ACPO : Type := {
    adcpo_acpo :> ADCPO;
    abot : adcpo_acpo;
    abot_least: forall (x:adcpo_acpo), abot <= x
}.


Arguments adcpo_acpo {_}.
Arguments abot {_}.
Arguments abot_least {_} _.

Definition ACPO2CPO (A : ACPO) : CPO :=
{|
  dcpo_cpo := @algebraic_dcpo (@adcpo_acpo A);
  bot := @abot A;
  bot_least := @abot_least A
|}.





