From Stdlib Require Import IndefiniteDescription ProofIrrelevance.
From Domain Require Export CPO.

Inductive LIFT (A:Type) : Type :=
lift : A -> LIFT A
| lbot : LIFT A.

Arguments lift {_} _.
Arguments lbot {_}.

Program Definition LIFT_Poset(A:Poset):Poset :=
{|
carrier :=  LIFT A;
default := lbot;
ord := fun x y => 
x = lbot \/ exists u v, x = lift u /\ y = lift v /\ u <= v;
|}.

Next Obligation.
destruct x; [right | now left].
exists c,c; repeat split; auto.
apply refl.
Qed.

Next Obligation.
destruct H as [Heq | (u & v & Hequ & Heqv & Hleuv)]; subst; 
[now left | right].
destruct H0 as [Habs | (u' & v' & Hequ' & Heqv' & Hleuv')]; subst; 
[discriminate | ].
injection Hequ'; intros; subst; clear Hequ'.
exists u,v'; repeat split; auto.
eapply trans; eauto.
Qed.

Next Obligation.
destruct H as [Heq | (u & v & Hequ & Heqv & Hleuv)]; subst;
destruct H0 as [Habs | (u' & v' & Hequ' & Heqv' & Hleuv')]; subst;
auto; try discriminate.
injection Hequ'; intros; subst; clear Hequ'.
injection Heqv'; intros; subst; clear Heqv'.
f_equal.
now apply antisym.
Qed.

Global Obligation Tactic := idtac.
Program Definition LIFT_PPO(A:Poset):PPO :=
{|
poset_ppo := LIFT_Poset A;
pbot := lbot;
|}.

Next Obligation.
intros a x.
destruct x.
-
 now left.
-
 apply refl.
Qed. 


Lemma lift_is_monotonic{A:Poset}:
is_monotonic (P1 := A) (P2 := LIFT_Poset A) lift.
Proof.
intros x y Hle.
right.
exists x, y; repeat split; auto.
Qed.


Lemma lift_is_rev_monotonic{A:Poset}:
is_rev_monotonic (P1 := A) (P2 := LIFT_Poset A) lift.
Proof.
intros x y Hle.
destruct Hle as [Habs | (u & v & Hequ & Heqv & Hle)];
[discriminate | subst].
injection Hequ; intros; subst.
injection Heqv; intros; now subst.
Qed.


Lemma is_directed_lift_right{A:Poset}(S : Setof A):
is_directed (P := A) S -> is_directed (P := LIFT_Poset A)
(fmap S lift).
Proof.
intro Hd.
apply @monotonic_directed ;auto.
apply lift_is_monotonic.
Qed.


Lemma no_lbot_all_lift{A:Type}(S: Setof (LIFT A)):
~member S lbot -> forall x,  member S x -> exists y, x = lift y.
Proof.
intros Hnm x Hm.
destruct x.
-
 now exists a.
- 
 contradiction.
Qed.

Lemma no_lbot_all_lift_sig {A:Type} (S: Setof (LIFT A)): ~member S lbot -> 
forall (u:{x : LIFT A | member S x}),exists y, proj1_sig u = lift y.
Proof.
intros Hnm (x &  Hmx).
cbn.
now apply no_lbot_all_lift in Hmx.
Qed.


Lemma no_lbot_sig_all_lift {A:Type} (S: Setof (LIFT A)): ~member S lbot
-> exists f  :{x : LIFT A | member S x} -> A, 
forall u, proj1_sig u = lift (f u).
Proof.
intro Hnm.
apply (functional_choice (fun (u:{x : LIFT A | member S x}) (v : A) =>
proj1_sig u = lift v)).
now apply  no_lbot_all_lift_sig.
Qed.


Lemma no_lbot_ex_func_lift {A:Poset} (S: Setof (LIFT A)): ~member S lbot
-> exists f : LIFT A -> A, forall x, member S x -> 
x  = lift (f x).
Proof.
intro Hnm.
apply no_lbot_sig_all_lift in Hnm.
destruct Hnm as (g & Hg).
eexists  (fun (x: LIFT A) => 
match (oracle (member S x) ) with
left Hmx =>
g (exist _ x Hmx)
| right _ => default
end).
intros x Hmx.
specialize (Hg (exist _ x Hmx)).
cbn in Hg.
destruct  (oracle (member S x)); [| contradiction].
now replace m with Hmx by apply proof_irrelevance.
Qed.


Definition extract_sig {A:Poset} (S: Setof (LIFT A)): ~member S lbot ->
{f : LIFT A -> A | forall x, member S x -> 
x  = lift (f x)}.
Proof.
intro Hnm.
apply constructive_indefinite_description.
now apply no_lbot_ex_func_lift.
Defined.

Definition extract {A:Poset} (S: Setof (LIFT A))(Hnm:~member S lbot) :
LIFT A -> A := proj1_sig (extract_sig S Hnm).

Lemma lift_extract{A:Poset} (S: Setof (LIFT A))(Hnm:~member S lbot) :
forall x, member S x -> x = lift (extract _ Hnm x).
Proof.
unfold extract,extract_sig.
apply proj2_sig.
Qed.

Lemma extract_lift{A:Poset} (S: Setof (LIFT A))(Hnm:~member S lbot)(a:A) :
member S (lift a) -> extract _ Hnm (lift a) = a.
Proof.
intros Hm.
apply antisym.
-
 apply lift_is_rev_monotonic.
 rewrite <- lift_extract; auto.
 apply refl.
-
 apply lift_is_rev_monotonic.
 rewrite <- lift_extract; auto.
 apply refl.
Qed.

Lemma extract_mono{A:Poset} (S: Setof (LIFT A))(Hnm:~member S lbot):
is_monotonic_on (P1 := LIFT_Poset A) (P2 := A)
(extract S Hnm) S.
Proof.
intros x y Hmx Hmy  Hle.
apply lift_is_rev_monotonic.
do 2 (rewrite <- lift_extract; auto).
Qed.



Lemma lub_lift_extract{A: DCPO}
(S: Setof (LIFT A)):
 is_directed  (P := LIFT_Poset A) S ->
 S <> single lbot ->
is_lub (P := LIFT_Poset A) S 
(lift (lub (d := A)(fmap (remove S lbot) (extract
(remove S lbot)
(remove_not_member
   S lbot))))).
Proof.
intros Hd Hne.
assert (Hne' : ~is_empty (remove S lbot)).
{
 destruct Hd as (Hnem &  _).
 eapply  not_empty_not_single_2dif in Hnem;
 eauto.
 rewrite not_empty_member.
 destruct Hnem as (y & Hmy & Hney).
 subst.
 exists y; repeat split;auto.
}
assert (is_directed (P := LIFT_Poset A) (remove S lbot)).
{
  split; auto.
  destruct Hd as (_ & Hd).
  subst.
  intros x y (Hmx & Hnx) (Hmy & Hny).
  specialize (Hd _ _ Hmx Hmy).
  destruct Hd as (z  & Hmz & Hxz & Hyz).
  exists z; repeat split; auto.
  intro Heq; subst.
  cbn in *.
  destruct Hyz as [Heq | (u & v & _ & Habs & _)]; 
  [contradiction |discriminate].
}
remember ((extract
(remove S lbot)
(remove_not_member
   S lbot))) as extra.
remember (fmap
(remove S lbot) extra) as S'.
assert (Hd' : is_directed (P := A) S').
{
 rewrite HeqS'.
 apply (@monotonic_on_directed (LIFT_Poset A) A (remove S lbot) extra);
 auto.
 subst.
 apply extract_mono.
} 
specialize (lub_is_lub _ Hd') as Hl.
split.
-
 intros x Hmx.
 destruct x.
 + 
  apply lift_is_monotonic.
  apply lub_is_upper; auto.
  subst.
  exists (lift c); repeat split; auto.
  * 
  intro Habs; discriminate Habs.
  *
    rewrite extract_lift;auto.
    split; auto.
    intro ; discriminate.
 +
  now left.
-
 intros y Huy.
 destruct Hl as (Hu & Hm).
 destruct y.
 {
    subst.
    apply lift_is_monotonic.
    apply Hm.
    intros x (u & (Hmu & Hnu) & Heq); subst.
    apply lift_is_rev_monotonic.
    apply Huy.
    rewrite <- lift_extract; auto.
    split;auto.
 }   
 destruct Hd as (Hn & _).
 rewrite (is_upper_pbot_empty_single_iff (P := LIFT_PPO A)) in Huy.
 tauto.
Qed.


Program Definition LIFT_DCPO(A:DCPO) : DCPO :=
 {|   
 dcpo_poset := LIFT_Poset A;
 lub :=  fun S  => 
 if  (oracle (S = single lbot)) then lbot
    else lift (A := A) (lub (d := A) 
     (fmap (remove S lbot)
           (extract (remove S lbot) (remove_not_member S lbot) )))
 |}.

Next Obligation.
intros A S Hd.
cbn.
destruct (oracle (is_directed (P := LIFT_Poset A) S));
[ | contradiction].
remember (oracle
(@eq (Setof (LIFT (@carrier (@dcpo_poset A)))) S
   (@single (LIFT (@carrier (@dcpo_poset A)))
      (@lbot (@carrier (@dcpo_poset A)))))) as o.
destruct o;subst;
[apply @is_lub_single |].
now apply lub_lift_extract.
Qed.


Program Definition LIFT_CPO (A:DCPO) : CPO :=
{| 
dcpo_cpo := LIFT_DCPO A;
bot := lbot
|}.

Next Obligation.
intros a x.
destruct x.
-
 now left.
-
 apply refl.
Qed. 
