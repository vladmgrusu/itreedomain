From Stdlib Require Export FunctionalExtensionality
PropExtensionality PeanoNat.
From Domain Require Export Haddock.
From Monad Require Export Monad.


Local Close Scope nat_scope.

Section Iter.

Variable M : MONAD.

Definition iterF
  [Y : Type] (m : M (unit + Y)) (rec : M Y) : M Y :=
do r <- m;
match r with
| inl x' => rec 
| inr y => ret M y
end.

Definition iter [Y : Type] (m: M (unit + Y))  : M Y :=
ffix (iterF m).



Lemma iterF_is_monotonic [Y : Type] (m:M (unit + Y)) :
@is_monotonic (M Y)  (M Y) (iterF m).
Proof.
intros f1 f2 Hle.
unfold iterF.
specialize (bind_continuous_snd M  (X := sum unit Y) Y m) as Hc.
rewrite continuous_iff_mono_commutes in Hc.
destruct Hc as (Hm & _).
apply Hm.
intros [ l| r ].
 - apply Hle.
 - apply refl.
Qed.

Lemma iterF_is_continuous [Y : Type] (m: M (unit + Y)) :
is_continuous (iterF m).
Proof.
intros T Hd.
unfold iterF.
split.
{
  apply monotonic_directed;auto.
  now apply iterF_is_monotonic.
}
assert (Hd' : is_directed
(P := EXP_Poset (unit + Y) (M Y))
(fmap T
   (fun (m : M Y) (c : unit + Y) =>
    match c with
    | inl _ => m
    | inr y => ret M y
    end)) ).
{
    apply (monotonic_directed
    (P1 := (M Y))
    (P2 := EXP_Poset (unit+Y) (M Y)));
    auto.
    intros u v Hle [x' | y'];
    [apply Hle | apply refl].
}
specialize (bind_continuous_snd M Y m) as Hc.
unfold is_continuous in Hc.
specialize (Hc (fmap T (fun (m:M Y) => 
fun (c : unit + Y) =>
match c with
inl x => m
|inr y => ret _ y
end
))).
rewrite <- fmap_comp in Hc.
unfold "°" in Hc.
specialize (Hc Hd').
destruct Hc  as (Hc1 & Hc2).
rewrite <- Hc2.
f_equal.
extensionality lr.
cbn.
destruct (oracle
     (is_directed
     (P := (EXP_Poset (unit + Y) (M Y)))
        (fmap T
           (fun (m: M Y) (c : unit + Y) =>
            match c with
            | inl _ => m
            | inr y => ret M y
            end))));
            [|contradiction].
destruct lr as  [ l | r].
-
 cbn. 
 f_equal.
 rewrite proj_fmap.
 rewrite <-fmap_comp.
 unfold "°".
 now rewrite fmap_id.
 -
  cbn. 
  rewrite proj_fmap.
  rewrite <-fmap_comp.
  unfold "°".
  rewrite fmap_cst.
  +
    now rewrite lub_single.
  +
     now destruct Hd.
Qed.     



Lemma iter_fixpoint (Y : Type) (m: M (unit + Y)) :
iter m =
do r <- m;
match r with
| inl _ => iter m
| inr y => ret M y
end.
Proof.
specialize (Kleene _ (iterF_is_continuous m)) as Hk.
now destruct Hk.
Qed.




Definition while (cond : M bool) (body : M unit) : M unit :=
iter
  (
    do b <- cond;
    if b then body;; ret M (inl tt) else ret M (inr tt)).

Notation "'While' cond {{ body }}" := (@while cond body) : monad_scope.


Definition iter_fuel [Y : Type] (n:nat) (m: M (unit + Y))  : M Y :=
iterate n bot (iterF m).

Lemma iter_fuel_S [Y : Type] (n:nat) (m: M (unit + Y))  :
iter_fuel (S n) m =
do r <- m;
match r with
| inl _ => iter_fuel n m
| inr y => ret M y
end.
Proof.
reflexivity.
Defined.

Definition while_fuel (n:nat) (cond : M bool) (body : M unit) : M unit :=
iter_fuel n
  (
    do b <- cond;
    if b then body;; ret M (inl tt) else ret M (inr tt)).

Lemma while_fuel_S (n : nat) (cond : M bool) (body : M unit) :
while_fuel (S n) cond body =
If cond then (body ;; while_fuel n  cond body) else ret M tt.
Proof.
unfold while_fuel at 1.
rewrite iter_fuel_S, bind_assoc.
f_equal.
extensionality b.
destruct b.
- rewrite bind_assoc, ret_left.
  reflexivity.
- rewrite ret_left.
  reflexivity.
Qed.

Lemma while_fixpoint (cond : M bool) (body : M unit) :
While cond {{ body }} =
If cond then (body ;; While cond {{ body}}) else ret M tt.
Proof.
unfold while.
rewrite iter_fixpoint at 1.
rewrite bind_assoc.
apply f_equal.
extensionality b.
destruct b.
- rewrite bind_assoc, ret_left.
  reflexivity.
- apply ret_left.
Qed.


Definition whileF(cond : M bool) (rec: M unit) 
:=
iterF  (
  do b <- cond;
  if b then rec ;; ret M (inl tt) else ret M (inr tt)).


Lemma whileF_is_monotonic (cond : M bool)(body:M unit) :
  is_monotonic (P1 := M unit) (P2 := M unit) (whileF cond body).
  Proof.
apply iterF_is_monotonic.
Qed.  


Lemma while_fuel_iterate_whileF (cond : M bool)(body:M unit)(n:nat) :
while_fuel n cond  body = 
iterate n bot (whileF cond  body).
Proof.
reflexivity.
Qed.


Lemma while_fuel_sum(cond : M bool)(body:M unit)(n m:nat):
while_fuel (n+m) cond body =
iterate  n (while_fuel m cond  body)  (whileF cond body).
Proof.
repeat rewrite while_fuel_iterate_whileF.
apply iterate_sum.
Qed.


Lemma while_whileF (cond : M bool) (body : M unit) :
while cond  body = whileF cond body (while cond  body).
Proof.
apply iter_fixpoint.
Qed.




Lemma while_lub_while_fuel (c : M bool) (b : M unit) :
while c b= lub (fun x => exists n, x = while_fuel n c b).
Proof.
reflexivity.
Defined.

Lemma iter_ret_inl{Y:Type}: iter (Y := Y) (ret M (inl tt)) = bot.
Proof.
unfold iter,ffix.
apply antisym; [| apply bot_least].
apply lub_is_minimal.
 - 
  apply iterate_directed.
  apply iterF_is_monotonic.
-
 intros x (n & Heq); subst.
 induction n.
 + 
  apply refl.
 +
  cbn.
  apply le_bot_eq in IHn.
  rewrite IHn.
  unfold iterF.
  rewrite ret_left.
  apply refl.
Qed.   

Lemma iter_ret_inr{Y:Type}(y:Y):iter (Y:= Y) (ret M (inr y)) = ret M y.
Proof.
unfold iter,ffix.
apply antisym.
-
  apply lub_is_minimal.
  + 
  apply iterate_directed, iterF_is_monotonic.
  +
   intros x (n & Heq);subst.
   induction n.
   *
    apply bot_least.
   *
    cbn.
    apply trans with (y := iterF (ret M (inr y)) (ret M y));
      [ now apply iterF_is_monotonic | ].
    unfold iterF.
    rewrite ret_left.
    apply refl.
-
  apply lub_is_upper;   
  [apply iterate_directed, iterF_is_monotonic |].
  exists (S O).
  cbn.
  unfold iterF.
  now rewrite ret_left.
Qed.

End Iter.

Notation "'While' cond {{ body }}" := (@while _ cond body) : monad_scope.

Lemma mmor_iter
  (M1 M2 : MONAD) (X : Type) (m : M1 (unit + X)) (f : MONAD_MORPHISM M1 M2) :
f X (iter M1 m) = iter M2 (f (unit + X) m).
Proof.
unfold iter,ffix.
specialize (mmor_continuous f X) as Hc.
unfold is_continuous in Hc.
specialize (Hc (fun x : M1 X =>
exists n : nat,
  x =
  iterate n bot
    (iterF M1 m))).
assert (Hd' : is_directed
(fun x : M1 X =>
      exists n : nat,
        x =
        iterate n bot
          (iterF M1 m))).
{
  apply iterate_directed.
  apply iterF_is_monotonic.
}
specialize (Hc Hd').
destruct Hc as (Hc1 & Hc2).
cbn in *.
rewrite Hc2.
f_equal.
extensionality my.
apply propositional_extensionality.
split; intro Hp.
{
  destruct Hp as (mf & (n & Heq') & Heq).
  subst.
  exists n.
  induction n.
  -
   cbn.
   now rewrite mmor_strict.
  -
   cbn.
   unfold iterF at 1.
   destruct f; cbn in *.
   rewrite mmor_bind.
   unfold iterF at 2.
   f_equal.
   extensionality u.
   destruct u.
   +
    apply IHn.
   +
    now rewrite mmor_ret.
}      
{
   destruct Hp as (n & Heq); subst.
   unfold fmap.
   exists ( iterate n bot (iterF M1 m)).
   split; [now exists n |].
   induction n.
  -
   cbn.

   now rewrite mmor_strict.
  -
   cbn.
   unfold iterF at 1 3.
   destruct f; cbn in *.
   rewrite mmor_bind.
   f_equal.
   extensionality lr.
   destruct lr as [ [] | r].
   +
    apply IHn.
   +
    now rewrite mmor_ret.
}
Qed.



Lemma mmor_while
  (M1 M2 : MONAD) (cond : M1 bool) (body : M1 unit)
 (f : MONAD_MORPHISM M1 M2) :
f unit (While cond {{ body }}) = While f bool cond {{ f unit body }}.
Proof.
unfold while.
rewrite mmor_iter, mmor_bind.
do 2 f_equal.
extensionality b.
destruct b.
- rewrite mmor_bind, mmor_ret.
  reflexivity.
- rewrite mmor_ret.
  reflexivity.
Qed.
