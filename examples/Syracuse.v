From Stdlib Require Export Bool NArith IndefiniteDescription.
From Monad Require Export Iter.
From StateT Require Export Equiv.
From Examples Require Export Lib.

Local Notation "m1 == m2" :=
  (@itree_equiv _ _ _ m1 m2) (at level 70, no associativity).

Definition Nget : itree_monad (stateT_effect N) nat :=
do x <- fget; ret _ (N.to_nat x).

Definition Nput (n : nat) : itree_monad (stateT_effect N) unit :=
fput (N.of_nat n).

Definition fsyracuse (n : nat) : itree_monad (stateT_effect N) nat :=
Nput n ;;
While do x <- Nget; ret _ (negb (x =? 1)) {{
  do x <- Nget;
  if Nat.even x then Nput (x / 2) else Nput (1 + 3 * x)
}} ;;
Nget.

Definition fsyracuse_N (n : N) : itree_monad (stateT_effect N) N :=
fput n ;;
While do x <- fget; ret _ (negb (x =? 1)%N) {{
  do x <- fget;
  if N.even x then fput (N.div2 x) else fput (1 + 3 * x)%N
}} ;;
fget.

Lemma fsyracuse_N_correct (n : N) :
itree_equiv (stateT_effect N) (stateT_step N)
  (fsyracuse_N n) (do x <- fsyracuse (N.to_nat n); ret _ (N.of_nat x)).
Proof.
unfold fsyracuse, Nput, Nget, fsyracuse_N.
rewrite N2Nat.id, bind_assoc, bind_assoc, bind_assoc, bind_assoc, bind_assoc.
eapply itree_bind_congr; [reflexivity | intros []].
etransitivity.
2:{
  apply itree_bind_congr.
  - apply itree_while_congr.
    + apply itree_bind_congr; [reflexivity | ].
      intro x.
      rewrite ret_left.
      apply itree_refl.
    + apply itree_bind_congr; [reflexivity | ].
      intro x.
      rewrite ret_left.
      apply itree_refl.
  - intros [].
    etransitivity.
    2:{
      apply itree_bind_congr; [reflexivity | ].
      intro x.
      rewrite ret_left, N2Nat.id.
      apply itree_refl.
    }
    rewrite ret_right.
    change fget with ((fun t => @fget N) tt).
    reflexivity.
}
cbn beta.
apply itree_bind_congr; [ | reflexivity].
apply itree_while_congr.
- apply itree_bind_congr; [reflexivity | ].
  intro x.
  rewrite Neqb2nat.
  reflexivity.
- apply itree_bind_congr; [reflexivity | ].
  intro x.
  rewrite Neven2nat.
  destruct Nat.even.
  + rewrite <- Nat.div2_div, <- N2Nat.inj_div2, N2Nat.id.
    reflexivity.
  + rewrite Nat2N.inj_add, Nat2N.inj_mul, N2Nat.id.
    reflexivity.
Qed.

Definition fwhile_pos_even_div2 : itree_monad (stateT_effect N) unit :=
While do x <- fget; ret _ (N.even x) {{
  do x <- fget;
  fput (N.div2 x)
}}.

Lemma while_fuel_0 (M : MONAD) (cond : M bool) (body : M unit) :
while_fuel M 0 cond body = bot.
Proof.
reflexivity.
Defined.

Fixpoint nb_iter (n:N) (i:nat) : nat :=
match i with
| 0 => 0
| S j => 
  if (negb (n =? 1)%N) then
    if N.even n
    then (nb_iter (while_even_div2 n) j) + nb_zeros n
    else S (nb_iter (1+ 3*n)%N j)
  else i
end.

Lemma while_even_div2_eq_0 (n : N) :
while_even_div2 n = 0%N -> n =0%N.
Proof.
induction n; intro Hw; auto.
discriminate.
Qed.

Lemma nb_zeros_nonzero (n : N) :
n <> 0%N -> N.even n = true -> nb_zeros n > 0.
Proof.
induction n; intros Hn He; [contradiction |].
destruct p; [discriminate | cbn ; lia | discriminate].
Qed.

Lemma nb_iter_above_diag (i : nat):
forall n,
n <> 0%N -> (i <= nb_iter n i)%nat.
Proof.
induction i; auto.
intros n Hn.
destruct n eqn:Heqn; [contradiction | ].
rewrite <- Heqn in *.
cbn.
destruct (negb (n =? 1)%N) eqn: Hneq1.
-
destruct (N.even n) eqn: Heven.
+ apply Nat.le_trans with (m := 
 S ( nb_iter (while_even_div2 n) i)).
 *
 apply le_n_S,IHi.
 intro Hw.
 apply while_even_div2_eq_0 in Hw.
 contradiction.
 *
 specialize (nb_zeros_nonzero Hn Heven) as Hgt.
 lia.
+  
 apply le_n_S,IHi.
 destruct n; [contradiction | cbn; lia ].
-
 lia.
Qed.

Lemma exp_not_0 (n : N) :
n <> 0%N ->
(if negb (n =? 1)%N
 then if N.even n then while_even_div2 n else (1 + 3 * n)%N
 else 1%N) <> 0%N.
Proof.
intro Hn.
destruct (negb (n =? 1)%N) eqn:Heqn1.
- 
 destruct (N.even n) eqn:Heven.
 +
  intro Hw.
  now apply Hn, while_even_div2_eq_0.
 + lia.
- intro; discriminate.
Qed.

Lemma zero_zeros_odd (n : N) :
n <> 0%N -> nb_zeros n = 0 -> N.even n = false.
Proof.
intros Hn Hz.
destruct n; [contradiction |].
destruct p;  auto.
cbn in *.
lia.
Qed.

Lemma non_zero_nb_zeros (n : N) :
n <> 0%N -> nb_zeros n > 0 -> N.even n = true.
Proof.
intros Hn Hz.
destruct n; [contradiction |].
destruct p;  auto; cbn in *; lia.
Qed.

Lemma nb_zeros_div2 (n : N) (k : nat) :
n <> 0%N -> nb_zeros n = S k -> nb_zeros (N.div2 n) = k.
Proof.
intros Hn Hz.
destruct n; [contradiction |].
destruct p;  auto; cbn in *; lia.
Qed. 

Lemma div2_not_zero (n : N) :
n <> 0%N ->  N.even n = true -> N.div2 n <> 0%N.
Proof.
intros Hn Hz.
destruct n; [contradiction |].
destruct p;  auto; cbn in *; lia.
Qed. 

Lemma even_not_1 (n : N) :
N.even n = true -> negb (n =? 1)%N = true.
Proof.
intro Heven.
destruct n; try lia;auto.
destruct p; auto.
Qed.

Lemma even2_while_even_div2 (n : N) :
n <> 0%N -> N.even n = true -> N.even (N.div2 n) = true ->
while_even_div2 n = while_even_div2 (N.div2 n).
Proof.
intros Hn He1 He2.
destruct n; [contradiction |].
destruct p ;cbn in *; auto; discriminate.
Qed.

Lemma even1_nb_zeros1 (n : N) :
n <> 0%N -> N.even n = true -> N.even (N.div2 n) = false -> nb_zeros n = 1.
Proof.
intros Hn He1 He2.
destruct n; [contradiction |].
destruct p ;cbn in *; auto; try discriminate.
destruct p; auto;discriminate.
Qed.

Lemma even1_while_even_div2 (n : N) :
n <> 0%N -> N.even n = true -> N.even (N.div2 n) = false ->
while_even_div2 n = N.div2 n.
Proof. 
intros Hn He1 He2.
destruct n; [contradiction |].
destruct p ;cbn in *; auto; try discriminate.
destruct p; auto;discriminate.
Qed.

Lemma internal_loop_S_spec_aux (k : nat) :
forall(n : N),
n <> 0%N ->
(S (nb_zeros n) <= k)%nat ->
itree_equiv (stateT_effect N) (stateT_step N)
(fput n;; 
  (while_fuel _ (S (nb_zeros n))
  (do y <- fget; ret _  (N.even y))
  (do y <- fget; fput (N.div2 y))))
  (fput n;; 
  (while_fuel _ k
  (do y <- fget; ret _  (N.even y))
  (do y <- fget; fput (N.div2 y)))).
Proof.
induction k ; intros n Hn Hk; [lia |].
rewrite while_fuel_S.
rewrite <- bind_assoc.
rewrite <- bind_assoc.
rewrite equiv_fput_fget.
rewrite  bind_assoc.
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
symmetry.
rewrite while_fuel_S.
rewrite <- bind_assoc.
rewrite <- bind_assoc.
rewrite equiv_fput_fget.
rewrite  bind_assoc.
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
destruct (N.even n) eqn:Heven; 
[| reflexivity].
rewrite <- bind_assoc.
rewrite equiv_fput_fget.
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
symmetry.
rewrite <- bind_assoc.
rewrite equiv_fput_fget.
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
rewrite <- bind_assoc.
rewrite equiv_fput_fput.
symmetry.
rewrite <- bind_assoc.
rewrite equiv_fput_fput.
rewrite  <- IHk.
-
 apply itree_bind_congr; [reflexivity | ].
 intros [].
 replace (S (nb_zeros (N.div2 n))) with (nb_zeros n);
 [reflexivity |].
 apply nb_zeros_nonzero in Heven; auto.
 rewrite nb_zeros_div2 with (k := (nb_zeros n) -1);
 auto;lia.
-
 now apply div2_not_zero.
-
 apply nb_zeros_nonzero in Heven; auto.
 rewrite nb_zeros_div2 with (k := (nb_zeros n) -1);
 auto;lia.
Qed.

Lemma fput_fbind_is_continuous_snd [X : Type] (n : X) :
is_continuous (fun k : itree_monad (stateT_effect X) unit => fput n;; k).
Proof.
apply (fbind_ignore_is_continuous_snd (fput n)).
Qed.

Lemma while_fuel_S_nb_zeros_spec_while (n : N) :
n <> 0%N ->
itree_equiv (stateT_effect N) (stateT_step N)
(fput n ;;fwhile_pos_even_div2)
(fput n;; 
  (while_fuel _ (S (nb_zeros n))
  (do y <- fget; ret _  (N.even y))
  (do y <- fget; fput (N.div2 y)))).
Proof.
intro Hn.
unfold fwhile_pos_even_div2.
rewrite while_lub_while_fuel.
replace (lub
(fun x : itree_monad (stateT_effect N) unit =>
 exists n0 : nat,
   x =
   while_fuel (itree_monad (stateT_effect N)) n0
     (do x0 <- fget;
      ret (itree_monad (stateT_effect N)) (N.even x0))
     (do x0 <- fget; fput (N.div2 x0)))) with
     (lub
     (fun x : itree_monad (stateT_effect N) unit =>
      exists n0 : nat, (S(nb_zeros n) <= n0)%nat /\
        x =
        while_fuel (itree_monad (stateT_effect N)) n0
          (do x0 <- fget;
           ret (itree_monad (stateT_effect N)) (N.even x0))
          (do x0 <- fget; fput (N.div2 x0)))).
{ 
match goal with
| |- _ ;; lub ?S == _ => 
 eassert (H := @fput_fbind_is_continuous_snd _ n S _)
end.
destruct H as [Hdir1 Hcont].
rewrite Hcont.
clear Hcont.
remember (single(fput n;;
while_fuel (itree_monad (stateT_effect N))
  (S (nb_zeros n))
  (do y <- fget;
   ret (itree_monad (stateT_effect N)) (N.even y))
  (do y <- fget; fput (N.div2 y)))) as K.
replace  
(fput n;;
while_fuel (itree_monad (stateT_effect N))
  (S (nb_zeros n))
  (do y <- fget;
   ret (itree_monad (stateT_effect N)) (N.even y))
  (do y <- fget; fput (N.div2 y))) with
  (lub K); [| subst; now rewrite lub_single].
apply itree_lub_congr; auto;
[subst;apply single_is_directed | | ].
-
intros m (y & ((k & Hlek & Heq') & Heq));
subst.
eexists.
split.
+
 rewrite member_single_iff.
 reflexivity.
+
 symmetry.
 now apply internal_loop_S_spec_aux.
-
 subst.
 intros m Hm.
 rewrite member_single_iff in Hm;subst.
 eexists.
 split; [ | reflexivity].
 eexists.
 split; [ | reflexivity].
 now exists (S (nb_zeros n)).
}
specialize (@ffix_suffix_enough
(itree_monad (stateT_effect N) unit) (whileF _  
(do y <- fget; ret _  (N.even y)) 
(do y <- fget; fput (N.div2 y))) (S (nb_zeros n))) as Hle.
unfold ffix,whileF,
ffix_suffix in Hle.
unfold while_fuel,iter_fuel.
rewrite <- Hle; [reflexivity |].
apply iterF_is_monotonic.
Unshelve.
apply iterate_suffix_directed.
apply iterF_is_monotonic.
Qed.

Lemma while_fuel_S_nb_zeros_spec (n : N) :
n <> 0%N -> 
itree_equiv (stateT_effect N) (stateT_step N) 
(fput n;;
 while_fuel (itree_monad (stateT_effect N)) (S (nb_zeros n))
   (do y <- fget; ret (itree_monad (stateT_effect N)) (N.even y))
   (do y <- fget; fput (N.div2 y)))
(fput n ;; fput (while_even_div2 n)).
Proof.
intros Hn.
remember (nb_zeros n) as k.
revert n Hn Heqk.
induction k ; intros n Hn Hk; symmetry in Hk.
-
apply zero_zeros_odd in Hk; auto.
rewrite while_fuel_S.
rewrite <- bind_assoc.
rewrite <- bind_assoc.
rewrite equiv_fput_fget.
rewrite  bind_assoc.
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
rewrite Hk.
specialize (equiv_ret_right _ (stateT_step N) unit (fput n)) as Heq.
cbn in *.
replace (fun x : unit => fret x) with 
(fun _ :unit =>
@fret
     (stateT_effect N)
     unit tt)
in Heq.
+
 setoid_rewrite Heq.
 setoid_rewrite equiv_fput_fput.
 replace (while_even_div2 n) with n; [reflexivity |].
 destruct n; [contradiction |].
 destruct p; auto.
 discriminate.
+
 extensionality x.
 now destruct x.
-
rewrite while_fuel_S.
rewrite <- bind_assoc.
rewrite <- bind_assoc.
rewrite equiv_fput_fget.
rewrite  bind_assoc.
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
rewrite non_zero_nb_zeros;auto; [ |lia].
rewrite <- bind_assoc.
rewrite equiv_fput_fget.
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
apply itree_bind_congr; [reflexivity |].
intros [].
setoid_rewrite IHk.
+
 specialize Hn as Hn'.
 apply non_zero_nb_zeros in Hn; [|lia ]. 
 rewrite equiv_fput_fput.
 replace (while_even_div2 (N.div2 n)) with
 (while_even_div2 n); [reflexivity |].
 destruct n; [contradiction |].
 destruct p; auto; cbn in *; discriminate.
+
 apply div2_not_zero; auto.
 apply non_zero_nb_zeros; auto;lia.
+
 symmetry.
 now apply nb_zeros_div2.
Qed.

Lemma internal_loop_S_spec (n : N) :
n <> 0%N -> 
itree_equiv (stateT_effect N) (stateT_step N)
(fput n ;;fwhile_pos_even_div2)
(fput n;; fput (while_even_div2 n)).
Proof.
intro Hn.
eapply itree_trans.
-
 now apply while_fuel_S_nb_zeros_spec_while.
-
 now apply while_fuel_S_nb_zeros_spec.
Qed.

Lemma fsyracuse_bin_S_correct_aux (n : N) :
n <> 0%N ->
N.even n = true ->
forall k,
itree_equiv (stateT_effect N) (stateT_step N)
(fput n;;
fput (while_even_div2 n);;
while_fuel (itree_monad (stateT_effect N)) k
  (do x <- fget; ret (itree_monad (stateT_effect N)) (negb (x =? 1)%N))
  (do x <- fget; (if N.even x then fput (N.div2 x) else fput (1 + 3 * x)%N)))
(fput n;;
while_fuel (itree_monad (stateT_effect N))
  (k + nb_zeros n)
  (do x <- fget; ret (itree_monad (stateT_effect N)) (negb (x =? 1)%N))
  (do x <- fget; (if N.even x then fput (N.div2 x) else fput (1 + 3 * x)%N))).
Proof.
intros Hn Heven k.
replace (k + nb_zeros n) with (nb_zeros n + k) by lia.
remember (nb_zeros n) as z.
revert n Hn Heven k Heqz.
induction z as [ | z IH ]; intros n Hn Heven k Heqz;
[apply nb_zeros_nonzero in Hn; auto; lia |].
symmetry in Heqz.
replace (S z + k) with (S (z + k)) by lia.
rewrite while_fuel_S.
symmetry.
do 3 rewrite <- bind_assoc.
rewrite equiv_fput_fget.
rewrite  bind_assoc.
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
assert (Hneq1: negb (n =? 1)%N = true) by 
(now apply even_not_1 in Heven).
rewrite Hneq1.
rewrite <- bind_assoc.
rewrite equiv_fput_fget.
rewrite  bind_assoc.
rewrite  bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
rewrite Heven.
destruct (N.even (N.div2 n)) eqn: Heven2.
-
 setoid_rewrite <- IH; auto.
 +
 rewrite <- bind_assoc.
 rewrite equiv_fput_fput.
 rewrite <- bind_assoc.
 rewrite equiv_fput_fput.
 symmetry.
 rewrite <- bind_assoc.
 rewrite equiv_fput_fput.
 apply itree_bind_congr.
 *
  now rewrite even2_while_even_div2.
 * intros [].
   reflexivity.
+
  now apply div2_not_zero.
+
 symmetry.
 now apply nb_zeros_div2.
-
 assert (Hz0 : z = 0) by
   (apply even1_nb_zeros1 in Hn;auto;lia).
 subst.
 cbn [plus].
 rewrite <- bind_assoc.
 rewrite equiv_fput_fput.
 symmetry.
 rewrite <- bind_assoc.
 rewrite equiv_fput_fput.
 apply itree_bind_congr.
 + now rewrite even1_while_even_div2.
 + intros [].
reflexivity.
Qed.

Lemma while_lub_while_iter_fuel (n:N):
(n <> 0)%N ->
fput n;;
while _
(do x <- fget; ret (itree_monad (stateT_effect N)) (negb (x =? 1)%N))
(do x <- fget; (if N.even x then fput (N.div2 x) else fput (1 + 3 * x)%N))
= 
fput n;;
lub (fun x => exists k, 
x = 
while_fuel _ (nb_iter n k)
(do x <- fget; ret (itree_monad (stateT_effect N)) (negb (x =? 1)%N))
(do x <- fget; (if N.even x then fput (N.div2 x) else fput (1 + 3 * x)%N))
).
Proof.
intro Hn.
f_equal.
extensionality x.
destruct x.
rewrite while_lub_while_fuel.
specialize 
(@ffix_subset_enough
 (itree_monad (stateT_effect N) unit)
 (whileF _
 (do x <- fget; 
 ret (itree_monad (stateT_effect N)) (negb (x =? 1)%N))
 (do x <- fget; (if N.even x then fput (N.div2 x) else fput (1 + 3 * x)%N))
 )) as He.
apply He.
-
 apply whileF_is_monotonic.
-
 intro i.
 now apply nb_iter_above_diag.
Qed.

Definition fsyracuse_bin (n : N) : itree_monad (stateT_effect N) N :=
fput n ;;
While do x <- fget; ret _ (negb (x =? 1)%N) {{
  do x <- fget;
  if N.even x then fwhile_pos_even_div2 else fput (x + N.succ_double x)%N
}} ;;
fget.

Lemma fsyracuse_bin_S_correct (n : N) :
(n <> 0)%N ->
itree_equiv (stateT_effect N) (stateT_step N)
  (fsyracuse_bin n) (fsyracuse_N n).
Proof.
intro Hn.
unfold fsyracuse_bin, fsyracuse_N.
do 2 rewrite <- bind_assoc.
apply itree_bind_congr; [ | intros []; apply itree_refl].
rewrite while_lub_while_iter_fuel;auto.
rewrite while_lub_while_fuel.
match goal with
| |- _ ;; lub ?S == _ => 
 eassert (H := @fput_fbind_is_continuous_snd _ n S _)
end.
destruct H as [Hdir1 Hcont].
rewrite Hcont.
clear Hcont.
match goal with
| |- _ == _ ;; lub ?S => eassert (H := @fput_fbind_is_continuous_snd _ n S _)
end.
destruct H as [Hdir2 Hcont].
rewrite Hcont.
clear Hcont.
apply itree_lub_congr; auto.
- clear Hdir1 Hdir2.
  intros m1 [m1' [ [n1 Hm1'] Hm1] ].
  subst m1 m1'.
  revert n Hn.
  induction n1 as [ | n1 IH]; intros n Hn.
  + eexists.
    split; [ | apply itree_refl].
    eexists.
    split; [ | reflexivity].
    exists 0.
    reflexivity.
  + destruct (IH (
      if negb (n =?1)%N then
        if N.even n then while_even_div2 n else (1 + 3 * n)%N
      else 1%N)) as
     [m2 [ [m2' [ [n2 Hm2'] Hm2] ] IH']]; 
     [now apply exp_not_0 |].
    clear IH.
    subst m2 m2'.
    rewrite while_fuel_S, bind_assoc.
    eexists (
      fput n;;
      if negb (n =? 1)%N then if N.even n then ?[m2tt] else ?[m2tf] else ?[m2f]
    ).
    split.
    { (* member*)
      destruct (negb (n =? 1)%N) eqn:Hneq1.
     {
      destruct (N.even n) eqn:Hnevn.
      {
        eexists.
        split.
        -
         eexists.
         reflexivity.
        -
         apply f_equal.
         extensionality u.
         destruct u.
         reflexivity.
      }
      {
        eexists.
        split.
        -
         eexists.
         reflexivity.
        -
         apply f_equal.
         extensionality u.
         destruct u.
         reflexivity.
      }
    }
    {
        eexists.
        split.
        -
         eexists.
         reflexivity.
        -
         apply f_equal.
         extensionality u.
         destruct u.
         reflexivity.
      }
    }
    {
      rewrite <- bind_assoc.
      rewrite equiv_fput_fget.
      rewrite bind_assoc.
      do 2 setoid_rewrite (equiv_ret_left _ (stateT_step N)).
      destruct (negb (n =? 1)%N) eqn: Hneq1.
      - rewrite <- bind_assoc, <- bind_assoc.
        rewrite equiv_fput_fget.
        rewrite bind_assoc, bind_assoc.
        setoid_rewrite (equiv_ret_left _ (stateT_step N)).
        destruct (N.even n) eqn: Heven.
        + rewrite <- bind_assoc.
          assert (Hdiv2 :
            itree_equiv (stateT_effect N) (stateT_step N)
              (fput n;; fwhile_pos_even_div2)
              (fput n;; fput (while_even_div2 n))) by
          now apply internal_loop_S_spec.     
          rewrite Hdiv2, bind_assoc.
          setoid_rewrite IH'.
          instantiate (1 := S n2).
          cbn [nb_iter].
          rewrite Hneq1,Heven.
          clear IH' Hdiv2.
          now apply fsyracuse_bin_S_correct_aux.
       +
        replace ((n + N.succ_double n)%N) with
        (1 + 3 * n)%N by lia.
        setoid_rewrite IH'.
        instantiate (1 := S n2).
        cbn [nb_iter].
        rewrite Hneq1,Heven.
        rewrite while_fuel_S.
        symmetry.
        rewrite <- bind_assoc, <- bind_assoc.
        rewrite equiv_fput_fget.
        rewrite bind_assoc, bind_assoc.
        setoid_rewrite (equiv_ret_left _ (stateT_step N)).
        rewrite Hneq1.
        setoid_rewrite (equiv_ret_left _ (stateT_step N)).
        do 2 rewrite <- bind_assoc.
        rewrite equiv_fput_fget.
        rewrite bind_assoc, bind_assoc.
        setoid_rewrite (equiv_ret_left _ (stateT_step N)).
        now rewrite Heven.
   -
   (* n = 1*)
    clear IH' Hn.
    instantiate (1 := 1).
    rewrite negb_false_iff in Hneq1.
    apply Neqb_ok in Hneq1.
    subst.
    cbn [nb_iter].   
    rewrite N.eqb_refl.
    cbn [negb].
    rewrite while_fuel_S.
    do 2 rewrite <- bind_assoc.
    rewrite equiv_fput_fget.
    do 2 rewrite bind_assoc.
    setoid_rewrite (equiv_ret_left _ (stateT_step N)).
    rewrite N.eqb_refl.
    cbn [negb].
    apply itree_bind_congr; [reflexivity |].
    intros [].
    now setoid_rewrite (equiv_ret_left _ _).
}   
-
 (* optimized simulates non-optimized*)
 clear Hdir1 Hdir2.
 intros m1 [m1' [ [n1 Hm1'] Hm1] ].
 subst m1 m1'.
 revert n Hn. 
 induction n1 as [ | n1 IH]; intros n Hn.
 + eexists.
   split; [ | apply itree_refl].
   eexists.
   split; [ | reflexivity].
   exists 0.
   reflexivity.
 + destruct (IH (
     if negb (n =?1)%N then
       if N.even n then while_even_div2 n else (1 + 3 * n)%N
     else 1%N)) as
    [m2 [ [m2' [ [n2 Hm2'] Hm2] ] IH']]; 
    [now apply exp_not_0 |].
   clear IH.
   subst m2 m2'.
   eexists (
     fput n;;
     if negb (n =? 1)%N then if N.even n then ?[m2tt] else ?[m2tf] else ?[m2f]
   ).
   split.
   { (*member*)
     destruct (negb (n =? 1)%N) eqn:Hneq1.
    {
     destruct (N.even n) eqn:Hnevn.
     {
       eexists.
       split.
       -
        eexists.
        reflexivity.
       -
        apply f_equal.
        extensionality u.
        destruct u.
        reflexivity.
     }
     {
       eexists.
       split.
       -
        eexists.
        reflexivity.
       -
        apply f_equal.
        extensionality u.
        destruct u.
        reflexivity.
     }
    } 
    {
       eexists.
       split.
       -
        eexists.
        reflexivity.
       -
        apply f_equal.
        extensionality u.
        destruct u.
        reflexivity.
   }
 }
{
 (* == *)
 destruct (negb (n =? 1)%N) eqn: Hneq1.
 -
  destruct ( N.even n) eqn:Heven.
  +
  instantiate (1 := S n2).
  cbn [nb_iter].
  rewrite Hneq1,Heven.
  rewrite while_fuel_S.
  symmetry.
  rewrite <- bind_assoc, <- bind_assoc.
  rewrite equiv_fput_fget.
  rewrite bind_assoc, bind_assoc.
  setoid_rewrite (equiv_ret_left _ (stateT_step N)).
  rewrite Hneq1.
  setoid_rewrite (equiv_ret_left _ (stateT_step N)).
  do 2 rewrite <- bind_assoc.
  rewrite equiv_fput_fget.
  rewrite bind_assoc, bind_assoc.
  setoid_rewrite (equiv_ret_left _ (stateT_step N)).
  rewrite Heven.
  rewrite <- bind_assoc.
  assert (Hdiv2 :
            itree_equiv (stateT_effect N) (stateT_step N)
              (fput n;; fwhile_pos_even_div2)
              (fput n;; fput (while_even_div2 n))) by
          now apply internal_loop_S_spec.     
  rewrite Hdiv2.
  rewrite bind_assoc.
  setoid_rewrite <- IH'.
  clear IH'.
  now apply fsyracuse_bin_S_correct_aux.
   +
   instantiate (1 := S n2).
   cbn [nb_iter].
   rewrite Hneq1,Heven.
   rewrite while_fuel_S.
   rewrite <- bind_assoc, <- bind_assoc.
   rewrite equiv_fput_fget.
   rewrite bind_assoc, bind_assoc.
   setoid_rewrite (equiv_ret_left _ (stateT_step N)).
   rewrite Hneq1.
   setoid_rewrite (equiv_ret_left _ (stateT_step N)).
  do 2 rewrite <- bind_assoc.
  rewrite equiv_fput_fget.
  rewrite bind_assoc, bind_assoc.
  setoid_rewrite (equiv_ret_left _ (stateT_step N)).
  rewrite Heven.
  rewrite while_fuel_S.
  symmetry.
  rewrite <- bind_assoc, <- bind_assoc.
  rewrite equiv_fput_fget.
  rewrite bind_assoc, bind_assoc.
  setoid_rewrite (equiv_ret_left _ (stateT_step N)).
  rewrite Hneq1.
  setoid_rewrite (equiv_ret_left _ (stateT_step N)).
  do 2 rewrite <- bind_assoc.
  rewrite equiv_fput_fget.
  rewrite bind_assoc, bind_assoc.
  setoid_rewrite (equiv_ret_left _ (stateT_step N)).
  rewrite Heven.
  replace ((n + N.succ_double n)%N) with
  ((1 + 3 * n)%N) by lia.
  apply itree_bind_congr; [reflexivity |].
  intros [].
  symmetry.
  apply IH'.
 - 
 clear IH' Hn.
 instantiate (1 := 1).
 rewrite negb_false_iff in Hneq1.
 apply Neqb_ok in Hneq1.
 rewrite Hneq1.
 cbn [nb_iter].   
 rewrite N.eqb_refl.
 cbn [negb].
 rewrite while_fuel_S.
 do 2 rewrite <- bind_assoc.
 rewrite equiv_fput_fget.
 do 2 rewrite bind_assoc.
 setoid_rewrite (equiv_ret_left _ (stateT_step N)).
 rewrite N.eqb_refl.
 cbn [negb].
 setoid_rewrite (equiv_ret_left _ (stateT_step N)).
 rewrite while_fuel_S.
 symmetry.
 do 2 rewrite <- bind_assoc.
 rewrite equiv_fput_fget.
 do 2 rewrite bind_assoc.
 setoid_rewrite (equiv_ret_left _ (stateT_step N)).
 rewrite N.eqb_refl.
 cbn [negb].
 now setoid_rewrite (equiv_ret_left _ (stateT_step N)).
}
Unshelve.
 * apply iterate_directed,iterF_is_monotonic.
 * apply iterate_subset_directed;
    [apply iterF_is_monotonic |].
    intro i.
    now apply nb_iter_above_diag.
Qed.

Lemma fsyracuse_bin_correct_S (n : N) :
(n <>0)%N ->
itree_equiv (stateT_effect N) (stateT_step N)
  (fsyracuse_bin n) (do x <- fsyracuse (N.to_nat n); ret _ (N.of_nat x)).
Proof.
intro Hn.
transitivity (fsyracuse_N n).
- now apply fsyracuse_bin_S_correct.
- apply fsyracuse_N_correct.
Qed.

Lemma internal_loop_0_spec_aux(n : nat) :
itree_equiv (stateT_effect N) (stateT_step N)
(fput 0%N;;
while_fuel _ n
  (do x <- fget;
   ret
     (itree_monad
        (stateT_effect N))
     (N.even x))
  (do x <- fget;
   fput (N.div2 x)))
(fput 0%N;;fbot).
Proof.
induction n; [reflexivity |].
rewrite while_fuel_S.
do 2 rewrite <-bind_assoc.
rewrite  equiv_fput_fget.
rewrite bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
rewrite bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
cbn [N.even].
do 2 rewrite <-bind_assoc.
rewrite  equiv_fput_fget.
do 2 rewrite bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
cbn [N.div2].
rewrite <-bind_assoc.
now rewrite  equiv_fput_fput.
Qed.

Lemma internal_loop_0_spec :
itree_equiv (stateT_effect N) (stateT_step N)
(fput 0%N;; fwhile_pos_even_div2) 
(fput 0%N;; fbot).
Proof.
unfold fwhile_pos_even_div2.
rewrite while_lub_while_fuel.
match goal with
| |- _ ;; lub ?S == _ => 
 eassert (H := @fput_fbind_is_continuous_snd _  0%N S _)
end.
destruct H as [Hdir1 Hcont].
rewrite Hcont.
clear Hcont.
remember (single (fput 0%N;;@fbot (stateT_effect N) unit)) as K.
replace  (fput 0%N;;@fbot (stateT_effect N) unit) with (lub K);
[ subst | subst ; apply lub_single].
apply itree_lub_congr; auto;
[apply single_is_directed | |].
-
 intros   m (y & (n & Hn) & Heq); subst.
 eexists.
 split; [apply member_single |].
 apply internal_loop_0_spec_aux.
-
 intros m Hm.
 rewrite member_single_iff in Hm; subst.
 eexists.
 split.
 +
  eexists.
  split.
  *
   eexists.
   reflexivity.
  *
   reflexivity.
 +
  now instantiate (1 := 0).
Unshelve.
apply iterate_directed,iterF_is_monotonic.
Qed.

Lemma fsyracuse_bin_0_left_aux
(n: nat):
itree_equiv (stateT_effect N) (stateT_step N)
(fput 0%N;;
while_fuel
  (itree_monad (stateT_effect N)) n
  (do x <- fget;
   ret (itree_monad (stateT_effect N))
     (negb (x =? 1)%N))
  (do x <- fget;
   (if N.even x
    then fwhile_pos_even_div2
    else fput (x + N.succ_double x)%N)))
    (fput 0%N;;fbot).
Proof.
induction n; [reflexivity|].
rewrite while_fuel_S.
do 2 rewrite <-bind_assoc.
rewrite  equiv_fput_fget.
rewrite bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
rewrite bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
assert (Hn01 : negb (0 =? 1)%N = true) by reflexivity.
rewrite Hn01.
do 2 rewrite <-bind_assoc.
rewrite  equiv_fput_fget.
do 2 rewrite bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
assert (He0 : N.even 0 = true) by reflexivity.
rewrite He0.
rewrite <-bind_assoc.
assert (Hdiv20 : 
itree_equiv (stateT_effect N) (stateT_step N)
(fput 0%N;; fwhile_pos_even_div2) (fput 0%N;; @fbot (stateT_effect N) unit))
 by apply internal_loop_0_spec.
rewrite Hdiv20.
rewrite bind_assoc.
apply itree_bind_congr; [reflexivity |].
intros [].
cbn.
now rewrite fbind_fbot.
Qed.

Lemma fsyracuse_bin_0_left:
itree_equiv (stateT_effect N) (stateT_step N)
  (fput 0%N;;
  While do x <- fget;
        ret
          (itree_monad
             (stateT_effect N))
          (negb (x =? 1)%N)
  {{do x <- fget;
    (if N.even x
     then fwhile_pos_even_div2
     else
      fput
        (x + N.succ_double x)%N)}}) (fput 0%N;;fbot).
Proof.
rewrite while_lub_while_fuel.
match goal with
| |- _ ;; lub ?S == _ => 
 eassert (H := @fput_fbind_is_continuous_snd _  0%N S _)
end.
destruct H as [Hdir1 Hcont].
rewrite Hcont.
clear Hcont.
remember (single (fput 0%N;;@fbot (stateT_effect N) unit)) as K.
replace  (fput 0%N;;@fbot (stateT_effect N) unit) with (lub K);
[ subst | subst ; apply lub_single].
apply itree_lub_congr; auto;
[apply single_is_directed | |].
{
 intros m (y & (n & Hn) & Heq);
 subst.
 exists ( (fput 0%N;;@fbot (stateT_effect N) unit));
 split; [apply member_single | ].
 apply fsyracuse_bin_0_left_aux.
}
{
  intros m Hm.
  rewrite member_single_iff in Hm; subst. 
  eexists (fput 0%N;;
  while_fuel
    (itree_monad (stateT_effect N))
    _
    (do x <- fget;
     ret
       (itree_monad (stateT_effect N))
       (negb (x =? 1)%N))
    (do x <- fget;
     (if N.even x
      then fwhile_pos_even_div2
      else
       fput (x + N.succ_double x)%N))).
  split.
  - 
   eexists.
   split.
   +
    eexists; reflexivity.
   +
    f_equal.
    extensionality x; destruct x.
    reflexivity. 
  -
   now instantiate (1 := 0).
 Unshelve.
 apply iterate_directed,iterF_is_monotonic.
}
Qed.

Lemma fsyracuse_bin_0_right_aux (n : nat) :
itree_equiv (stateT_effect N) (stateT_step N)
(fput 0%N;;
while_fuel
  (itree_monad (stateT_effect N)) n
  (do x <- fget;
   ret (itree_monad (stateT_effect N))
     (negb (x =? 1)%N))
  (do x <- fget;
   (if N.even x
    then fput (N.div2 x)
    else fput (1 + 3 * x))%N))
    (fput 0%N;;fbot).
Proof.
induction n; [reflexivity|].
rewrite while_fuel_S.
do 2 rewrite <-bind_assoc.
rewrite  equiv_fput_fget.
rewrite bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
rewrite bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
assert (Hn01 : negb (0 =? 1)%N = true) by reflexivity.
rewrite Hn01.
do 2 rewrite <-bind_assoc.
rewrite  equiv_fput_fget.
do 2 rewrite bind_assoc.
setoid_rewrite (equiv_ret_left _ (stateT_step N)).
assert (He0 : N.even 0 = true) by reflexivity.
rewrite He0.
rewrite <-bind_assoc.
rewrite  equiv_fput_fput.
cbn.
exact IHn.
Qed.

Lemma fsyracuse_bin_0_right:
itree_equiv (stateT_effect N) (stateT_step N)
(fput 0%N;;
While do x <- fget;
      ret
        (itree_monad
           (stateT_effect
              N))
        (negb
           (x =? 1)%N)
{{do x <- fget;
  (if N.even x
   then fput (N.div2 x)%N
   else
    fput (1 + 3 * x)%N)}})
(fput 0%N;; fbot).
Proof.
rewrite while_lub_while_fuel.
match goal with
| |- _ ;; lub ?S == _ => 
 eassert (H := @fput_fbind_is_continuous_snd _ 0%N S _)
end.
destruct H as [Hdir1 Hcont].
rewrite Hcont.
clear Hcont.
remember (single (fput 0%N;;@fbot (stateT_effect N) unit)) as K.
replace  (fput 0%N;;@fbot (stateT_effect N) unit) with (lub K);
[ subst | subst ; apply lub_single].
apply itree_lub_congr; auto;
[apply single_is_directed | |].
{
 intros m (y & (n & Hn) & Heq);
 subst.
 exists ( (fput 0%N;;@fbot (stateT_effect N) unit));
 split; [apply member_single | ].
 apply fsyracuse_bin_0_right_aux.
}
{
  intros m Hm.
  rewrite member_single_iff in Hm; subst. 
  eexists (fput 0%N;;
  while_fuel
    (itree_monad (stateT_effect N))
    _
    (do x <- fget;
     ret
       (itree_monad (stateT_effect N))
       (negb (x =? 1)%N))
    (do x <- fget;
     (if N.even x
      then fput (N.div2 x)
      else
       fput (1+ 3* x)%N))).
  split.
  - 
   eexists.
   split.
   +
    eexists; reflexivity.
   +
    f_equal.
    extensionality x; destruct x.
    reflexivity. 
  -
   now instantiate (1 := 0).
 Unshelve.
 apply iterate_directed,iterF_is_monotonic.
}
Qed.

Lemma fsyracuse_bin_0_correct :
itree_equiv (stateT_effect N) (stateT_step N)
  (fsyracuse_bin 0%N) (fsyracuse_N 0%N).
Proof.
unfold fsyracuse_bin, fsyracuse_N.
do 2 rewrite <- bind_assoc.
apply itree_bind_congr; [ | intros []; apply itree_refl].
rewrite fsyracuse_bin_0_left.
now rewrite fsyracuse_bin_0_right.
Qed.

Lemma fsyracuse_bin_correct (n : N) :
itree_equiv (stateT_effect N) (stateT_step N)
  (fsyracuse_bin n) (fsyracuse_N n).
Proof.
destruct n.
-  apply fsyracuse_bin_0_correct.
- apply fsyracuse_bin_S_correct; lia.
Qed.
(**
Section Syracuse.

Variable M : MONAD.

Definition syracuse (n : nat) : stateT_monad nat M nat :=
put n ;;
While do x <- get; ret _ (negb (x =? 1)) {{
  do x <- get;
  if Nat.even x then put (x / 2) else put (1 + 3 * x)
}} ;;
get.

Definition while_pos_even_div2 : stateT_monad N M unit :=
While do x <- get; ret _ (N.even x) {{
  do x <- get;
  put (N.div2 x)
}}.

Definition syracuse_bin (n : N) : stateT_monad N M N :=
put n ;;
While do x <- get; ret _ (negb (x =? 1)%N) {{
  do x <- get;
  if N.even x then while_pos_even_div2 else put (x + N.succ_double x)%N
}} ;;
get.

End Syracuse.
*)