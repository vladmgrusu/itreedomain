From Stdlib Require Import List FunctionalExtensionality Logic.Eqdep
ProofIrrelevance Lia IndefiniteDescription.
(*PropExtensionality IndefiniteDescription .*)
From Domain Require Export Completion Exp.
Import ListNotations.

Program Fixpoint list_from_seq{P:Type}(n:nat)(s : forall i, i < n -> P) :
 list P :=
match n with
|0 => nil 
|S n'  => cons (s 0 _)(list_from_seq n' (fun i _ => s (S i) _))
end.

Next Obligation.
lia.
Qed.

Next Obligation.
lia.
Qed.


Lemma list_from_seq_length{P:Type}: forall n (s:forall i, i < n -> P),
length (list_from_seq n s) = n.
Proof.
induction n; intros s; auto.
cbn; f_equal.
apply IHn.
Qed.

Lemma list_from_seq_nth{P:Type}(d:P): forall n (s:forall i, i < n -> P)
j (Hjn :j < n), nth j (list_from_seq n s) d = s j Hjn.
Proof.
induction n; intros s j Hjn; [lia |].
destruct j; cbn.
-
f_equal.
apply proof_irrelevance.
-
 cbn.
 remember ((fun (i : nat) (H : i < n) =>
 s (S i)
   (list_from_seq_obligation_2
      P (S n) s n eq_refl i H))) as s'.
 assert (Hjn' : j < n) by lia.
 rewrite IHn with (Hjn := Hjn').
 subst.
 f_equal.
 apply proof_irrelevance.
Qed.


Program Fixpoint 
 seq_from_list{P:Type}(l:list P) (i:nat)(Hlt: i < length l) : P :=
match l with
|nil => False_rect _ _
|a :: l'  => match i with
             0 => a
             | S j => seq_from_list l' j _
             end
end.

Next Obligation.
cbn in Hlt; lia.
Qed.

Next Obligation.
cbn in *; lia.
Qed.


Lemma seq_from_list_from_seq{P:Type}(n:nat):
forall (s : forall i, i < n -> P) (i:nat)
(Hlt: i < n)(Hlt': i < length (list_from_seq n s) ),
seq_from_list(list_from_seq n s) i Hlt' = s i Hlt.
Proof.
induction n as [ | m IH] ; intros s i Hlt Hlt'; [lia |].
destruct i.
-
 cbn.
 f_equal.
 apply proof_irrelevance.
-
 cbn.
 unshelve erewrite IH; [lia |].
 f_equal.
 apply proof_irrelevance.
Qed.

Lemma list_from_seq_from_list{P:Type}(l : list P) :
list_from_seq (length l) (seq_from_list l) = l.
Proof.
induction l as [| a l' IH].
-
  reflexivity.
-
  cbn.
  f_equal.
  assert (Heq : list_from_seq (length l')
  (fun (i : nat) (H : i < length l') =>
   seq_from_list l' i
     (seq_from_list_obligation_2 P (a :: l') 
        (S i)
        (list_from_seq_obligation_2 P (S (length l'))
           (fun (i0 : nat) (Hlt : i0 < S (length l')) =>
            match i0 as i' return (i' = i0 -> P) with
            | 0 => fun _ : 0 = i0 => a
            | S j =>
                fun Heq_i : S j = i0 =>
                seq_from_list l' j
                  (seq_from_list_obligation_2 P 
                     (a :: l') i0 Hlt a l' eq_refl j Heq_i)
            end eq_refl) (length l') eq_refl i H) a l' eq_refl
        i eq_refl)) = list_from_seq (length l') (seq_from_list l')).
  +
   f_equal.
   extensionality i.
   extensionality Hlt.
   f_equal.
   apply proof_irrelevance.
  +
   now rewrite Heq.
Qed.
   



Inductive lprod{P:Type}: list (Setof P) -> Setof (list P):=
|lprod_nil : lprod nil nil
|lprod_cons : forall (S:Setof P) (p:P) L l,
member S p -> lprod L l -> lprod (cons S L)(cons p l).

Lemma lprod_length{P:Type} : forall L (l: list P), 
lprod L l -> length l = length L.
Proof.
induction L; intros l Hl; inversion Hl; subst;auto.
cbn.
now rewrite IHL.
Qed.

Lemma lprod_member{P:Type}(d:P) : forall L (l: list P), 
lprod L l -> forall i, i < length l -> member (nth i L empty) (nth i l d).
Proof.
intros  L l Hl.
induction Hl; intros i Hlt; cbn in Hlt; try lia.
destruct i; cbn; auto.
apply IHHl.
lia.
Qed.

Lemma lprod_nil_eq{P:Type}:
lprod (P:= P) [] = single [].
Proof.
apply set_equal; split; intros Hmx.
-
 inversion Hmx; subst; apply member_single.
-
 rewrite member_single_iff in Hmx;subst; constructor.
Qed.

Lemma lprod_cons_eq{P:Type}(A: Setof P) L:
lprod (A :: L) =
  fun l => exists a l', l = cons a l' /\ member A a /\ lprod L l'.
Proof.
apply set_equal; split; intros Hmx.
-
inversion Hmx; subst; clear Hmx.
unfold member; cbn.
now exists p, l.
-
 destruct Hmx as (p & l & Heql & Hmp & Hl); subst.
 now constructor.
Qed. 





Lemma member_lprod{P:Type}(d:P) : forall L (l:list P),
length l = length L ->
(forall i, i < length L  -> member (nth i L empty) (nth i l d)) ->
lprod L l.
Proof.
induction L; intros l Hel Ha.
-
 destruct l; [constructor | cbn in Hel; lia].
-
 destruct l; [cbn in Hel; lia | constructor].
 +
  apply (Ha 0); cbn; lia.
 +
  apply IHL; auto.
  intros i Hlt.
  apply (Ha (S i)); cbn; lia.
 Qed.  




Inductive list_le{P: Poset} : list P -> list P -> Prop :=
|nil_le : list_le nil nil
|cons_le : forall a a' l l',
a <= a' -> list_le l l' -> list_le (a::l)(a'::l').


Lemma list_le_refl{P:Poset} : forall (l : list P), list_le l l.
Proof.
induction l; constructor; auto; apply refl.
Qed.

Lemma list_le_trans{P:Poset} : forall (l1 l2 l3:list P),
list_le l1 l2 -> list_le  l2 l3 -> list_le l1 l3.
Proof.
intros l1 l2 l3  Hl1l2.
revert l3.
induction Hl1l2; intros l3 Hl2l3; auto.
inversion Hl2l3; subst.
constructor.
-
  eapply trans; eauto.
-
 eapply IHHl1l2 ; eauto. 
Qed.    

Lemma  list_le_antisym{P:Poset} : forall (l1 l2:list P),
list_le l1 l2 -> list_le  l2 l1 -> l1 = l2.
Proof.
intros l1 l2 Hl1l2.
induction Hl1l2; intro Hl2l3; auto.
inversion Hl2l3 ; subst.
f_equal;auto.
now apply antisym.
Qed.   

Lemma list_le_length{P:Poset}: forall (l l' : list P),
list_le l l' -> length l = length l'.
Proof.
intros l l' Hm.
induction Hm; auto.
cbn;  now rewrite IHHm.
Qed.

Lemma list_le_nth{P:Poset} :
forall (l l': list P), list_le l l' ->
forall i, i < length l' -> nth i l default <= nth i l' default.
Proof.
intros l l' Hle.
induction Hle; intros i Hlt; [apply refl |].
destruct i; cbn in *; auto.
apply IHHle;lia.
Qed.

Lemma nth_list_le{P:Poset} :
forall (l l': list P), length l = length l' ->
(forall i, i < length l' -> nth i l default <= nth i l' default) ->
list_le l l'.
Proof.
induction l; intros l' Heq Ha; destruct l'; cbn in Heq; try lia; 
constructor.
-
 apply (Ha 0); cbn; lia.
-
 apply IHl; auto.
 intros i Hlt.
 apply (Ha (S i)).
 cbn; lia.
Qed. 

 Definition list_Poset(P:Poset) : Poset :=
{|
  carrier := list P;
  ord := list_le;
  default := [];
  refl := list_le_refl;
  trans := list_le_trans;
  antisym := list_le_antisym
|}.

Definition lnth{P:Poset}(i : nat)(l: list P) := nth i l (@default P).


Lemma lnth_is_monotonic{P:Poset}: forall i, 
is_monotonic (P1 := list_Poset P) (lnth i).
intros i l l' Hle.
revert i.
induction Hle; intros i; [apply refl |].
destruct i; auto.
apply IHHle.
Qed.


Lemma is_directed_lnth{P:Poset}:
forall (S:Setof (list P)), is_directed (P := list_Poset P) S ->
forall i, is_directed (fmap S (lnth i)).
Proof.
intros S Hd i.
apply (@monotonic_directed (list_Poset P)); auto.
apply lnth_is_monotonic.
Qed.


Lemma hd_is_monotonic{P:Poset}: 
is_monotonic (P1 := list_Poset P) (hd default).
Proof.
replace (hd default) with (@lnth P 0); [apply lnth_is_monotonic |].
extensionality l; now destruct l.
Qed.


Lemma is_directed_hd{P:Poset}:
forall (S:Setof (list P)), is_directed (P := list_Poset P) S ->
is_directed (fmap S (hd default)).
Proof.
intros S Hd.
apply (@monotonic_directed (list_Poset P)); auto.
apply hd_is_monotonic.
Qed.

Lemma tl_is_monotonic{P:Poset}: 
is_monotonic (P1 := list_Poset P) (P2 := list_Poset P) 
 (tl (A := P)).
intros l l' Hle.
induction Hle; auto.
apply refl.
Qed.


Lemma is_directed_tl{P:Poset}:
forall (S:Setof (list P)), is_directed (P := list_Poset P) S ->
is_directed (P := list_Poset P)  (fmap S (tl (A := P))).
Proof.
intros S Hd.
apply (@monotonic_directed (list_Poset P)); auto.
apply tl_is_monotonic.
Qed.



Lemma is_not_empty_lprod{P:Type}(d:P): forall (L:list (Setof P)),
(forall i, i < length L -> ~is_empty (nth i L empty)) ->
~is_empty (lprod  L).
intros L Ha.
rewrite not_empty_member.
unfold member.
assert (Ha' : forall i, i < length L ->
  {x : P |  member (nth i L empty) x}).
{
   intros i Hlt.
   specialize (Ha _ Hlt).
   rewrite not_empty_member in Ha.
   apply constructive_indefinite_description in Ha.
   destruct Ha as (x & Hmx).
   now exists x.
}
exists (list_from_seq (P:= P) 
(length L) (fun i Hi => proj1_sig (Ha' i Hi))).
apply member_lprod with (d := d).
-
 now rewrite list_from_seq_length.
-
 intros i Hi.
 rewrite list_from_seq_nth with (Hjn := Hi).
 apply proj2_sig.
Qed.


Definition is_halfdir{P:Poset}(S: Setof P) :=
   forall x y, member S x -> member S y -> 
    exists z, member S z /\ x <= z /\ y <= z.

 Lemma directed_nonempty_halfdir{P:Poset}(S: Setof P):
 is_directed S <-> ~is_empty S /\ is_halfdir S.
 Proof.
 unfold is_directed, is_halfdir.
 tauto.
 Qed.


 Lemma directed_implies_halfdir{P:Poset}(S: Setof P):
 is_directed S -> is_halfdir S.
 Proof.
 unfold is_directed, is_halfdir.
 tauto.
 Qed.


 Lemma is_halfdir_lprod{P:Poset}: forall (L:list (Setof P)),
 (forall i, i < length L -> is_halfdir (nth i L empty)) ->
 is_halfdir (P:= list_Poset P)(lprod  L).
 Proof.
 induction L; intros Ha.
 -
  rewrite lprod_nil_eq.
  apply directed_implies_halfdir.
  apply @single_is_directed.
 - 

  intros x y Hmx Hmy.
  rewrite lprod_cons_eq in Hmx, Hmy.
  destruct Hmx as (u & l & Heq & Hm & Hl); subst.
  destruct Hmy as (v & l' & Heq & Hm' & Hl'); subst.
  assert (Hah : is_halfdir a) by (apply (Ha  0); cbn; lia).
  specialize (Hah _ _ Hm Hm').
  destruct Hah as (z & Hmz  & Hleuz & Hlevz).
  assert (HLh :  is_halfdir (P:= list_Poset P) (lprod L)).
  {
   apply IHL.
   intros i Hlt.
   apply (Ha (S i)); cbn; lia.
  }
  specialize (HLh _ _ Hl Hl').
  destruct HLh as (l'' & Hml'' & Hle' & Hle'').
  exists (z :: l''); repeat split;
   [| now constructor | now constructor ].
  rewrite lprod_cons_eq.
  now exists z,l''.
Qed.



Lemma is_directed_lprod{P:Poset}: forall (L:list (Setof P)),
(forall i, i < length L -> is_directed (nth i L empty)) ->
is_directed (P:= list_Poset P)(lprod  L).
Proof.
intros L Ha.
rewrite directed_nonempty_halfdir.
split.
-
 apply (is_not_empty_lprod (@default P)).
 intros i Hlt.
 specialize (Ha i Hlt).
 rewrite directed_nonempty_halfdir in Ha.
 now destruct Ha.
-
apply is_halfdir_lprod.
intros i Hlt.
specialize (Ha i Hlt).
rewrite directed_nonempty_halfdir in Ha.
now destruct Ha.
Qed.

Lemma directed_same_length{P:Poset}:
forall (S: Setof (list P)), is_directed (P:= list_Poset P) S -> 
forall l1 l2, member S l1 -> member S l2 -> length l1 = length l2.
Proof.
intros S (Hne & Hd) l1 l2 Hm1 Hm2.
destruct (Hd _ _ Hm1 Hm2) as (l & Hml & Hle1 & Hle2).
apply list_le_length in Hle1, Hle2; congruence.
Qed.


Definition common_length_sig{P:Poset}
(S: Setof (list P))(Hd : is_directed (P:= list_Poset P) S):
{n : nat |forall l, member S l -> length l = n}.
apply constructive_indefinite_description.
specialize (directed_same_length _  Hd) as Ha.
destruct Hd as (Hne & _).
rewrite not_empty_member in Hne.
destruct Hne as (l & Hml).
exists (length l); intros l' Hm.
now apply Ha.
Qed.

Definition common_length{P:Poset}
(S: Setof (list P)) : nat :=
match (oracle (is_directed (P:= list_Poset P) S)) with
| left Hd => proj1_sig (common_length_sig S Hd)
|right _ => 0
end.



Lemma common_length_hd{P:Poset}
(S: Setof (list P))(Hd : is_directed (P:= list_Poset P) S): 
common_length S = proj1_sig (common_length_sig S Hd).
Proof.
unfold common_length.
destruct (oracle (is_directed  (P:= list_Poset P) S))  ; 
[|contradiction].
do 2 f_equal.
apply proof_irrelevance.
Qed.



Lemma common_length_common{P:Poset}
(S: Setof (list P))(Hd : is_directed (P:= list_Poset P) S): 
forall l, member S l -> length l = common_length S.
Proof.
intros l Hm.
rewrite common_length_hd with (Hd := Hd).
destruct (common_length_sig S Hd); cbn in *.
now apply e.
Qed.




Lemma directed_nil{P:Poset}:
forall (S: Setof (list P)), is_directed (P:= list_Poset P) S ->
(member S [] <-> S = single []).
Proof.
intros S Hd.
split; intros Hm; [| subst; apply member_single].
apply set_equal; split; intros Hmx.
-
  rewrite member_single_iff.
  apply  directed_same_length with (l1 := x) (l2 := []) in Hd;
  auto.
  destruct x; auto; cbn in Hd; lia.
-
  now rewrite member_single_iff in Hmx; subst.
Qed.    



Lemma is_upper_hd{P:Poset}(l:list P) (S : Setof (list P))(a:P):
is_upper (P := list_Poset P)  S (a :: l) ->
is_upper (P:= P) (fmap S (lnth 0)) a.
Proof.
intros Hu x (y & Hmy & Heq); subst.
destruct y. 
-
 specialize (Hu _ Hmy).
 now inversion Hu.
-
 cbn.
 specialize (Hu _ Hmy).
 now inversion Hu.
Qed.



Lemma is_upper_tl{P:Poset}(l:list P) (S : Setof (list P))(a:P):
is_upper (P := list_Poset P)  S (a :: l) ->
is_upper (P := list_Poset P) (fmap S (tl (A := P))) l.
Proof.
intros Hu x (y & Hmy & Heq); subst.
destruct y; specialize (Hu _ Hmy); now inversion Hu.
Qed.



Lemma is_upper_cons{P:Poset}(l:list P) (S : Setof (list P))(a:P):
~member S [] ->
is_upper (P := list_Poset P) (fmap S (tl (A := P))) l -> 
is_upper (P:= P) (fmap S (lnth 0)) a->
is_upper (P := list_Poset P)  S (a :: l).
Proof.
intros  Hne Hul Hua.
intros x Hmx.
destruct x; [contradiction | ].
constructor.
- 
 apply Hua.
 now exists (c :: x).
-
 apply Hul.
 now exists (c :: x).
 Qed.



Lemma is_lub_tl{P:Poset}(l:list P) (a:P) (S : Setof (list P)):
is_lub  (P := list_Poset P) S (a :: l) ->
is_lub (P := list_Poset P) (fmap S (@tl P)) l.
Proof.
intros  (Hu & Hm).
split. 
-
 intros x (y & Hmy & Heq); subst.
 specialize (Hu _ Hmy).
 inversion Hu; subst; clear Hu.
 assumption.
-
  intros y Huy.
  apply is_upper_cons with (a:= a) in Huy.
  +
  specialize (Hm _ Huy).
  now inversion Hm.
  +
   intro Habs.
   specialize (Hu _ Habs).
   inversion Hu.
  +
  intros x (z & Hmz & Heq); subst.
  specialize (Hu _ Hmz).
  now inversion Hu; subst.
Qed.



Lemma is_lub_hd{P:Poset}(l:list P) (a:P) (S : Setof (list P)):
is_lub  (P := list_Poset P) S (a :: l) ->
is_lub (P := P) (fmap S (lnth 0)) a.
Proof.
intros (Hu & Hm).
split.
- 
   intros x (y & Hmy & Heq); subst.
   specialize (Hu _ Hmy).
   now inversion Hu; subst.
-
 intros y Hmy.
 assert (Hnm : ~member S [])
 by (intro Hm'; specialize (Hu _ Hm'); now inversion Hu).

 apply is_upper_tl in Hu.
 eapply is_upper_cons  with (a:= y) (l:= l) in Hnm; auto.
 specialize (Hm _ Hnm); now inversion Hm.
 Qed.
 
 


Lemma is_lub_nth{P:Poset}(l:list P) : forall (S : Setof (list P)),
is_lub (P := list_Poset P) S l-> forall i, i < length l ->
is_lub (fmap S (lnth i)) (lnth i l).
Proof.
induction l; intros S Hl i Hlt; cbn in Hlt; [lia |].
destruct i; cbn in *.
-
  eapply is_lub_hd; eauto.
-
 apply is_lub_tl in Hl.
 apply PeanoNat.lt_S_n in Hlt.
 specialize (IHl _ Hl _ Hlt).
 rewrite <- fmap_comp in IHl.
 unfold lnth in *.
replace ((fun l : list P
=>
nth i l default)
° tl (A:=P)) with ((fun l0 : list P =>
nth (Datatypes.S i) l0
  default)) in IHl; auto.
extensionality x.
unfold comp; cbn.
destruct x; auto.
now destruct i.
Qed.



Lemma is_lub_cons{P:Poset}(l:list P) (a:P) (S : Setof (list P)):
is_directed  (P := list_Poset P) S ->
 S <> single [] ->
is_lub (P := P) (fmap S (lnth 0)) a ->
is_lub (P := list_Poset P) (fmap S (@tl P)) l ->
is_lub  (P := list_Poset P) S (a ::l).
Proof.
intros Hd Hne (Hau & Ham) (Hlu & Hlm).
split.
-
 apply is_upper_cons; auto. 
 intro Hm.
 rewrite directed_nil in Hm; [contradiction | auto].
-
 intros y Huy.
 cbn in *.
 specialize Hd as Hn.
 destruct Hn as (Hn & _).
 apply not_empty_not_single_2dif with (x := []) in Hn;auto.
 destruct Hn as (w & Hmx & Hdw).
 destruct w; [contradiction | clear Hdw].
 specialize Huy as Huy'.
 specialize (Huy' _ Hmx). (* copy first ?*)
 inversion Huy'; subst; clear Huy'.
 constructor.
 +
  apply is_upper_hd in Huy.
  now apply Ham.
 +
  apply is_upper_tl in Huy.
  now apply Hlm.
Qed.

 
Lemma is_lub_nil{P:Poset}:
forall (S : Setof (list P))
(Hd:is_directed (P := list_Poset P) S),
common_length S = 0 -> is_lub (P := list_Poset P) S [].
Proof.
intros S Hd Hcl.
assert (Ha : forall l, member S l -> length l = 0) by
 (intros l Hm; 
 now rewrite <- common_length_common with (l := l) in Hcl).
 replace S with (single ([]:list P)); [apply @is_lub_single |].
 apply set_equal; split; intro Hm.
 + 
  rewrite member_single_iff in Hm; subst.
  specialize Hd as Hne.
  destruct Hne as (Hne & _).
  rewrite not_empty_member in Hne.
  destruct Hne as (x & Hmx).
  specialize (Ha _ Hmx).
  destruct x; auto; cbn in Ha; lia.
 +
   rewrite member_single_iff. 
   specialize (Ha _ Hm).
   destruct x; auto; cbn in Ha; lia.
Qed.


Lemma common_fmap_tl{P:Poset}(S:Setof (list P))
(Hd:is_directed (P := list_Poset P) S)(n:nat):
common_length S = Datatypes.S n ->
common_length
  (fmap S (tl (A:=P))) = n.
Proof.
intros Hcl.
assert (Ha : forall (l : list P),
member S l -> length l = Datatypes.S n).
{
   intros l Hm.
   rewrite <- Hcl.
   now apply common_length_common.
}
assert (Ha' :  forall (l : list P),
member (fmap S (tl (A:=P))) l -> length l = n).
{
   intros l (l' & Hm' & Heq); subst.
   specialize (Ha _ Hm').
   destruct l'; cbn in Ha; [ lia |].
   cbn.
   injection Ha; intros;auto.
}
remember (common_length (fmap S (tl (A:=P)))) as x.
unshelve erewrite common_length_hd in Heqx;
[now apply is_directed_tl| ].
destruct (common_length_sig
(fmap S
   (tl (A:=P)))
(is_directed_tl S
   Hd)).
cbn in Heqx; subst.
specialize (is_directed_tl S
Hd) as Hnt.
destruct Hnt as (Hnt & _).
rewrite not_empty_member in Hnt.
destruct Hnt as (x & Hmx).
specialize (e _ Hmx).
specialize (Ha' _ Hmx).
congruence.
Qed.


Lemma is_lub_from_nth{P:Poset}(l:list P):
forall (S : Setof (list P))(Hd:is_directed (P := list_Poset P) S),
common_length S = length l ->
(forall i, i < length l ->
is_lub (fmap S (lnth i)) (lnth i l)) ->
is_lub (P := list_Poset P) S l.
Proof.
induction l; intros S Hd Hcl Ha; [eapply is_lub_nil; eauto | ].
apply is_lub_cons; auto.
-
  intros Heqs.
  subst.
  cbn in Hcl.
  rewrite <- common_length_common with (l := []) in Hcl;
  [ | apply @single_is_directed | apply  member_single].
  cbn in Hcl; lia.
 -
 apply (Ha 0); cbn; lia.
 -
 specialize (is_directed_tl S Hd) as Hdt.
 specialize (IHl _ Hdt).
 apply IHl.
 +
  cbn in Hcl.
  now apply common_fmap_tl.
 +
  intros i Hlt.
  apply le_n_S in Hlt.
  specialize (Ha _ Hlt); cbn in Ha.
  apply le_S_n in Hlt.
  unfold lnth in *.
  rewrite <- fmap_comp.
  replace ((fun l0 : list P =>
  nth i l0 default) ° tl (A:=P)) 
  with ((fun l : list P => nth
   (Datatypes.S i)
   l default)); auto.
  extensionality x.
  destruct x; auto.
  unfold "°"; now destruct i.
 Qed.  

Definition list_lub_sig{P:DCPO}(S: Setof (list P)) 
(Hd: is_directed (P := list_Poset P) S) : 
{l : list P |is_lub (P := list_Poset P) S l}.
Proof.
exists (list_from_seq (common_length S) 
(fun i _ => lub (fmap S (lnth i))) ).
apply is_lub_from_nth; auto.
-
 now rewrite list_from_seq_length.
-
 rewrite list_from_seq_length. 
 intros i Hlt.
 unfold lnth.
 rewrite list_from_seq_nth; auto.
 apply lub_is_lub.
 apply (@monotonic_directed (list_Poset P)); auto.
 apply lnth_is_monotonic.
Defined.

Definition list_lub{P:DCPO}(S: Setof (list P)) :=
match (oracle (is_directed (P := list_Poset P) S)) with
| left Hd => proj1_sig (list_lub_sig S Hd)
| right _ => []
end.


Program Definition list_DCPO (P:DCPO) :=
{|
   dcpo_poset := list_Poset P;
   lub := list_lub
|}.

Next Obligation.
unfold list_lub.
destruct (oracle (is_directed (P := list_Poset P) S));
[| contradiction].
apply proj2_sig.
Qed.

 
Lemma list_lub_dir{P:DCPO}(S: Setof (list P)) 
  (Hd :is_directed (P := list_Poset P) S): 
  list_lub S = 
  list_from_seq (common_length S) 
                (fun i _ => lub (fmap S (lnth i))).
Proof.
unfold list_lub.
destruct (oracle (is_directed (P := list_Poset P) S));
[| contradiction].
unfold list_lub_sig.
cbn.
replace i with Hd; auto.
apply proof_irrelevance.
Qed.


Lemma common_length_lub{P:DCPO}
(S: Setof (list P))(Hd : is_directed (P:= list_Poset P) S): 
length (list_lub S) = common_length S.
Proof.
specialize Hd as Hn.
destruct  Hn as (Hn & _).
rewrite not_empty_member in Hn.
destruct Hn as (x & Hmx).
cbn in *.
specialize(lub_is_upper (D := list_DCPO P) _ Hd) as Hu.
specialize (Hu _ Hmx).
replace (common_length S) with (length x);  [  | 
rewrite common_length_common with (S := S); auto].
symmetry.
now apply list_le_length.
Qed.

Lemma cons_hd_is_monotonic{P : Poset}: 
forall (l:list P),
is_monotonic (P2 := list_Poset P) (fun x => x :: l).
Proof.
intros l x y Hle.
constructor; auto.
apply list_le_refl.
Qed.

Lemma cons_hd_is_continuous{P : DCPO}: 
forall (l:list P),
is_continuous (P2 := list_DCPO P) (fun x => x :: l).
Proof.
intro l.
apply continuous_iff_mono_commutes.
split; [apply cons_hd_is_monotonic|].
intros S x Hd Hl.
apply is_lub_cons.
-
apply monotonic_directed;
[apply cons_hd_is_monotonic | assumption].
-
 intros Habs.
 rewrite set_equal in Habs.
 specialize (Habs []).
 assert (Hm: member
 (fmap S
    (fun x : P =>
     x :: l)) []) by (rewrite Habs; apply member_single).
 destruct Hm as (y & Hmy & Heq);discriminate.
 -
   rewrite <- fmap_comp.
   replace (lnth 0
   ° (fun x0 : P => x0 :: l)) with (id (X := P)); 
   [now rewrite fmap_id |].
   now extensionality y.
-
 rewrite <- fmap_comp.
 replace ((tl (A:=P)
 ° (fun x0 : P => x0 :: l))) with (fun _:P => l).
 +
  rewrite fmap_cst; [| now destruct Hd].
  apply @is_lub_single.
 +
  now extensionality y. 
Qed.

Lemma cons_tl_is_monotonic{P : Poset}: 
forall (a :P),
is_monotonic (P1 := list_Poset P) (P2 := list_Poset P)
(fun l => a :: l).
Proof.
intros a x y Hle.
constructor; auto; apply refl.
Qed.

Lemma cons_tl_is_continuous{P : DCPO}: 
forall (a :P),
is_continuous (P1 := list_DCPO P) (P2 := list_DCPO P)
(fun l => a :: l).
Proof.
intros a.
apply continuous_iff_mono_commutes.
split; [apply cons_tl_is_monotonic|].
intros S x Hd Hl.
apply is_lub_cons.
-
apply monotonic_directed;
[apply cons_tl_is_monotonic | assumption].
-
 intros Habs.
 rewrite set_equal in Habs.
 specialize (Habs []).
 assert (Hm: member
 (fmap S
    (fun x : list P =>
     a :: x)) []) by (rewrite Habs; apply member_single).
 destruct Hm as (y & Hmy & Heq);discriminate.
 -
   rewrite <- fmap_comp.
   cbn.
   replace (lnth 0
   ° (fun l : list P => a :: l)) with (fun _:list P => a).
   + 
    rewrite @fmap_cst; [| now destruct Hd].
    apply is_lub_single.
   +
   now extensionality y.
-
 rewrite <- fmap_comp.
 cbn.
 replace ((tl (A:=P)
° (fun l : list P => a :: l))) with (id (X:= list P)).
 +
  now rewrite fmap_id.
 + 
  now extensionality y. 
Qed.


Lemma is_compact_hd{P:DCPO}: forall(l: list_DCPO P) (a:P),
is_compact (D := list_DCPO P) (a :: l) -> is_compact a.
Proof.
intros l a Hc S Hd lu Hlu Hle.
apply is_lub_lub_eq1 in Hlu; auto; subst.
remember (fmap S (fun x => x::l)) as SL.
 assert (HDL : is_directed (P := list_Poset P) SL) by
 (
   subst;
   apply  @monotonic_directed; auto;
   apply cons_hd_is_monotonic
 ).
assert(Hl' : (list_lub (P := P) SL) = (lub S) :: l).
{
   subst.
   specialize (cons_hd_is_continuous l) as Hcl.
   rewrite continuous_iff_mono_commutes in Hcl.
   destruct Hcl as (_ & Hcl).
   unfold commutes_with_lub in Hcl.
   specialize (Hcl _ (lub S) Hd (lub_is_lub _ Hd)).
   apply is_lub_lub_eq1 in Hcl; auto.
}
specialize (Hc _ HDL _ (@lub_is_lub (list_DCPO P) _ HDL)).
cbn in Hc.
rewrite Hl' in Hc.
assert (Hlel :(list_le (a :: l) (lub S :: l))) by
(constructor; auto; apply list_le_refl).
specialize (Hc Hlel).
destruct Hc as (l' & Hml' & Hlel').
inversion Hlel'; subst; clear Hlel'.
destruct Hml' as (u & Hmu & Heq); subst.
injection Heq; intros; subst; clear Heq.
now exists u.
Qed.


Lemma is_compact_tl{P:DCPO}: forall(l: list_DCPO P) (a:P),
is_compact (D := list_DCPO P) (a :: l) -> 
is_compact (D := list_DCPO P) l.
Proof.
intros l a Hc S Hd lu Hlu Hle.
apply is_lub_lub_eq1 in Hlu; auto; subst.
remember (fmap S (fun l => a::l)) as SL.
 assert (HDL : is_directed (P := list_Poset P) SL) by
 (
   subst;
   apply  @monotonic_directed; auto;
   apply cons_tl_is_monotonic
 ). 
assert(Hl' : (list_lub (P := P) SL) = a :: (lub S)).
{
   subst.
   specialize (cons_tl_is_continuous a) as Hcl.
   rewrite continuous_iff_mono_commutes in Hcl.
   destruct Hcl as (_ & Hcl).
   unfold commutes_with_lub in Hcl.
   cbn in  *.
   specialize (Hcl _ (@lub (list_DCPO P) S) Hd
    (@lub_is_lub (list_DCPO P) _ Hd)).
   apply (@is_lub_lub_eq1  (list_DCPO P)) in Hcl; auto.
}
specialize (Hc _ HDL _ (@lub_is_lub (list_DCPO P) _ HDL)).
cbn in Hc.
rewrite Hl' in Hc. 
assert (Hlel :(list_le (a :: l) (a :: (lub S)))) by
(constructor; auto; apply refl).
specialize (Hc Hlel).
destruct Hc as (l' & Hml' & Hlel').
inversion Hlel'; subst; clear Hlel'.
destruct Hml' as (u & Hmu & Heq); subst.
injection Heq; intros; subst; clear Heq.
now exists u.
Qed.


Lemma is_compact_nth{P:DCPO}: forall(l: list_DCPO P),
is_compact (D := list_DCPO P) l -> forall i, i < length l ->
is_compact (lnth i l).
Proof.
induction l; intros Hc i Hlt; cbn in Hlt; [lia|].
destruct i.
-
 cbn.
 eapply is_compact_hd; eauto.
-
 cbn.
 apply IHl; [|lia].
 eapply is_compact_tl; eauto.
Qed.


From Domain Require Import Product.


Lemma cons_is_continuous{P : DCPO}: 
is_continuous (P1 := PROD_DCPO P (list_DCPO P))
 (P2 := list_DCPO P)
(fun p => fst p :: snd p).
Proof.
apply argwise_continuous.
-
 intro a.
 cbn.
 apply cons_tl_is_continuous.
-
 intro l.
 cbn.
 apply cons_hd_is_continuous.
Qed.


Definition decons{P:Type}(d:P) (l : list P) :=
   ((hd d l), (tl l)).

Lemma decons_is_monotonic{P:Poset}:
is_monotonic (P1 := list_Poset P)
(P2 := PROD_Poset P (list_Poset P))
(decons default).
Proof.
intros l l' Hle.
constructor; cbn; auto.
apply hd_is_monotonic; auto.
now apply tl_is_monotonic.
Qed.



Lemma hd_is_continuous{P:DCPO}:
is_continuous (P1 := list_DCPO P)
(P2 := P) (hd default).
Proof.
rewrite continuous_iff_mono_commutes; split; 
[apply hd_is_monotonic|].
intros S l Hd.
destruct (oracle (member S [])).
{
   rewrite directed_nil with (S := S) in m;auto.
   subst.
   intro Hl.
   apply is_lub_lub_eq1 in Hl; [| apply @single_is_directed].
   rewrite @lub_single in Hl;subst.
   cbn.
   split.
   - 
    intros x (y & Hmy & Heq); subst.
    change (member (single[]) y) in Hmy.
    rewrite member_single_iff in Hmy;subst; apply refl.
   -
    intros y Hu.
    apply Hu.
    exists []; split; auto.
    apply member_single.
}
 specialize Hd as Hn.
 destruct Hn as (Hn & _).
 rewrite directed_nil with (S := S) in n;auto.
 destruct (not_empty_not_single_2dif  _ _ Hn n) as (x & Hmx & Hnx).
 destruct x; [contradiction | clear Hnx].
 specialize Hd as Hcl.
 apply common_length_common with (l := c:: x) in Hcl; auto.
 cbn in Hcl.
 remember (length x) as m.
 clear Heqm.
 intros (Hu & Hm).
 split.
-
 intros u (y & Hmy & Heq); subst.
 apply hd_is_monotonic.

 now apply Hu.
-
 intros y Huy. 
 specialize (Hu _ Hmx).
 inversion Hu ; subst; clear Hu.
 cbn.
 assert (Hu' : 
 is_upper S (y :: (list_lub (fmap S (tl (A := P)))))).
 {
  intros u Hmu.
  destruct u; [rewrite directed_nil with (S := S) in Hmu; auto;subst;
    contradiction | ].
  constructor.
  -
  apply Huy.
  now exists (c0 :: u).
  -
   apply (lub_is_upper (D := list_DCPO P));
   [apply @monotonic_directed; auto; apply tl_is_monotonic |].
   now exists (c0 :: u).
 }
 specialize (Hm _ Hu').
 now inversion Hm.
 Qed.  
   
   


Lemma tl_is_continuous{P:DCPO}:
is_continuous (P1 := list_DCPO P)
(P2 := list_DCPO P) (@tl P).
Proof.
rewrite continuous_iff_mono_commutes; split; 
[apply tl_is_monotonic|].
intros S l Hd.
destruct (oracle (member S [])).
{
   rewrite directed_nil with (S := S) in m;auto.
   subst.
   intro Hl.
   apply is_lub_lub_eq1 in Hl; [| apply @single_is_directed].
   rewrite @lub_single in Hl;subst.
   cbn.
   split.
   - 
    intros x (y & Hmy & Heq); subst.
    change (member (single[]) y) in Hmy.
    rewrite member_single_iff in Hmy;subst; apply refl.
   -
    intros y Hu.
    apply Hu.
    exists []; split; auto.
    apply member_single.
}
specialize Hd as Hn.
 destruct Hn as (Hn & _).
 rewrite directed_nil with (S := S) in n;auto.
 destruct (not_empty_not_single_2dif  _ _ Hn n) as (x & Hmx & Hnx).
 destruct x; [contradiction | clear Hnx].
intros (Hu & Hm).
split.
 -
  intros z (y & Hmy & Heq); subst.
  apply tl_is_monotonic.
  now apply Hu.
-
 intros y  Huy.
 assert (Hu' : 
 is_upper (P := list_Poset P) S
  ((lub (d := P) ((fmap S (hd default))))::y)).
{
intros v Hmv.
destruct v;[rewrite directed_nil with (S := S) in Hmv; auto;subst;
contradiction | ].
constructor.
- 
 apply lub_is_upper;
 [apply monotonic_directed; auto; apply hd_is_monotonic |].
 now exists (c0 ::v).
-
 apply Huy.
 now exists (c0 ::v).
}
specialize (Hm _ Hu').
now inversion Hm.
Qed.


Lemma is_compact_cons{P:DCPO}: forall(l: list_DCPO P) (a:P),
is_compact a ->
is_compact (D := list_DCPO P) l ->
is_compact (D := list_DCPO P) (a :: l).
Proof.
intros l a Hca Hcl S Hd lu Hlu Hle.
apply is_lub_lub_eq1 in Hlu; auto; subst.
cbn in *.
assert  (Hlp : ord (p :=PROD_Poset P (list_Poset P)) 
(decons default (a::l))  
(decons default (lub (d := list_DCPO P) S))) by
 (now apply decons_is_monotonic).
 destruct Hlp as (Ha & Hl); cbn in *.
 replace (hd default (list_lub S)) with
 (lub (fmap S (hd default))) in Ha; [ |
    specialize (@hd_is_continuous P) as Hc;
    destruct (Hc S) as (_ & Hc'); auto
 ].
 replace (tl (list_lub S)) with 
  (lub (d := list_DCPO P)(fmap S (@tl P))) in Hl;
  [ |
   specialize (@tl_is_continuous P) as Hc;
   destruct (Hc S) as (_ & Hc'); auto
  ].
 assert  (Hda : is_directed  (fmap S (hd default)))by
   (apply (monotonic_directed (P1 := list_Poset P)); auto;
   apply hd_is_monotonic).
assert  (Hdl : is_directed (P := list_Poset P) (fmap S (tl (A := P))))
by
 (apply  (monotonic_directed (P1:= list_Poset P) (P2:= list_Poset P));
 auto; apply tl_is_monotonic).
specialize (Hca _ Hda _ (lub_is_lub _ Hda) Ha).
specialize (Hcl _ Hdl _ (@lub_is_lub (list_DCPO P) _ Hdl) Hl).
destruct Hca as (b & ( y & Hmy & Heq) & Hleb);
subst.
destruct Hcl as (b & ( z & Hmz& Heq) & Hlez);
subst.
inversion Hle; subst.
specialize (common_length_lub _ Hd) as Hcl.
rewrite <- H1 in Hcl; cbn in Hcl.
symmetry in Hcl.
clear Ha Hl  H1 H2 H3.
remember (length l') as n.
clear Heqn.
specialize Hd as Hd'.
specialize Hd' as (_ & Hd').
cbn in Hd'.
specialize (Hd' _ _ Hmy Hmz).
destruct Hd' as (w & Hmw & Hleyw & Hlezw).
exists w; split; auto.
assert (Hlw : length w  = Datatypes.S n) by
   (rewrite <- Hcl;
   apply common_length_common; auto).
destruct w; [cbn in Hlw; lia |].
constructor.
-
 inversion Hleyw; subst.
 cbn in Hleb.
 eapply trans; eauto.
-
inversion Hlezw; subst.
cbn in Hlez.
eapply list_le_trans; eauto.
Qed.



Lemma nil_is_compact{P:DCPO}: is_compact (D:= list_DCPO P) [].
Proof.
intros S Hd lu Hlu Hle.
apply is_lub_lub_eq1 in Hlu; auto; subst.
inversion Hle; subst; clear Hle.
specialize Hd as Hd'.
destruct Hd' as (Hne & _).
rewrite not_empty_member in Hne.
destruct Hne as (x & Hm); auto.
apply lub_is_upper with (x := x) in Hd; cbn in *;auto.
rewrite <- H in Hd.
inversion Hd.
exists x; split; auto.
rewrite <- H0.
constructor.
Qed.

Lemma is_compact_from_all_nth{P:DCPO}: forall(l: list_DCPO P),
(forall i, i < length l ->
is_compact (lnth i l)) ->
is_compact (D := list_DCPO P) l.
Proof.
induction l; intros Ha.
- apply nil_is_compact.
- 
 apply is_compact_cons.
 +
  apply (Ha 0); cbn; lia.
 +
  apply IHl.
  intros i Hlt.
  apply (Ha (S i)).
  cbn; lia.
Qed.



Lemma is_compact_iff_all_nths_compact{P:DCPO}: forall(l: list_DCPO P),
is_compact (D := list_DCPO P) l <->
(forall i, i < length l ->
is_compact (lnth i l)).
Proof.
split; intro Hc.
-
 now apply is_compact_nth.
-
 now apply is_compact_from_all_nth.
Qed. 
  

Lemma map_compact
{P1 P2:DCPO}(l:list P1)(f : P1 -> P2):
(forall x, is_compact x -> is_compact (f x)) ->
is_compact (D := list_DCPO P1) l -> 
is_compact (D := list_DCPO P2) (map f l).
Proof.
intros Ha Hc.
rewrite is_compact_iff_all_nths_compact.
rewrite is_compact_iff_all_nths_compact in Hc.
rewrite length_map.
intros i Hlt.
specialize (Hc _ Hlt).
unfold lnth in *.
rewrite nth_indep with (d' := f default); [ | now rewrite length_map].
rewrite map_nth.
now apply Ha.
Qed.

Lemma compacts_le_lprod{P:DCPO}: forall (l:list_DCPO P),
compacts_le (P := list_DCPO P) l = 
lprod (list_from_seq (length l)
  (fun i _ =>  compacts_le (lnth i l))).
Proof.
intro l.
apply set_equal; split; intro Hm.
-
 destruct Hm as (Hc & Hle).
 cbn in *.
 apply member_lprod with (d := default).
 +
  rewrite list_from_seq_length.
  now apply list_le_length.
 +
  rewrite list_from_seq_length.
  intros i Hlt.
  rewrite list_from_seq_nth; auto.
  split.
  *
   apply is_compact_nth; auto.
   replace (length x) with (length l);auto.
   now apply list_le_length in Hle.
  *
   now apply list_le_nth.
-
  assert (Hleq : length x = length l) by
   (apply lprod_length in Hm;
   now rewrite list_from_seq_length in Hm).
  split.
  +
   apply is_compact_from_all_nth.
   intros i Hlt.
   apply lprod_member with (d := default)(i := i) in Hm;
   auto.
    rewrite list_from_seq_nth in Hm; [now destruct Hm | lia].
  +
   apply nth_list_le; auto.
   intros i Hlt.
   apply lprod_member with (d := default)(i := i) in Hm;
   try lia.
   rewrite  list_from_seq_nth in Hm; auto; now destruct Hm.
Qed.   

Lemma my_algebraic_dir{P:ADCPO}: 
forall (l : list P),
is_directed (P := list_DCPO P) (compacts_le  (P := list_DCPO P) l).
Proof.
intro l.
rewrite compacts_le_lprod.
apply is_directed_lprod.
rewrite list_from_seq_length.
intros i Hl.
rewrite list_from_seq_nth; auto.
apply algebraic_dir.
Qed.


Lemma common_length_compacts_le{P:ADCPO}:
forall (l:list P), common_length 
 (compacts_le (P := list_DCPO P)l) = length l.
Proof.
intro l.
specialize (my_algebraic_dir l) as Hc.
destruct Hc as (Hne & _).
rewrite not_empty_member in Hne.
destruct Hne as (x & Hcx).
specialize (common_length_common _ (my_algebraic_dir l) _ Hcx) as Hql.
destruct Hcx as (_ & Hlex).
apply list_le_length in Hlex; congruence.
Qed.



Lemma my_algebraic_lub{P:ADCPO}: 
forall (l : list P), l = lub (d := list_DCPO P) 
 (compacts_le  (P := list_DCPO P) l).
intro l.
apply  (is_lub_lub_eq1 (D := list_DCPO P)); [| apply my_algebraic_dir].
apply is_lub_from_nth; [apply my_algebraic_dir | 
 apply common_length_compacts_le | ].
intros i Hlt.
split.
-
 intros x (y & (Hcy & Hley) & Heq); subst.
 now apply lnth_is_monotonic.
-
 intros y Hu.
 unfold is_upper in Hu.
 assert (Hu' : 
 forall l', list_le l' l -> is_compact (D := list_DCPO P) l' ->
  lnth i l' <= y ).
{
intros l' Hle' Hc.
apply Hu.
exists l'; repeat split; auto.
}
clear Hu.
revert i Hlt y Hu'.
induction l; intros i Hlt y Huy; cbn in Hlt; [lia |].
specialize (my_algebraic_dir l) as Hl.
destruct Hl as (Hne & _).
rewrite not_empty_member in Hne.
destruct Hne as (l' & Hcl' & Hle').
destruct i; cbn in *.
+
rewrite algebraic_lub at 1.
apply lub_is_minimal; [apply algebraic_dir |].
intros x (Hcx & Hlex).
apply (Huy (x :: l')); [now constructor | ].
apply is_compact_cons; auto.
+
 apply IHl; [lia |].
 intros l'' Hle'' Hcl''.
 specialize (algebraic_dir a) as Haa.
 destruct Haa as (Hne & _).
 rewrite not_empty_member in Hne.
 destruct Hne as (a' & Hca' & Hlea').
 apply (Huy (a' :: l'')); [now constructor |].
 apply is_compact_cons; auto.
 Qed.
  
 
Definition list_ADCPO (P:ADCPO) : ADCPO :=
{|
   algebraic_dcpo := list_DCPO P;
   algebraic_dir := my_algebraic_dir;
   algebraic_lub := my_algebraic_lub
|}.


Lemma  map_mono{P Q:Poset}(l l' : list P) (f : P -> Q):
is_monotonic f -> 
list_le l  l'  -> list_le  (map f l)  (map f l').
Proof.
intros Hm  Hle.
induction Hle; cbn ; constructor; [now apply Hm | auto].
Qed.

Lemma  map_rev_mono{P Q:Poset}(l l' : list P) (f : P -> Q):
is_rev_monotonic f -> 
 list_le  (map f l)  (map f l') -> list_le l  l'.
Proof.
intros Hm  Hle.
remember (map f l) as fl; remember (map f l') as fl'.
revert l l' Heqfl Heqfl'.
induction Hle; intros l1 l2 Heqfl Heqfl'; cbn.
 - 
  symmetry in Heqfl,Heqfl'.
  apply map_eq_nil in Heqfl,Heqfl'; subst; apply list_le_refl.
 -
   
   destruct l1; destruct l2; try discriminate.
   cbn in *.
   injection Heqfl; intros; subst.
   injection Heqfl'; intros; subst.
   constructor.
   +
    now apply Hm.
   +
    now apply IHHle.
Qed.     
    

Program Definition list_COMP{P:Poset}(c: COMPLETION P):
 COMPLETION (list_Poset P) :=
{|
   alg := list_ADCPO (alg c);
   inject :=  map (@inject P c);
   rev_inj := map (@rev_inj P c)
|}.

Next Obligation.
split; intros Hle.
-  apply map_mono; auto.
   intros x y Hl.
   now rewrite <- inject_bimono.
-     
 apply map_rev_mono in Hle; auto.
 intros x y Hl.
 now rewrite <- inject_bimono in Hl.
Qed.

Next Obligation.
intros P c p.
apply is_compact_from_all_nth.
rewrite length_map.
intros i Hlt.
unfold lnth.
replace (nth i (map (@inject P c) p) default) with
(nth i (map (@inject P c) p)
     (inject default));
      [| erewrite nth_indep; eauto; now rewrite length_map ].
rewrite map_nth.
apply inject_compact.
Qed.

Next Obligation.
intros P l l' p Hc.
cbn in *.
split; intro Hm.
-
 rewrite <- Hm.
 rewrite map_map.
 cbn in *.
 clear Hm p.
 induction l'; [reflexivity | cbn].
 f_equal.
 +
  rewrite inject_rev_inj; auto.
  now apply is_compact_hd in Hc.
 +
  apply IHl'.
  now apply is_compact_tl in Hc.
-
 rewrite <- Hm.
 rewrite map_map.
 replace (fun x : P =>
   rev_inj (inject x)) with (@id P); [now rewrite map_id |].
 extensionality x.
 now rewrite rev_inj_inject.
Qed.



Goal forall (P : Poset) (c:COMPLETION P),
@carrier (list_COMP c) = 
list (@carrier c).
Proof.
reflexivity.
Qed.


Lemma rev_is_monotonic{A:Poset} :
is_monotonic 
  (P1 := list_Poset A)
  (P2 := list_Poset A)
(@rev A).
Proof.
intros x y Hle.
apply nth_list_le.
-
 do 2 rewrite length_rev.
 now apply list_le_length.
-
 rewrite length_rev.
 intros i Hlt.
 rewrite rev_nth; [|  apply list_le_length in Hle; now rewrite Hle].
 rewrite rev_nth; auto.
 specialize Hle as Hl.
 apply list_le_length in Hl; rewrite Hl.
 apply list_le_nth with (i := length y - S i) in Hle; auto.
 lia.
 Qed.

 Lemma map_is_monotonic{A B:Poset}:
 forall (l : list A),
 is_monotonic 
 (P1 := EXP_Poset A B)
   (P2 := list_Poset B)
 (fun f => map f l).
Proof.
cbn.
intros l f g Hle.
apply nth_list_le.
-
 now do 2 rewrite length_map.
-
 rewrite length_map.
 intros i Hlt.
 rewrite nth_indep with (d' := (f default)); 
 [| now rewrite length_map].
 rewrite map_nth.
 rewrite nth_indep with (d' := (g default)); 
 [| now rewrite length_map].
 rewrite map_nth.
 apply Hle.
 Qed.


From Domain Require Import Lift.

Definition list_CPO (P:DCPO) := LIFT_CPO (list_DCPO P).
