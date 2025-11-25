From Stdlib Require Import FunctionalExtensionality PropExtensionality
 IndefiniteDescription Classical List Lia JMeq.
From Domain Require Export Container Haddock Product Exp.


Definition itree (F : Type -> Type) (X : Type) :=
    LPC (unit + Type)
    (fun x => 
     match x with
     inl _ => Empty_set
     | inr Y => Y
     end)
     (fun x => 
     match x with
     inl _ => X
     | inr Y => F Y
     end).


Definition pure{F : Type -> Type}{X : Type}(x:X) : 
  itree F X  :=  lnode 
  (inl tt) x (fun (x:Empty_set)   => lnbot).

Definition impure{F : Type -> Type}
{X Y : Type} (fy : F Y) (k : Y -> itree F X) :  itree F X 
 := lnode (inr Y) fy  k.

Definition fbot{F : Type -> Type}{X : Type} := @lnbot 
    (unit + Type)
    (fun x => 
     match x with
     inl _ => Empty_set
     | inr Y => Y
     end)
     (fun x => 
     match x with
     inl _ => X
     | inr Y => F Y
     end).



Lemma pure_not_fbot{F : Type -> Type}{X : Type}:
forall (x:X), pure (F := F) x <> fbot.
Proof.
intros x Heq.
specialize (@lnode_not_lnbot (unit + Type)
(fun x => 
 match x with
 inl _ => Empty_set
 | inr Y => Y
 end)
 (fun x => 
 match x with
 inl _ => X
 | inr Y => F Y
 end) (inl tt) x (fun (x:Empty_set)   => lnbot)
) as Hneq.
unfold pure,fbot in Heq.
contradict Hneq.
now rewrite Heq.
Qed.

Lemma impure_not_fbot{F : Type -> Type}
{X Y : Type}: forall (fy : F Y) (k : Y -> itree F X),
impure fy k  <> fbot.
Proof.
intros fy k Heq.
specialize (@lnode_not_lnbot (unit + Type)
(fun x => 
 match x with
 inl _ => Empty_set
 | inr Y => Y
 end)
 (fun x => 
 match x with
 inl _ => X
 | inr Y => F Y
 end) (inr Y) fy k
) as Hneq.
unfold impure,fbot in Heq.
contradict Hneq.
now rewrite Heq.
Qed.


Lemma pure_not_impure{F : Type -> Type}
{X Y : Type}: forall (x:X) (fy : F Y) (k : Y -> itree F X),
pure (F := F) x <> impure fy k.
Proof.
intros x fy k Heq.
unfold pure,impure in Heq.
assert (Habs : inl tt = inr Y); [ | discriminate].
eapply lnode_ord_same_shape.
rewrite Heq.
apply refl.
Qed.

Lemma pure_is_injective{F : Type -> Type}
{X: Type}: forall (x y:X),
 pure (F := F) x = pure (F := F) y -> x = y.
Proof.
intros x y Heq.
unfold pure in Heq.
apply lnode_injective in Heq.
destruct Heq as (_ & _ & Heq).
inversion Heq; subst.
now apply inj_pair2 in H1.
Qed.



Lemma impure_is_injective{F : Type -> Type}
{X Y Y': Type}: forall (fy : F Y) (fy' : F Y')
(k : Y -> itree F X) (k' : Y' -> itree F X),
impure fy k = impure fy' k' -> 
Y = Y' /\ JMeq fy fy' /\ JMeq k k'.
Proof.
intros fy fy' k k' Heq.
unfold impure in Heq.
apply lnode_injective in Heq.
destruct Heq as (He & Heq & Heq'); split; auto.
now injection He.
Qed.


Lemma fcases{F:Type -> Type}{X:Type} (f : itree F X):
({x: X | f = pure x} + 
{Y:Type & { fy : F Y & {k : Y -> itree F X | f = impure fy k }}}) + 
{f = fbot}.
Proof.
destruct (lcases f).
-
 destruct s.
 destruct s.
 destruct x.
 +
  destruct u.
  destruct s; subst.
  left; left.
  exists x0.
  unfold pure.
  f_equal.
  extensionality z; destruct z.
 +
  destruct s.
  left; right.
  exists T, x0, x.
  now subst.
-
  subst.
  now right.
Qed.


Lemma fcases_fbot{F:Type -> Type}{X:Type}: 
fcases (@fbot F X) = inright (eq_refl  (@fbot F X) ).
Proof.
(destruct (fcases fbot)); auto.
repeat destruct s.
-
 specialize (pure_not_fbot (F := F) x) as Hneq.
 now contradict Hneq.
-
 specialize (impure_not_fbot x0 x1) as Hneq.
 now contradict Hneq.
-
 f_equal.
  apply proof_irrelevance.      
Qed.


Lemma fcases_pure (F : Type -> Type) (X : Type) (x : X) :
@fcases F X (pure x) = inleft (inl (exist  _ x eq_refl)).
Proof.
destruct (fcases (pure x)) as [ [[x' Hm] | (Y & fy & k & Hm)] | Hm].
- generalize Hm.
  apply pure_is_injective in Hm.
  subst x'.
  intro Hm.
  do 3 f_equal.
  apply proof_irrelevance.
- contradict Hm.
  apply pure_not_impure.
- contradict Hm.
  apply pure_not_fbot.
Qed.

Lemma fcases_impure
  (F : Type -> Type) (X Y : Type) (fx : F X) (k : X -> itree F Y) :
@fcases F Y (impure fx k) =
inleft (inr (existT _  X (existT _ fx (exist _ k eq_refl)))).
Proof.
destruct (fcases (impure fx k)) as [ [[x Hm] | (Z & fz & k' & Hm)] | Hm].
- contradict Hm.
  symmetry.
  apply pure_not_impure.
- do 2 f_equal.
  generalize Hm.
  apply impure_is_injective in Hm.
  destruct Hm as (Heq1 & Heq2 & Heq3).
  subst Z.
  apply JMeq_eq in Heq2, Heq3.
  subst k' fz.
  intro Hm.
  do 3 f_equal.
  apply proof_irrelevance.
- contradict Hm.
  apply impure_not_fbot.
Qed.



Definition fbisim{F : Type -> Type}{X : Type}:=
    @bisim (unit + Type)
    (fun x => 
     match x with
     inl _ => Empty_set
     | inr Y => Y
     end)
     (fun x => 
     match x with
     inl _ => X
     | inr Y => F Y
     end).


Lemma fbisim_unfold {F : Type -> Type}{X : Type}:
forall (m m' : itree F X), fbisim m m' <->
( m = fbot /\ m' = fbot) \/
(exists x, m = pure x /\ m' = pure x) \/
(exists Y (fy: F Y) k k', m = impure fy k /\ m' = impure fy k' /\ 
forall x, fbisim (k x) (k' x)).
Proof.
intros m m'.
split; intro Hh.
-
 unfold fbisim in Hh.
 rewrite bisim_unfold in Hh.
 destruct Hh as 
  [(Heq & Heq') | (a & l & f & f' &  (Heq & Heq' & Heq''))]; 
 subst; [now left | right].
 destruct a as [ | Y].
 +
  left.
  cbn in f, f'.
  destruct u.
  unfold pure.
  exists l; split; f_equal; now extensionality w.
 +
  right.
  unfold impure.
  now exists Y, l, f, f'.
-
unfold fbisim.
destruct Hh as 
 [(Heq & Heq') | [(x & Heq & Heq')
  | (Y & fy & k & k' & Heq & Heq' & Ha) ]]; subst; 
  try (now rewrite bisim_iff_eq).
 unfold impure.
 rewrite bisim_unfold.
 right.
 now exists (inr Y), fy, k, k'.
Qed. 


Lemma fbisim_coind{F : Type -> Type}{X:Type}:
forall  (R: binary (itree F X) (itree F X)),
 (forall (m m' : itree F X),
 R m m' -> ( m = fbot /\ m' = fbot) \/
 (exists x, m = pure x /\ m' = pure x) \/
 (exists Y (fy: F Y) k k', m = impure fy k /\ m' = impure fy k' /\ 
 forall x, R (k x) (k' x))) 
 -> forall (m m' : itree F X), R m m' -> fbisim m m'.
Proof.
intros R Hco m m' HR.
apply bisim_coind with (R :=R); auto.
intros c c' HR'.
specialize (Hco c c' HR').
destruct Hco as 
  [(Heq & Heq') | [(x & Heq & Heq')
  | (Y & fy & k & k' & Heq & Heq' & Ha) ]];
    subst; [now left | 
    right | right ].
-
  exists (inl tt), x, 
    (fun _:Empty_set => fbot),
    (fun _:Empty_set => fbot); 
    repeat split; auto.
  now intro.
-
  exists (inr Y), fy, k, k';
   repeat split; auto.
Qed.
   



Lemma fbisim_strong_coind{F : Type -> Type}{X:Type}:
forall  (R: binary (itree F X) (itree F X)),
 (forall (m m' : itree F X),
 R m m' -> ((m = fbot /\ m' = fbot) \/
 (exists x, m = pure x /\ m' = pure x) \/
 (exists Y (fy: F Y) k k', m = impure fy k /\ m' = impure fy k' /\ 
 forall x, R (k x) (k' x))) \/ fbisim m m') 
 -> forall (m m' : itree F X), R m m' -> fbisim m m'.
Proof.
intros R Ha m m' HR.
destruct  (Ha _ _ HR) as [ Hco | Hb]; auto.
apply fbisim_coind 
with (R := fun (u v : itree F X) => (R u v \/ fbisim u v)); auto.
intros u v Hr.
destruct Hr as [Hr | Hr].
-
destruct (Ha _ _ Hr); auto.
  + 
   destruct H as 
   [(He1 & He2) |
    [(x & He) |
      (Y & fy & k & k' & He1 & He2 & Ha' )] ].
   *
    now left.
   *
    right;left.
    now exists x.
   *
   right;right.
   exists Y,fy,k,k'; repeat split; auto.
 +
  rewrite fbisim_unfold in H.          
  destruct H as 
  [(He1 & He2) |
   [(x & He) |
     (Y & fy & k & k' & He1 & He2 & Ha' )] ].
  *
   now left.
  *
   right;left.
   now exists x.
  *
  right;right.
  exists Y,fy,k,k'; repeat split; auto.
-
rewrite fbisim_unfold in Hr.
destruct Hr as 
[(He1 & He2) |
 [(x & He) |
   (Y & fy & k & k' & He1 & He2 & Ha' )] ].
+
 now left.
+
 right;left.
 now exists x.
+
right;right.
exists Y,fy,k,k'; repeat split; auto.
Qed.

Lemma fbisim_iff_eq{F : Type -> Type}{X:Type}:
forall (m m' : itree F X),
fbisim m m' <-> m = m'.
Proof.
unfold fbisim;split; intro Hh.
-
 now rewrite bisim_iff_eq in Hh.
-
 now rewrite bisim_iff_eq.
Qed. 
 
Lemma impure_is_monotonic{F : Type -> Type}{X Y : Type} (fy : F Y):
is_monotonic 
(P1 := (EXP_Poset _ _))
(P2 := itree F X)
(impure fy).
Proof.
intros x y Hle.
apply lnode_is_monotonic.
intro u.
apply (Hle u).
Qed.


Definition itree_CPO{F : Type -> Type}{X: Type} :=
{|dcpo_cpo := itree F X ; bot := fbot; bot_least := lnbot_least |}.



Lemma itree_ord_inv{F:Type -> Type}{X}(m m' : itree F X):
m <= m' ->
m = fbot \/
 (exists x, m = pure (F:=F) x /\ m' = pure (F:= F) x) \/
 (exists (Z:Type) fz k k', 
   m = impure (Y := Z) fz k /\ 
   m' = impure (Y := Z) fz k' /\
  forall y, k y <= k' y).
Proof.
intros Hle.
cbn in Hle.
destruct (fcases m) as
    [ [(x & He) | (Z & fz & k & He)]| He]; subst;
destruct (fcases m') as
    [ [(x' & He) | (Z' & fz' & k' & He)]| He]; subst;
    try (now left).
-
 right;left.
 exists x; split; auto.
 f_equal.
 now apply lnode_ord_labels_eq in Hle.
-
 apply lnode_ord_same_shape in Hle.
 discriminate.
-
 left.
 now apply (le_bot_eq (C := @itree_CPO F X) )in Hle.
-
 apply lnode_ord_same_shape in Hle.
 discriminate.
-
 right;right.
 exists Z,fz,k.
 specialize Hle as Heq.
 unfold impure in Heq.
 apply lnode_ord_same_shape in Heq; injection Heq; 
 intros; subst.
 exists k';  repeat split; auto.
 +
  f_equal.
  now apply lnode_ord_labels_eq in Hle.
 +
  now apply lnode_ord_func_ord in Hle.
-
 left.
 now apply (le_bot_eq (C := @itree_CPO F X) )in Hle.
 Qed.


Lemma impure_is_rev_monotonic{F:Type -> Type}{X Y:Type} (fy: F Y):
is_rev_monotonic (P1 := EXP_Poset Y (itree F X)) (P2 := itree F X) (impure fy).
Proof.
intros u v Hle.
apply itree_ord_inv in Hle. 
destruct Hle as [Heq | [(w & Heq1 & Heq2) | 
(W & fw &  c & c' & Heq1 & Heq2 & Ha)]]; subst.
-
 contradict Heq; apply impure_not_fbot.
-
 symmetry in Heq1; contradict Heq1;
 apply pure_not_impure.
-
 apply impure_is_injective in Heq1,Heq2.
 destruct Heq1 as (Heq & Hj1 & Hj2); subst. 
 destruct Heq2 as (Heq & Hj1 & Hj2); subst.
 intro u.
 apply Ha.
Qed.


Program Definition itree_ACPO{F : Type-> Type}{X: Type}
:=
{|adcpo_acpo := itree F X;abot := fbot|}.

Next Obligation.
intros.
apply lnbot_least.
Qed.

(*finite interaction trees*)


Definition finite_itree (F : Type -> Type) (X : Type) :=
    LFPC (unit + Type)
    (fun x => 
     match x with
     inl _ => Empty_set
     | inr Y => Y
     end)
     (fun x => 
     match x with
     inl _ => X
     | inr Y => F Y
     end).

  
Lemma empty_finite_support{T:Type}(b:T):
forall (f: Empty_set -> T), is_finite (support f b).
Proof.
intros f.
exists nil.
intros [].
Qed.


Definition fpure{F : Type -> Type}{X : Type}(x:X) : 
     finite_itree F X  :=  flcnode
     (inl tt) x {|Exp.func := fun e:Empty_set => 
     match (e:Empty_set) with end; 
     Exp.fsup := empty_finite_support Lcbot (fun e:Empty_set => 
     match e with end) |}.


Definition fimpure{F : Type -> Type}
   {X Y : Type} (fy : F Y) 
   (k : finitely_supported Y (finite_itree F X) Lcbot):  finite_itree F X 
    := flcnode (inr Y) fy  k.


Lemma finite_itree_ind{F : Type -> Type}(X: Type)
(P : finite_itree F X -> Prop) :
P Lcbot ->
(forall x, P (fpure (F:= F) x)) ->
(forall Y (fy : F Y) k, 
( (forall (y:Y) , P (Exp.func _ k y)) -> P (fimpure fy k)))->
forall (ff : finite_itree F X), P ff.
Proof.
intros Hb Hp Hi ff.
apply LFPC_ind; auto.
intros [ [] | Y].
-
 intros x f _.
 unfold fpure in Hp.
 specialize (Hp x).
 destruct f as (f & Hf).
 cbn in Hp.
 replace (fun e : Empty_set =>
 match
   e
   return
     (LFPC (unit + Type)
        (fun x : unit + Type =>
         match x with
         | inl _ => Empty_set
         | inr Y => Y
         end)
        (fun x0 : unit + Type =>
         match x0 with
         | inl _ => X
         | inr Y => F Y
         end))
 with
 end) with f in Hp by (extensionality u; destruct u).
 now replace Hf with (empty_finite_support Lcbot f)
 by now apply proof_irrelevance.
 -
  intros fy (f & Hf) Ha.
  apply Hi,Ha.
Qed.  

Lemma inject_fpure{F : Type-> Type}{X : Type}(x: X):
(inject (c := itree F X) (fpure (F := F) x)) = (pure (F := F) x).
Proof.
unfold pure.
rewrite lnode_extends_flcnode.
-
 apply f_equal.
 unfold fpure.
 f_equal.
 apply fin_sup_equal.
 extensionality y; destruct y.
-
 apply compacts_are_functions_with_finite_support_and_compact_values.
 split; [ | intros []].
 apply empty_finite_support.
Qed.


Lemma inject_continuation{F: Type -> Type}{X Y : Type}
(k: finitely_supported Y
      (finite_itree F X) Lcbot) :
is_compact (D := EXP_Poset Y (itree F X))
  (fun y : Y =>
   inject  (c := itree F X)(Exp.func Lcbot k y)).
Proof.
apply
  (@compacts_are_functions_with_finite_support_and_compact_values
  Y (@itree_ACPO F X)).
  split.
  -
  destruct k.
  cbn.
  destruct fsup as (l & Hl).
  exists l.
  intros y Hmy.
  apply Hl.
  intro Heq.
  apply Hmy.
  now rewrite Heq.
  -
  intro a.
  apply inject_compact.
 Qed.   


Lemma inject_fimpure{F : Type-> Type}{X Y: Type}
(fy: F Y): forall k,
(inject (c := itree F X) (fimpure fy k)) =
(impure fy (fun y : Y => inject (c := itree F X) (Exp.func _ k y))).
intro k.
unfold impure.
rewrite lnode_extends_flcnode; [ | apply inject_continuation].
apply f_equal.
unfold fimpure.
f_equal.
destruct k eqn:Hk.
unfold rev_inj.
cbn.
apply fin_sup_equal.
cbn.
extensionality y.
destruct ( oracle
(@is_compact
   (EXP_Poset Y
      (@dcpo_poset
         (@algebraic_dcpo
            (@alg
               (@poset_ppo
                  (LFPC_PPO (unit + Type)
                     (fun x : unit + Type =>
                      match x with
                      | @inl _ _ _ => Empty_set
                      | @inr _ _ Y0 => Y0
                      end)
                     (fun x : unit + Type =>
                      match x with
                      | @inl _ _ _ => X
                      | @inr _ _ Y0 => F Y0
                      end)))
               (LPC (unit + Type)
                  (fun x : unit + Type =>
                   match x with
                   | @inl _ _ _ => Empty_set
                   | @inr _ _ Y0 => Y0
                   end)
                  (fun x : unit + Type =>
                   match x with
                   | @inl _ _ _ => X
                   | @inr _ _ Y0 => F Y0
                   end))))))
   (fun y0 : Y =>
    @inject
      (@poset_ppo
         (LFPC_PPO (unit + Type)
            (fun x : unit + Type =>
             match x with
             | @inl _ _ _ => Empty_set
             | @inr _ _ Y0 => Y0
             end)
            (fun x : unit + Type =>
             match x with
             | @inl _ _ _ => X
             | @inr _ _ Y0 => F Y0
             end))) (itree F X) (func y0)))).
-
 now rewrite rev_inj_inject.
-
 contradict n.
 specialize (@inject_continuation F X Y k) as Hi.
 now subst.
Qed.


  
(*misc*)
Lemma is_lub_pure_remove{F:Type -> Type}{X:Type} :
forall (S : Setof (itree F X)) (x: X),
is_directed (P := itree F X)  S -> 
is_lub  (P := itree F X) S (pure (F := F) x) -> 
remove S fbot = single (pure (F := F) x).
Proof.
intros S x Hd Hl.
assert (Hn: S <> single fbot).
{
 intro Heq;subst.
 destruct Hl as (Hu & Hm).
 specialize (@single_pbot_upper_pbot (CPO2PPO(itree_CPO(F:=F)(X := X)))) as Hp.
 specialize (Hm _ Hp).
 apply (itree_ord_inv) in Hm.
 destruct Hm as [Heq | [(w & Heq1 & Heq2) | 
(Z & fz & k & k' & Heq1 & Heq2 & Ha)]]; subst.
-
 contradict Heq; apply pure_not_fbot.
-
 symmetry in Heq2 ;contradict Heq2; apply pure_not_fbot.
-
contradict Heq1; apply pure_not_impure.
}
destruct Hd as (Hne &_).
rewrite (@is_lub_remove_bot (CPO2PPO(itree_CPO(F:=F)(X := X)))) in Hl; auto.
apply set_equal; intro y ; split; intro Hm.
-
 rewrite member_single_iff.
 destruct Hl as (Hu & Hmin).
 specialize (Hu _ Hm).
 apply (itree_ord_inv) in Hu.
 destruct Hu as [Heq | [(w & Heq1 & Heq2) | 
(Z & fz & k & k' & Heq1 & Heq2 & Ha)]]; subst;auto.
+
 destruct Hm; contradiction.
+
contradict Heq2; apply pure_not_impure.
-
rewrite member_single_iff in Hm; subst.
apply not_empty_not_single_2dif in Hn; auto.
destruct Hn as (y & Hmy & Hny).
assert (Hmn: member (remove S fbot) y) by now split.
destruct Hl as (Hu & _).
specialize (Hu _ Hmn).
apply (itree_ord_inv) in Hu.
destruct Hu as [Heq | [(w & Heq1 & Heq2) | 
(Z & fz & k & k' & Heq1 & Heq2 & Ha)]]; subst;auto;
 try contradiction.
 +
  apply pure_is_injective in Heq2; intros; subst.
  split; auto.
 +
  now apply pure_not_impure in Heq2.
Qed.
 
Lemma is_lub_pure{F:Type -> Type}{X:Type} :
forall (S : Setof (itree F X)) (x: X),
is_directed (P := itree F X)  S -> 
is_lub  (P := itree F X) S (pure (F := F) x) -> 
S = single (pure (F := F) x) \/ 
S = (fun m => m = fbot \/ m = pure (F := F) x).
Proof.
intros S x Hd Hl.
eapply is_lub_pure_remove in Hd;eauto.
destruct (oracle (member S fbot)).
- 
right.
apply set_equal; intro y ; split; intro Hm.
+
unfold member; cbn.
destruct (oracle (y = fbot )); [now left | right].
assert (Hmr: member (remove S fbot) y); [split; auto |].
rewrite Hd in Hmr.
now rewrite member_single_iff in Hmr.
+
unfold member in Hm; cbn in Hm.
destruct Hm as [Hm | Hm]; subst; auto.
assert (Hmr: member (remove S fbot) (pure x)).
*
  rewrite Hd.
  apply member_single.
*
 now destruct Hmr.
-
rewrite not_member_remove_eq in Hd; auto.
Qed.



Lemma ffucp_aux3_aux_aux1{F:Type -> Type}{X:Type}
(S: Setof (itree F X)) (Z: Type) (fz: F Z) (k: Z -> itree F X):
~member S fbot -> is_upper S (impure fz k) ->
forall x, member S x -> exists y, x = impure fz y.
Proof.
intros Hnm Hu x Hm.
specialize (Hu _ Hm).
apply itree_ord_inv in Hu.
destruct Hu as [Heq | [(w & Heq1 & Heq2) | 
(W & fw & c & kc' & Heq1 & Heq2 & Ha)]]; subst;
[contradiction | | ].
- symmetry in Heq2; contradict Heq2; apply pure_not_impure.
-
 apply impure_is_injective in Heq2.
 destruct Heq2 as (HeqT & Hj1 & Hj2); subst.
 now exists c.
Qed. 
 

Lemma ffucp_aux3_aux_aux2{F:Type -> Type}{X:Type}
(S: Setof (itree F X)) (Z: Type) (fz: F Z) (k: Z -> itree F X):
~member S fbot -> is_upper S (impure fz k) ->
forall {x : {m | member S m}},
 exists y, proj1_sig x = impure fz y.
Proof.
intros Hnm Hu (x & Hx).
cbn.
eapply ffucp_aux3_aux_aux1; eauto.
Qed.


Lemma ffucp_aux3_aux_aux3{F:Type -> Type}{X:Type}
(S: Setof (itree F X)) (Z: Type) (fz: F Z) (k: Z -> itree F X):
~member S fbot -> is_upper S (impure fz k) ->
exists (f : {m | member S m} -> (Z -> (itree F X))),
forall x, proj1_sig x = impure fz (f x).
Proof.
intros Hnm Hu.
apply (@functional_choice ({m | member S m}) ((Z -> (itree F X))) (fun x y =>  proj1_sig x = impure fz y)).
eapply ffucp_aux3_aux_aux2; eauto.
Qed.


Lemma ffucp_aux3_aux_aux4{F:Type -> Type}{X:Type}
(S: Setof (itree F X)) (Z: Type) (fz: F Z) (k: Z -> itree F X):
~member S fbot -> is_upper S (impure fz k) ->
exists (f : itree F X -> (Z -> (itree F X))),
forall x, member S x -> x = impure fz (f x).
 Proof.
intros Hnm Hu.
specialize (ffucp_aux3_aux_aux3 S Z fz k Hnm Hu)
as Hex.
destruct Hex as (g & Hag).
exists
(fun m => 
match (oracle (member S m)) with
left Hm =>  g (exist _ m Hm)
| right Hnm => fun _ => fbot
end).
intros x Hmx.
destruct (oracle (member S x)); [| contradiction].
exact (Hag (exist _ x m)).
Qed.

Lemma ffucp_aux3_aux_aux5{F:Type -> Type}{X:Type}
(S: Setof (itree F X)) (Z: Type) (fz: F Z) (k: Z -> itree F X) (Hnm: ~member S fbot) (Hu: is_upper S (impure fz k)):
{f : itree F X -> (Z -> (itree F X)) | 
forall x, member S x -> x = impure fz (f x)}.
 Proof.
 apply constructive_indefinite_description.
 eapply ffucp_aux3_aux_aux4; eauto.
 Qed.



Definition rev_impure{F:Type -> Type}{X:Type}
(S: Setof (itree F X)) (Z: Type) (fz: F Z) (k: Z -> itree F X) (Hnm: ~member S fbot) (Hu: is_upper S (impure fz k))
: itree F X -> Z -> itree F X 
:=
proj1_sig (ffucp_aux3_aux_aux5 S Z fz k Hnm Hu).



Lemma impure_rev_impure{F:Type -> Type}{X:Type}
(S: Setof (itree F X)) (Z: Type) (fz: F Z) (k: Z -> itree F X) (Hnm: ~member S fbot) (Hu: is_upper S (impure fz k)):
forall x, member S x -> x = impure fz (rev_impure S _ fz k Hnm Hu x).
Proof.
intros.
now apply 
 (proj2_sig (ffucp_aux3_aux_aux5 S Z fz k Hnm Hu)).
Qed.




Lemma rev_impure_is_monotonic_on{F:Type -> Type}{X Z:Type} 
(S : Setof (itree F X))
(fz: F Z)
(k : Z -> itree F X)
(Hnm : ~member S fbot)
(Hu: is_upper (P := itree F X) S (impure fz k)):
is_monotonic_on (P1 :=(itree F X)) (P2 :=  EXP_Poset Z (itree F X)) (rev_impure S Z fz k Hnm Hu) S.
Proof.
intros x y Hmx Hmy Hle.
specialize (impure_rev_impure  S Z fz k Hnm Hu) as Hr.
rewrite (Hr _ Hmx) in Hle.
rewrite (Hr _ Hmy) in Hle.
now apply impure_is_rev_monotonic in Hle.
Qed.


Lemma fmap_rev_impure_impure{F:Type -> Type}{X Z:Type} 
(S : Setof (itree F X))
(fz: F Z)
(k : Z -> itree F X)
(Hnm : ~member S fbot)
(Hu: is_upper (P := itree F X) S (impure fz k)):
 S =
fmap (fmap S (rev_impure S Z fz k Hnm Hu))
  (impure fz).
Proof. 
apply set_equal; intros x; split; intro Hm.
-
 rewrite <- fmap_comp.
 exists x; split; auto.
 now apply impure_rev_impure.
-
rewrite <- fmap_comp in Hm.
destruct Hm as (y & Hmy & Heq);subst.
specialize (impure_rev_impure S Z fz k Hnm Hu _ Hmy) as Hr.
unfold comp.
now rewrite <- Hr.
Qed.


Lemma ffucp_aux3_aux{F:Type -> Type}{X:Type}
(S: Setof (itree F X)):
is_directed S -> 
forall (Z: Type) (fz: F Z) (k: Z -> itree F X),
 is_lub S (impure fz k)
->
 exists (K : Setof (Z -> itree F X)),
 is_directed (P := EXP_Poset Z (itree F X)) K /\
 remove S fbot = fmap K (impure fz) /\
 is_lub  (P := EXP_Poset Z (itree F X)) K k.
Proof.
intros Hd Z fz k Hl.
assert (Hn: S <> single fbot).
{
 intro Heq;subst.
 destruct Hl as (Hu & Hm).
 specialize (@single_pbot_upper_pbot (CPO2PPO(itree_CPO(F:=F)(X := X)))) as Hp.
 specialize (Hm _ Hp).
 apply (itree_ord_inv) in Hm.
 destruct Hm as [Heq | [(w & Heq1 & Heq2) | 
(W & fw &  c & c' & Heq1 & Heq2 & Ha)]]; subst.
-
 now apply impure_not_fbot in Heq.
-
 symmetry in Heq1; now apply pure_not_impure in Heq1.
-
symmetry in Heq2;
now apply impure_not_fbot in Heq2.
}
specialize Hd as Hne.
destruct Hne as (Hne & _).
rewrite  (is_lub_remove_bot (P := CPO2PPO (@itree_CPO F X)) S (impure fz k) Hne Hn) in Hl.
apply (remove_pbot_directed (P := CPO2PPO (@itree_CPO F X))) in Hd; auto.
cbn in *.
specialize (remove_not_member S fbot) as Hnm.
remember (remove S fbot) as S'.
clear HeqS' Hn Hne S.
rename S' into S.
specialize Hl as Hu.
destruct Hu as (Hu & _).
exists (fmap S (rev_impure S _ fz k Hnm Hu)).
split; [ | split ].
- 
 apply @monotonic_on_directed; auto.
 apply rev_impure_is_monotonic_on.
- 
 apply fmap_rev_impure_impure.
-
 specialize (fmap_rev_impure_impure S fz k Hnm Hu)
 as HS.
 remember (fmap S (rev_impure S Z fz k Hnm Hu)) as S'.
 rewrite HS in Hl.
 assert (Hd' : is_directed (P := (EXP_Poset Z (itree F X))) S').
 {
  rewrite HeqS'.
  apply @monotonic_on_directed; auto.
  apply rev_impure_is_monotonic_on.
 }
 clear S Hd Hnm Hu HeqS' HS.
 rename S' into S, Hd' into Hd.
 assert (Hd' : is_directed ( fmap S (impure fz)) ).
 {
    apply (monotonic_directed
    (P1 := EXP_Poset Z (itree F X))
    (P2 := itree F X)); auto.
    apply impure_is_monotonic.
 }
 split.
 {
   intros u Hmu.
   destruct Hl as (Hu & Hm).
   cbn in *.
   remember (impure fz u) as v.
   assert (Hmv :member (fmap S (impure fz)) v)
    by (subst; now exists u).
   specialize (Hu _ Hmv);
   subst.
   now apply impure_is_rev_monotonic in Hu.   
 }
  cbn.
  intros y Huy.
  destruct Hl as (Hu & Hm).
  cbn in *.
  remember (impure fz y) as v.
  assert (Huv : is_upper (fmap S (impure fz)) (impure fz y)).
  {
    intros z (w & Hmw & Heq); subst.
    apply impure_is_monotonic.
    now apply Huy.
  }
  specialize (Hm _ Huv).
  now apply impure_is_rev_monotonic in Hm.
 Qed.
