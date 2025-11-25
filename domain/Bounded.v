From Stdlib Require Export ProofIrrelevance Reals.
From Domain Require Export CPO.

Global Set Implicit Arguments.

Global Obligation Tactic := idtac.

Local Open Scope R_scope.

Record Bounded (a b : R) : Type := {
  bounded_val :> R;
  bounded_prop : a <= bounded_val <= b
}.

Lemma bounded_equal (a b : R) (x y : Bounded a b) :
bounded_val x = bounded_val y -> x = y.
Proof.
intro Heq.
destruct x as [x Hx], y as [y Hy].
cbn in Heq.
destruct Heq.
f_equal.
apply proof_irrelevance.
Qed.

Program Definition bounded_lub_nonempty
  (a b : R) (S : Setof (Bounded a b)) (Hnempty : ~is_empty S) : R :=
proj1_sig (completeness (fmap S (@bounded_val a b)) _ _).

Next Obligation.
intros a b S _.
exists b.
intro r.
intros ([r' Hbetween] & _ & Heq).
cbn in Heq.
subst r'.
exact (proj2 Hbetween).
Qed.

Next Obligation.
cbn.
intros a b S Hnempty.
rewrite not_empty_member in Hnempty.
destruct Hnempty as [r Hin].
exists r.
exists r.
split; [exact Hin | reflexivity].
Qed.

Definition bounded_lub_val (a b : R) (S : Setof (Bounded a b)) : R :=
match oracle (is_empty S) with
| left _ => a
| right Hnempty => bounded_lub_nonempty Hnempty
end.

Lemma bounded_lub_val_is_bounded
  (a b : R) (Hle : a <= b) (S : Setof (Bounded a b)) :
a <= bounded_lub_val S <= b.
Proof.
unfold bounded_lub_val.
destruct (oracle (is_empty S)) as [_ | Hnempty].
- split; [apply Rle_refl | exact Hle].
- cbn.
  unfold bounded_lub_nonempty.
  destruct completeness as [m [Hup Hleast] ].
  cbn.
  split.
  + rewrite not_empty_member in Hnempty.
    destruct Hnempty as [ [r Hbetween] Hin].
    transitivity r; [exact (proj1 Hbetween) | ].
    apply Hup.
    eexists.
    split; [exact Hin | reflexivity].
  + apply Hleast.
    intros r ([r' Hbetween] & Hin & Heq).
    cbn in Heq.
    subst r'.
    exact (proj2 Hbetween).
Qed.

Definition bounded_lub (a b : R) (Hle : a <= b) (S : Setof (Bounded a b)) :
Bounded a b := {|
  bounded_val := bounded_lub_val S;
  bounded_prop := bounded_lub_val_is_bounded Hle S
|}.

Program Definition Bounded_Poset (a b : R) (Hle : a <= b) : Poset := {|
  carrier := Bounded a b;
  default := {|
    bounded_val := a
  |};
  ord := fun x y => x <= y;
  refl := Rle_refl;
  trans := Rle_trans;
  antisym := _
|}.

Next Obligation.
intros a b Hle.
split; [apply Rle_refl | exact Hle].
Qed.

Next Obligation.
cbn.
intros a b _ x y Hxy Hyx.
apply bounded_equal, Rle_antisym; [exact Hxy | exact Hyx].
Qed.

Lemma bounded_lub_is_lub
  (a b : R) (Hle : a <= b) (S : Setof (Bounded_Poset Hle)) :
is_lub S (bounded_lub Hle S).
Proof.
split.
- intros x Hin.
  cbn in *.
  unfold bounded_lub_val.
  destruct (oracle (is_empty S)) as [Hempty | Hnempty].
  + rewrite is_empty_no_member in Hempty.
    contradict Hin.
    apply Hempty.
  + unfold bounded_lub_nonempty.
    destruct completeness as [m [Hup Hleast] ].
    cbn.
    clear Hleast.
    apply Hup.
    exists x.
    split; [exact Hin | reflexivity].
- cbn.
  intros x Hup.
  unfold bounded_lub_val.
  destruct oracle as [Hempty | Hnempty];
   [exact (proj1 (bounded_prop x)) | ].
  unfold bounded_lub_nonempty.
  destruct completeness as [m [Hup' Hleast] ].
  cbn.
  apply Hleast.
  intros r ([r' Hbetween] & Hin & Heq).
  cbn in Heq.
  subst r'.
  specialize (Hup {| bounded_val := r; bounded_prop := Hbetween |}).
  cbn in Hup.
  apply Hup, Hin.
Qed.

Program Definition Bounded_DCPO (a b : R) (Hle : a <= b) : DCPO := {|
  dcpo_poset := Bounded_Poset Hle;
  lub := fun S =>  bounded_lub Hle S
|}.

Next Obligation.
cbn.
intros a b Hle S Hdir.
apply bounded_lub_is_lub.
Qed.


Program Definition Bounded_CPO (a b : R) (Hle : a <= b) : CPO := {|
  dcpo_cpo := Bounded_DCPO Hle;
  bot := {| bounded_val := a |}
|}.

Next Obligation.
intros a v Hle.
split; [apply Rle_refl | exact Hle].
Qed.

Next Obligation.
cbn.
intros a b _ [x [Hax Hxb] ].
exact Hax.
Qed.
