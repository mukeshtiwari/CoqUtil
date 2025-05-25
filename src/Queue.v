Require Import
  Program.Wf
  Vector
  List
  Arith
  Lia.

Import ListNotations.

Section Queue.

Variable L : nat.
Hypothesis H : 0 < L.

Lemma mod_lt: forall f,
  f mod L < L.
Proof.
  intros. apply Nat.mod_upper_bound.
  inversion H; subst. auto. auto.
Qed.

Theorem array_to_queue_obligation : forall (f r : nat), f < r -> r - S f < r - f.
Proof.
  intros * ha.
  abstract nia.
Qed.

Fixpoint array_to_queue_rec (f r : nat) (vec : Vector.t (option nat) L) 
  (acc : Acc lt (r - f)) : list (option nat) := 
  match lt_dec f r with 
    | left pf => (array_to_queue_rec (S f) r vec (Acc_inv acc (array_to_queue_obligation _ _ pf))) ++ 
          [Vector.nth vec (Fin.of_nat_lt (mod_lt f))]
    | right _ => nil 
  end. 

Definition array_to_queue (f r : nat) (vec : Vector.t (option nat) L)  := 
  match lt_dec f r with 
    | left pf => (array_to_queue_rec f r vec (lt_wf (r - f))) 
    | right _ => nil 
  end.

Lemma rec_irr : forall r f vec (acc acc' : Acc lt (r - f)),
    array_to_queue_rec f r vec acc = array_to_queue_rec f r vec acc'.
Proof.
  fix ihn 4.
  intros *.
  destruct acc, acc'.
  cbn. destruct (lt_dec f r); cbn.
  f_equal.
  eapply ihn.
  exact eq_refl.
Qed.

Theorem array_to_queue_rec_length_aux : forall x (vec : Vector.t (option nat) L) 
  f r acc, x = r - f -> length (array_to_queue_rec f r vec acc) = x.
Proof.
  intro x.
  induction (Wf_nat.lt_wf x) as [x _ ihn].
  intros * ha.
  specialize (ihn (r - S f)).  subst.
  destruct (lt_dec f r) as [ha | ha].
  + 
    specialize (ihn ltac:(nia) vec (S f) r).
    assert (hb : Acc lt (r - S f)).
    constructor.  intros. 
    inversion acc as [hacc]. 
    apply hacc. nia.
    specialize (ihn hb eq_refl).
    destruct acc; cbn. 
    destruct (lt_dec f r) as [hc | hc]; try nia.
    cbn. rewrite length_app. cbn.
    rewrite rec_irr with (acc' := hb).
    rewrite ihn. nia.
  +
    destruct acc; cbn.
    destruct (lt_dec f r); try nia.
    cbn. nia.
Qed.
  
Theorem array_to_queue_length : forall (vec : Vector.t (option nat) L) f r,
  length (array_to_queue f r vec) = r - f.
Proof.
  intros *. unfold array_to_queue. 
  destruct (lt_dec f r) as [ha | ha].
  + 
    eapply array_to_queue_rec_length_aux. 
    reflexivity.
  + 
    cbn; nia. 
Qed.
