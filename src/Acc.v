Require Import Lia
  Coq.Unicode.Utf8
  Coq.Bool.Bool 
  Coq.Init.Byte
  Coq.NArith.NArith
  Coq.Strings.Byte
  Coq.ZArith.ZArith
  Coq.Lists.List.

Lemma N_acc : forall n : nat, Acc lt n.
Proof.
    induction n.
    + constructor; intros ? Hy.
      nia.
    + apply Acc_intro.
      intros y Hy.
      apply Acc_intro.
      intros z Hz.
      inversion IHn as (Ih).
      apply Ih.
      nia. 
Qed.
