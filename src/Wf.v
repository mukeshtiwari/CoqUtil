Section Wf.

  Definition Nat := nat.
  
  Context 
    {A : Type}
    (f : A -> Nat).
  
  Definition ltof (a b : A) := f a < f b.

  Lemma acc_bounded : forall n (a : A), 
    f a < n -> Acc ltof a.
  Proof.
    induction n as [|n IHn];
    simpl.
    +
      intros ? Ha.
      nia.
    +
      intros ? Ha.
      constructor.
      intros ? Hb.
      unfold ltof in Hb.
      eapply IHn.
      nia.
  Qed.


  Theorem acc_ltof : ∀ a : A, Acc ltof a .
  Proof.
    intros a.
    eapply (acc_bounded (S (f a))).
    nia.
  Qed.
  
  Theorem well_founded_ltof: well_founded ltof.
  Proof.
    unfold well_founded.
    eapply acc_ltof.
  Qed.

End Wf.
