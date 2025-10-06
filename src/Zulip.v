From Coq Require Import Lia Arith.
(* Thanks to Li-yao *)
Section Gcd.

  Fixpoint gcd_rec (n m : nat) (acc : Acc lt (n + m)) {struct acc} :  nat.
  Proof.
    refine
        (match n as n' return n = n' -> _
         with
         | 0 => fun Ha  => m
         | S n' =>
             fun Ha =>
               match m as m' return m = m' -> _
               with
               | 0 => fun Hb => n
               | S m' => fun Hb => _
               end eq_refl
         end eq_refl).
    destruct (m  <? n) eqn:Hc.
    +
      (* m < n *)
      refine (gcd_rec (n - m) m _).
       pose proof (Acc_inv acc) as Hd.
       eapply Hd; (abstract nia).
    +
       (* n <= m *)
      refine (gcd_rec n (m - n) _).
      pose proof (Acc_inv acc) as Hd.
      eapply Hd; (abstract nia).
  Defined.


  

  Definition gcd : nat -> nat -> nat.
  Proof.
    intros n m.
    eapply (gcd_rec n m).
    eapply lt_wf.
  Defined.

  Eval compute in gcd 48 18. (* Nice! Love it! *)


  (* the Acc argument is irrelevant *)
  Lemma gcd_rec_irr : forall n m (acc acc' : Acc lt (n + m)),
      gcd_rec n m acc = gcd_rec n m acc'.
  Proof.
    fix Ihn 3.
    intros n m acc acc'.
    destruct acc, acc'.
    destruct n; simpl.
    - reflexivity.
    - destruct m; simpl.
      + reflexivity.
      + destruct (S m <? S n) eqn:Hc.
        * apply Ihn.
        * apply Ihn.
  Qed.


  
  Theorem gcd_m_n_swap : forall (n m : nat), m < n -> gcd n m = gcd (n - m) m.
  Proof.
    intros n m H.
    unfold gcd at 1.
    simpl.
    destruct n.
    - reflexivity.
    - destruct m.
      + reflexivity.
      + assert (S m <? S n = true).
        { apply Nat.ltb_lt. lia. }
        rewrite H0.
        apply gcd_rec_irr.
  Defined.


  Theorem gcd_n_m_swap : forall (n m : nat), n <= m -> gcd n m = gcd n (m - n).
   Proof.
     intros n m Ha.
     unfold gcd at 1; simpl.
     destruct n as [|n].
     +
       cbn; abstract nia.
     +
       destruct m as [|m].
       ++
         simpl. abstract nia.
       ++
         assert (Hb: S m <? S n = false).
         eapply Nat.ltb_ge; exact Ha.
         rewrite Hb.
         eapply gcd_rec_irr.
  Defined.
         
  Theorem gcd_ind : forall (P : nat -> nat -> nat -> Type),
      (forall m, P 0 m m) ->
      (forall n, P (1 + n) 0 (1 + n)) ->
      (forall (n m : nat), m < n -> 
          P (n - m) (1 + m) (gcd (n - m) (1 + m)) -> P (1 + n) (1 + m) (gcd (1 + n) (1 + m))) ->
      (forall (n m : nat), n <= m ->
          P (1 + n) (m - n) (gcd (1 + n) (m - n)) -> P (1 + n) (1 + m) (gcd (1 + n) (1 + m))) ->
      forall (n m : nat),  P n m (gcd n m).
  Proof.
    intros * Ha Hb Hc Hd n m.
    refine((fix fn (n : nat) (m : nat) (acc : Acc lt (n + m)) {struct acc} :=
              match n as n' return n = n' -> _
              with
              | 0 => fun He => _ 
              | S n' => fun He =>
                       match m as m' return m = m' -> _
                       with
                       | 0 => fun Hf => _
                       | S m' => fun Hf => _ 
                       end eq_refl
              end eq_refl) n m _); [eapply Ha | eapply Hb | | ].
    +
   
      destruct (m <? n) eqn:Hg.
      ++
        eapply Nat.ltb_lt in Hg.
        eapply Hc; subst; try assumption; try (abstract nia).
        eapply fn.
        pose proof (Acc_inv acc) as Hh.
        eapply Hh.
        (abstract nia).
      ++
        eapply Nat.ltb_ge in Hg.
        eapply Hd; subst; try assumption; try (abstract nia).
        eapply fn.
        pose proof (Acc_inv acc) as Hh.
        eapply Hh.
        (abstract nia).
    +
      eapply lt_wf.
  Defined.
  

  
  (* Proof by reflection *)

  
  Inductive gcd_type : nat -> nat -> nat -> Type :=
  | fz m : gcd_type 0 m m
  | sz n : gcd_type (1 + n) 0 (1 + n)
  | frec m n p : m < n -> gcd_type (n - m) (1 + m) p -> gcd_type (1 + n) (1 + m) p 
  | srec m n p : n <= m -> gcd_type (1 + n) (m - n) p -> gcd_type (1 + n) (1 + m) p.

  

  Theorem gcd_fix_gcd_type : forall (n m : nat), gcd_type n m (gcd n m).
  Proof.
   intros n m.
   induction n, m, (gcd n m) using gcd_ind.
   +
     subst; constructor.
   +
     subst; constructor.
   +
     eapply frec; try assumption.
     rewrite gcd_m_n_swap.
     simpl; exact IHn0.
     abstract nia.
   +
     eapply srec; try assumption.
     rewrite gcd_n_m_swap.
     simpl; exact IHn0.
     abstract nia.
  Defined.

  
     
  Theorem gcd_type_gcd_fix : forall (n m p : nat), gcd_type n m p -> p = gcd n m.
  Proof.
    intros n m p Ha.
    induction Ha as [ | |m n p Ha Hb IHn |m n p Ha Hb IHn].
    +
      cbn; reflexivity.
    +
      cbn; destruct n; reflexivity.
    +
      rewrite gcd_m_n_swap; try assumption.
      nia.
    +
      rewrite gcd_n_m_swap; try assumption.
      nia.
  Qed.
  

End Gcd.


Eval compute in gcd_fix_gcd_type 10 19.
From Stdlib Require Import Extraction.
Recursive Extraction gcd_fix_gcd_type.
