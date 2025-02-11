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


From Coq Require Import List Utf8 RelationClasses
  PeanoNat Psatz Inverse_Image Wf_nat.



Section Wf. 

  Theorem well_founded_fn {A : Type} (P : A -> Prop) : forall (f : A -> nat),
    (forall (a : A), (forall (b : A), f b < f a -> P b) -> P a) -> forall (a : A), P a.
  Proof.
    intros f Ha a.
    refine ((fix Fn (u : A) (acc : Acc lt (f u)) {struct acc} : P u := 
      match f u as u' return f u = u' -> _ with 
      | 0 => fun (Hb : f u = 0) => Ha _ (fun (b : A) (Hc : f b < f u) => _ ) 
      | S n => fun Hb => 
        match acc with 
        | Acc_intro _ R => Ha u (fun (b : A) 
          (Hc : f b < f u) => Fn b (R (f b) Hc))
        end
      end eq_refl) a _); [abstract nia | eapply lt_wf].
  Qed.

  Theorem well_founded_acc {A : Type} (P : A -> Prop) : forall (f : A -> nat),
    (forall (a : A), (forall (b : A), f b < f a -> P b) -> P a) -> 
    forall (a : A), P a.
  Proof.
    intros f Ha a.
    refine((fix Fn (u : A) (acc : Acc lt (f u)) : P u := 
      match acc with 
      | Acc_intro _ R => 
        Ha u (λ (b : A) (Hb : f b < f u), Fn b (R (f b) Hb))
      end) a _); eapply lt_wf.
  Qed.


End Wf. 
