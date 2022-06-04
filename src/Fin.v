From Coq Require Import PeanoNat.
From Equations Require Import Equations.

Section Fin. 

  Inductive Fin : nat -> Type :=
  | Fz {n : nat} : Fin (S n)
  | Fs {n : nat} : Fin n -> Fin (S n).


  
  Fixpoint n_to_fin (n : nat) : Fin (S n) :=
    match n with
    | 0 => Fz 
    | S n' => Fs (n_to_fin n')
  end.



  Fixpoint fin_to_n {n : nat} (f : Fin n) : nat :=
    match f with 
    | Fz => 0 
    | Fs t => S (fin_to_n t)
    end.
  


  Lemma n_to_fin_to_fin_to_n_id : 
    forall (n : nat), fin_to_n (n_to_fin n) = n.
  Proof.
    refine (
      fix Fn n :=
        match n with 
        | 0 => eq_refl 
        | S n' => _ 
        end).
      simpl; rewrite Fn.
      exact eq_refl.
  Qed.


  Lemma fin_inv_0 (f : Fin 0) : False.
  Proof.
    refine (match f with end).
  Defined.
  
 
  Lemma fin_inv_S {n : nat} (f : Fin (S n)) :
    (f = Fz) + {t | f = Fs t}.
  Proof.
    refine (match f with
      | Fz => _ 
      | Fs s => _ 
      end);
      [left | right; exists s]; 
      exact eq_refl.
  Defined.
  


  Lemma cast_fin : forall {n : nat} (f : Fin (S n)), 
    Fin (S (fin_to_n f)).
  Proof.
    refine (fix Fn n :=
      match n as n' return n = n' -> _ with
      | 0 => fun Hn f => _ 
      | S n' => fun Hn f => _
      end eq_refl);
    subst.
    + 
      pose proof (fin_inv_S f) as [Ha | (t & Hb)].
      subst; simpl.
      exact Fz.
      pose proof (fin_inv_0 t) as Hf; 
      refine (match Hf with end).
    + 
      pose proof (fin_inv_S f) as [Ha | (t & Hb)].
      subst; simpl.
      exact Fz.
      pose proof (Fn _ t) as Ft.
      subst; simpl.
      exact (Fs Ft).
  Defined. (* or Qed? *)
   

  Lemma fin_to_n_to_n_to_fin_id : 
    forall (n : nat) (f : Fin (S n)), 
      n_to_fin (fin_to_n f) = @cast_fin _ f.
  Proof.
    refine (fix Fn n :=
      match n as n' return n = n' -> _ with
      | 0 => fun Hn f => _ 
      | S n' => fun Hn f => _
      end eq_refl);
    subst.
    + 
      pose proof (fin_inv_S f) as [Ha | (t & Hb)].
      subst; simpl.
      exact eq_refl.
      pose proof (fin_inv_0 t) as Hf; 
      refine (match Hf with end).
    + 
      pose proof (fin_inv_S f) as [Ha | (t & Hb)].
      subst; simpl.
      exact eq_refl.
      pose proof (Fn _ t) as Ft.
      subst; simpl.
      rewrite Ft.
      reflexivity.
  Qed.

  



  
  

    


  


  
