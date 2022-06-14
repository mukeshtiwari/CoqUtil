From Coq Require Import 
  PeanoNat Lia.

Section Fin. 

  Inductive Fin : nat -> Type :=
  | Fz {n : nat} : Fin (S n)
  | Fs {n : nat} : Fin n -> Fin (S n).


  
  Fixpoint nat_to_fin (n : nat) : Fin (S n) :=
    match n with
    | 0 => Fz 
    | S n' => Fs (nat_to_fin n')
  end.



  Fixpoint fin_to_nat {n : nat} (f : Fin n) : nat :=
    match f with 
    | Fz => 0 
    | Fs t => S (fin_to_nat t)
    end.
  


  Lemma nat_to_fin_and_fin_to_nat_inv : 
    forall (n : nat), fin_to_nat (nat_to_fin n) = n.
  Proof.
    refine (
      fix Fn n :=
        match n with 
        | 0 => eq_refl 
        | S n' => _ 
        end).
      simpl; rewrite Fn.
      exact eq_refl.
  Defined.


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
    Fin (S (fin_to_nat f)).
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
  Defined.
   

  Lemma fin_to_nat_and_nat_to_fin_inv : 
    forall (n : nat) (f : Fin (S n)), 
      nat_to_fin (fin_to_nat f) = @cast_fin _ f.
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
  Defined.




  Lemma FS_inj : 
    forall {n} (x y : Fin n), Fs x = Fs y ->  x = y.
  Proof.
    intros ? ? ? Heq.
    refine
      match 
        Heq in _ = a 
        return 
        match 
          a as a' in Fin n 
          return 
            match n with 
            | 0 => Prop 
            | S n' => Fin n' -> Prop
            end 
        with
        | Fz => fun _ => True 
        | Fs y => fun x' => x' = y
        end x
    with
    | eq_refl => eq_refl 
    end.
  Defined.
  

  (*

    inversion Heq as (Heqq).
    apply Eqdep.EqdepTheory.inj_pair2.
    exact Heqq.
  Qed.
  *)

  Lemma fin_to_nat_lt :
    forall {n : nat} (f : Fin n), 
    fin_to_nat f < n.
  Proof.
    induction n.
    + intros f.
      pose proof (fin_inv_0 f) as Hf;
      refine (match Hf with end).
    + intros f. 
      pose proof (fin_inv_S f) as [H | (t & H)].
      subst; simpl.
      apply Nat.lt_0_succ.
      subst; simpl.
      apply Lt.lt_n_S,
      IHn.
  Defined.

    
  (** of_nat p n returns the p{^ th} element of 
      fin n if p < n, othewise a proof that n <= p else *)
  Definition of_nat : forall (p n : nat), 
    (Fin n) + {m | p = n + m}.
  Proof.
    intros p n.
    revert n p.
    refine (fix Fn n := 
      match n as n' return n' = n -> 
        forall pt, (Fin n') + {m | pt = n' + m}  with
      | 0 => fun He p => inr (exist _ p eq_refl)
      | S n' => fun He p => 
        match p as p' return p = p' -> _ with 
        | 0 => fun Hp => inl Fz
        | S p' => fun Hp => match Fn n' p' with 
          | inl t => inl (Fs t) 
          | inr (exist _ m e) => inr (exist _ m _)
          end 
        end eq_refl
      end eq_refl).
      rewrite e.
      reflexivity.
  Defined.


  Definition of_nat_lt : forall {p n : nat}, p < n -> Fin n.
  Proof.
    intros ? ?.
    revert n p.
    refine 
      (fix Fn n :=
        match n as n' 
          return n = n' -> 
            forall p, p < n' -> Fin n'
        with
        | 0 => fun Hn p Hp => False_rect _ (PeanoNat.Nat.nlt_0_r p Hp)
        | S n' => fun Hn p => 
            match p as p' 
              return p = p' -> p' < S n' -> Fin (S n') 
            with 
            | 0 => fun Hp Hsp => @Fz _  
            | S p' => fun Hp Hsp => 
              @Fs _ (Fn n' p' (proj2 (Nat.succ_lt_mono _ _ ) Hsp)) 
            end eq_refl 
        end eq_refl).
  Defined.


  Require Import Eqdep_dec Arith.

  Fact uip_nat {n : nat} (e : n = n) : e = eq_refl.
  Proof. apply UIP_dec, eq_nat_dec. Qed.

  Fact le_inv n m (H : n <= m) :
      (exists e : m = n, eq_rect _ _ H _ e = le_n n)
    \/ (exists m' (e : m = S m') (H' : n <= m'), 
      eq_rect _ _ H _ e = le_S _ _ H').
  Proof.
    revert m H.
    intros ? [ | m H ].
    + left; now exists eq_refl.
    + right; now exists m, eq_refl, H.
  Qed.

  Require Import Equations.Prop.Equations.
  Set Equations With UIP.
  Scheme le_indd := Induction for le Sort Prop.

  Lemma le_pair_ind :
    forall (n : nat)
    (P : forall m : nat, n <= m -> n <= m -> Prop),
    P n (le_n n) (le_n n) ->
    (forall (m : nat) (l h : n <= m), P m l h ->
      P (S m) (le_S n m l) (le_S n m h)) ->
    forall (m : nat) (l h : n <= m), P m l h.
  Proof.
    intros ? P Hb Hc.
    refine(
      fix Fn m l :=
      match l as lp in (_ <= mp) return forall h, P mp lp h with
      | le_n _  => _ 
      | le_S _ m lp => _
      end).
    + intro h.
      inversion h.
      assert (Ht : h = le_n n \/ exists w, h = le_S _ _ h).
      destruct (le_inv _ _ h) as [ (e & H) | (m' & e & H1 & H2) ].
      ++ now rewrite (uip_nat e) in H.
      ++ nia.
    + intro h.
      destruct (le_inv _ _ h) as [ (e & H) | (m' & e & H1 & H2) ].
      ++ nia.
      ++ injection e; intros H3.
        revert e H1 H2; rewrite <- H3; intros e H1 H2.


      
  Admitted.
