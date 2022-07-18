Require Import Nat
  PeanoNat Coq.Logic.EqdepFacts
  Coq.Logic.Eqdep_dec
  Coq.Arith.Peano_dec.



Section Vector.

  Inductive Vector (A : Type) : nat -> Type := 
  | Nil : Vector A 0 
  | Cons n : A -> Vector A n -> Vector A (S n).


  Check Nil.
  Eval compute in Nil nat.
  Check Cons.
  Eval compute in Cons _ _ 10 (Nil nat).
  Eval compute in Cons _ _ 20 (Cons _ _ 10 (Nil nat)).
  
  Arguments Nil {A}.
  Arguments Cons {A n}.
  Eval compute in Cons 20 (Cons 10 Nil).


  Fixpoint vector_append_first {A : Type} {m n : nat} 
    (u : Vector A m) (v : Vector A n) : Vector A (m + n) :=
    match u with 
    | Nil => v 
    | Cons h t => Cons h (vector_append_first t v)
    end.
    
  Fixpoint vector_append_second {A : Type} {m n : nat} 
    (u : Vector A m) (v : Vector A n) : Vector A (m + n) :=
    match u as u' in Vector _ m' 
      return m = m' -> Vector A (m' + n)
    with 
    | Nil => fun Hm => v (* m = 0 *)
    | Cons h t => fun Hm => Cons h (vector_append_second t v) 
      (* m = S m' for some m' *)
    end eq_refl.

  Fixpoint vector_append_third {A : Type} {m n : nat} 
    (u : Vector A m) (v : Vector A n) : Vector A (m + n).
  Proof.
    refine(
      match u as u' in Vector _ m' 
      return m = m' -> Vector A (m' + n)
    with 
    | Nil => fun _ => v  
    | Cons h t => fun _ => 
      (Cons h (vector_append_third _ _ _ t v))
    end eq_refl).
  Defined.
   
  


  Definition vector_append_fourth {A : Type} {m n : nat} 
     (u : Vector A m) (v : Vector A n) : Vector A (m + n).
  Proof.
    generalize dependent n.
    generalize dependent m.
    refine(
      fix Fn m u {struct u} := 
      match u as u' in Vector _ m'  
        return forall (pf : m = m'), 
          u = eq_rect m' (fun w => Vector A w) 
              u' m (eq_sym pf) ->
          forall n : nat, 
          Vector A n -> Vector A (m' + n) 
      with 
      | Nil => fun _ _ _  v => v  
      | Cons h t => fun _ _ _ v =>
      (Cons h (Fn _ t _ v))
      end eq_refl eq_refl).
  Defined.

  
  Lemma vector_nil_l {A : Type} {m : nat} :
    forall (u : Vector A m),
    vector_append_fourth Nil u = u.
  Proof.
    refine (fun _ => eq_refl).
  Qed.

  Definition cast_vector {A : Type} {m n : nat} : 
    Vector A m -> m = n -> Vector A n.
  Proof.
    (* 
    intros u H.
    exact (eq_rect m (fun w => Vector A w) u n H). *)
    refine (fun u H => 
      match H with 
      | eq_refl => u
      end).
  Defined.
    

  Fact uip_nat {n : nat} (e : n = n) : e = eq_refl.
  Proof. apply UIP_dec, eq_nat_dec. Qed.


  Lemma cast_vector_rewrite_gen_tactic {A : Type} {m n : nat} :
    forall (a : A) 
    (u : Vector A m) 
    (Ha : S m = S n)
    (Hb : m = n),
    cast_vector (Cons a u) Ha = 
    Cons a (cast_vector u Hb).
  Proof.
    intros ? ? ? ?;
    subst.
    rewrite (uip_nat Ha).
    exact eq_refl.
  Qed.

 
  
  Lemma cast_vector_rewrite_gen_prog {A : Type} {m n : nat} :
    forall (a : A) 
    (u : Vector A m) 
    (Ha : S m = S n)
    (Hb : m = n),
    cast_vector (Cons a u) Ha = 
    Cons a (cast_vector u Hb).
  Proof.
    intros ? ? ?.
    refine(
      match Ha as Ha' in _ = (S n')
        return 
          forall (pf : n' = n),
          Ha = eq_rect (S n') _ Ha' (S n) (eq_S n' n pf) ->  
          forall (Hb : m = n'),
          cast_vector (Cons a u) Ha' = Cons a (cast_vector u Hb)
      with
      | eq_refl => fun pf Hpf Hb => _
      end eq_refl eq_refl).
      rewrite (uip_nat Hb).
      exact (eq_refl).
  Defined.
      
      
      
  Lemma cast_vector_rewrite {A : Type} {m : nat} :
    forall (a :  A) (u : Vector A m),
    cast_vector (Cons a u) (plus_n_O (S m)) =
    Cons a (cast_vector u (plus_n_O m)).
  Proof.
    intros a u.
    apply cast_vector_rewrite_gen_prog.
  Qed.


  Lemma vector_nil_r {A : Type} {m : nat} :
    forall (u : Vector A m),
    vector_append_fourth u Nil = 
    cast_vector u (plus_n_O m).
  Proof.
    induction u.
    + simpl.
      refine 
        match plus_n_O 0 with 
        | eq_refl => eq_refl
        end.
    + simpl.
      symmetry.
      pose proof cast_vector_rewrite a u as Hu.
      eapply eq_trans.
      ++ exact Hu.
      ++ f_equal.
         exact (eq_sym IHu).
  Qed.        






    


  
    
   