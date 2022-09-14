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


  Lemma append_nil_left {A : Type} {n : nat} :
    forall (v : Vector A n), 
    vector_append_fourth Nil v = v.
  Proof.  
    refine (fun v => eq_refl).
  Defined.
  

  Definition cast_vector {A : Type} {m n : nat} :
    Vector A m -> m = n -> Vector A n.
  Proof.
    intros u H.
    refine 
      match H with 
      | eq_refl => u 
      end.
  Defined.

  
  Lemma uip_nat {n : nat} (pf : n = n) : pf = eq_refl.
  Proof.
    apply UIP_dec,
    eq_nat_dec.
  Qed.
  

  Lemma append_nil_right_ind_gen_tactic {A : Type}
    {n m : nat} :
    forall (a : A) (u : Vector A n)
    (Ha : S n = S m)
    (Hb : n = m),
    cast_vector (Cons a u) Ha = 
    Cons a (cast_vector u Hb).
  Proof.
    intros *.
    subst.
    assert (Hapf : Ha = eq_refl).
    apply uip_nat.
    rewrite Hapf.
    simpl.
    reflexivity.
  Defined.

  Lemma append_nil_right_ind_gen_prog {A : Type}
    {n m : nat} :
    forall (a : A) u
    (Ha : S m = S n)
    (Hb : m = n),
    cast_vector (Cons a u) Ha = 
    Cons a (cast_vector u Hb).
  Proof.
    intros a u Ha.
    refine(
      match Ha as Ha' in (_ = S n')
        return forall (pf : n = n'), 
        Ha = eq_rect (S n') _ Ha' (S n) 
            (eq_S _ _ (eq_sym pf)) -> 
        forall Hb : m = n',
        cast_vector (Cons a u) Ha' =
        Cons a (cast_vector u Hb)
      with 
      | eq_refl => fun Hpf Hb Hbpf => 
        match Hbpf as Hbpf' in (_ = m')
        return forall (pf : m = m'), 
          Hbpf' = eq_rect m _ eq_refl m' pf -> 
          cast_vector (Cons a u) eq_refl =
          eq_rect (S m') _ (Cons a (cast_vector u Hbpf'))
          (S m) (eq_S _ _ (eq_sym pf)) 
        with
        | eq_refl => _
        end eq_refl _ 
      end eq_refl eq_refl).
    + intros *.
      cbn.
      rewrite (uip_nat pf).
      simpl.
      reflexivity.
    + simpl.
      apply uip_nat. 
  Defined.
  

  Lemma append_nil_right_ind {A : Type} {n : nat} :
    forall (a : A) (u : Vector A n),
    cast_vector (Cons a u) (plus_n_O (S n)) = 
    Cons a (cast_vector u (plus_n_O n)). 
  Proof.
    intros *.
    apply append_nil_right_ind_gen_tactic.
  Qed.


  Lemma append_nil_right {A : Type} {n : nat} : 
    forall (u : Vector A n),
    vector_append_fourth u Nil = 
    cast_vector u (plus_n_O n).
  Proof.
    induction u.
    + simpl.
      refine 
        match (plus_n_O 0) with 
        | eq_refl => eq_refl
        end.
    + simpl.
      rewrite IHu.
      symmetry.
      apply append_nil_right_ind.
  Qed.

  
  (* generalisation is the key *)
  Lemma append_associative {A : Type} :
    forall {m : nat} (u : Vector A m) 
    {n o : nat} (v : Vector A n) (w : Vector A o)
    (Ha : m + n + o = m + (n + o)),
    vector_append_fourth u (vector_append_fourth v w) =
    cast_vector (vector_append_fourth (vector_append_fourth u v) w) Ha.
  Proof.
    refine(
      fix Fn m u {struct u} := 
      match u as u' in Vector _ m' 
      return m = m' ->  _ 
      with 
      | Nil => _ 
      | Cons _ _ => _ 
      end eq_refl).
      + intros Hb ? ? ? ? ?;
        simpl in * |- *.
        assert (Ht : Ha = eq_refl).
        apply uip_nat.
        subst; simpl.
        exact eq_refl.
      + intros Hb ? ? ? ? ?; 
        simpl in * |- *.
        inversion Ha as (Haa).
        erewrite append_nil_right_ind_gen_prog 
        with (Hb := Haa).
        f_equal.
        apply Fn.
  Defined.


























    
   