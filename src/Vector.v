
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


   