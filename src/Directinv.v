From Coq Require Import Utf8 Fin Vector.
Import VectorNotations.


Section Inv.

  Theorem option_inv {A : Type} (a b : A) (e : Some a = Some b) : a = b.
  Proof.
    refine
      match e in _ = y return 
        (match y return A -> Prop 
        with 
        | Some y' => fun i => i = y' 
        | None => fun _ => True
        end a)
      with 
      | eq_refl => eq_refl
      end.
  Defined.

  Theorem option_inv_ret {A : Type} (a b : A) (e : Some a = Some b) : a = b.
  Proof.
    pose(ret := fun (y : option A) (a : A) => 
        match y return A -> Prop
        with 
        | Some v => fun i => i = v
        | None => fun _ => False
        end a). 
    refine 
      match e as e' in _ = y return ret y a with 
      | eq_refl => eq_refl
      end.
  Defined.

  Theorem fin_inv {n : nat} (a b : Fin.t n) (e : FS a = FS b) : a = b.
  Proof.
    refine 
      match e in _ = y return 
        (match y in Fin.t n' return Fin.t (pred n') -> Prop 
        with 
        | FS i => fun x => x = i 
        | F1 => fun _ => False 
        end a)
      with 
      | eq_refl => eq_refl
      end.
  Defined.
  
  
  Theorem vec_inv_tail {n : nat} {A : Type} (a b : A) 
    (u v : Vector.t A n) (e : a :: u = b :: v) : u = v.
  Proof.
    refine 
      match e in _ = y return 
      (match y in Vector.t _ n' return Vector.t _ (pred n') -> Prop 
      with
      | [] => fun _ => False
      | _ :: y' => fun i => i = y'  
      end u)
      with 
      | eq_refl => eq_refl 
      end.
  Defined.


  Definition exist_inj {A : Type} {P : A -> Prop} (u v : A) 
    (pfu : P u) (pfv : P v) (e : exist _ u pfu = exist _ v pfv) : u = v.
  Proof.
    refine 
     match e in _ = y return 
     (match y return A -> Prop with 
     | exist _ x _ => fun i => i = x
     end u)
     with 
     | eq_refl => eq_refl
     end.
  Defined.

End Inv.



Section Vect.

  Inductive p {A : Type} : ∀ (n : nat), Vector.t A n -> Prop :=
  | pnil : p 0 []
  | pcons (n : nat) (h : A) (v : Vector.t A n) : p n v -> p (1 + n) (h :: v).
  
  
  Theorem pcons_inv {A : Type} : ∀ (n : nat) (h : A) (t : Vector.t A n), 
    p (1 + n) (h :: t) -> p n t.
  Proof.
    intros n h t ha.
    pose(ret := fun (n0 : nat) => 
        match n0 as n0' return ∀ (t0 : Vector.t A n0'), p n0' t0  -> Prop 
        with 
        | 0 => fun (t0 : Vector.t A 0) (eb : p 0 t0) => True
        | S n0' => fun (t0 : Vector.t A (S n0')) => 
          match t0 as t0' in Vector.t _ n1 return p n1 t0' -> Prop 
          with 
          | [] => fun (ea : p 0 []) => False
          | ha :: ta => fun (ea : p _ (ha :: ta)) => p _ ta 
          end
        end).  
    refine 
      match ha as ha' in p n' t' return ret n' t' ha' 
      with 
      | pnil => I 
      | pcons n' h' v' ha => ha
      end.
  Defined.

End Vect.
