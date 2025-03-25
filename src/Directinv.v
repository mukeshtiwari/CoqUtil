From Coq Require Import Utf8 Fin Vector.
Import VectorNotations.


Section Inv.

  Theorem option_inv {A : Type} (a b : A) (e : Some a = Some b) : a = b.
  Proof.
    refine
      match e in _ = y return 
        (match y return Prop 
        with 
        | Some y' => a = y' 
        | None => True
        end)
      with 
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
