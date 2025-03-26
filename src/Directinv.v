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
  
  Theorem fin_inv_ret {n : nat} (a b : Fin.t n) (e : FS a = FS b) : a = b.
  Proof.
    pose (ret := fun (n : nat)  =>
      match n as n' return Fin.t n' -> Fin.t (pred n') -> Prop 
      with 
      | 0 => fun (y : Fin.t 0) (a : Fin.t (pred 0)) => True 
      | S n' => fun (y : Fin.t (S n')) => 
        match y as y' in Fin.t m return Fin.t (pred m) -> Prop 
        with 
        | FS i => fun a => a = i 
        | F1 => fun _ => True 
        end
      end).
    refine 
      match e in _ = y return ret _ y a 
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

  Theorem vec_inv_tail_ret {n : nat} {A : Type} (a b : A) 
    (u v : Vector.t A n) (e : a :: u = b :: v) : u = v.
  Proof.
    pose(ret := fun (n : nat) => 
    match n as n' return Vector.t _ n' -> Vector.t _ (pred n') -> Prop 
    with 
    | 0 => fun (y : Vector.t A 0) (u : Vector.t A (pred 0)) => True 
    | S n' => fun (y : Vector.t A (S n')) =>
      match y as y' in Vector.t _ m return Vector.t _ (pred m) -> Prop 
      with 
      | [] => fun a => True 
      | h :: t => fun a => a = t 
      end
    end).
    refine 
      match e in _ = y return ret (S n) y u
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


  Definition exist_inj_ret {A : Type} {P : A -> Prop} (u v : A) 
    (pfu : P u) (pfv : P v) (e : exist _ u pfu = exist _ v pfv) : u = v.
  Proof.
    pose(ret := fun (y : @sig _ P) =>
      match y as y' in @sig _ _ return A -> Prop 
      with 
      | exist _ u pfu => fun i => i = u 
      end).
    refine 
      match e as e' in _ = y return ret y u
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

  Theorem vector_inv {A : Type} : ∀ (n : nat) (v : Vector.t A n), 
    match v as v' in Vector.t _ m return Vector.t _ m -> Prop 
    with
    | [] => fun u => u = []
    | h :: t => fun u => u = h :: t 
    end v.
  Proof.
    destruct v; exact eq_refl.
  Defined.

  

  Theorem vector_rect {A : Type} : ∀ (P : ∀ (n : nat), Vector.t A n -> Type),
    P 0 [] -> (∀ (n : nat) (h : A) (v : Vector.t A n), P n v -> P (S n) (h :: v)) ->
    ∀ (n : nat) (v : Vector.t A n), P n v.
  Proof.
    intros * ha hb.
    pose(ret := fun (Q : ∀ (n : nat), Vector.t A n -> Type) (n : nat) =>
      match n as n0 return Vector.t _ n0 -> Type with 
      | 0 => fun (v : Vector.t A 0) => 
        match v as v' in Vector.t _ m return Type 
        with
        | [] => Q 0 []
        | _ => False 
        end 
      | S n' => fun (v : Vector.t A (S n')) =>
        match v as v' in Vector.t _ m return Type 
        with 
        | [] => False 
        | h :: t => Q _ (h :: t)
        end 
      end).
    (* There is nothing much gain from the previous maneuver *)
    refine(fix fn (n : nat) (v : Vector.t A n) :  P n v :=
      match v as v' in Vector.t _ n0 return P n0 v'  
      with 
      | []  => ha 
      | h :: t => hb _ h t (fn _ t)
      end).
  Defined.
  
  

  Theorem vector_rect_type {A : Type} : ∀ (P : ∀ (n : nat), Vector.t A n -> Type),
    P 0 [] -> (∀ (n : nat) (h : A) (v : Vector.t A n), P n v -> P (S n) (h :: v)) ->
    ∀ (n : nat) (v : Vector.t A n), P n v.
  Proof.
    intros * ha hb.
    refine 
      (fix fn (n : nat) {struct n} : ∀ (v : Vector.t A n), P n v := 
        match n as n0 return ∀ (v0 : Vector.t A n0), P n0 v0 
        with 
        | 0 => fun (v : Vector.t _ 0) =>  
          match v as v' in Vector.t _ m return 
            (match m as m' return Type with 
            | 0 => P m v'
            | _ => True 
            end)
          with
          | [] => ha 
          | _ => I  
          end 
        | S n' => fun (v : Vector.t _ (S n')) =>
          match v as v' in Vector.t _ m return m = S n' -> 
            (match m return Type with 
            | 0 => True
            | _ => P m v' 
            end)
          with 
          | [] => fun _ => I 
          | Vector.cons _ h n0 t => fun hc => _
          end eq_refl 
        end).
        inversion hc as [hd]; clear hc.
        subst.  
        exact (hb _ h t (fn _ t)).
  Defined.


End Vect.
