(* 
https://gist.github.com/DmxLarchey/ee2ae2d134e467adadbb6a90befe6a41 
https://types22.inria.fr/files/2022/06/TYPES_2022_slides_25.pdf
*)

From Coq Require Import Utf8 Fin Vector.
Import VectorNotations.

Section EQ.

  Definition option_lift {A : Type} (P : A -> Prop) (o : option A) : Prop :=
    match o return Prop 
    with
    | Some a => P a 
    | None => False
    end.

  Theorem option_inv {A : Type} (a b : A) (e : Some a = Some b) : a = b.
  Proof.
    refine 
      match e in @eq _ _ y return option_lift (@eq _ a) y 
      with 
      | eq_refl => eq_refl 
      end.
  Defined.

  Definition fin_lift {n : nat} (P : Fin.t n -> Prop) (i : Fin.t (S n)) : Prop :=
    match i in Fin.t m return (Fin.t (pred m) -> Prop) -> Prop  
    with
    | FS i => fun P => P i 
    | F1 => fun _ => False
    end P.

  Theorem fin_inv {n : nat} (a b : Fin.t n) (e : FS a = FS b) : a = b.
  Proof.
    refine 
      match e in @eq _ _ y return fin_lift (@eq _ a) y 
      with 
      | eq_refl => eq_refl 
      end.
  Defined.

  Definition vec_lift_head {A : Type} {n : nat}  (P : A -> Prop) (a : Vector.t A n) : Prop :=
    match a with 
    | [] => False 
    | u :: _ => P u 
    end.

  Theorem vec_inv_head {n : nat} {A : Type} (a b : A) 
    (u v : Vector.t A n) (e : a :: u = b :: v) : a = b.
  Proof.
    refine
      match e in (@eq _ _ y) return vec_lift_head (@eq _ a) y 
      with 
      | eq_refl => eq_refl
      end.
  Defined.


  Definition vec_lift_tail {n : nat} {A : Type} (P : Vector.t A n -> Prop) 
    (u : Vector.t A (S n)) : Prop :=
    match u in Vector.t _ m return (Vector.t A (pred m) -> Prop) -> Prop 
    with
    | _ :: uy => fun P => P uy 
    | _ => fun _ => False
    end P.

  Theorem vec_inv_tail {n : nat} {A : Type} (a b : A) 
    (u v : Vector.t A n) (e : a :: u = b :: v) : u = v.
  Proof.
    refine
      match e in _ = y return vec_lift_tail (@eq _ u) y 
      with 
      | eq_refl => eq_refl
      end.
  Defined.

End EQ.

Section Fin. 

  Inductive Fin : nat -> Type :=
  | Fz {n : nat} : Fin (S n)
  | Fs {n : nat} : Fin n -> Fin (S n).

  Inductive Fin_shape_O : Fin 0 -> Type := .

  Inductive Fin_shape_S {n} : Fin (S n) -> Type :=
  | Fin_shape_S_fst : Fin_shape_S Fz
  | Fin_shape_S_nxt i : Fin_shape_S (Fs i).

  Let Fin_invert_t {n} : Fin n -> Type :=
    match n with 
    | O   => Fin_shape_O
    | S n => Fin_shape_S
    end.

  Definition Fin_invert {n} (i : Fin n) : Fin_invert_t i :=
    match i with
    | Fz   => Fin_shape_S_fst
    | Fs i => Fin_shape_S_nxt i
    end.


  Lemma fin_inversion : 
    forall (n : nat) (P : Fin (S n) -> Type), 
    P Fz -> (forall (f : Fin n), P (Fs f)) ->
    forall fw : Fin (S n), P fw.
  Proof.
    intros n P HP1 HP2 fw.
    now destruct (Fin_invert fw).
  Qed.

  
  Lemma fin_ind : 
    forall (P : forall {n : nat}, Fin n -> Type), 
    (forall {n : nat}, @P (S n) Fz) -> (forall {n : nat} (f : Fin n), P f -> P (Fs f)) ->
    forall {n : nat} (fw : Fin n), P fw.
  Proof.
    intros P fa fb.
    refine(
      fix Fn {n : nat} (fw : Fin n) : P n fw :=
      match fw with 
      | @Fz nt => fa nt 
      | @Fs nt i => fb nt i (Fn i)
      end).
  Defined.
    

End Fin.

Section Vect.

  Inductive vect_shape {A : Type} : forall {n : nat}, Vector.t A n -> Type :=
  | vect_shape_O : @vect_shape A 0 []
  | vect_shape_S {n : nat} (a : A) (v : Vector.t A n) : @vect_shape A (S n) (a :: v).


  Let vect_invert_t {A : Type} {n : nat} : Vector.t A n -> Type := vect_shape.


  Definition vect_invert {n : nat} {A : Type} (v : Vector.t A n) : vect_invert_t v :=
    match v with 
    | [] => vect_shape_O
    | ua :: ub => vect_shape_S ua ub 
    end.

  Lemma vect_inv {A : Type} : 
    forall (P : forall {n : nat}, Vector.t A n -> Type), 
    P [] -> (forall {n : nat} (a : A) (u : Vector.t A n), P (a :: u)) -> 
    forall {n : nat} (v : Vector.t A n) , P v.
  Proof.
    intros * fa fb *.
    now destruct (vect_invert v).
  Defined.

  Lemma vect_ind {A : Type} : 
    forall (P : forall {n : nat}, Vector.t A n -> Type), 
    P [] -> (forall {n : nat} (a : A) (u : Vector.t A n), P u -> P (a :: u)) -> 
    forall {n : nat} (v : Vector.t A n) , P v.
  Proof.
    intros * fa fb.
    refine(fix Fn {n : nat} (v : Vector.t A n) : P n v :=
    match v with 
    | [] => fa 
    | va :: vb => fb _ va vb (Fn vb)  
    end).
  Defined.
  
End Vect.



Section Ev.

  Inductive Even : nat -> Prop :=
  | ev_O : Even 0 
  | ev_S {n : nat} : Even n -> Even (2 + n).

  (* 
  Inductive even_shape_S  : forall {n : nat}, Even n -> Prop :=
  | even_0 : even_shape_S ev_O
  | even_S {n : nat} (i : Even n) : even_shape_S (ev_S i).
  *)
    
  Inductive even_shape_0 : Even 0 -> Prop := 
  | even_0 : even_shape_0 ev_O.
  
  Inductive even_shape_1 : Even 1 -> Prop  :=.
    
  Inductive even_shape_S : forall {n : nat}, Even (2 + n) -> Prop :=
  | even_S {n : nat} (i : Even n) : even_shape_S (ev_S i).
  
  
  Definition even_invert_t {n : nat} : Even n -> Prop := 
    match n with 
    | 0 => even_shape_0
    | 1 => even_shape_1
    | S (S n) => even_shape_S
    end.
  

  (* 
  Definition even_invert {n : nat} (e : Even n) : 
    match n return Even n -> Prop 
    with 
    | 0 => even_shape_0 
    | 1 => even_shape_1
    | S (S n) => even_shape_S 
    end e := 
    match e with 
    | ev_O => even_0
    | ev_S i => even_S i 
    end.
  *)


  Definition even_invert {n : nat} (e : Even n) : even_invert_t e := 
    match e with 
    | ev_O => even_0
    | ev_S i => even_S i 
    end.



  Lemma Even_O_inv (e : Even 0) (P : Even 0 → Prop) :
    P ev_O → P e.
  Proof. now destruct (even_invert e). Qed.

  Lemma Even_1_inv (e : Even 1) : False.
  Proof. now destruct (even_invert e). Qed.

      
  Lemma Even_S_inv n (e : Even (2 + n)) (P : Even (2 + n) → Prop) :
    (∀ u : Even n, P (ev_S u)) → P e.
  Proof. now destruct (even_invert e). Qed.



  (** Now with dependent pattern matching *)

  Definition Even_inv_alt_t {n} : Even n → Prop :=
    match n with
    | 0       => λ e, ∀ (P : Even 0 → Prop), P ev_O → P e
    | 1       => λ _, False
    | S (S m) => λ e, ∀ (P : Even (2+m) → Prop), (∀ (u : Even m), P (ev_S u)) → P e
    end.

  Definition Even_inv_alt {n} (e : Even n) : Even_inv_alt_t e :=
    match e with
    | ev_O   => λ _ H, H
    | ev_S i => λ _ H, H _
    end.

  (** Even 0, Even 1 and Even (2+_) inversions using an auxiliary
    inductive predicate, as in "smaller inversions" *)

  Definition Even_O_inv_alt (e : Even 0) :
    ∀ (P : Even 0 → Prop), P ev_O → P e :=
    Even_inv_alt e.

  Definition Even_1_inv_alt (e : Even 1) : False :=
    Even_inv_alt e.

  Definition Even_S_inv_alt n (e : Even (2+n)) :
    ∀P : Even (2+n) → Prop, (∀u, P (ev_S u)) → P e :=
    Even_inv_alt e.
End Ev.

