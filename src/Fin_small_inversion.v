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

(* inversion principal Vector *)
Print Vector.t.
(*
Inductive t (A : Type) : nat → Type :=   nil : t A 0 | cons : A → ∀ n : nat, t A n → t A (S n).

*)
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

