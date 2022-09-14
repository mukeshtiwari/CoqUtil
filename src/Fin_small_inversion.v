(* 
https://gist.github.com/DmxLarchey/ee2ae2d134e467adadbb6a90befe6a41 
https://types22.inria.fr/files/2022/06/TYPES_2022_slides_25.pdf
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

  Lemma fin_ind : 
    forall (n : nat) (P : Fin (S n) -> Type), 
    P Fz -> (forall (f : Fin n), P (Fs f)) ->
    forall fw : Fin (S n), P fw.
  Proof.
    intros n P HP1 HP2 fw.
    now destruct (Fin_invert fw).
  Qed.

End Fin.