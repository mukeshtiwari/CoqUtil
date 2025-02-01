From Coq Require Import Utf8.


Section Ev.

  
  Inductive Even : nat -> Prop :=
  | ev_0 : Even 0
  | ev_2 {n : nat} : Even n -> Even (2 + n).

  Theorem ev_ss : forall (n : nat), Even (2 + n) -> Even n.
  Proof.
    intros * Ha.
    inversion Ha; assumption.
  Qed.

  (* Relation between the inductive type *)
  Inductive even_shape_0 : Even 0 -> Prop :=
  | evs_0 : even_shape_0  ev_0.


  Inductive even_shape_1 : Even 1 -> Prop := .
  
  Inductive even_shape_2 {n : nat} : Even (2 + n) -> Prop :=
  | evs_2 (e : Even n) : even_shape_2 (ev_2 e).

 
  Definition even_inv_t (n : nat) : Even n -> Prop :=
    match n with 
    | 0 => even_shape_0
    | 1 => even_shape_1
    | _ => even_shape_2
    end.

  (* But why are we doing this? *)
  Definition even_inv {n : nat} (e : Even n) : even_inv_t n e :=
    match e with 
    | ev_0 => evs_0
    | ev_2 i => evs_2 i 
    end.

  (* inversion principle *)

  Theorem Even_0_inv (P : Even 0 -> Prop) (e : Even 0) :
    P ev_0 -> P e.
  Proof.
    now destruct (even_inv e).
  Defined.


  Theorem Even_1_inv (P : Even 1 -> Prop) (e : Even 1) : False.
  Proof.
     now destruct (even_inv e).
  Defined.

  Theorem Even_2_inv (n : nat) (P : Even (2 + n) -> Prop) (e : Even (2 + n)) :
     (∀ (u : Even n), P (ev_2 u)) -> P e.
  Proof.
    now destruct (even_inv e).
  Defined.

  Theorem ev_sss : forall (n : nat), Even (2 + n) -> Even n.
  Proof.
    intros * Ha.
    eapply Even_2_inv with n;
    auto.
  Qed.

  Theorem ev_o : forall (e : Even 0), e = ev_0.
  Proof.
    intro e.
    now eapply Even_0_inv with (P := fun e => e = ev_0).
  Qed.


End Ev.
