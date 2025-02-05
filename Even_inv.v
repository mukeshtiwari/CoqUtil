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

  Theorem ev_ssss : forall (n : nat) (e : Even (2 + n)), ∃ (p : Even n), e = ev_2 p.
  Proof.
    intros *.
    eapply (Even_2_inv n (fun (u : Even (2 + n)) => ∃ (p : Even n), u = ev_2 p) e).
    intro u; exists u; exact eq_refl.
  Qed.


End Ev.



Section Ex.

  Print exist.
  (* Inductive sig (A : Type) (P : A → Prop) : Type :=   exist : ∀ x : A, P x → {x : A | P x}. *)

  
  Inductive sig_shape {A : Type} {P : A -> Prop} : @sig A P -> Prop := 
  | sigs (x : A) (pf : P x) : sig_shape (exist P x pf).

  Definition sig_inv_t {A : Type} {P : A -> Prop} : @sig A P -> Prop :=
    fun p => @sig_shape A P p.

  Definition sig_inv {A : Type} {P : A -> Prop} (e : @sig A P) : sig_inv_t e :=
  match e with 
  | exist _ x pf => sigs x pf 
  end.


  Theorem sig_inv_P : forall (A : Type) (P : A -> Prop) (Psig : @sig A P -> Prop)
    (e : @sig A P), (forall (x : A) (pf : P x), Psig (exist P x pf)) -> Psig e.
  Proof.
    intros * Ha.
    now destruct (sig_inv e).
  Defined.


  Definition exist_lift_value {A P} (Q : A -> Prop) (e : @sig A P) : Prop :=
    match e return (A -> Prop) -> Prop with 
    | exist _ x _ => fun P => P x 
    end Q.
  
  Definition exist_inj {A : Type} {P : A -> Prop} (u v : A) (pfu : P u) (pfv : P v) 
    (e : exist _ u pfu = exist _ v pfv) : u = v := 
    match e in _ = y return exist_lift_value (eq u) y  
    with 
    | eq_refl => eq_refl
    end.

  Definition exist_inj_proof_lift {A P} (Q : forall a, P a -> Prop) (e : @sig A P) : Prop :=
  match e return (forall (a : A), P a -> Prop) -> Prop with 
  | exist _ x pf => fun P => P x pf 
  end Q.
  
  (* 
  Definition exist_inj_proof {A : Type} {P : A -> Prop} (Hdec : forall x y : A, {x = y} + {x <> y}) 
    (u v : A) (pfu : P u) (pfv : P v) 
    (e : exist _ u pfu = exist _ v pfv) (pf : u = v) : 
    pfu = eq_rect v P pfv u (eq_sym pf) := 
    match e in _ = y return exist_inj_proof_lift (JMeq pfu) y 
    with 
    | eq_refl => eq_refl
    end. 
   *)

End Ex.

