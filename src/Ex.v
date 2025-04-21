From Stdlib Require Import Arith
Equality.


Inductive Ex (n : nat) : Type :=
  | X : Ex n.

Definition Cast (n : nat) {n'} 
  (eq : n = n') (e : Ex n) : Ex n'.
Proof.
  set (ret_type := (fun n =>  Ex n) : (nat -> Type) : Type ).
  refine
    match eq in _ = m return ret_type m with
    | eq_refl => e
    end.
Defined.

Lemma dim_help {x y} (H: x =? y = true) : x = y.
Proof.
  apply Nat.eqb_eq; easy.
Defined.

Definition test {dim} (n : nat) : Ex dim.
  destruct (n =? dim) eqn:H.
  + apply (Cast _ (dim_help H)).
    apply (X n).
  + apply (X dim).
Defined.

Lemma test_lemma : forall n, @test n n = X n.
Proof.
  intros; unfold test.
  set (fn := fun (n : nat) (o : bool) (ha : (n =? n) = o) =>
    (if o as b return ((n =? n) = b -> Ex n)
    then fun H : (n =? n) = true => Cast n (dim_help H) (X n)
    else fun _ : (n =? n) = false => X n) ha).
  change ((if n =? n as b return ((n =? n) = b -> Ex n)
  then fun H : (n =? n) = true => Cast n (dim_help H) (X n)
  else fun _ : (n =? n) = false => X n) eq_refl) with 
  (fn n (n =? n) eq_refl).
  enough (forall u v ha, fn u v ha = X u) as hb.
  eapply hb.
  intros *. destruct v; cbn.
  +
    unfold Cast, dim_help.
    destruct (Nat.eqb_eq u u) as (fa & fb).
    destruct (fa ha); reflexivity.
  +
    reflexivity.
Qed.

(* proof using generalizing *)
Lemma test_lemma : forall n, @test n n = X n.
Proof.
  intros; unfold test.
  generalize (eq_refl (n =? n)).
  generalize (n =? n) at 2 3 as u.
  destruct u as [ | ]; intros; 
  unfold Cast, dim_help.
  +
    destruct (Nat.eqb_eq n n) as (fa & fb).
    destruct (fa e); reflexivity.
  +
    reflexivity.
Qed.
