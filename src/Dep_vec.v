(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)

(* Part of the idx/vec code come from

      https://github.com/DmxLarchey/Kruskal-Trees

   and follows the "Smaller inversions" technique
   of JF Monin, Types 2022

*)

From Coq Require Import Utf8.
From Coq Require Fin Vector.

Set Implicit Arguments.

Notation idx := Fin.t.
Notation idx_fst := Fin.F1.
Notation idx_nxt := Fin.FS.

Notation 𝕆 := idx_fst.
Notation 𝕊 := idx_nxt.

Section idx_rect.

  Inductive idx_shape_O : idx 0 → Type := .

  Inductive idx_shape_S {n} : idx (S n) → Type :=
    | idx_shape_S_fst : idx_shape_S 𝕆
    | idx_shape_S_nxt i : idx_shape_S (𝕊 i).

  Let idx_invert_t n : idx n → Type :=
    match n with
      | O   => idx_shape_O
      | S n => idx_shape_S
    end.

  Definition idx_invert {n} (i : idx n) : idx_invert_t i :=
    match i with
      | 𝕆   => idx_shape_S_fst
      | 𝕊 i => idx_shape_S_nxt i
    end.

  Definition idx_O_rect X (i : idx 0) : X :=
    match idx_invert i with end.

  Variables (n : nat)
            (P : idx (S n) → Type)
            (P_0 : P 𝕆)
            (P_S : ∀i, P (𝕊 i)).

  Definition idx_S_rect i : P i :=
    match idx_invert i with
      | idx_shape_S_fst => P_0
      | idx_shape_S_nxt i => P_S i
    end.

End idx_rect.

Arguments idx_invert {_} _ /.
Arguments idx_S_rect {_ _} _ _ _ /.

Section idx_nxt_inj.

  Variable (n : nat).

  Definition idx_S_inv : idx (S n) → option (idx n) := idx_S_rect None Some.

  Fact idx_S_inv_fst : idx_S_inv 𝕆 = None.            Proof. reflexivity. Qed.
  Fact idx_S_inv_nxt i : idx_S_inv (𝕊 i) = Some i.    Proof. reflexivity. Qed.

  Fact idx_nxt_inj (i j : idx n) (H : 𝕊 i = 𝕊 j) : i = j.
  Proof.
    apply f_equal with (f := idx_S_inv) in H.
    cbn in H; now inversion H.
  Qed.

End idx_nxt_inj.

Arguments idx_S_inv {_} i /.

#[local] Reserved Notation "v ⦃ p ⦄" (at level 1, format "v ⦃ p ⦄").
#[local] Reserved Notation "x '##' y" (at level 60, right associativity).

Notation vec := Vector.t.
Notation vec_nil := Vector.nil.
Notation vec_cons := Vector.cons.

Arguments vec_nil {A}.
Arguments vec_cons {A} _ {n}.

#[local] Notation "∅" := vec_nil.
#[local] Infix "##" := vec_cons.

Section vec_prj.

  Variable (X : Type).

  Fixpoint vec_prj n (v : vec _ n) : idx n → X :=
    match v with
      | ∅    => idx_O_rect _
      | x##v => λ i,
      match idx_S_inv i with
        | None   => x
        | Some j => v⦃j⦄
      end
    end
  where "v ⦃ i ⦄" := (@vec_prj _ v i).

  Goal ∀n x (v : vec _ n),   (x##v)⦃𝕆⦄   = x.   Proof. reflexivity. Qed.
  Goal ∀n x (v : vec _ n) i, (x##v)⦃𝕊 i⦄ = v⦃i⦄. Proof. reflexivity. Qed.

End vec_prj.

Arguments vec_prj {X n}.

#[local] Notation "v ⦃ i ⦄" := (vec_prj v i).

Section hvec.

  Inductive hvec : forall {n}, vec Type n → Type :=
    | hvec_nil : hvec ∅
    | hvec_cons {n X V} : X → @hvec n V → hvec (X##V).

  Fixpoint hvec_prj {n V} (v : @hvec n V) : ∀i, V⦃i⦄ :=
    match v with
      | hvec_nil      => λ i, idx_O_rect _ i
      | hvec_cons x v => λ i,
      match idx_invert i in idx_shape_S j return (_##_)⦃j⦄  with
        | idx_shape_S_fst   => x
        | idx_shape_S_nxt j => hvec_prj v j
      end
    end.

  Fixpoint hvec_func {n} (V : vec Type n) : (∀i, V⦃i⦄) → hvec V :=
    match V with
      | ∅    => λ _, hvec_nil
      | X##V => λ f, hvec_cons (f 𝕆) (hvec_func V (λ i, f (𝕊 i)))
    end.

  Fact hvec_prj_func n (V : vec Type n) f i : hvec_prj (hvec_func V f) i = f i.
  Proof.
    induction V as [ | n X V IHV ] in f, i |- *; simpl; destruct (idx_invert i); auto.
    apply IHV.
  Qed.

  Fixpoint hvec_set {n} {V : vec Type n} (v : hvec V) : ∀i, V⦃i⦄ → hvec V :=
    match v with
      | hvec_nil      => λ i _, hvec_nil
      | @hvec_cons _ X _ x v => λ i,
      match idx_invert i in idx_shape_S j return (_##_)⦃j⦄ → hvec (X##_) with
        | idx_shape_S_fst   => λ y, hvec_cons y v
        | idx_shape_S_nxt j => λ y, hvec_cons x (hvec_set v j y)
      end
    end.

  Fact hvec_set_eq n V v i x : hvec_prj (@hvec_set n V v i x) i = x.
  Proof.
    induction v as [ | n X V y v IHv ] in i, x |- *; simpl; destruct (idx_invert i); auto.
    apply IHv.
  Qed.

  Fact hvec_set_neq n V v i j x : i ≠ j → hvec_prj (@hvec_set n V v i x) j = hvec_prj v j.
  Proof.
    induction v as [ | n X V y v IHv ] in i, j, x |- *; simpl;
      destruct (idx_invert i); destruct (idx_invert j) as [ | j ]; simpl; auto.
    + intros []; auto.
    + intros H; apply IHv; contradict H; subst; auto.
  Qed.

End hvec.
