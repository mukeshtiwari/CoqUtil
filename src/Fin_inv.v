Require Import Fin Utf8.

Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.


Theorem fin_inv : ∀ (n : nat) (f : Fin.t n), 
  match n as np return n = np -> Fin.t np -> Type 
  with 
  | 0 => fun Ha _  => False
  | S n'  => fun Ha ft => ((ft = @Fin.F1 n') + Sigma (u : Fin.t n'), ft = Fin.FS u)%type
  end eq_refl f.
Proof.
  destruct n as [|n].
  +
    intro Ha.
    refine match Ha with end.
  +
    intros f.
    refine 
      match f with 
      | Fin.F1 => _
      | Fin.FS t => _ 
      end; [left | right].
    ++
      exact eq_refl.
    ++
      exists t; exact eq_refl.
Defined.

    

Lemma Fin_t_S_inv : ∀ n (P : t (S n) → Type),
   P F1 → (∀ i : Fin.t n, P (FS i)) →  ∀ i : Fin.t (S n), P i.
Proof.
  induction n.
  +
    intros * Ha Hb i.
    destruct (fin_inv 1 i) as [Hc | (u & Hc)].
    ++
      subst; exact Ha.
    ++
      refine match (fin_inv 0 u) with end.
  +
    intros * Ha Hb i.
    destruct (fin_inv _ i) as [Hc | (u & Hc)].
    ++
      subst; exact Ha.
    ++
      eapply IHn; subst;
      [exact (Hb u)| intro v; exact (Hb u) | exact u].
Defined.


Lemma Fin_t_S_inv_gen : ∀ (P : ∀ (n : nat), t (S n) → Type),
   (∀ (n : nat), P n F1) → 
   (∀ (n : nat) (i : Fin.t n), P n (FS i)) →  
   ∀ (n : nat) (i : Fin.t (S n)), P n i.
Proof.
  intros * Ha Hb.
  induction n as [| n Ihn].
  +
    intro i.
    destruct (fin_inv 1 i) as [Hc | (u & Hc)].
    ++
      subst; exact (Ha 0).
    ++
       refine match (fin_inv 0 u) with end.
  +
    intro i.
    destruct (fin_inv _ i) as [Hc | (u & Hc)].
    ++
      subst.
      eapply Ha.
    ++
      subst.
      eapply Hb.
Defined.


Lemma Fin_t_S_inv_Dominique n (P : t (S n) → Type) :
   P F1 → (∀ i : t n, P (FS i)) →  ∀ i : t (S n), P i.
Proof.
  intros Ha Hb i.
  destruct (fin_inv _ i) as [Hc | (u & Hc)].
  +
    subst; exact Ha.
  +
    subst; eapply Hb.
Defined.



Lemma Fin_t_S_inv_Dominique_gen n (P : t (S n) → Type) :
   P F1 → (∀ i : t n, P (FS i)) →  ∀ i : t (S n), P i.
Proof.
  intros * Ha Hb i.
  (* Is this possible to prove by induciotn on i? *)
  


  (* 
  generalize dependent n.
  set (fn := fun (w : nat) (Pa : Fin.t (S w) -> Type) (Ha : w = n) (v : Fin.t (S w))  => Pa v).
  intro i.
  change (P i) with (fn n P eq_refl i).
  induction i.
  *)
Admitted.

