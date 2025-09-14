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


Theorem fin_inv_destruct : ∀ (n : nat) (f : Fin.t n), 
  match n return Fin.t n -> Type 
  with 
  | 0 => fun _  => IDProp
  | S n'  => fun ft => ((ft = @Fin.F1 n') + Sigma (u : Fin.t n'), ft = Fin.FS u)%type
  end f.
Proof.
  intros *.
  destruct f as [|f'];
  [left; exact eq_refl | right].
  exists f. exact eq_refl.
Defined.


Theorem fin_inv_convoy : ∀ (n : nat) (f : Fin.t n), 
  match n return Fin.t n -> Type 
  with 
  | 0 => fun _  => IDProp
  | S n'  => fun ft => ((ft = @Fin.F1 n') + Sigma (u : Fin.t n'), ft = Fin.FS u)%type
  end f.
Proof.
  intros *.
  refine
    (match f as f' in Fin.t n' return 
      (match n' return Fin.t n' -> Type 
      with 
      | 0 => fun _  => IDProp
      | S n'  => fun ft => ((ft = @Fin.F1 n') + 
        Sigma (u : Fin.t n'), ft = Fin.FS u)%type
      end f')
    with 
    | Fin.F1 => inl eq_refl
    | Fin.FS f' => inr (exist _ f' eq_refl)
    end). 
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


Lemma Fin_t_S_inv_convoy : ∀ (n : nat) (P : t (S n) → Type),
   P F1 → (∀ (i : Fin.t n), P (FS i)) →  ∀ (i : Fin.t (S n)), P i.
Proof.
  intros * ha hb i.
  refine
  (match i as i' in Fin.t n'
    return 
    ∀ (pfa : S n = n'),
    (match n' as n'' return n' = n'' -> Fin.t n'' -> Type 
    with 
    | 0 => fun _ _ => IDProp 
    | S n'' => fun (pfb : n' = S n'') (f : Fin.t (S n'')) => 
      P (eq_rect (S n'') Fin.t f _ (eq_sym (eq_trans pfa pfb))) 
    end eq_refl i')
  with 
  | Fin.F1 => fun pfa => _ 
  | Fin.FS f' => fun pfa => _ 
  end eq_refl); cbn;
  inversion pfa as [pfaa]; subst;
  assert (pfa = eq_refl) by apply Eqdep_dec.UIP_refl_nat;
  subst; cbn; [exact ha | exact (hb f')].
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


Definition Fin_t_0_inv i : ∀ (P : t 0 → Type), P i :=
  match i with end.

Definition Fin_t_S_inv n i :
  ∀ (P : t (S n) → Type), P F1 → (∀i, P (FS i)) → P i.
Proof.
  refine 
    match i with 
    | F1 => _ 
    | FS j => _ 
    end.
  +
    intros * Ha Hb.
    exact Ha.
  +
    intros * Ha Hb.
    exact (Hb j).
Defined.
