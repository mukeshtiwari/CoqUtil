From Stdlib Require Import Utf8 Vector Fin.
Import VectorNotations.

Section Hvect.

  Inductive Hvect : ∀ (n : nat), Vector.t Type n -> Type :=
  | Hnil : Hvect 0 [] 
  | Hcons {A : Type} {n : nat} {V : Vector.t Type n} :  
    A -> Hvect n V -> Hvect (S n) (A :: V).
    
  Check (Hcons true (Hcons 1 Hnil)).
  Check (Hcons nat (Hcons bool Hnil)).

  Definition fin_inv : forall (n : nat) (f : Fin.t (S n)),
      (f = Fin.F1) + {f' | f = Fin.FS f'}.
  Proof.
    intros n f.
    refine
      match f as fp in Fin.t n' return
            (match n' as n'' return Fin.t n'' -> Type
             with
             | 0 => fun (e : Fin.t 0) => IDProp
             | S m' => fun (e : Fin.t (S m')) =>
                         ((e = F1) + {f' : Fin.t m' | e = FS f'})%type
             end fp)
      with
      | Fin.F1 => inl eq_refl
      | Fin.FS f' => inr (exist _ f' eq_refl)
      end.
  Defined.

  
  Definition hvect_nth_fin {n : nat}  
    {v : Vector.t Type n} (u : Hvect n v) : forall (f : Fin.t n), Vector.nth v f.
  Proof.
    generalize dependent n.
    refine(fix fn (n : nat) (v : Vector.t Type n) (hv : Hvect n v) {struct hv} :
            forall (f : Fin.t n), v[@f] :=
             match hv in Hvect n' v' return forall (f : Fin.t n'), v'[@f] with
             | Hnil => fun f => match f with end 
             | @Hcons _ n' _ hvh hvt => fun (f : Fin.t (S n')) => _ 
                                                                     
             end).
    destruct (fin_inv _ f) as [ha | (f' & ha)]; subst; cbn;
      [exact hvh | eapply fn; exact hvt].
    Show Proof.
  Defined.

  
  Eval compute in hvect_nth_fin (Hcons true (Hcons 1 Hnil)) (FS F1).

  
  Definition hvect_nth {n : nat}  
    (f : Fin.t n) {v : Vector.t Type n} (u : Hvect n v) : Vector.nth v f.
  Proof.
    generalize dependent n.
    refine(fix fn {n : nat} (f : Fin.t n) {struct f} : 
      ∀ (v : Vector.t Type n), Hvect n v → v[@f] := 
      match f as f' in Fin.t n' return ∀ (v : Vector.t Type n'), 
        Hvect n' v → v[@f']
      with 
      | Fin.F1 => fun v hv => _ 
      | Fin.FS f => fun v hv => _ 
      end).
    +     
      refine 
        (match hv in Hvect n' v' return
              (match n' as n'' return Vector.t Type n'' -> Type
               with
               | 0 => fun _ => IDProp
               | S m' => fun (e : Vector.t Type (S m')) => e[@F1]
               end v')    
        with 
        | Hcons hvh hvt => hvh
        end).
    + 
      refine
        (match hv in Hvect n' v' return forall (pf : n' = S n0), 
               (match n' as n'' return
                      Fin.t (Nat.pred n'') -> Vector.t Type n'' -> Type
                with
                | 0 => fun _ _ => IDProp
                | S m' => fun (ea : Fin.t m') (v : Vector.t Type (S m')) =>
                           v[@FS ea]
                end (eq_rec_r (λ np : nat, t (Nat.pred np))
                       (f : t (Nat.pred (S n0))) pf) v')
         with
         | Hnil => fun _ => idProp
         | Hcons hvh hvt => fun pf => _ 
         end eq_refl); cbn.
      eapply fn.
      exact hvt.
  Defined.


End Hvect.
