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
             match hv with
             | Hnil => fun f => match f with end 
             | @Hcons _ n' _ hvh hvt => fun (f : Fin.t (S n')) => _ 
             end).
    destruct (fin_inv _ f) as [ha | (f' & ha)]; subst; cbn;
      [exact hvh | eapply fn; exact hvt].
    Show Proof.
  Defined.

  
  Eval compute in hvect_nth_fin (Hcons true (Hcons 1 Hnil)) (FS F1).

End Hvect. 
