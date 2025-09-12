From Stdlib Require Import Utf8 Fin Psatz List.

Definition cardinality (n : nat) (A : Type) : Prop :=
  exists (f : A -> Fin.t n) (g : Fin.t n -> A),
    (forall x, g (f x) = x) ∧ (forall y, f (g y) = y).


Definition bool_to_Fin_2 (x : bool) : Fin.t 2 :=
  if x then Fin.FS Fin.F1 else Fin.F1.


Definition Fin_2_to_bool (y : Fin.t 2) : bool :=
  match y with
    | F1 => false
    | FS F1 => true
    | _ => false (* bogus! *)
  end.

Theorem bool_cardinality_2 :
  cardinality 2 bool.
Proof.
  unfold cardinality.
  exists bool_to_Fin_2.
  exists Fin_2_to_bool.
  split.
  +
    destruct x; cbn; reflexivity.
  +
    intro y. 
    refine
    (match y as y' in Fin.t n' 
      return 
        forall (pf : n' = 2), 
        (match n' return Fin.t n' -> Type 
        with 
        | 2 => fun (eb : Fin.t 2) => 
          match eb as eb' in Fin.t n'' return n'' = 2 -> Fin.t n'' -> Type 
          with 
          | _ => fun pfa eb' => 
            (bool_to_Fin_2 (Fin_2_to_bool (eq_rect _ Fin.t eb' 2 pfa))) = 
              (eq_rect _ Fin.t eb' 2 pfa)
          end eq_refl eb
        | _ => fun _ => IDProp 
        end y')
    with 
    | F1 => _ 
    | FS f => 
      match f with 
      | F1 => _ 
      | @FS nw t => _  
      end
    end eq_refl).
    ++
      intros ha.
      assert (n = 1). nia.
      subst. exact eq_refl.
    ++
      intro ha.
      assert (n0 = 0). nia.
      subst. reflexivity.
    ++
      intro ha.
      assert (nw = 0). nia.
      subst. cbn. 
      refine match t with end.
Qed.
