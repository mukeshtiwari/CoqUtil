From Stdlib Require Import Utf8 Vector Fin.
Import VectorNotations.

Section Hvect.

  Inductive Hvect : ∀ (n : nat), Vector.t Type n -> Type :=
  | Hnil : Hvect 0 [] 
  | Hcons {A : Type} {n : nat} {V : Vector.t Type n} :  
    A -> Hvect n V -> Hvect (S n) (A :: V).
    
  Check (Hcons true (Hcons 1 Hnil)).
  Check (Hcons nat (Hcons bool Hnil)).

  Definition fin_inv : ∀ (n : nat) (f : Fin.t (S n)),
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

  
  Definition hvect_nth_fin {n : nat} {v : Vector.t Type n} 
    (u : Hvect n v) : ∀ (f : Fin.t n), Vector.nth v f.
  Proof.
    generalize dependent n.
    refine(fix fn (n : nat) (v : Vector.t Type n) 
      (hv : Hvect n v) {struct hv} : forall (f : Fin.t n), v[@f] :=
      match hv in Hvect n' v' return forall (f : Fin.t n'), v'[@f] 
      with
      | Hnil => fun f => match f with end 
      | @Hcons _ n' _ hvh hvt => fun (f : Fin.t (S n')) => _ 
      end).
    destruct (fin_inv _ f) as [ha | (f' & ha)]; subst; cbn;
    [exact hvh | eapply fn; exact hvt].
  Defined.

  
  Eval compute in hvect_nth_fin (Hcons true (Hcons 1 Hnil)) (FS F1).

  
  Definition hvect_nth {n : nat} (f : Fin.t n) 
    {v : Vector.t Type n} (u : Hvect n v) : Vector.nth v f.
  Proof.
    generalize dependent n.
    refine(fix fn {n : nat} (f : Fin.t n) {struct f} : 
      ∀ (v : Vector.t Type n), Hvect n v → v[@f] := 
      match f as f' in Fin.t n' return ∀ (v : Vector.t Type n'), 
        Hvect n' v → v[@f']
      with 
      | @Fin.F1 nf => fun v hv => _ 
      | @Fin.FS nf f => fun v hv => _ 
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
        (match hv in Hvect n' v' return forall (pf : n' = S nf), 
          (match n' as n'' return
                Fin.t (Nat.pred n'') -> Vector.t Type n'' -> Type
          with
          | 0 => fun _ _ => IDProp
          | S m' => fun (ea : Fin.t m') (v : Vector.t Type (S m')) => v[@FS ea]
          end (eq_rec_r (λ np : nat, t (Nat.pred np))
              (f : t (Nat.pred (S nf))) pf) v')
         with
         | Hnil => fun _ => idProp
         | Hcons hvh hvt => fun pf => _ 
         end eq_refl); cbn.
      eapply fn.
      exact hvt.
  Defined.  
  
  Eval compute in hvect_nth (FS F1) (Hcons true (Hcons 1 Hnil)).

  
  Definition hvect_map {n : nat} {va vb : Vector.t Type n} (hv : Hvect n va)
   (f : ∀ (i : Fin.t n), Vector.nth va i -> Vector.nth vb i) : Hvect n vb.
  Proof.
    generalize dependent n.
    refine(fix fn n va vb hv {struct hv} : 
      (∀ i : Fin.t n, va[@i] → vb[@i]) → Hvect n vb := 
      match hv as hv' in Hvect n' va' return ∀ (pf : n = n'), 
        (∀ i : Fin.t n', va'[@i] → vb[@(eq_rec_r _ i pf)]) → 
        Hvect n' (@eq_rect _ n _ vb n' pf)
      with 
      | Hnil => _
      | Hcons hvh hvt => _ 
      end eq_refl).
    +
      intros * ha. 
      generalize dependent va.
      generalize dependent vb.
      rewrite pf; cbn.
      intros * ha * hv.
      revert ha.
      refine 
        match vb as vb' in Vector.t _ n' return 
          (match n' as np return Vector.t _ np -> Type 
          with 
          | 0 => fun e => (∀ i : t 0, False_rect Type (case0 (λ _ : t 0, False) i) → 
            e[@i]) →  Hvect 0 e
          | S m' => fun e => IDProp
          end vb')
        with 
        | [] => fun ea => Hnil
        end.
    +
      intros * ha.
      generalize dependent va.
      generalize dependent vb.
      rewrite pf; cbn.
      intro vb.
      intros * ha * hv.
      revert ha.
      refine
        (match vb as vb' in Vector.t _ nw return ∀ (pfa : S n0 = nw),
          (match nw as np return ∀ (pfb : nw = np), 
            Vector.t _ np -> Type 
          with 
          | 0 => fun pfb e => IDProp 
          | S n'' => fun pfb e => ((∀ i : Fin.t (S n''), 
            match i in (Fin.t m')
            return (Vector.t Type (Nat.pred m') → Type)
            with
            | @F1 n1 => fun _ =>  T
            | @FS n1 p' => fun (v' : Vector.t Type n1) => v'[@p']
            end (@eq_rect _ (S n0) (fun nt => Vector.t Type (Nat.pred nt)) t (S n'') 
                (eq_trans pfa pfb)) → e[@i]) → Hvect (S n'') e)
          end eq_refl vb')
        with 
        | [] => fun _ => idProp
        | vbh :: vbt => fun pfa ha => _   
        end eq_refl); inversion pfa; subst.
        refine (Hcons (ha Fin.F1 hvh) _).
        eapply fn; [exact hvt | ].
        intros i hi.
        assert (hc : pfa = eq_refl) by 
        (apply Eqdep_dec.UIP_refl_nat).
        subst; cbn in ha.
        exact (ha (Fin.FS i) hi).
  Defined.


End Hvect.

From Stdlib Require Import Extraction.
Extraction Language OCaml.
Extraction hvect_nth.
Extraction hvect_nth_fin.
Recursive Extraction hvect_map.
