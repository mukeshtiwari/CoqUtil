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


  Definition hvect_head {n : nat} {v : Vector.t Type (S n)} 
    (hu : Hvect (S n) v) : 
    match v as v' in Vector.t _ n' return 
      (match n' as np return Vector.t _ np -> Type 
      with
      | 0 => fun e => IDProp  
      | S n'' => fun (e : Vector.t Type (S n'')) => Type 
      end v') 
    with 
    | vh :: vt => vh 
    end.
  Proof.
    refine 
      match hu as hu' in Hvect np e return 
        (match np as np' return Vector.t _ np' -> Type 
        with
        | 0 => fun e => IDProp 
        | S np' => fun (v : Vector.t Type (S np')) => 
             match v as v' in Vector.t _ n' return 
              (match n' as np return Vector.t _ np -> Type 
              with
              | 0 => fun e => IDProp  
              | S n'' => fun (e : Vector.t Type (S n'')) => Type 
              end v') 
            with 
            | [] => idProp
            | vh :: _ => vh 
            end 
        end e)
      with 
      | Hcons hut hvt  => hut 
      end.
  Defined. 


  Definition hvect_tail {n : nat} {v : Vector.t Type (S n)} 
    (hu : Hvect (S n) v) : Hvect n 
    (match v as v' in Vector.t _ n' return 
      (match n' as np return Vector.t _ np -> Type 
      with
      | 0 => fun e => IDProp  
      | S n'' => fun (e : Vector.t Type (S n'')) => Vector.t Type n''
      end v') 
    with 
    | vh :: vt => vt
    end).
  Proof.
   refine 
    (match hu as hu' in Hvect n' e return 
      (match n' as n'' return Vector.t Type n'' -> Type 
      with
      | 0 => fun _ => IDProp
      | S n'' => fun (v : Vector.t Type (S n'')) => 
        Hvect n'' (match v as v' in Vector.t _ n' return 
          (match n' as np return Vector.t _ np -> Type 
          with
          | 0 => fun e => IDProp  
          | S n'' => fun (e : Vector.t Type (S n'')) => Vector.t Type n''
          end v') 
        with 
        | vh :: vt => vt
        end)
      end e)
    with 
    | Hcons hu hv => hv 
    end).
  Defined.


  Definition hvect_nth_fin : ∀ {n : nat} {v : Vector.t Type n}, Hvect n v ->
    ∀ (f : Fin.t n), Vector.nth v f.
  Proof.
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

  
  Definition hvect_nth : ∀ {n : nat} (f : Fin.t n) 
    {v : Vector.t Type n}, Hvect n v -> Vector.nth v f.
  Proof.
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
          (match n' as n'' return Fin.t (Nat.pred n'') -> 
            Vector.t Type n'' -> Type
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
  
  Definition hvect_map : ∀  {n : nat} {va vb : Vector.t Type n}, Hvect n va ->
   (∀ (i : Fin.t n), Vector.nth va i -> Vector.nth vb i) -> Hvect n vb.
  Proof.
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
          | 0 => fun e => (∀ i : t 0, False_rect Type 
            (case0 (fun _ : t 0 =>  False) i) →  e[@i]) →  Hvect 0 e
          | S m' => fun _ => IDProp
          end vb')
        with 
        | [] => fun ea => Hnil 
        | _ => idProp
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
          (match nw as np return ∀ (pfb : nw = np), Vector.t _ np -> Type 
          with 
          | 0 => fun (pfb : nw = 0) (e : Vector.t Type 0) => IDProp
          | S n'' => fun (pfb : nw = S n'') (e : Vector.t Type (S n'')) => 
            ((∀ i : Fin.t (S n''), 
              match i in (Fin.t m')
              return (Vector.t Type (Nat.pred m') → Type)
              with
              | @F1 n1 => fun _ => T
              | @FS n1 p' => fun (v' : Vector.t Type n1) => v'[@p']
              end (@eq_rect _ (S n0) (fun nt => Vector.t Type (Nat.pred nt)) 
                t (S n'') (eq_trans pfa pfb)) → e[@i]) → Hvect (S n'') e)
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


  
  Definition hvect_filter : ∀ {n : nat} {va : Vector.t Type n}, Hvect n va ->
   (∀ (i : Fin.t n), Vector.nth va i -> bool) ->
   {m : nat & {vb : Vector.t Type m & Hvect m vb}}.
  Proof.
    refine(fix fn (n : nat) (va : Vector.t Type n) (hv : Hvect n va) {struct hv} : 
      (∀ i : t n, va[@i] -> bool) -> {m : nat & {vb : Vector.t Type m & Hvect m vb}} := 
      match hv as hv' in Hvect n' va' return ∀ (pf : n = n'),
        ((∀ i : Fin.t n', va'[@i] -> bool) -> 
          {m : nat & {vb : Vector.t Type m & Hvect m vb}})
      with 
      | Hnil => fun ha fi => existT _ 0 (existT _ [] Hnil)
      | Hcons hvh hvt => fun ha fi => 
        match fi F1 hvh as fii return fi F1 hvh = fii -> 
        {m : nat & {vb : Vector.t Type m & Hvect m vb}}
        with 
        | true => fun hb => _  
        | false => fun hb => _ 
        end eq_refl
      end eq_refl).
    +
      (* True case *)
      assert (hc : (∀ i : Fin.t n0, t[@i] → bool)).
      intros i hi.
      exact (fi (Fin.FS i) hi).
      destruct (fn _ t hvt hc) as (m & vb & hv').
      exists (S m), (T :: vb).
      exact (Hcons hvh hv').
    + 
      (* false case *)
      assert (hc : (∀ i : Fin.t n0, t[@i] → bool)).
      intros i hi.
      exact (fi (Fin.FS i) hi).
      exact (fn _ t hvt hc).
  Defined.

  
  Definition fn_type : ∀ {n : nat}, Vector.t Type n -> forall (Acc : Type), Type.
  Proof.
    refine(fix fn (n : nat) (va : Vector.t Type n) acc : Type := 
      match va as va' in Vector.t _ n' 
      with 
      | [] => acc -> acc
      | vah :: vat => vah -> fn _ vat acc 
      end).
  Defined.

  
  Definition hvect_fold : ∀ {n : nat} {va : Vector.t Type n}, 
    Hvect n va -> ∀ {Acc : Type}, fn_type va Acc -> Acc -> Acc.
  Proof.
    refine(fix fn (n : nat) (va : Vector.t Type n) 
      (hv : Hvect n va) {struct hv} : ∀ (Acc : Type), 
        fn_type va Acc -> Acc -> Acc := 
      match hv in Hvect n' va' return 
        ∀ (Acc : Type), fn_type va' Acc -> Acc -> Acc 
      with 
      | Hnil => fun _ f => f 
      | Hcons hvh hvt => fun Acc fc => fn _ _ hvt _ (fc hvh) 
      end).
  Defined.

 
  Definition hvect_zip : ∀ {n : nat} {va : Vector.t Type n},
    Hvect n va -> ∀ {vb : Vector.t Type n}, Hvect n vb -> 
    Hvect n (Vector.map2 prod va vb).
  Proof.
     refine(fix fn (n : nat) (va : Vector.t Type n)
      (hva : Hvect n va) {struct hva} : ∀ (vb : Vector.t Type n), 
      Hvect n vb -> Hvect n (Vector.map2 prod va vb) :=
      match hva as hva' in Hvect n' va' return 
        ∀ (vb : Vector.t Type n'), Hvect n' vb -> Hvect n' (Vector.map2 prod va' vb)
      with 
      | Hnil => fun vb hvb => _ 
      | Hcons hvah hvat => fun vb hvb => _ 
      end).
    +
      refine 
        (match hvb as hvb' in Hvect n' vb' return 
          (match n' as n'' return Vector.t _ n'' -> Type
          with 
            | 0 => fun (e : Vector.t Type 0) => Hvect 0 (map2 prod [] e)
            | S n'' => fun _ =>  IDProp
            end vb')
        with 
        | Hnil => Hnil
        end).
    +
      refine
        (match hvb as hvb' in Hvect n' vb' return ∀ (pf : S n0 = n'),
          (match n' as n'' return Vector.t _ (Nat.pred n'') -> Vector.t _ n'' -> Type
          with 
            | 0 => fun _ _ => IDProp 
            | S n'' => fun (et : Vector.t Type n'') (eb : Vector.t Type (S n'')) =>  
                Hvect (S n'') (map2 prod (T :: et) eb)
            end (@eq_rect _ (S n0) (fun np => Vector.t Type (Nat.pred np)) 
              t n' pf) vb')
        with 
        | Hnil => fun _ => idProp
        | Hcons hvbh hvbt => fun pf => _  
        end eq_refl);
        inversion pf as [ha]; subst. 
        assert (hb : pf = eq_refl) by 
        (apply Eqdep_dec.UIP_refl_nat).
        subst; cbn.
        refine(Hcons (hvah, hvbh) (fn _ _ hvat _ hvbt)).
  Defined.  
   
End Hvect.


Section Test.

  Arguments Vector.cons {_} & _ _ _.
  Definition va : Vector.t Type 3 := [nat; bool; nat].
  Definition vb : Vector.t Type 3 := [bool; nat; bool].
  Definition hva := Hcons 9 (Hcons true (Hcons 10 Hnil)).
  
  Definition fn : ∀ (i : Fin.t 3), Vector.nth va i -> Vector.nth vb i.
  Proof.
    intro fin.
    unfold va, vb.
    destruct (fin_inv _ fin) as [ha | (f' & ha)]. subst; cbn.
    exact (fun x => if Nat.leb x 10 then true else false).
    destruct (fin_inv _ f') as [hb | (f'' & hb)]. subst; cbn.
    exact (fun x => if x then 0 else 1).
    destruct (fin_inv _ f'') as [hc | (f''' & hc)]. subst; cbn.
    exact (fun x => if Nat.leb 11 x then true else false).
    refine match f''' with end.
  Defined.

  Eval compute in @hvect_map _ va vb hva fn.
  Eval compute in fn_type [nat; bool; nat] nat.
  Eval compute in fn_type va nat.
  Definition vc : Vector.t Type 3 := [nat; nat; nat].
  Definition hvc : Hvect 3 vc := Hcons 4 (Hcons 5 (Hcons 6 Hnil)).
  Definition f : fn_type vc nat. 
  Proof.
    cbn. 
    exact (fun x y z u => x + y + z + u).
  Defined.
  Eval compute in @hvect_fold 3 vc nat hvc f 0.
  Eval compute in @hvect_head _ vc hvc.
  Eval compute in hvect_tail hvc.
  Eval compute in hvect_zip hva hvc.

End Test.

Require Import Extraction.
Extraction Language OCaml.
Recursive Extraction hvect_filter.
Extraction hvect_zip.
