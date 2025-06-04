From Stdlib Require Import Utf8 Vector Fin Psatz.
Import VectorNotations.

Section UIP.

  (* Set Printing Implicit. *)
  Theorem uip_nat : ∀ (n : nat) (pf : n = n), pf = @eq_refl nat n.
  Proof.
    refine(fix fn (n : nat) : ∀ (pf : n = n), pf = @eq_refl nat n := 
      match n as n' in nat return 
        ∀ (pf : n' = n'), pf = @eq_refl nat n' 
      with 
      | 0 => fun pf => _ 
      | S np => fun pf => _ 
      end). 
    +
      refine
        (match pf as pf' in _ = n' return 
          (match n' as n'' return 0 = n'' -> Type 
          with 
          | 0 => fun (e : 0 = 0) => e = @eq_refl _ 0 
          | S n' => fun _ => IDProp 
          end pf')
        with 
        | eq_refl => eq_refl
        end).
      +
        specialize (fn np (f_equal Nat.pred pf)).
        change eq_refl with (f_equal S (@eq_refl _ np)).
        rewrite <-fn; clear fn.
        refine 
        (match pf as pf' in _ = n' return 
          (match n' as n'' return S np = n'' -> Type 
          with 
          | 0 => fun _ => IDProp
          | S n'' => fun e => e = f_equal S (f_equal Nat.pred e)
          end pf')
        with 
        | eq_refl => eq_refl
        end).
  Defined.

  Theorem uip_nat_irr : ∀ (n : nat) (ha hb : n = n), ha = hb.
  Proof.
    intros *. 
    pose proof (uip_nat _ ha).
    pose proof (uip_nat _ hb).
    subst.
    exact eq_refl.
  Defined.

  Theorem uip_nat_irr_ind : ∀ (n : nat) (ha hb : n = n), ha = hb.
  Proof.
    refine(fix fn (n : nat) : ∀ (ha hb : n = n), ha = hb := 
      match n as n' in nat return ∀ (ha hb : n' = n'), ha = hb
      with 
      | 0 => _ 
      | S n' => _ 
      end).
    +
      intro ha. 
      refine
        (match ha as ha' in _ = np return
          (match np as np' return 0 = np' -> Type 
          with 
          | 0 => fun (e : 0 = 0) => ∀ (hb : 0 = 0), e = hb
          | S np' => fun _ => IDProp
          end ha')
        with 
        | eq_refl => fun hb => _ 
        end).
      refine
        (match hb as hb' in _ = np return 
         (match np as np' return 0 = np' -> Type 
          with 
          | 0 => fun (e : 0 = 0) =>  eq_refl = e
          | S np' => fun _ => IDProp
          end hb')
        with 
        | eq_refl => eq_refl
        end).
    +
      (* Induction case *)
      intro ha.     
      refine
        (match ha as ha' in _ = np return 
          (match np as np' return S n' = np' -> Type 
          with 
          | 0 => fun _ => IDProp 
          | S np' => fun (e : S n' = S np') => ∀ (hb : S n' = S np'), e = hb
          end ha')
        with 
        | eq_refl => _ 
        end).
      intro hb.
      change eq_refl with (f_equal S (@eq_refl _ n')).
      specialize (fn n' eq_refl (f_equal Nat.pred hb)).
      rewrite fn. 
      clear fn. clear ha.
      refine
        (match hb as hb' in _ = np return 
          (match np as np' return S n' = np' -> Type 
          with 
          | 0 => fun _ => IDProp 
          | S np' => fun (e : S n' = S np') => 
            f_equal S (f_equal Nat.pred e) = e
          end hb')
        with 
        | eq_refl => eq_refl
        end). 
  Defined.

  Theorem le_inv : ∀ (n m : nat) (e : le n m),
    (exists H : m = n, eq_rect m  (fun w => le n w) e n H = le_n n) ∨
    (exists mp (H : m = S mp) (Hle : le n mp), eq_rect m _ e (S mp) H = le_S n mp Hle).
  Proof.
    intros n m e.
    refine
      (match e as e' in le _ m' return 
        (exists H : m' = n, eq_rect m' (fun w => le n w) e' n H = le_n n) ∨
        (exists mp (H : m' = S mp) (Hle : le n mp), eq_rect m' _ e' _ H = le_S n mp Hle)
      with 
      | le_n _ => or_introl (ex_intro _ eq_refl eq_refl)
      | le_S _ np p => or_intror 
        (ex_intro _ np (ex_intro _ eq_refl (ex_intro _ p eq_refl)))
      end).
  Defined.

  (* Thanks Johannes! *)
  Theorem le_unique_specialize_earlier : ∀ (n m : nat) (ha hb : le n m), ha = hb.
  Proof.
    refine(fix fn (n m : nat) (ha : le n m) {struct ha} : 
      ∀ (hb : le n m), ha = hb := 
      match ha as ha' in le _ m' return ∀(pfa : m = m'), 
        ha = @eq_rect nat m' (fun w => le n w) ha' m (eq_sym pfa) -> 
        ∀ (hb : le n m'), ha' = hb 
      with
      | le_n _ =>  _ 
      | le_S _ m' pfb => _
      end eq_refl eq_refl).
    +
      intros * hb hc.
      generalize dependent hc.
      refine(fun hc => 
        match hc as hc' in _ ≤ n' return ∀ (pfb : n = n'), 
          le_n n' = @eq_rect _ n (fun w => w ≤ n') hc' n' pfb  
        with 
        | le_n _ => _ 
        | le_S _ nw pfb => _ 
        end eq_refl).     
        ++
          intros *. 
          assert (hd : pfb = eq_refl) by 
          (apply uip_nat).
          subst; cbn; exact eq_refl. 
        ++
          intros pfc. subst.
          abstract nia.  
    +
      (* here we have pfb, the structurally smaller value *)
      specialize (fn _ _ pfb). 
      intros * hb hc.
      generalize dependent pfb.
      generalize dependent pfa.
      generalize dependent hc.
      refine(fun hc => 
        match hc as hc' in _ ≤ (S mp) return ∀ (pf : mp = m') pfa pfb fn hb,
          le_S n mp (@eq_rect _ m' (fun w => n ≤ w) pfb mp (eq_sym pf)) = hc'
        with 
        | le_n _ => _ 
        | le_S _ nw pfc => _
        end eq_refl).
      ++
        destruct n as [| n].
        +++ exact idProp.
        +++
          intros * hb. abstract nia. 
      ++
        intros * hb hd. subst; cbn.
        f_equal. eapply hb. 
  Defined.  

  Theorem le_unique_another : ∀ (n m : nat) (ha hb : le n m), ha = hb.
  Proof.
    refine(fix fn (n m : nat) (ha : le n m) {struct ha} : 
      ∀ (hb : le n m), ha = hb := 
      match ha as ha' in le _ m' return ∀(pfa : m = m'), 
        ha = @eq_rect nat m' (fun w => le n w) ha' m (eq_sym pfa) -> 
        ∀ (hb : le n m'), ha' = hb 
      with
      | le_n _ =>  _ 
      | le_S _ m' pfb => _ 
      end eq_refl eq_refl).
    +
      intros * hb hc.
      refine(match hc as hc' in _ ≤ n' return ∀ (pfb : n = n'), 
          le_n n' = @eq_rect _ n (fun w => w ≤ n') hc' n' pfb  
        with 
        | le_n _ => _ 
        | le_S _ nw pfb => _ 
        end eq_refl).     
        ++
          intros *. 
          assert (hd : pfb = eq_refl) by 
          (apply uip_nat).
          subst; cbn; exact eq_refl. 
        ++
          intros pfc. subst.
          abstract nia.  
    +
      specialize (fn _ _ pfb).
      intros * hb hc.
      refine(match hc as hc' in _ ≤ (S mp) return ∀ (pf : mp = m'),
          le_S n mp (@eq_rect _ m' (fun w => n ≤ w) pfb mp (eq_sym pf)) = hc'
        with 
        | le_n _ => _ 
        | le_S _ nw pfc => _
        end eq_refl).
      ++
        destruct n as [| n].
        +++ exact idProp.
        +++
          intros *. abstract nia.
      ++
        intros *. subst; cbn.
        f_equal. eapply fn.
  Defined.
  
  
  Theorem le_unique : ∀ (n m : nat) (ha hb : le n m), ha = hb.
  Proof.
    refine(fix fn (n m : nat) (ha : le n m) {struct ha} : 
      ∀ (hb : le n m), ha = hb := 
      match ha as ha' in le _ m' return ∀(pfa : m = m'), 
        ha = @eq_rect nat m' (fun w => le n w) ha' m (eq_sym pfa) -> 
        ∀ (hb : le n m'), ha' = hb 
      with
      | le_n _ =>  _ 
      | le_S _ m' pfb => _ 
      end eq_refl eq_refl).
    +
      intros * hb hc.
      generalize dependent hc.
      refine(fun hc => 
        match hc as hc' in _ ≤ n' return ∀ (pfb : n = n'), 
          le_n n' = @eq_rect _ n (fun w => w ≤ n') hc' n' pfb  
        with 
        | le_n _ => _ 
        | le_S _ nw pfb => _ 
        end eq_refl).     
        ++
          intros *. 
          assert (hd : pfb = eq_refl) by 
          (apply uip_nat).
          subst; cbn; exact eq_refl. 
        ++
          intros pfc. subst.
          abstract nia.  
    +
      specialize (fn _ _ pfb).
      intros * hb hc. 
      generalize dependent pfb.
      generalize dependent pfa.
      generalize dependent hc.
      refine(fun hc => 
        match hc as hc' in _ ≤ mp return ∀ (pf : mp = S m') pfa pfb hb hc,
          le_S n m' pfb = @eq_rect _ mp _ hc' (S m') pf   
        with 
        | le_n _ => _ 
        | le_S _ nw pfc => _
        end eq_refl).
      ++
        intros * hb hd. subst. 
        abstract nia.
      ++
        intros * hb hd.   
        inversion pf as [hpf]; subst.
        assert (hd : pf = eq_refl) by 
        (apply uip_nat). 
        subst; cbn. 
        f_equal; eapply hb.
  Defined.

  Theorem fin_eq : ∀ {n} (x y : Fin.t n), 
    Fin.FS x = Fin.FS y -> x = y.
  Proof.
    intros n x y ha.
    refine
      (match ha in _ = a return 
        (match a as a' in Fin.t n' return 
          Fin.t (Nat.pred n') -> Type
        with 
        | Fin.F1 => fun _ => IDProp
        | Fin.FS f => fun u => u = f
        end x)
      with 
      | eq_refl => eq_refl
      end). 
  Defined.

     
End UIP. 


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
      (match n' as np return Type 
      with
      | 0 => IDProp  
      | S n'' => Type 
      end) 
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
               (match n' as np return Type 
              with
              | 0 => IDProp  
              | S n'' => Type 
              end) 
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
      (match n' as np return Type 
      with
      | 0 => IDProp  
      | S n'' => Vector.t Type n''
      end) 
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
          (match n' as np return Type 
          with
          | 0 => IDProp  
          | S n'' => Vector.t Type n''
          end) 
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


  Definition hvect_nth_fin_ind : ∀ {n : nat} {v : Vector.t Type n}, Hvect n v ->
    ∀ (f : Fin.t n), Vector.nth v f.
  Proof.
    refine(fix fn (n : nat) (v : Vector.t Type n) 
      (hv : Hvect n v) {struct hv} : forall (f : Fin.t n), v[@f] :=
      match hv in Hvect n' v' return forall (f : Fin.t n'), v'[@f] 
      with
      | Hnil => fun f => match f with end 
      | @Hcons _ n' vt hvh hvt => fun f => _ 
      end).
    refine
      (match f as f' in Fin.t np return ∀ (pf : S n' = np), 
        (∀ f : Fin.t n', vt[@f]) ->
        (match np as np' return Vector.t Type (Nat.pred np') -> Fin.t np' -> Type 
        with
        | 0 => fun _ _  => IDProp
        | S n' => fun ea eb => (T :: ea)[@eb]
        end
        (eq_rect (S n') (fun w => Vector.t Type (Nat.pred w)) vt np pf) f')
        with 
        | Fin.F1 => fun _ _ => hvh
        | @Fin.FS nw fp => fun pfa fret => _
        end eq_refl (fn _ vt hvt)). 
        cbn. 
        inversion pfa; subst; cbn.
        assert (ha : pfa = eq_refl) by 
        (apply uip_nat). subst; cbn.
        eapply fret. 
  Defined. 

  
  Eval compute in hvect_nth_fin_ind (Hcons true (Hcons 1 Hnil)) (FS F1).

  
  Definition hvect_nth : ∀ {n : nat} (f : Fin.t n) 
    {v : Vector.t Type n}, Hvect n v -> Vector.nth v f.
  Proof.
    refine(fix fn {n : nat} (f : Fin.t n) {struct f} : 
      ∀ (v : Vector.t Type n), Hvect n v → v[@f] := 
      match f as f' in Fin.t n' return ∀ (v : Vector.t Type n'), 
        Hvect n' v → v[@f']
      with 
      | @Fin.F1 nf => fun v hv => _ 
      | @Fin.FS nf fp => fun v hv => _ 
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
              (fp : Fin.t (Nat.pred (S nf))) pf) v')
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
      | @Hcons vah na vat hvh hvt => _ 
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
        (match vb as vb' in Vector.t _ nw return ∀ (pfa : S na = nw),
          (match nw as np return ∀ (pfb : nw = np), Vector.t _ np -> Type 
          with 
          | 0 => fun (pfb : nw = 0) (e : Vector.t Type 0) => IDProp
          | S n'' => fun (pfb : nw = S n'') (e : Vector.t Type (S n'')) => 
            ((∀ i : Fin.t (S n''), 
              match i in (Fin.t m')
              return (Vector.t Type (Nat.pred m') → Type)
              with
              | @F1 n1 => fun _ => vah
              | @FS n1 p' => fun (v' : Vector.t Type n1) => v'[@p']
              end (@eq_rect _ (S na) (fun nt => Vector.t Type (Nat.pred nt)) 
                vat (S n'') (eq_trans pfa pfb)) → e[@i]) → Hvect (S n'') e)
          end eq_refl vb')
        with 
        | [] => fun _ => idProp
        | vbh :: vbt => fun pfa ha => _
        end eq_refl); inversion pfa; subst.
        refine (Hcons (ha Fin.F1 hvh) _).
        eapply fn; [exact hvt | ]. 
        intros i hi.
        assert (hc : pfa = eq_refl) by 
        (apply uip_nat).
        subst; cbn in ha.
        exact (ha (Fin.FS i) hi). 
  Defined.

  Definition hvect_map_specialized : ∀  {n : nat} {va vb : Vector.t Type n}, Hvect n va ->
   (∀ (i : Fin.t n), Vector.nth va i -> Vector.nth vb i) -> Hvect n vb.
  Proof.
    refine(fix fn n va vb hv {struct hv} : 
      (∀ i : Fin.t n, va[@i] → vb[@i]) → Hvect n vb := 
      match hv as hv' in Hvect n' va' return ∀ (pf : n = n'), 
        (∀ i : Fin.t n', va'[@i] → vb[@(eq_rec_r _ i pf)]) → 
        Hvect n' (@eq_rect _ n _ vb n' pf)
      with 
      | Hnil => _
      | @Hcons vah na vat hvh hvt => let ret := fun vb fi => 
           fn na vat vb hvt fi in _   (* I instantiated the induction hypothesis here *)
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
      clearbody ret; clear fn.
      intros * ha.
      generalize dependent va.
      generalize dependent vb.
      rewrite pf; cbn.
      intro vb.
      intros * ha * hv.
      revert ha.
      refine
        (match vb as vb' in Vector.t _ nw return ∀ (pfa : S na = nw),
          (match nw as np return ∀ (pfb : nw = np), Vector.t _ np -> Type 
          with 
          | 0 => fun (pfb : nw = 0) (e : Vector.t Type 0) => IDProp
          | S n'' => fun (pfb : nw = S n'') (e : Vector.t Type (S n'')) => 
            ((∀ i : Fin.t (S n''), 
              match i in (Fin.t m')
              return (Vector.t Type (Nat.pred m') → Type)
              with
              | @F1 n1 => fun _ => vah
              | @FS n1 p' => fun (v' : Vector.t Type n1) => v'[@p']
              end (@eq_rect _ (S na) (fun nt => Vector.t Type (Nat.pred nt)) 
                vat (S n'') (eq_trans pfa pfb)) → e[@i]) → Hvect (S n'') e)
          end eq_refl vb')
        with 
        | [] => fun _ => idProp
        | vbh :: vbt => fun pfa ha => _
        end eq_refl); inversion pfa; subst.
        refine (Hcons (ha Fin.F1 hvh) _).
        eapply ret. 
        intros i hi.
        assert (hc : pfa = eq_refl) by 
        (apply uip_nat).
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
        (apply uip_nat).
        subst; cbn.
        refine(Hcons (hvah, hvbh) (fn _ _ hvat _ hvbt)).
  Defined.

  Definition hvect_zip_specialized {n : nat} {va vb : Vector.t Type n}
    {hva : Hvect n va} (hvb : Hvect n vb) : Hvect n (Vector.map2 prod va vb).
  Proof.
    generalize dependent n.
    refine(fix fn (n : nat) (va vb : Vector.t Type n)
      (hva : Hvect n va) {struct hva} : Hvect n vb ->
      Hvect n (Vector.map2 prod va vb) :=
      match hva as hva' in Hvect n' va' return ∀ (pf : n = n'),
      (Hvect n' (@eq_rect _ n _ vb n' pf) ->
      Hvect n' (Vector.map2 prod va' (@eq_rect _ n _ vb n' pf)))
      with
      | Hnil => fun pf hvb => _
      | @Hcons vah na vat hvah hvat => fun pf hvb => 
        let ret := fun vb hvbt => fn na vat vb hvat hvbt in _ 
      end eq_refl).
    +
      generalize dependent vb.
      rewrite pf; cbn; intros vb hvb.
      refine
        match vb as vb' in Vector.t _ n' return
        (match n' as n'' return Vector.t _ n'' -> Type
        with
        | 0 => fun e => Hvect 0
          (Vector.case0 (fun _ : Vector.t Type 0 => Vector.t Type 0)
          [] e)
        | _ => fun _ => IDProp
        end vb')
        with
        | [] => Hnil
        end.
    +
      clearbody ret. clear fn.
      generalize dependent vb.
      rewrite pf. intros vb hvb.
      cbn in hvb.
      change (eq_rect (S na) (Vector.t Type) vb (S na) eq_refl)
      with vb.
      generalize dependent vat.
      refine
      (match hvb as hvb' in Hvect n' vb' return ∀ (pf : S na = n'),
        (match n' as n'' return Vector.t _ n'' -> Type
         with
          | 0 => fun _ => IDProp
          | S n'' => fun (eb : Vector.t Type (S n'')) =>
            ∀ (vat : Vector.t Type n''), Hvect n'' vat → 
            (∀ ec : Vector.t Type n'', Hvect n'' ec → Hvect n'' (map2 prod vat ec)) →
              Hvect (S n'') (map2 prod (vah :: vat) eb)
          end vb')
      with
      | Hnil => fun _ => idProp
      | Hcons hvbh hvbt => fun ha t hvat => _
      end eq_refl).
      intros ret.
      eapply eq_sym in ha. subst.
      inversion ha; subst; clear ha. 
      refine(Hcons (hvah, hvbh) _).
      eapply ret. exact hvbt.
  Defined.

  Fixpoint hvect_app {n m : nat} {va : Vector.t Type n} {vb : Vector.t Type m}
    (hva : Hvect n va) (hvb : Hvect m vb) : 
    Hvect (n + m) (Vector.append va vb) :=
    match hva as hv' in Hvect n' v' 
      return Hvect (n' + m) (Vector.append v' vb) 
    with
    | Hnil => hvb
    | Hcons hvah hvat => Hcons hvah (hvect_app hvat hvb)
    end.

  Definition hvect_to_vect: ∀ {n : nat} {v : Vector.t Type n},
    Hvect n v -> Vector.t (sigT (fun A => A)) n.
  Proof.
    refine(fix fn (n : nat) (v : Vector.t Type n) 
      (hv : Hvect n v) {struct hv}: 
      Vector.t (sigT (fun A => A)) n := 
      match hv as hv' in Hvect n' v' return 
        Vector.t (sigT (fun A => A)) n' 
      with 
      | Hnil => @Vector.nil _ 
      | Hcons hvh hvt => _ 
      end).
    refine (@Vector.cons _ _ _ _).
    exists T. exact hvh.
    eapply fn. exact hvt.
  Defined.

  Definition vect_to_hvect : ∀ {n : nat}, Vector.t (sigT (fun A => A)) n -> 
    {v : Vector.t Type n &  Hvect n v}.
  Proof.
    refine(fix fn (n : nat) (v : Vector.t (sigT (fun A => A)) n) {struct v} : 
       {u : Vector.t Type n &  Hvect n u} := 
       match v as v' in Vector.t _ n' return 
        {u : Vector.t Type n' &  Hvect n' u} 
      with 
      | [] => existT _ [] Hnil
      | vh :: vt => _
      end).
    destruct (fn _ vt) as (u & hv).
    destruct vh as (vhh & vht).
    exists (vhh :: u).
    exact (Hcons vht hv). 
  Defined.

  Definition hvect_to_fin : ∀ {n : nat} {v : Vector.t Type n}, 
    Hvect n v -> ∀ (f : Fin.t n), Vector.nth v f.
  Proof.
    refine(fix fn (n : nat) (v : Vector.t Type n)
      (hv : Hvect n v) {struct hv} : ∀ (f : Fin.t n), Vector.nth v f := 
      match hv as hv' in Hvect n' v' return 
        ∀ (f : Fin.t n'), Vector.nth v' f
      with 
      | Hnil => fun f => match f with end
      | Hcons hvh hvt => fun f => _ 
      end).
    refine 
      (match f as f' in Fin.t n' return ∀ (pf : S n0 = n'),
        (match n' as n'' return Vector.t Type (Nat.pred n'') -> Fin.t n'' -> Type 
        with
        | 0 => fun _ _ => IDProp 
        | S n'' => fun (ea : Vector.t Type n'') (eb : Fin.t (S n'')) => 
          (T :: ea)[@eb]
        end (@eq_rect _ (S n0) (fun np => Vector.t Type (Nat.pred np)) 
            t n' pf) f')
      with 
      | Fin.F1 => fun _ => hvh 
      | Fin.FS f' => fun pf => _
      end eq_refl); cbn.
      inversion pf as [ha]; subst.
      assert (hb : pf = eq_refl) by 
      (apply uip_nat).
      subst; cbn.
      eapply fn. exact hvt.
  Defined.

  Definition fin_to_hvect : ∀ {n : nat} {v : Vector.t Type n}, 
    (∀ (f : Fin.t n), Vector.nth v f) -> Hvect n v.
  Proof.
    refine(fix fn (n : nat) {struct n} : ∀ (v : Vector.t Type n), 
    (∀ (f : Fin.t n), Vector.nth v f) -> Hvect n v := 
    match n as n' in nat return ∀ (pf : n = n') (v : Vector.t Type n'), 
    (∀ (f : Fin.t n'), Vector.nth v f) -> Hvect n' v 
    with 
    | 0 => fun ha v f => _ 
    | S n' => fun ha => _ 
    end eq_refl).
    +
      refine 
        (match v as v' in Vector.t _ n' return 
          (match n' as n'' return Vector.t Type n'' -> Type 
          with 
          | 0 => fun e : Vector.t Type 0 => Hvect 0 e 
          | S n'' => fun _ => IDProp 
          end v') 
        with 
        | [] => Hnil 
        end).
    +
      intro v.
      refine 
        (match v as v' in Vector.t _ np return ∀ (pf : S n' = np),
          (match np as n'' in nat return Vector.t Type n'' -> Type 
          with 
          | 0 => fun _ => IDProp
          | S n'' => fun (e : Vector.t Type (S n'')) => (∀ f : t (S n''), e[@f]) → Hvect (S n'') e
          end v')
        with
        | [] => fun hb => idProp
        | vh :: vt => fun ha f => _
        end eq_refl).
        eapply eq_sym in ha.
        inversion ha; subst.
        refine (Hcons (f Fin.F1) _).
        eapply fn. intro i.
        exact (f (Fin.FS i)).
  Defined.

  Definition vector_tail {A : Type} {n : nat} : 
    Vector.t A (S n) -> Vector.t A n.
  Proof.
    intro v.
    refine
      (match v as v' in Vector.t _ n' return
        (match n' return Type
        with 
        | 0 => IDProp
        | S n'' => Vector.t A n''
        end)
      with
      | vh :: vt => vt 
      end). 
  Defined.

  
  Definition vector_head {A : Type} {n : nat} : 
    Vector.t A (S n) -> A.
  Proof.
    intro v.
     refine
      (match v as v' in Vector.t _ n' return
        (match n' return Type
        with 
        | 0 => IDProp
        | S n'' => A 
        end)
      with
      | vh :: _ => vh 
      end). 
  Defined. 


  Theorem hvect_inv_head : ∀ {n : nat} {vh : Type} {vt : Vector.t Type n} 
    (hvha hvhb : vh) (hvta hvtb : Hvect n vt), 
    Hcons hvha hvta = Hcons hvhb hvtb -> hvha = hvhb.
  Proof.
    intros * ha.
    refine
      (match ha as ha' in _ = hv'  return 
        (match hv' in Hvect n' v' return 
          (match n' as n'' in nat  
          with
          | 0 => fun _ => Type 
          | S n'' => fun (e : Vector.t Type (S n'')) => 
              vector_head e -> Type 
          end v') 
        with 
        | Hnil => IDProp
        | @Hcons vh' ne vt' hvh' hvt' => fun (e : vh') => e = hvh' 
        end hvha)
      with 
      | eq_refl => eq_refl 
      end). 
  Defined.


  Theorem hvect_inv_tail : ∀ {n : nat} {vh : Type} {vt : Vector.t Type n} 
    (hvha hvhb : vh) (hvta hvtb : Hvect n vt), 
    Hcons hvha hvta = Hcons hvhb hvtb -> hvta = hvtb.
  Proof.
    intros * ha. 
    refine
      (match ha as ha' in _ = hv' return 
        (match hv' as hv'' in Hvect n' v' return 
          (match n' as n'' return Vector.t Type n'' -> Type
          with
          | 0 => fun _  => Type
          | S n'' => fun (e : Vector.t Type (S n'')) => 
           Hvect n'' (vector_tail e) -> Type
          end v')
        with 
        | Hnil => IDProp
        | @Hcons vh' ne vt' hvh' hvt' => fun (e : Hvect ne vt') => e = hvt'
        end hvta)
      with 
      | eq_refl => eq_refl
      end). 
  Defined.

  Theorem hvec_update {n : nat} {v : Vector.t Type n} {nt : Type}
    (hv : Hvect n v) (i : Fin.t n) (e : nt) : Hvect n (Vector.replace v i nt).
  Proof.
    generalize dependent n.
    refine(fix fn (n : nat) (v : Vector.t Type n) (hv : Hvect n v) : 
      ∀ i : Fin.t n, Hvect n (replace v i nt) := 
      match hv as hv' in Hvect n' v' return 
        ∀ i' : Fin.t n', Hvect n' (replace v' i' nt) 
      with
      | Hnil => fun f => match f with end
      | @Hcons vh ne vt hvh hvt => let ret := fn ne vt hvt in fun f => _ 
      end); clearbody ret; clear fn.
    refine
      (match f as f' in Fin.t n' return ∀ (pf : S ne = n'),
        (match n' as n'' return Type -> Vector.t Type (Nat.pred n'') -> 
          Fin.t n'' -> Type 
        with 
        | 0 => fun _ _ _  => IDProp
        | S n'' => fun vha vta fa =>  Hvect (S n'') 
          (replace (vha :: vta) fa nt)
        end vh (@eq_rect _ (S ne) (fun w => Vector.t Type (Nat.pred w)) vt 
          n' pf) f')
      with
      | Fin.F1 => _ 
      | @Fin.FS nw f' => _ 
      end eq_refl); cbn.
    +
      intros *. 
      inversion pf as [pfa]; subst.
      assert (ha : pf = eq_refl) by 
      (apply uip_nat). 
      subst; cbn.
      refine(Hcons e hvt).
    +
      intros *.
      inversion pf as [pfa]; subst.
      assert (ha : pf = eq_refl) by 
      (apply uip_nat). 
      subst; cbn.
      refine(Hcons hvh (ret f')).
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
  Eval compute in @hvect_fold 3 vc hvc nat f 0.
  Eval compute in @hvect_head _ vc hvc.
  Eval compute in hvect_tail hvc.
  Eval compute in hvect_zip hva hvc.
  Eval compute in hvect_app hva hvc.
  Eval compute in hvect_to_vect hva.
  Eval compute in  vect_to_hvect (hvect_to_vect hva).
  Eval compute in hvect_to_fin hvc (FS F1).

End Test.

Require Import Extraction.
Extraction Language OCaml.
Recursive Extraction hvect_filter.
Extraction hvect_zip.
