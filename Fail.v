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


  Theorem le_unique_fail : ∀ (n m : nat) (ha hb : le n m), ha = hb.
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
      intros * hb hc.
      generalize dependent pfb.
      generalize dependent pfa.
      generalize dependent hc.
      refine(fun hc => 
        match hc as hc' in _ ≤ (S mp) return ∀ (pf : mp = m') pfa pfb hb,
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
        intros * hb. subst; cbn.
        f_equal. eapply fn. 
        Fail Guarded.
  Admitted.
  
    

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
      intros * hb hc. 
      generalize dependent pfb.
      generalize dependent pfa.
      generalize dependent hc.
      refine(fun hc => 
        match hc as hc' in _ ≤ mp return ∀ (pf : mp = S m') pfa pfb hb,
          le_S n m' pfb = @eq_rect _ mp _ hc' (S m') pf   
        with 
        | le_n _ => _ 
        | le_S _ nw pfc => _
        end eq_refl).
      ++
        intros * hb. subst. 
        abstract nia.
      ++
        intros * hb.   
        inversion pf as [hpf]; subst.
        assert (hd : pf = eq_refl) by 
        (apply uip_nat). 
        subst; cbn. 
        f_equal; eapply fn.
  Defined.


  Theorem le_unique_didnot_fail : ∀ (n m : nat) (ha hb : le n m), ha = hb.
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


(* this one works *)
  Theorem le_unique_fail : ∀ (n m : nat) (ha hb : le n m), ha = hb.
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
    + (* here we have pfb, the structurally smaller value *)
      specialize (fn _ _ pfb).
      Guarded.
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
        intros * fn hb. subst; cbn.
        f_equal. eapply fn.
  Defined.

