From Stdlib Require Import Utf8.


Theorem uip_pf : ∀ (n : nat) (pf : n = n), pf = eq_refl n.
Proof.
  induction n as [| n ihn].
  +
    intro pf. 
    change (pf = eq_refl) with 
    (match 0 as n return 0 = n -> Prop 
    with 
    | 0 => fun e => e = eq_refl
    | _ => fun e => False
    end pf).
    destruct pf; reflexivity.
  +
    intro pf.
    specialize ihn with (f_equal pred pf).
    change eq_refl with (f_equal S (@eq_refl _ n)).
    rewrite <- ihn; clear ihn.
    change (pf = f_equal S (f_equal Nat.pred pf)) with 
    (match S n as n' return S n = n' -> Prop with
    | 0 => fun _ => False
    | S n' => fun e =>
        e = f_equal S (f_equal pred e)
    end pf).
    destruct pf; cbn;
    reflexivity.
Defined.


(* small inversion *)
Set Printing Implicit.

From Stdlib Require Import Utf8 Vector Fin.
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
          (match n' as n'' return 0  = n'' -> Type 
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

End UIP. 
