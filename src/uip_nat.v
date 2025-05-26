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
    refine(match pf as pf' in _ = n' return 
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
