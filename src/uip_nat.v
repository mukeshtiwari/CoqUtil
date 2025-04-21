From Stdlib Require Import Utf8.


Theorem uip_pf : ∀ (n : nat) (pf : n = n), pf = eq_refl n.
Proof.
  induction n as [| n ihn].
  +
    intro pf. 
    change (match 0 as n return 0 = n -> Prop 
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
    change (match S n as n' return S n = n' -> Prop with
    | 0 => fun _ => False
    | S n' => fun e =>
        e = f_equal S (f_equal pred e)
    end pf).
    destruct pf; cbn;
    reflexivity.
Defined.
