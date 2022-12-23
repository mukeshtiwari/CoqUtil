import Init.WF
import Init.Data.Nat

    
theorem nat_lt : ∀ n : Nat, 
  Acc (fun (x y : Nat) => x < y) n := by 
  intros n 
  induction n with 
  | zero =>
    focus
      apply Acc.intro
      intros y Hy
      cases Hy
  | succ n ih => 
      focus 
        apply Acc.intro
        intros y Hy 
        apply Acc.intro 
        intros z Hz 
        cases ih with
        | _ _ R => 
          apply R  
          have Ht := Nat.le_of_lt_succ Hy 
          have Hw := Nat.lt_of_lt_of_le Hz Ht 
          exact Hw 
