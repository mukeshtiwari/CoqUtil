From Coq Require Import Arith Utf8 Psatz
  Peano.



Section Wf_div.

 
  Theorem nat_div :  nat -> forall (b : nat),
    0 < b -> nat * nat.
  Proof.
    intro a.
    cut (Acc lt a); 
    [revert a |].
    +
      refine(fix nat_div a (acc : Acc lt a) {struct acc} : 
        forall b : nat, 0 < b -> nat * nat := 
        match acc with 
        | Acc_intro _ f => fun b Ha => 
          match (lt_eq_lt_dec a b) with 
          | inleft Hb => 
            match Hb with 
            | left Hc => (0, a)
            | right Hc => (1, 0) 
            end 
          | inright Hb => 
            match nat_div (a - b) _ b Ha with 
            | (q, r) => (S q, r)
            end 
          end
        end).
      assert (Hc : (a - b) < a).
      abstract nia.
      exact (f (a - b) Hc).
    +
      eapply lt_wf.
  Defined.

End Wf_div.
