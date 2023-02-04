From Coq Require Import Arith Utf8 Psatz
  Peano NArith.

Section Wf_Ndiv.
  Local Open Scope N_scope.
 
  Lemma N_lexico_trichotomy : forall (x y : N),
    {x < y} + {x = y} + {y < x}.
  Proof.
  refine (λ n1 n2,
    match N.compare n1 n2 as c return N.compare n1 n2 = c → _ with
    | Lt => λ H, inleft (left (proj2 (N.compare_lt_iff _ _) H))
    | Eq => λ H, inleft (right (N.compare_eq _ _ H))
    | Gt => λ H, inright (proj1 (N.compare_gt_iff _ _) H)
    end eq_refl).
  Defined.


  Theorem nat_div_N :  N -> forall (b : N),
    (0 < b) -> N * N.
  Proof.
    intro a.
    cut (Acc lt (N.to_nat a)); 
    [revert a |].
    +
      refine(fix nat_div a (acc : Acc lt (N.to_nat a)) {struct acc} : 
        forall b : N, (0 < b)%N -> N * N := 
        match acc with 
        | Acc_intro _ f => fun b Ha => 
          match (N_lexico_trichotomy a b) with 
          | inleft Hb => 
            match Hb with 
            | left Hc => (0, a)
            | right Hc => (1, 0) 
            end 
          | inright Hb => 
            match nat_div (a - b) _ b Ha with 
            | (q, r) => (N.add 1 q, r)
            end 
          end
        end).
      assert (Hc : (N.to_nat (a - b) < N.to_nat a)%nat).
      abstract nia.
      exact (f (N.to_nat (a - b)) Hc).
    +
      eapply lt_wf.
  Defined.

End Wf_Ndiv.
