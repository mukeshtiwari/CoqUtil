Section Rec.

  Variable
    (A B : Type)
    (Hadec : forall x y : A, {x = y} + {x <> y})
    (Hbdec : forall x y : B, {x = y} + {x <> y}).

  Inductive Node : Type :=
  | N : A -> Forest -> Node
  with 
  Forest : Type :=
  | Emp : Forest
  | F : Node -> Forest -> Forest.

 
  Scheme Node_mut := Induction for Node Sort Type
  with Forest_mut := Induction for Forest Sort Type.
 

  Lemma eq_dec_Node : 
    forall (n₁ n₂ : Node), {n₁ = n₂} + {n₁ <> n₂}.
  Proof.
    apply (Node_mut
      (fun (n₁ : Node) =>
        forall (n₂ : Node), {n₁ = n₂} + {n₁ <> n₂})
      (fun (nt₁ : Forest) =>
        forall (nt₂ : Forest), {nt₁ = nt₂} + {nt₁ <> nt₂})).
    + intros * Hn *.
      destruct n₂ as (ah & ft).
      destruct (Hn ft) as [H | H].
      ++ subst.
         destruct (Hadec a ah) as [Ha | Ha].
          +++ 
            left; subst; exact eq_refl.
          +++
            right; intro Hf.
            congruence.
      ++ right; intros Hf.
         congruence.
    + intros *.
      destruct nt₂ as [| nt ft].
      ++ left; exact eq_refl.
      ++ right; intro Hf.
         congruence.
    + intros * Hna * Hnb *.
      destruct nt₂ as [| nt ft].
      ++ right; intros Hf;
         congruence.
      ++ destruct (Hna nt) as [H | H];
         destruct (Hnb ft) as [Hc | Hc].
         - left; subst; exact eq_refl.
         - right; intro Hf; congruence.
         - right; intro Hf; congruence.
         - right; intro Hf; congruence.      
  Defined.
 
End Rec.

