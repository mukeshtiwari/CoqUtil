From Coq Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef 
  BinPos. 
From Algebra Require Import 
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import 
  Prob Distr. 
From Utility Require Import Util. 
From ExtLib Require Import Monad. 
From Crypto Require Import Sigma.  

Import MonadNotation 
  VectorNotations.

#[local] Open Scope monad_scope.

(* Discrete Logarithm Zero Knowlege Proof *) 
Section DL. 
  (* Underlying Field of Vector Space *)
  Context 
    {F : Type}
    {zero one : F} 
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}. 
    (* decidable equality on Field *)

  (* Vector Element *)
  Context 
    {G : Type} 
    {gid : G} 
    {ginv : G -> G}
    {gop : G -> G -> G} 
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}. 
    (* decidable equality on G *)
    

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  #[local] Notation "( a ; c ; r )" := 
    (mk_sigma _ _ _ a c r).


  Section Okamoto.

      Section Def. 
        (* 
          h = g₁^x₁ ⋅ g₂^x₂
        *)
        Definition okamoto_protocol (x₁ x₂ : F) 
          (g₁ g₂ h : G) (u₁ u₂ : F) (c : F)  : @sigma_proto F G 1 1 2 := 
          ([(gop g₁ g₂)^u₁]; [c]; [u₁ + c * x₁; u₂ + c * x₂]).

        
        Definition okamoto_accepting_conversation 
          (g₁ g₂ h : G) (v : @sigma_proto F G 1 1 2) : bool. 
        Proof.
          refine
            match v with 
            | (a; c; r) => _ 
            end.
          destruct (vector_inv_S a) as (ah & _).
          destruct (vector_inv_S c) as (ch & _).
          destruct (vector_inv_S r) as (r₁ & rh & _).
          destruct (vector_inv_S rh) as (r₂ & _).
          refine 
            match Gdec (gop (g₁^r₁) (g₂^r₂)) (gop ah (h^ch))
            with 
            | left _ => true 
            | right _ => false 
            end.
        Defined.

        (* https://cs.pwr.edu.pl/kutylowski/articles/prezentacja_SCC-AsiaCCS.pdf *)
        Definition okamoto_simulator 
          (g₁ g₂ h : G) (u₁ u₂ : F) (c : F) : @sigma_proto F G 1 1 2 :=
          ([gop (gop (g₁^u₁) (g₂^u₂)) (h^(opp c))]; [c]; [u₁; u₂]).

      End Def.

      Section Proofs.

      End Proofs.
  End Okamoto.
End DL.
