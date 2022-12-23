From Coq Require Import List Psatz
  Permutation.
Require Import Utf8.
Import ListNotations.


Section SetEquality.

  Context 
    {A : Type}
    (R : A -> A -> bool).
  
  Definition equality_set (xs ys : list A) : Prop :=
    forall x, In x xs <-> In x ys.
    


  Fixpoint go (z : A) (xs : list A) : list A * list A :=
    match xs with 
    | [] => ([], [])
    | (x :: xs) => 
      match go z xs with 
      | (ys, zs) => 
        match R x z with 
        | true => (x :: ys, zs)
        | _ => (ys, x :: zs) 
        end 
      end
    end.

  

  Theorem go_app : 
    ∀ (xs ys zs : list A) (z : A), 
    (ys, zs) = go z xs -> Permutation (ys ++ zs) xs.
  Proof.
    induction xs as [|xh xst Fn];
    simpl;
    intros ? ? ? Hb.
    +
     inversion Hb; subst; 
     reflexivity.
    +
      destruct (go z xst) as [ys' zs'] eqn:Hg.
      destruct (R xh z); inversion Hb;
      simpl in * |- *; subst;
      eauto using Permutation_sym, 
      Permutation_cons,
      Permutation_cons_app, 
      Permutation_sym.
  Qed.
     

     
  Theorem go_decreasing_on_second : 
    ∀ (xs ys zs : list A) (z : A), 
    (∀ x : A, R x x = true) ->
    In z xs ->
    (ys, zs) = go z xs -> 
    List.length zs < List.length xs.
  Proof.
    induction xs as [|ax xs IHx];
    simpl.
    +
      intros ? ? ? Rref Ha Hb.
      refine (match Ha with end).
    +
      intros ? ? ? Rref Ha Hb.
      destruct (go z xs) as [xs' zs'] eqn:Hc.
      case_eq (R ax z);
      intros Hd;
      rewrite Hd in Hb.
      ++
        destruct Ha as [Ha | Ha].
        +++
          pose proof go_app _ _ _ _ (eq_sym Hc) as He.
          eapply Permutation_length in He;
          rewrite <-He, app_length;
          inversion Hb; subst; clear Hb.
          nia.
        +++
          inversion Hb; subst; clear Hb.
          pose proof IHx _ _ _ Rref Ha (eq_sym Hc) as He.
          nia.
      ++
        destruct Ha as [Ha | Ha].
        +++
          inversion Hb; subst; clear Hb.
          now rewrite Rref in Hd.
        +++
          inversion Hb; subst; clear Hb.
          pose proof IHx _ _ _ Rref Ha (eq_sym Hc) as He.
          simpl; nia.
  Qed.

  Definition List := list.
  Theorem groupBy :  
    (∀ x : A, R x x = true) -> List A -> List (List A).
  Proof.
    intros Rref xs.
    refine((fix Fn xsp 
      (acc : Acc (fun x y => List.length x < List.length y) xsp)
      {struct acc} := _) xs _).
    refine(
      match xsp as xst return xsp = xst -> _ 
      with
      | [] => fun Ha => []
      | x :: xs' => fun Ha => _ 
      end eq_refl).
    refine( 
      match go x (x :: xs') as gx 
        return go x (x :: xs') = gx -> _ 
      with 
      | (ys, zs) => fun Hb => _  
      end eq_refl).
    assert (Hc : In x (x :: xs')) by 
    (simpl; left; reflexivity).
    pose proof go_decreasing_on_second (x :: xs') ys zs x
      Rref Hc (eq_sym Hb) as Hd.
    assert (He : Acc (λ x y : list A, length x < length y) zs).
    eapply Acc_inv with xsp;
    [exact acc | rewrite Ha; exact Hd].
    exact (ys :: Fn zs He).
    eapply (Wf_nat.well_founded_ltof _ 
        (fun x => List.length x)).
  Defined.
    
 
End SetEquality.

Eval compute in (groupBy Nat.eqb PeanoNat.Nat.eqb_refl 
  [3; 1; 1; 3; 1; 3; 5; 4; 6; 4]).
