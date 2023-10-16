Require Import List Utf8 Vector Fin Psatz
  Peano_dec. 
Import Notations ListNotations.


Section Definitions. 

  Definition fin (n : nat) : Type := {i | i < n}.

  Definition fin_to_Fin : 
    ∀ {n : nat}, fin n -> Fin.t n. 
  Proof.
    induction n as [|n IHn];
    intro Ha. 
    + 
      exfalso.
      inversion Ha as [x Hb].
      refine 
      (match Hb with end).
    + 
      inversion Ha as [x Hb].
      refine
      (match x as x' return x = x' -> _ 
      with 
      | 0 => fun Hc => Fin.F1 
      | S y => fun Hc => _ 
      end eq_refl).
      rewrite Hc in Hb.
      assert (Hd : fin n).
      exists y. abstract nia.
      exact (Fin.FS (IHn Hd)).
  Defined. 

  
  Definition Fin_to_fin : 
     ∀ {n : nat}, Fin.t n  -> fin n. 
  Proof.
    refine
    (fix Fn n fn {struct fn} := 
    match fn as fn' in Fin.t n' 
      return 
        forall (pf : n = n'), 
        fn' = eq_rect n (fun w => Fin.t w) fn n' pf -> _ 
    with 
    | Fin.F1 => fun _ _ => exist _ 0 _
    | Fin.FS t => fun Ha Hb => match Fn _ t with 
      | exist _ i Hc => exist _ (S i) _ 
    end  
    end eq_refl eq_refl);
    abstract nia. 
  Defined.
    
      (* My goal is replace all n0 by n 
      revert fn Hb. 
      rewrite Ha.
      intros * Hb.
      rewrite <- Eqdep_dec.eq_rect_eq_dec in Hb.
      *)
      (* I can also use subst *)

 
  
    
  Theorem fin_Fin_id :
    forall (n : nat) (u : fin n), 
      Fin_to_fin (fin_to_Fin u) = u. 
  Proof.
    induction n; intro u. 
    + 
      inversion u as [i Ha];
      try nia. 
    +
      destruct u as [i Ha] eqn:Hb.
      destruct i as [|i].
      ++
        simpl; f_equal.
        eapply le_unique.
      ++
        simpl; rewrite IHn.
        f_equal.
        eapply le_unique. 
  Qed.


  Theorem Fin_Fin_id : 
    forall (n : nat) (u : Fin.t n),
     fin_to_Fin (Fin_to_fin u) = u. 
  Proof.
    refine 
    (fix Fn n fn {struct fn} : fin_to_Fin (Fin_to_fin fn) = fn := 
      match fn as fn' in Fin.t n' return 
        forall (pf : n = n'), 
        fn' = eq_rect n (fun w => Fin.t w) fn n' pf -> _ 
      with 
      | Fin.F1 => _ 
      | Fin.FS t => _ 
      end eq_refl eq_refl).
    +
      intros * Ha; simpl.
      reflexivity.
    +
      intros * Ha; simpl.
      destruct (Fin_to_fin t) as [b Hb] eqn:Hc.
      simpl; f_equal.
      rewrite <-Fn; f_equal.
      rewrite Hc; f_equal.
      eapply le_unique.
  Qed.

     



  Eval compute in (@fin_to_Fin 3 (exist _ 2 _)).
  Eval compute in (@Fin_to_fin 3 Fin.F1).

End Definitions.



Require Import Lia
  Coq.Unicode.Utf8
  Coq.Bool.Bool
  Coq.Init.Byte
  Coq.NArith.NArith
  Coq.Strings.Byte
  Coq.ZArith.ZArith
  Coq.Lists.List.


Section Complicated.

  Open Scope N_scope.

  Definition np_total (np : N):  (np <? 256 = true) ->  byte.
  Proof.
    intros H.
    refine(match (np <? 256) as b return ∀ mp, np = mp ->
        (mp <? 256) = b -> _ with
    | true => fun mp Hmp Hmpt =>
        match of_N mp as npt return _ = npt -> _ with
        | Some x => fun _ => x
        | None => fun Hf => _
        end eq_refl
    | false => fun mp Hmp Hmf => _
    end np eq_refl eq_refl).
    abstract(
    apply of_N_None_iff in Hf;
    apply N.ltb_lt in Hmpt; nia).
    abstract (subst; congruence).
  Defined.



  Lemma np_true : forall np (Ha : np <? 256 = true) x,
    of_N np = Some x -> np_total np Ha = x.
  Proof.
    intros * Hb; unfold np_total.
    generalize (np_total_subproof0 np Ha) as f.
    generalize (eq_refl (np <? 256)) as Hc. 
    generalize (np <? 256) at 2 3 as u.
    intros *. 
    destruct u; [|congruence].
    generalize (np_total_subproof np np eq_refl Hc) as b. 
    rewrite Hb; intros * Hd.
    reflexivity.
  Qed.

End Complicated.
