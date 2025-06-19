From Stdlib Require Import Utf8 Vector PeanoNat Peano_dec 
  Psatz.
Import VectorNotations EqNotations.

Module Rev.
Section Rev.

  Context {A : Type}.

  Lemma invert_eq_rect {x y} (P : A -> Type) (hb : x = y) (ha : P x) (hc : P y) :
    hc = rew [P] hb in ha → ha = rew <- [P] hb in hc.
  Proof.
    intros * hd.
    rewrite hd, rew_opp_l.
    reflexivity.
  Defined.

  Fixpoint vector_rev {n : nat} (v : Vector.t A n) : Vector.t A n.
  Proof.
    refine
      match v as v' in Vector.t _ n' return Vector.t A n'
      with 
      | [] => []
      | @Vector.cons _ vh nw vt =>
          rew [Vector.t A] (Nat.add_1_r nw) in 
          (vector_rev _ vt ++ [vh])
      end.
  Defined.

  Lemma rew_cons {n} (h : A) (t : Vector.t A n) {m} (e : n = m) :
    rew [Vector.t A] (f_equal S e) in (h :: t) =
    h :: (rew [Vector.t A] e in t).
  Proof.
    destruct e; reflexivity.
  Defined.

  Lemma proof_irr : ∀ (n : nat), (Nat.add_1_r (S n)) = (f_equal S (Nat.add_1_r n)).
  Proof.
    intros.
    apply Eqdep_dec.UIP_dec, eq_nat_dec.
  Qed.


  Theorem vector_app_assoc  : forall (n : nat)
    (vn : Vector.t A n), forall (m : nat) (vm : Vector.t A m),
    forall (r : nat) (vr : Vector.t A r),
    forall (e : n + (m + r) =  n + m + r),
    (vn ++ vm) ++ vr = rew [Vector.t A] e in 
    (vn ++ (vm ++ vr)).
  Proof.
    intros n vn.
    induction vn.
    + intros. cbn.
      assert (e = eq_refl).
      eapply Eqdep_dec.UIP_dec, eq_nat_dec.
      subst. cbn. reflexivity.
    +
      intros. cbn in e |- *.
      inversion e as [ea].
      replace e with (f_equal S ea) by 
      (apply Eqdep_dec.UIP_dec, eq_nat_dec).
      rewrite rew_cons.
      f_equal. eapply IHvn. 
  Qed.


  Theorem vector_app_assoc_dual  : forall (n : nat)
    (vn : Vector.t A n), forall (m : nat) (vm : Vector.t A m),
    forall (r : nat) (vr : Vector.t A r),
    forall (e : n + (m + r) =  n + m + r),
    rew <- [Vector.t A] e in ((vn ++ vm) ++ vr) = 
    (vn ++ (vm ++ vr)).
  Proof.
    intros *.
    pose proof (vector_app_assoc n vn m vm r vr e) as ha.
    rewrite ha, rew_opp_l. 
    exact eq_refl.
  Qed.


  Fixpoint rev_app_emp : ∀ (m : nat) (v : Vector.t A m),
    rew [t A] Nat.add_comm m 0 in (v ++ []) = v.
  Proof.
    intros n v.
    destruct v as [|vh n vt].
    + cbn. 
      assert (ha : Nat.add_comm 0 0 = eq_refl) by 
      (eapply Eqdep_dec.UIP_dec, eq_nat_dec).
      rewrite ha. reflexivity.
    +
      cbn. 
      specialize (rev_app_emp _ vt).
      replace (Nat.add_comm (S n) 0) with 
      (f_equal S (Nat.add_comm n 0)) by 
      (apply Eqdep_dec.UIP_dec, eq_nat_dec).
      rewrite rew_cons. f_equal.
      rewrite rev_app_emp. 
      exact eq_refl.
  Qed.
  

  
  Lemma rew_app {n m k} (v : Vector.t A n) (w : Vector.t A k) (e : n = m) :
    rew [Vector.t A] (f_equal (fun x => x + k) e) in (v ++ w) =
    (rew [Vector.t A] e in v) ++ w.
  Proof.
    destruct e; reflexivity.
  Defined.

  Lemma rew_app_aux {n m k} (v : Vector.t A n) (w : Vector.t A k) (e : k = m) :
    rew [Vector.t A] (f_equal (fun x => n + x) e) in (v ++ w) =
    (v ++ rew [Vector.t A] e in w).
  Proof.
    destruct e; reflexivity.
  Defined.


  Fixpoint rev_app : forall (n : nat) (va : Vector.t A n) 
    (m : nat) (vb : Vector.t A m), 
    vector_rev (va ++ vb) = rew [Vector.t A] (Nat.add_comm m n) in 
    (vector_rev vb ++ vector_rev va).
  Proof.
    destruct va as [|vah n vat].
    + cbn. intros *. 
      rewrite rev_app_emp. exact eq_refl.
    +
      cbn. intros *.
      specialize (rev_app _ vat m vb). 
      rewrite rev_app.
      remember (vector_rev vb) as rvb.
      remember (vector_rev vat) as rvat.
      rewrite <-rew_app.
      rewrite <-rew_app_aux. 
      erewrite vector_app_assoc with (e := (Nat.add_assoc m n 1)).
      rewrite !rew_compose. 
      f_equal. 
      apply Eqdep_dec.UIP_dec, eq_nat_dec.
  Qed.


  Theorem rev_app_dual : forall (n : nat) (va : Vector.t A n) 
    (m : nat) (vb : Vector.t A m), 
    (vector_rev vb ++ vector_rev va) = rew <- [Vector.t A] (Nat.add_comm m n) in 
    vector_rev (va ++ vb).
  Proof.
    intros *.
    pose proof (rev_app n va m vb) as ha.
    rewrite ha, rew_opp_l. 
    exact eq_refl.
  Qed.
  

  Fixpoint rew_push_out : ∀ (n : nat) (v : Vector.t A n) (h : A), 
    vector_rev (rew [Vector.t A] Nat.add_1_r n in
    (v ++ [h])) = rew [Vector.t A] Nat.add_1_r n in vector_rev (v ++ [h]).
  Proof.
    intros n v.
    destruct v as [| vh n vt].
    + cbn. intros *.
      rewrite !rew_compose.
      assert (ha : Nat.add_1_r 0 = eq_refl).
      eapply Eqdep_dec.UIP_dec, eq_nat_dec.
      rewrite !ha; cbn.
      rewrite ha; cbn.
      exact eq_refl.
    +
      cbn. intros *.
      rewrite !rew_compose.
      specialize(rew_push_out _ vt h).
      rewrite proof_irr.
      rewrite rew_cons. cbn.
      rewrite rew_push_out.
      rewrite proof_irr.
      rewrite <-rew_compose.
      f_equal.
      rewrite <-rew_app.
      f_equal. 
      apply Eqdep_dec.UIP_dec, eq_nat_dec.
  Qed.


  Lemma transport_shiftin n (v : Vector.t A n) (e : n = n) :
    rew [Vector.t A] e in v = v.
  Proof.
    assert (ha : e = eq_refl).
    (apply Eqdep_dec.UIP_dec, eq_nat_dec).
    rewrite ha. cbn. exact eq_refl.
  Qed.


  Fixpoint vector_rev_rev : ∀ (n : nat) (v : Vector.t A n), vector_rev (vector_rev v) = v.
  Proof.
    destruct v as [| h n v]. 
    + exact eq_refl.
    + cbn. 
      rewrite rew_push_out.
      rewrite rev_app.
      cbn. rewrite vector_rev_rev.
      now rewrite rew_compose, !transport_shiftin.
  Qed.

End Rev.
End Rev.


Module EQRev.
  Section EQRev.

    Context {A : Type}.

    Fixpoint vector_rev {n : nat} (v : Vector.t A n) : Vector.t A n.
    Proof.
      refine
        match v as v' in Vector.t _ n' return Vector.t A n'
        with 
        | [] => []
        | @Vector.cons _ vh nw vt =>
            rew dependent [fun y p => Vector.t A y] (Nat.add_1_r nw) in 
            (vector_rev _ vt ++ [vh]) 
        end.
    Defined.


  Lemma rew_cons {n} (h : A) (t : Vector.t A n) {m} (e : n = m) :
    rew dependent [fun y p => Vector.t A y] (f_equal S e) in (h :: t) =
    h :: (rew dependent [fun y p => Vector.t A y] e in t).
  Proof.
    destruct e; reflexivity.
  Defined.

  Lemma proof_irr : ∀ (n : nat), (Nat.add_1_r (S n)) = (f_equal S (Nat.add_1_r n)).
  Proof.
    intros.
    apply Eqdep_dec.UIP_dec, eq_nat_dec.
  Qed.


  Theorem vector_app_assoc  : forall (n : nat)
    (vn : Vector.t A n), forall (m : nat) (vm : Vector.t A m),
    forall (r : nat) (vr : Vector.t A r),
    forall (e : n + (m + r) =  n + m + r),
    (vn ++ vm) ++ vr = rew dependent [fun y p => Vector.t A y] e in 
    (vn ++ (vm ++ vr)).
  Proof.
    intros n vn.
    induction vn.
    + intros. cbn. 
      assert (e = eq_refl).
      eapply Eqdep_dec.UIP_dec, eq_nat_dec.
      subst. cbn. reflexivity.
    +
      intros. cbn in e |- *.
      inversion e as [ea].
      replace e with (f_equal S ea) by 
      (apply Eqdep_dec.UIP_dec, eq_nat_dec).
      rewrite rew_cons.
      f_equal. eapply IHvn.
  Qed.

  Theorem rew_dep_rewrite {m n : nat} (e : m = n) (v : Vector.t A m) : 
    rew dependent <- [fun y _ => Vector.t A y] e in
    rew dependent [fun u _ => Vector.t A u] e in v = v.
  Proof.
    refine
      match e with 
      | eq_refl => eq_refl
      end.
  Qed.
  
  Theorem vector_app_assoc_dual  : forall (n : nat)
    (vn : Vector.t A n), forall (m : nat) (vm : Vector.t A m),
    forall (r : nat) (vr : Vector.t A r),
    forall (e : n + (m + r) =  n + m + r),
    rew dependent <- [fun y p => Vector.t A y] 
    e in ((vn ++ vm) ++ vr) = 
    (vn ++ (vm ++ vr)).
  Proof.
    intros *.
    pose proof (vector_app_assoc n vn m vm r vr e) as ha.
    pose proof (f_equal (fun x => rew dependent eq_sym e in x) ha) as hb.
    cbn in hb. rewrite ha.
    rewrite rew_dep_rewrite.
    reflexivity.
  Qed.

  Fixpoint rev_app_emp : ∀ (m : nat) (v : Vector.t A m),
    rew dependent [fun y _ => Vector.t A y] Nat.add_comm m 0 in (v ++ []) = v.
  Proof.
    intros n v.
    destruct v as [|vh n vt].
    + cbn. 
      assert (ha : Nat.add_comm 0 0 = eq_refl) by 
      (eapply Eqdep_dec.UIP_dec, eq_nat_dec).
      rewrite ha. reflexivity.
    +
      cbn. 
      specialize (rev_app_emp _ vt).
      replace (Nat.add_comm (S n) 0) with 
      (f_equal S (Nat.add_comm n 0)) by 
      (apply Eqdep_dec.UIP_dec, eq_nat_dec).
      rewrite rew_cons. f_equal.
      rewrite rev_app_emp. 
      exact eq_refl.
  Qed.


  Lemma rew_app {n m k} (v : Vector.t A n) (w : Vector.t A k) (e : n = m) :
    rew dependent [fun y _ => Vector.t A y] (f_equal (fun x => x + k) e) in (v ++ w) =
    (rew dependent [fun y _ => Vector.t A y] e in v) ++ w.
  Proof.
    destruct e; reflexivity.
  Defined.

  Lemma rew_app_aux {n m k} (v : Vector.t A n) (w : Vector.t A k) (e : k = m) :
    rew dependent [fun y _ => Vector.t A y] (f_equal (fun x => n + x) e) in (v ++ w) =
    (v ++ rew dependent [fun y _ => Vector.t A y]  e in w).
  Proof.
    destruct e; reflexivity.
  Defined.

  End EQRev.
End EQRev.
