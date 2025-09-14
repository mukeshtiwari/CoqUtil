(* https://www-verimag.imag.fr/~monin/Proof/Small_inversions/2022/eqle/html/Eqle.diag_nat_inv.html *)
From Coq Require Import Utf8 Vector.

Import VectorNotations.

Section Inv.


  Theorem vec_inv {A : Type} : ∀ (n : nat) (v : Vector.t A n), 
    match n as n' return Vector.t _ n' -> Prop 
    with 
    | 0 => fun (v : Vector.t _ 0) => v = @Vector.nil A
    | S n' => fun (v : Vector.t _ (S n')) => 
      exists (h : A) (t : Vector.t A n'), v = Vector.cons _ h _ t 
    end v.
  Proof.
    intros n v.
    refine 
      match v as v' in Vector.t _ n' return 
        (match n' as n'' return Vector.t _ n'' -> Prop 
        with 
        | 0 => fun (u : Vector.t _ 0) => u = @Vector.nil A
        | S n' => fun (u : Vector.t _ (S n')) => 
          exists (h : A) (t : Vector.t A n'), u = Vector.cons _ h _ t 
        end v') 
      with 
      | [] => eq_refl
      | h :: t => ex_intro _ h (ex_intro _ t eq_refl)
      end.
  Defined.


  Inductive diag : nat -> nat -> Prop :=
  | zcase : diag 0 0
  | scase x y : diag x y -> diag (S x) (S y).


  Theorem diag_inv : ∀ (x y : nat) (d : diag x y), 
    match x, y return diag x y -> Prop 
    with 
    | 0, 0 => fun (ha : diag 0 0) => ha = zcase
    | S x, S y => fun (ha : diag (S x) (S y)) => 
      exists (d : diag x y), ha = scase x y d
    | _ , _ => fun _ => False  
    end d.
  Proof.
    intros x y d.
    destruct d.
    + exact eq_refl.
    + exact (ex_intro _ d eq_refl).
  Defined.

 Theorem diag_inv_convoy : ∀ (x y : nat) (d : diag x y), 
    match x, y return diag x y -> Prop 
    with 
    | 0, 0 => fun (ha : diag 0 0) => ha = zcase
    | S x, S y => fun (ha : diag (S x) (S y)) => 
      exists (d : diag x y), ha = scase x y d
    | _ , _ => fun _ => False  
    end d.
  Proof.
    intros x y d.
    refine
      (match d as d' in diag x' y' return 
        (match x', y' return diag x' y' -> Prop 
        with 
        | 0, 0 => fun (ha : diag 0 0) => ha = zcase
        | S x'', S y'' => fun (ha : diag (S x'') (S y'')) => 
          exists (d'' : diag x'' y''), ha = scase x'' y'' d''
        | _ , _ => fun _ => False  
        end d')
      with 
      | zcase => eq_refl
      | scase x' y' d' => (ex_intro _ d' eq_refl)
      end).
  Defined.


  Lemma diag_inv_z : ∀ (d : diag 0 0), d = zcase.
  Proof.
    intro d.
    refine 
      match d with 
      | zcase => eq_refl
      | _ => idProp 
      end.
  Defined.

  Lemma diag_inv_s : ∀ (x y : nat) (d : diag (S x) (S y)),
    exists (u : diag x y), d = scase x y u.
  Proof.
    intros x y d.
    refine 
      match d with 
      | zcase => idProp
      | scase u v ha => ex_intro _ ha eq_refl
      end.
  Defined.

    

  Lemma diag_refl {x} : diag x x.
  Proof.
    induction x as [|x Ihx].
    +
      exact zcase.
    +
      exact (scase _ _ Ihx).
  Defined.

  Lemma eq_diag {x y} (e : x = y) : diag x y.
  Proof.
    case e.
    exact diag_refl.
  Defined.

  Lemma diag_back {x} : ∀ {y}, diag x y → x = y.
  Proof.
    intros y d.
    induction d as [| x y d Ihx].
    + exact eq_refl.
    + exact (f_equal S Ihx).
  Defined.

  Lemma diag_back_isrefl {x} : ∀ (d : diag x x), eq_refl = diag_back d.
  Proof.
    induction x as [ | x IHx]; simpl; intro d.
    -
      pose proof (diag_inv_z d) as ha.
      rewrite ha; cbn.
      exact eq_refl.
    - 
      destruct (diag_inv_s _ _ d) as (u & dd).
      rewrite dd; simpl. rewrite <-IHx; simpl.
      exact eq_refl.
  Defined.

  Lemma diag_mono {x y} (e : x = y) : e = diag_back (eq_diag e).
  Proof.
    case e; simpl.
    rewrite <-diag_back_isrefl;
    exact eq_refl.
  Defined.

  Corollary UIP_nat_smallinv (x: nat) (e : x = x) : eq_refl = e.
  Proof.
    rewrite (diag_mono e).
    apply diag_back_isrefl.
  Defined.

  Fixpoint unique_diag x y (d : diag x y) : ∀ d', d = d'.
  Proof.
    destruct d as [| x y d]; intro d'.
    +
      destruct (diag_inv_z d'); 
      exact eq_refl.
    +
      destruct (diag_inv_s _ _ d') as (d'' & ha);
      subst; f_equal.
      eapply unique_diag.
  Defined.


  Fixpoint diagTF (x y : nat) : Prop :=
    match x, y with 
    | 0, 0 => True 
    | S x, S y => diagTF x y 
    | _, _ => False
    end.

  Definition diagTF_refl {x} : diagTF x x.
  Proof.
    induction x as [|x ihx]; cbn;
    [exact I | exact ihx].
  Defined.

  Definition eq_diagTF {x y} (e : x = y) : diagTF x y.
  Proof.
    case e; eapply diagTF_refl.
  Defined.

  Definition diagTF_back {x y} : ∀ (tf : diagTF x y), x = y.
  Proof.
    revert y.
    induction x as [|x ihx]; 
    destruct y as [| y]; simpl;
    intro ha; try (destruct ha).
    + exact eq_refl.
    + exact (f_equal S (ihx y ha)).
  Defined.

  Definition diagTF_back_isrefl {x} : ∀ (tf : diagTF x x), eq_refl = diagTF_back tf.
  Proof.
    induction x as [| x ihx]; simpl.
    +
      intro tf; destruct tf.
      exact eq_refl.
    +
      intro tf.
      rewrite <-ihx; simpl;
      exact eq_refl.
  Defined.

  Lemma diagTF_mono {x y} (e : x = y) : e = diagTF_back (eq_diagTF e).
  Proof.
    case e; simpl.
    rewrite <-diagTF_back_isrefl;
    exact eq_refl.
  Defined.

  Corollary UIP_diagTF (x: nat) (e : x = x) : eq_refl = e.
  Proof.
    rewrite (diagTF_mono e).
    apply diagTF_back_isrefl.
  Defined.

  Corollary UIP_diagTF2 (x y: nat) (e e' : x = y) : e = e'.
  Proof.
    revert e'.
    case e. apply UIP_diagTF.
  Defined.


  
  Lemma UIP_refl_nat (n:nat) (e : n = n) : e = eq_refl.
  Proof.
    induction n as [|n ihn].
    +
      change (match 0 as n return 0 = n -> Prop 
      with 
      | 0 => fun (e : 0 = 0) => e = eq_refl
      | S n => fun (e : 0 = S n) => False
      end e).
      destruct e; exact eq_refl.
    +
      specialize (ihn (f_equal pred e)).
      change eq_refl with (f_equal S (@eq_refl _ n)).
      rewrite <-ihn; clear ihn.
      change (match S n as n' return S n = n' -> Prop with 
      | 0 => fun e => False 
      | S n' => fun e => e = f_equal S (f_equal pred e)
      end e).
      pattern (S n) at 2 3, e.
      destruct e.
      exact eq_refl.
  Defined.

End Inv.
