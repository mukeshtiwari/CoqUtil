From Coq Require Import List Utf8 RelationClasses
                 PeanoNat Psatz.


Section Accinv.

  Inductive Accinv {A : Type} (R : A -> A -> Prop) (x : A) : Prop :=
    | Accinv_intro : (forall y : A, R x y -> Accinv R y) -> Accinv R x.


  Lemma Accinv_inv {A : Type} (R : A -> A -> Prop) :
    forall (x : A), Accinv R x -> forall y : A, R x y -> Accinv R y.
  Proof.
    intros x Ha y Hb.
    inversion Ha as [Hc].
    exact (Hc _ Hb).
  Defined.


  Definition well_founded_inv {A : Type} (R : A -> A -> Prop) :=
    forall (a : A), Accinv R a.


  Theorem well_founded_inv_type {A : Type} (R : A -> A -> Prop) (Rwf : well_founded_inv R) :
    forall (P : A -> Type), (forall x : A, (forall y : A, R x y -> P y) -> P x) ->
    forall a : A, P a.
  Proof.
   intros * Ha a.
   eapply Accinv_rect with R;
     [intros * Hb Hc |].
   eapply Ha; intros u Hd.
   eapply Hc; exact Hd.
   eapply Rwf.
  Qed.


  Theorem well_founded_inv_prop {A : Type} (R : A -> A -> Prop) (Rwf : well_founded_inv R) :
    forall (P : A -> Prop), (forall x : A, (forall y : A, R x y -> P y) -> P x) ->
    forall a : A, P a.
  Proof.
    intros * Ha *.
    eapply well_founded_inv_type with R;
      assumption.
  Qed.


  Theorem well_founded_inv_set {A : Type} (R : A -> A -> Prop) (Rwf : well_founded_inv R) :
    forall (P : A -> Set), (forall x : A, (forall y : A, R x y -> P y) -> P x) ->
    forall a : A, P a.
  Proof.
    intros * Ha *.
    eapply well_founded_inv_type with R;
      assumption.
  Qed.


  Fixpoint Fixinv_F
    {A : Type} {R : A -> A -> Prop} {P : A -> Type}
    (F : forall x : A, (forall y : A, R x y -> P y) -> P x)
    (x : A) (acc : Accinv R x) : P x.
  Proof.
    refine (F x (fun (y : A) (u : R x y) =>
                   Fixinv_F A R P F y (Accinv_inv R x acc y u))).
  Defined.

  Scheme Accinv_dep := Induction for Accinv Sort Type.


  Theorem Fixinv_F_eq
    {A : Type} {R : A -> A -> Prop} {P : A -> Type}
    (F : forall x : A, (forall y : A, R x y -> P y) -> P x) (x : A) (acc : Accinv R x) :
    F x (fun (y : A) (h  : R x y) => Fixinv_F F y (Accinv_inv R x acc y h)) =
      Fixinv_F F x acc.
  Proof.
    destruct acc using Accinv_dep; reflexivity.
  Qed.

  
  Definition Fixinv
    {A : Type} {R : A -> A -> Prop} {P : A -> Type}
    (Rwf : well_founded_inv R) 
    (F : forall x : A, (forall y : A, R x y -> P y) -> P x)
    (x : A) : P x := Fixinv_F F x (Rwf x).



  Lemma Fixinv_F_inv
    {A : Type} {R : A -> A -> Prop} {P : A -> Type}
    (F : forall x : A, (forall y : A, R x y -> P y) -> P x)
    (Finv_ext :
      forall (x : A) (f g : forall (y : A), R x y -> P y),
        (forall (y : A) (p : R x y), f y p = g y p) -> F x f = F x g)
    (Rwf : well_founded_inv R) : 
    forall (x : A) (u v : Accinv R x), Fixinv_F F x u = Fixinv_F F x v.
  Proof.
    intro x; induction (Rwf x) as [yt Hyt IHyt]; intros u v.
    rewrite <- (Fixinv_F_eq F yt u); rewrite <- (Fixinv_F_eq F yt v);
      intros.
    apply Finv_ext.
    intros ? ?.
    eapply IHyt; exact p.
  Qed.



  Lemma Fixinv_eq {A : Type} {R : A -> A -> Prop} {P : A -> Type}
    (F : forall x : A, (forall y : A, R x y -> P y) -> P x)
    ( Finv_ext :
      forall (x : A) (f g : forall (y : A), R x y -> P y),
        (forall (y : A) (p : R x y), f y p = g y p) -> F x f = F x g)
    (Rwf : well_founded_inv R) : 
    forall (x : A), Fixinv Rwf F x = F x (fun (y : A) (p : R x y) => Fixinv Rwf F y).
    Proof using Type*.
      intro x; unfold Fixinv.
      rewrite <- Fixinv_F_eq.
      apply Finv_ext; intros.
      apply Fixinv_F_inv;
        try assumption.
    Qed.
  
  
  Theorem acc_inv_acc {A : Type} {R : A -> A -> Prop} {Ht : Transitive R} :
    forall (x : A), Acc R x -> Accinv (fun u v => R v u) x.
  Proof.
    refine
      (fix fn (x : A) (acc : Acc R x) {struct acc} :=
         match acc with
         | Acc_intro _ f => _
         end).
    constructor; intros y Hy. 
    constructor; intros u Hu. 
    eapply fn. eapply f.
    eapply Ht;
      [exact Hu | exact Hy].
  Defined.

  Theorem acc_acc_inv {A : Type} {R : A -> A -> Prop} {Ht : Transitive R} :
    forall (x : A), Accinv R x -> Acc (fun u v => R v u) x.
  Proof.
    intros x Hx.
    induction Hx as [x Hx IHx].
    constructor; intros y Hy.
    constructor; intros u Hu.
    eapply IHx. eapply Ht;
      [exact Hy | exact Hu].
  Defined.


End Accinv.
