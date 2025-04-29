From Stdlib Require Import List Eqdep.
Import ListNotations.      


Section Prefix.

  Variable (A : Type).

  Inductive prefix : list A -> list A -> Type :=
  | pempty l : prefix [] l
  | pcons a l1 l2 : prefix l1 l2 -> prefix (a::l1) (a::l2).


  Hint Constructors prefix : core.

  (* eq_rect
     : forall (A : Type) (x : A) (P : A -> Type),
    P x -> forall y : A, x = y -> P y *)
  Fact prefix_inv_dep l m (w : prefix l m) :
    match l as l' in list _ return forall m, prefix l' m -> Prop
    with
    | []  => fun me (e : prefix [] me) => e = pempty me
    | a :: l' => fun me (e : prefix (a :: l') me) =>
      exists (r : list A) (ha : me = a :: r) (hb : prefix l' r),
      e = @eq_rect _ (a :: r ) _ (@pcons a l' r hb) _ (eq_sym ha)
    end m w.
  Proof.
    destruct w as [| a l1 l2 ha];
    [reflexivity | ].
    exists l2, eq_refl, ha.
    reflexivity.
  Qed.


  Hypothesis A_UIP : forall {x y : A} (e1 e2 : x = y), e1 = e2.

  Definition cons_eq {x y : A } {l m : list A} : x = y -> 
    l = m -> x::l = y::m.
  Proof. intros; subst; trivial. Defined. 

  
  Fact list_eq_inv {l m} (e : l = m) :
    match l return forall m, l = m -> Prop with
    | []   => fun m =>
      match m return _ = m -> Prop with
      | [] => fun e => e = eq_refl
      | _  => fun _ => False
      end
    | x::l => fun m =>
      match m return _ = m -> Prop with
      | []   => fun _ => False
      | y::m => fun e => exists (f : x = y) (h : l = m), e = cons_eq f h
      end
    end _ e.
  Proof.
    destruct e.
    destruct l; auto.
    now exists eq_refl, eq_refl.
  Qed.



  Fact list_UIP (l m : list A) (e1 e2 : l = m) : e1 = e2.
  Proof.
    destruct e2.
    induction l as [ | x l IHl ].
    + apply (list_eq_inv e1).
    + destruct (list_eq_inv e1) as (f & h & ->).
      now rewrite (A_UIP f eq_refl), (IHl h).
  Qed.

  (* Unicity of prefix proof *)
  Fact prefix_UP l m (p1 p2 : prefix l m) : p1 = p2.
  Proof.
    revert l m p1 p2.
    refine (fix fn l m p1 { struct p1 } := _).
    destruct p1 as [ m | a l m h ]; intros p2.
    + rewrite (prefix_inv_dep _ _ p2); reflexivity.
    + destruct (prefix_inv_dep _ _ p2) as (m' & e & h' & e').
      inversion e; subst m'.
      rewrite (list_UIP _ _ e eq_refl) in e'; simpl in e'.
      rewrite e'; f_equal.
      apply fn.
  Qed.

  Theorem prefix_empty : forall (l : list A) (w : prefix nil l), 
    w = pempty l.
  Proof.
    intros *.
    pose proof (prefix_inv_dep []) as ha. cbn in ha.
    eapply ha.
  Qed.

  Theorem eq_inv : forall (a : A) (r : list A) (ha : a :: r = a :: r), 
    ha = eq_refl.
  Proof.
    intros *.
    eapply UIP_refl.
  Qed.
    
  Theorem prefix_cons : forall (l1 l2 : list A) (a : A) 
    (w : prefix (a :: l1) (a :: l2)), exists (hu : prefix l1 l2), 
    w = @pcons a l1 l2 hu.
  Proof.
    intros *.
    destruct (prefix_inv_dep (a :: l1) (a :: l2) w) as (r & ha & hb & hc).
    inversion ha; subst.
    exists hb.  
    assert (ha = eq_refl) by apply eq_inv.
    rewrite H. reflexivity.
  Qed.
  

End Prefix.
