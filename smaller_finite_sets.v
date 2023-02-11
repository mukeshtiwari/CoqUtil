
(* ------------------------------------------------------------ *)
(* Similar to finite_set from itp13 with
- odd/F1 renamed as even/FO
- the paramater is the cardinal
- addition
- computing the half using the Braga method
- independent issue: additional technique to be used in other 
  typical situations "Ã  la Lionel"
 https://www-verimag.imag.fr/~monin/Proof/Small_inversions/2021/smaller_finite_set.v
*)

Require Import Extraction.

Definition T := True.
Definition F := False.

Section sec_absurd.
  Variable X : Type.
  Variable f: F.

  Definition P: Prop := T. (* an arbitrary inductive proposition *)

  Let Fixpoint loop (x:P) : X := loop (match f with end).

  Hypothesis p: P.
  Definition Floop_P : X := loop p.
End sec_absurd.

Definition Floop_T (X: Type) (f: F) : X :=
  (fix loop (_:T) := loop (match f with end)) I.
Definition Floop_F (X: Type) : F -> X :=
  (fix loop f := loop (match f with end)).
Definition Floop (X: Type) : F -> X :=
  (fix loop t (f:F) := loop tt (match f with end)) tt.
Definition Fexc {X: Type} (f: F) : X :=
  match Floop Empty_set f with end.
Extraction Fexc.

(*=============================================================== *)
(* Bounded nat *)

(* The type t n represents a finite set of cardinal n,
   whose elements are numbered from FO to FS (... (FS FO)   *)
Inductive t : nat -> Set :=
    | FO {n} : t (S n)
    | FS {n} : t n -> t (S n).

Inductive t_O : Set :=.

Inductive t_S (n : nat) : Set :=
    | FO' : t_S n
    | FS' : t n -> t_S n.

Definition t' : nat -> Set :=
  fun n =>
    match n with
    | O => t_O
    | S n => t_S n
    end.

Definition t_t' {n} (i : t n) : t' n :=
  match i with
  | @FO n0 => FO' n0
  | @FS n0 i0 => FS' n0 i0
  end.

(* Useful when the name of the hyp to be inverted has occurences,
   a situation met by Lionel Rieg *)
Definition t'_t {n} (i : t' n) : t n :=
  match n return t' n -> t n with
  | 0 => fun i => match i with end
  | S n => fun i => match i with
                    | FO' _ => FO
                    | FS' _ i => FS i
                    end
  end i.

(* The useful identity *)
Lemma t_t'_id {n} (i : t n) : t'_t (t_t' i) = i.
Proof. destruct i; reflexivity. Qed.

(* FYI *)
Lemma t'_t_id {n} (i : t' n) : t_t' (t'_t i) = i.
Proof.
  destruct n as [ | n]; simpl in i.
  - destruct i.
  - destruct i; reflexivity.
Qed.

(* Generic use *)
Section sec_example.
  Variable P : forall n, t n -> Prop.
  Lemma case_t_S n :
    P (S n) FO -> (forall i, P (S n) (FS i)) ->
    forall (i : t (S n)), P (S n) i.
  Proof.
    intros P0 PS i.
    destruct i as [n' | n' i'] (* stuck *). Undo 1.
    inversion i (* stuck *). subst. Undo 2.
    rewrite <- (t_t'_id i).
    destruct (t_t' i) as [ | i']; clear i; simpl.
    - exact P0.
    - apply PS.
  Qed.
End sec_example.

(* Unfinished exercise : induction principle at a given level *)
Section sec_induc.
  Variable P : forall n, t n -> Prop.
  Variable n: nat.
  Variable P0 : P (S n) FO.
  Variable PS : forall i, P n i -> P (S n) (FS i).

  Fixpoint rec_t_S (i : t (S n)) : P (S n) i.
  Proof.
    destruct i as [n' | n' i'] (* stuck *). Undo 1.
    inversion i (* stuck *). Undo 1.
    rewrite <- (t_t'_id i).
    destruct (t_t' i) as [ | i']; clear i; simpl.
    - exact P0.
    - apply PS. 
  Abort.
End sec_induc.
                                                       
(* *)

Inductive even : forall {n}, t n -> Prop :=
  | even_0 {n} :           even (@FO n)
  | even_SS {n} (i: t n) : even i -> even (FS (FS i)).

(* Precise version keeping info saying that the arg is (S _) *)
Inductive ieven0 : nat -> Prop :=
| ieven_0' n : ieven0 (S n).
(* But then even'_even_id cannot be proved (unicity of ieven_0' needed) *)
(* That said, even_even'_id is more important *)

(* Functional version of even0 *)
Inductive even0_0 : Prop := .

Inductive even0_S : Prop :=
  | even_0' : even0_S.

Definition even0 (n: nat) : Prop :=
  match n with
  | O   => even0_0
  | S _ => even0_S
  end.


Inductive evenSS {n} (i: t n) : Prop :=
   | even_SS' : even i -> evenSS i.

Definition even' : forall {n}, t n -> Prop :=
  fun n i =>
    match i with
    | @FO n => even0 (S n)
    | FS (FS i) => evenSS i
    | _ => False
    end.

Definition even_even' {n} {i: t n} (e : even i) : even' i :=
  match e with
  | @even_0 n  => even_0'
  | even_SS i e => even_SS' i e
  end.

(* Pour une utilisation Ã  la Lionel *)
Definition even'_even {n} {i: t n} : even' i -> even i :=
  match i with
  | FO   => fun e' => even_0
  | FS i =>
    match i with
      | FO   => fun e' => match e' with end
      | FS i => fun e' => match e' with even_SS' _ e => even_SS i e end
    end
  end.

(* The useful identity *)
Lemma even_even'_id {n} {i: t n} (e: even i) : even'_even (even_even' e) = e.
Proof. destruct e; reflexivity. Qed.

(* FYI *)
Lemma even'_even_id {n} {i: t n} (e: even' i) : even_even' (even'_even e) = e.
Proof.
  destruct i as [n | n i]; simpl in e.
  - simpl. destruct e. reflexivity.
  - destruct i as [n | n i]; simpl in e.
    + destruct e.
    + destruct e. reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* Applications *)

(* The basic one *)
Lemma even_SS_inv : forall n (i: t n), even (FS (FS i)) -> even i.
Proof.
  intros n i e2.
  inversion e2. subst. (* terrible *) Undo 2.
  destruct (even_even' e2) as [e]. exact e.
Qed.

(* Additions and even numbers *)

(* Simpler than lift1, but unused here *)
Fixpoint lift2 {n} (i : t n) m : t (n + m) :=
  match i in t n return t (n + m) with
  | FO => FO
  | FS i => FS (lift2 i m)
  end.

Definition t_n_Sm {n m} (i: t (S (m + n))) : t (m + S n).
  rewrite <- plus_n_Sm; exact i.
Defined.

Fixpoint lift1 m {n} (i : t n) : t (m + n) :=
  match i in t n return t (m + n) with
  | FO => t_n_Sm FO
  | FS i => t_n_Sm (FS (lift1 m i))
  end.

Fixpoint Fplus {n m : nat} (i : t n) (j : t m) : t (n + m) :=
  match i with
  | @FO n => lift1 (S n) j
  | FS i => FS (Fplus i j)
  end.


Fixpoint even_lift2 {n} (i: t n) : forall m, even (lift2 i m) -> even i.
Proof.
  intros m e.
  destruct i as [ | n i]; simpl in e.
  - constructor 1.
  - destruct i as [ | n i]; simpl in e.
    + destruct (even_even' e).
    + destruct (even_even' e) as [e']. constructor 2. apply (even_lift2 n i m e').
Qed.

Fixpoint even_lift1 m {n} {i: t n} : even (lift1 m i) -> even i.
Proof.
  intro e.
  destruct i as [ | n i]; simpl in e.
  - constructor 1.
  - destruct i as [ | n i];
      repeat (unfold t_n_Sm in e; rewrite <- plus_n_Sm in e; simpl in e).
    + destruct (even_even' e).
    + destruct (even_even' e) as [e']. constructor 2. apply (even_lift1 m n i e').
Qed.

Lemma even_plus_left n m (i: t n) (j: t m) : even (Fplus i j) -> even i -> even j.
Proof.
  intros eij ei.
  induction ei as [ | n i ei IHei]; simpl in eij.
  - apply (even_lift1 (S n) eij).
  - inversion eij. subst. (* terrible ! *) Undo 2.
    destruct (even_even' eij) as [eij']. exact (IHei eij').
Qed.

(* Structurally smaller version *)

Definition shape {n} (i: t n) : Prop :=
  match i with FS (FS i) => T | _ => F end.

Definition sh n : Prop :=
  match n with S (S n) => T | _ => F end.

(* Interactive version *)
Lemma shape_sh_inter {n} (i : t n): shape i -> sh n.
Proof.
  destruct i as [ | n1 [ | n2 i]]; intro G; now case G.
Qed.

(* Explicit version *)
Definition shape_sh {n} {i: t n} : shape i -> sh n :=
  match i in t n return shape i -> sh n with
 | FO => fun G => match G with end
 | FS i =>
     match i in t n return shape (FS i) -> sh (S n) with
     | FO => fun G => match G with end
     | FS i => fun G => I
     end
 end.

Definition pr2 n : sh n -> nat :=
  match n with
  | S (S x) => fun _ => x
  | _ => fun G => Fexc G
  end.

Fail Definition fpred2 m (j: t m) : forall G : shape j, t (pr2 m (shape_sh G)) :=
  match j in t m return forall G: shape j, t (pr2 m (shape_sh G)) with
  | FS (FS j) => fun G => j
  | _ => fun G => Fexc G
  end.

Definition fpred2 {m} (j: t m) : forall G : shape j, t (pr2 m (shape_sh G)) :=
  match j in t m return forall G: shape j, t (pr2 m (shape_sh G)) with
  | FS j =>
    match j in t m return forall G: shape (FS j), t (pr2 (S m) (shape_sh G)) with
    | FS j => fun G => j
    | _ => fun G => Fexc G
    end
  | _ => fun G => Fexc G
  end.

Definition Ï€even {n} {i: t n} (D: even (FS (FS i))) : even i :=
  match D in even j return
    forall G: shape j, even (fpred2 j G) with
  | even_SS i e => fun G => e
  | _ => fun G => match G with end
  end I.

(* Can be used in place of even_even' below *)
Lemma not_even_1_coq : forall n, ~even (FS (@FO n)).
Proof. intros n e; inversion e. Qed.
     
Fixpoint half {n} (i: t n) (D: even i) {struct D} : nat :=
  match i with
  | FO => fun _ => 0
  | FS i =>
    match i return even (FS i) -> nat with
    | FO => fun D => Fexc (even_even' D)
    | FS i => fun D => S (half i (Ï€even D))
    end
  end D.

Extraction half.

