(* Toy language of expressions https://www-verimag.imag.fr/~monin/Proof/Small_inversions/2021/eval_exp.v  *)
Inductive te : Type :=
  | Te_const : nat -> te
  | Te_plus : te -> te -> te
  | Te_div0 : te -> te.

Inductive val : Type :=
  | Nval  : nat -> val
  | Bval  : bool -> val.

(* Evaluation *)
Inductive eval : te -> val -> Prop :=
  | E_Const : forall n,
      eval (Te_const n) (Nval n)
  | E_Plus : forall t1 t2 n1 n2,
      eval t1 (Nval n1) ->
      eval t2 (Nval n2) ->
      eval (Te_plus t1 t2) (Nval (n1 + n2)).

(* Auxiliary inductive definitions when the 1st arg is constructed *)
Inductive eval_Const_1 n : val -> Prop :=
  | E_Const_1 : eval_Const_1 n (Nval n).
Inductive eval_Plus_1 t1 t2 : val -> Prop :=
  | E_Plus_1 : forall n1 n2,
      eval t1 (Nval n1) ->
      eval t2 (Nval n2) ->
      eval_Plus_1 t1 t2 (Nval (n1 + n2)).
Inductive eval_Div0_1 (t1: te) : val -> Prop :=.

Definition eval_1 : te -> val -> Prop :=
  fun t =>
    match t with
    | Te_const n => eval_Const_1 n
    | Te_plus t1 t2 => eval_Plus_1 t1 t2
    | Te_div0 t1 => eval_Div0_1 t1
    end.

Definition eval_eval_1 {t v} : eval t v -> eval_1 t v :=
  fun e =>
    match e with
    | E_Const n => E_Const_1 n
    | E_Plus t1 t2 n1 n2 e1 e2 => E_Plus_1 t1 t2 n1 n2 e1 e2
    end.

(* Interactive version *)
Definition eval_eval_1_inter {t v} : eval t v -> eval_1 t v.
Proof. intro e; destruct e; constructor; assumption. Qed.

(* Explicit version *)
Definition eval_eval_1_bavard {t v} : eval t v -> eval_1 t v :=
  fun e =>
    match e in eval t v return eval_1 t v with
    | E_Const n (*t := Te_const n, v := Nval n*) => E_Const_1 n : (eval_Const_1 n) (Nval n)
    | E_Plus t1 t2 n1 n2 e1 e2 (*t := Te_plus t1 t2, v := Nval (n1 + n2)*) 
      => E_Plus_1 t1 t2 n1 n2 e1 e2 : (eval_Plus_1 t1 t2) (Nval (n1 + n2))
    end.

(* Auxiliary inductive definitions when the 2nd arg is constructed *)
(* Moderately useful, because the contents of 2nd argument is not 
   constructed itself. 
   No cases for Bval, and 2 cases for Nval.
   For the second, an auxiliary equality is introduced. *)

Inductive eval_Nat_2 (n: nat) : te -> Prop :=
  | E_Const_2 : eval_Nat_2 n (Te_const n)
  | E_Plus_2 : forall t1 t2 n1 n2,
      eval t1 (Nval n1) ->
      eval t2 (Nval n2) ->
      n = n1 + n2 ->
      eval_Nat_2 n (Te_plus t1 t2).

Inductive eval_Bool_2 (b: bool) : te -> Prop :=.

Definition eval_2 : te -> val -> Prop :=
  fun t v =>
    match v with
    | Nval n => eval_Nat_2 n
    | Bval b => eval_Bool_2 b
    end t.

Definition eval_eval_2 {t v} : eval t v -> eval_2 t v :=
  fun e =>
    match e with
    | E_Const n => E_Const_2 n
    | E_Plus t1 t2 n1 n2 e1 e2 => E_Plus_2 (n1 + n2) t1 t2 n1 n2 e1 e2 eq_refl
    end.

(* Auxiliary inductive definitions when args 1 and 2 are constructed *)

(* Symmetrical version, with 2 indices. 
   Combines _1 and _2, with cumbersome additional equalities *)
Module S. 
Inductive eval_Const_Nval_1_2 (c n : nat) : Prop :=
  | E_Const_Nval_1_2 : c = n -> eval_Const_Nval_1_2 c n.
Inductive eval_Plus_Nval_1_2 t1 t2 n : Prop :=
  | E_Plus_Nval_1_2 : forall n1 n2,
      eval t1 (Nval n1) ->
      eval t2 (Nval n2) ->
      n = n1 + n2 ->
      eval_Plus_Nval_1_2 t1 t2 n.
Inductive eval_other_Nval_1_2 : Prop :=.

Definition eval_1_2 : te -> val -> Prop :=
  fun t v =>
    match t, v with
    | Te_const c, Nval n => eval_Const_Nval_1_2 c n
    | Te_plus t1 t2, Nval n => eval_Plus_Nval_1_2 t1 t2 n
    | _, _ => eval_other_Nval_1_2
    end.

Definition eval_eval_1_2 {t v} : eval t v -> eval_1_2 t v :=
  fun e =>
    match e with
    | E_Const n => E_Const_Nval_1_2 n n eq_refl
    | E_Plus t1 t2 n1 n2 e1 e2 => E_Plus_Nval_1_2 t1 t2 (n1 + n2) n1 n2 e1 e2 eq_refl
    end.
End S.

(* Asymmetrical version, with 1 param and 1 indice:
   the first has precedence over the second, because it is
   "more constructed". Then the cumbersome equalities can be removed *)
Module A.
Inductive eval_Const_Nval_1_2 n : nat -> Prop :=
  | E_Const_Nval_1_2 : eval_Const_Nval_1_2 n n.
Inductive eval_Plus_Nval_1_2 t1 t2 : nat -> Prop :=
  | E_Plus_Nval_1_2 : forall n1 n2,
      eval t1 (Nval n1) ->
      eval t2 (Nval n2) ->
      eval_Plus_Nval_1_2 t1 t2 (n1 + n2).
Inductive eval_other_Nval_1_2 : Prop :=.

Definition eval_1_2 : te -> val -> Prop :=
  fun t v =>
    match t, v with
    | Te_const c, Nval n => eval_Const_Nval_1_2 c n
    | Te_plus t1 t2, Nval n => eval_Plus_Nval_1_2 t1 t2 n
    | _, _ => eval_other_Nval_1_2
    end.

Definition eval_eval_1_2 {t v} : eval t v -> eval_1_2 t v :=
  fun e =>
    match e with
    | E_Const n => E_Const_Nval_1_2 n
    | E_Plus t1 t2 n1 n2 e1 e2 => E_Plus_Nval_1_2 t1 t2 n1 n2 e1 e2
    end.
End A.

Notation eval_eval_1_2 := A.eval_eval_1_2.

Section varP.

Variable P : val -> Prop.

Lemma test_ev1 :
  forall v , P v -> eval (Te_plus (Te_const 1) (Te_const 0)) v -> v = Nval 1.
Proof.
  intros v p e.
  destruct (eval_eval_1 e) as [n1 n2 e1 e2].
  destruct (eval_eval_1_2 e1).
  destruct (eval_eval_1_2 e2).
  reflexivity.
Qed.

Lemma test_ev1_S :
  forall v , P v -> eval (Te_plus (Te_const 1) (Te_const 0)) v -> v = Nval 1.
Proof.
  intros v p e.
  destruct (eval_eval_1 e) as [n1 n2 e1 e2].
  generalize (S.eval_eval_1_2 e1). simpl. intro e1'.
  destruct (S.eval_eval_1_2 e1) as [eq1].
  destruct (S.eval_eval_1_2 e2) as [eq2].
  subst. reflexivity.
Qed.

Lemma test_ev2:
  eval (Te_plus (Te_const 1) (Te_const 0)) (Bval true) -> False.
Proof.
intro e. destruct (S.eval_eval_1_2 e).
Qed.

Lemma test_ev2':
  eval (Te_plus (Te_const 1) (Te_const 0)) (Nval 0) -> False.
Proof.
  intro e.
  cut (0=1). discriminate.
  pattern 0 at 1.
  destruct (eval_eval_1_2 e) as [n1 n2 e1 e2].
  destruct (eval_eval_1_2 e1).
  destruct (eval_eval_1_2 e2).
  reflexivity.
Qed.

Lemma test_ev3:
  forall n, n < 5 -> eval (Te_plus (Te_const 1) (Te_const 0)) (Nval n) -> n = 1.
Proof.
  intros n l e. 
  destruct (eval_eval_1_2 e) as [n1 n2 e1 e2].
  destruct (eval_eval_1_2 e1).
  destruct (eval_eval_1_2 e2).
  reflexivity.
Qed.

Lemma test_ev3_S:
  forall n, n < 5 -> eval (Te_plus (Te_const 1) (Te_const 0)) (Nval n) -> n = 1.
Proof.
  intros n l e. 
  destruct (S.eval_eval_1_2 e) as [n1 n2 e1 e2 eq].
  destruct (S.eval_eval_1_2 e1) as [eq1].
  destruct (S.eval_eval_1_2 e2) as [eq2].
  subst. reflexivity.
Qed.

End varP.

(* ------------------------------------------------------------ *)

(* Non-deterministic evaluation, in order to illustrate
   several cases matching an "input"
*)

Section varQ.

Variable Q : te -> Prop.

Inductive eval_nd: te -> val -> Prop :=
  | E_Const_nd : forall n,
      eval_nd (Te_const n) (Nval n)
  | E_Plus_nd1 : forall t1 t2 n1 n2,
      eval_nd t1 (Nval n1) ->
      eval_nd t2 (Nval n2) ->
      eval_nd (Te_plus t1 t2) (Nval (n1 + n2))
  | E_Plus_nd2 : forall t1 t2 n2,
      Q t1 ->
      eval_nd t2 (Nval n2) ->
      eval_nd (Te_plus t1 t2) (Nval n2).

(* Auxiliary inductive definitions *)
Inductive eval_nd_Const_1 n : val -> Prop :=
  | E_Const_nd_1 : eval_nd_Const_1 n (Nval n).
Inductive eval_nd_Plus_1 t1 t2 : val -> Prop :=
  | E_Plus_nd1_1 : forall n1 n2,
      eval_nd t1 (Nval n1) ->
      eval_nd t2 (Nval n2) ->
      eval_nd_Plus_1 t1 t2 (Nval (n1 + n2))
  | E_Plus_nd2_1 : forall n2,
      Q t1 ->
      eval_nd t2 (Nval n2) ->
      eval_nd_Plus_1 t1 t2 (Nval n2).
Inductive eval_Div0_1_2 (t1 : te) : val -> Prop :=.

Definition eval_nd_1 : te -> val -> Prop :=
  fun t =>
    match t with
    | Te_const n => eval_nd_Const_1 n
    | Te_plus t1 t2 => eval_nd_Plus_1 t1 t2
    | Te_div0 t1 => eval_Div0_1_2 t1
    end.

Definition eval_nd_eval_nd_1 {t v} : eval_nd t v -> eval_nd_1 t v :=
  fun e =>
    match e with
    | E_Const_nd n => E_Const_nd_1 n
    | E_Plus_nd1 t1 t2 n1 n2 e1 e2 => E_Plus_nd1_1 t1 t2 n1 n2 e1 e2
    | E_Plus_nd2 t1 t2 n2 q e2 => E_Plus_nd2_1 t1 t2 n2 q e2
    end.

Inductive eval_nd_Const_Nval_1_2 n : nat -> Prop :=
  | E_Const_nd_Nval_1_2 : eval_nd_Const_Nval_1_2 n n.
Inductive eval_nd_Plus_Nval_1_2 t1 t2 : nat -> Prop :=
  | E_Plus_nd_Nval1_1_2 : forall n1 n2,
      eval_nd t1 (Nval n1) ->
      eval_nd t2 (Nval n2) ->
      eval_nd_Plus_Nval_1_2 t1 t2 (n1 + n2)
  | E_Plus_nd_Nval2_1_2 : forall n2,
      Q t1 ->
      eval_nd t2 (Nval n2) ->
      eval_nd_Plus_Nval_1_2 t1 t2 n2.

Definition eval_nd_1_2 : te -> val -> Prop :=
  fun t v =>
    match t, v with
    | Te_const c, Nval n => eval_nd_Const_Nval_1_2 c n
    | Te_plus t1 t2, Nval n => eval_nd_Plus_Nval_1_2 t1 t2 n
    | _, _ => False
    end.

Definition eval_nd_eval_nd_1_2 {t v} : eval_nd t v -> eval_nd_1_2 t v :=
  fun e =>
    match e with
    | E_Const_nd n => E_Const_nd_Nval_1_2 n
    | E_Plus_nd1 t1 t2 n1 n2 e1 e2 => E_Plus_nd_Nval1_1_2 t1 t2 n1 n2 e1 e2
    | E_Plus_nd2 t1 t2 n2 q e2 => E_Plus_nd_Nval2_1_2 t1 t2 n2 q e2
    end.

Lemma test_ev_nd2:
  forall t, eval_nd (Te_plus (Te_const 0) (Te_const 1)) t-> t = Nval 1.
Proof.
  intros t e.
  destruct (eval_nd_eval_nd_1 e) as [n1 n2 e1 e2 | n2 q e2].
  - destruct (eval_nd_eval_nd_1_2 e1). destruct (eval_nd_eval_nd_1_2 e2). reflexivity.
  - destruct (eval_nd_eval_nd_1_2 e2). reflexivity.
Qed.


Lemma test_ev_nd3:
  forall n, eval_nd (Te_plus (Te_const 0) (Te_const 1)) (Nval n) -> n = 1.
Proof.
  intros n e.
  destruct (eval_nd_eval_nd_1_2 e) as [n1 n2 e1 e2 | n2 q e2].
  - destruct (eval_nd_eval_nd_1_2 e1). destruct (eval_nd_eval_nd_1_2 e2). reflexivity.
  - destruct (eval_nd_eval_nd_1_2 e2). reflexivity.
Qed.

End varQ.
