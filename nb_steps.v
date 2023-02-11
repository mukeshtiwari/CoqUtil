(**************************************************************)
(*   Copyright                                                *)
(*             Jean-FranÃ§ois Monin           [+]              *)
(*             Dominique Larchey-Wendling    [*]              *)
(*                                                            *)
(*            [+] Affiliation VERIMAG - Univ. Grenoble-Alpes  *)
(*            [*] Affiliation LORIA -- CNRS                   *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)
(* https://www-verimag.imag.fr/~monin/Proof/Small_inversions/2021/nb_steps.v *)

Require Import Utf8 Extraction.

(* Target : nb of g steps to get some condition b
      let rec  ns x = match b x with true => 0 | false => S (ns (g x))
   Easy case: b corresponds to a constructor, say O in nat
      let  rec ns0 x = match x with O => 0 | S _ => S (ns0 (g x))
   Algorithm using an accumulator
    let rec nsa x n = match b x with true => n | false => nsa (g x) (S n)
    let rec ns0a x n = match x with O => n | S _ => ns0a (g x) (S n)
   We prove that ns0/ns computes the same result as ns0a/nsa
*)

Section sec_nb_steps.

Variable (X : Type) (g : X -> X) (b : X -> bool).

Let is_false (x: bool) := match x with false => True | _ => False end.

Unset Elimination Schemes.

Inductive ð”»ns (x: X) : Prop :=
  | ð”»ns_tr : b x = true â†’ ð”»ns x
  | ð”»ns_fa : b x = false â†’ ð”»ns (g x) â†’ ð”»ns x
.

Scheme ð”»ns_ind := Induction for ð”»ns Sort Prop.
Check ð”»ns_ind.
(*
âˆ€ P : âˆ€ x : X, ð”»ns x â†’ Prop,
      (âˆ€ (x : X) (e : b x = true), P x (ð”»ns_tr x e))
    â†’ (âˆ€ (x : X) (e : b x = false) (ð”» : ð”»ns (g x)), P (g x) ð”» â†’ P x (ð”»ns_fa x e ð”»))
    â†’ âˆ€ (x : X) (ð”» : ð”»ns x), P x ð”»
 *)


(* prj_ð”»ns a little bit more complicated *)

Let false_true {x} : x = false -> x = true -> False.
Proof. intros ->; discriminate. Qed.

Print false_true.

Definition prj_ð”»ns {x} (E: b x = false) (D :  ð”»ns x) :  ð”»ns (g x) :=
  match D with
  | ð”»ns_tr _ E'   => match false_true E E' with end
  | ð”»ns_fa _ _ D  => D
  end.

Section sec_direct_ns.
(* "Let" in order to forget ns and nsa after this section *)  
Let
Fixpoint ns x (D: ð”»ns x) : nat :=
  match b x as bx return b x = bx â†’ _ with
  | true => Î» E, 0
  | false => Î» E, S (ns (g x) (prj_ð”»ns E D))
  end eq_refl.

Let
Fixpoint nsa x (n: nat) (D: ð”»ns x) : nat :=
  match b x as bx return b x = bx â†’ _ with
  | true => Î» E, n
  | false => Î» E, nsa (g x) (S n) (prj_ð”»ns E D)
  end eq_refl.

Lemma ns_nsa_n_direct : âˆ€x (D: ð”»ns x) n, nsa x n D = ns x D + n.
Proof.
 induction D as [x E | x E D IHD]; intro n; simpl.
  - rewrite E. reflexivity.
  - rewrite IHD. rewrite E. rewrite <- plus_n_Sm. reflexivity.
Qed.

Corollary ns_nsa_direct : âˆ€x (D: ð”»ns x), nsa x 0 D = ns x D.
Proof. intros x D. now rewrite ns_nsa_n_direct, plus_n_O. Qed.

End sec_direct_ns.

Set Elimination Schemes.

(* ---------------------------------------------------------------------- *)

Reserved Notation "x 'âŸ¼ns' y" (at level 70, no associativity).
Inductive ð”¾ns (x: X) : nat â†’ Prop :=
  | in_grns_0   : b x = true  â†’  x âŸ¼ns 0
  | in_grns_1 o : b x = false â†’  g x âŸ¼ns o  â†’  x âŸ¼ns S o
where "x âŸ¼ns o" := (ð”¾ns x o).

Reserved Notation "x ',' n 'âŸ¼nsa' y" (at level 70, no associativity).
Inductive ð”¾nsa (x: X) (n: nat) : nat â†’ Prop :=
  | in_grnsa_0   : b x = true  â†’  x, n âŸ¼nsa n
  | in_grnsa_1 o : b x = false â†’  g x, S n âŸ¼nsa o  â†’  x, n âŸ¼nsa o
where "x , n âŸ¼nsa o" := (ð”¾nsa x n o).

Fact ð”¾ns_fun x u v : x âŸ¼ns u  â†’  x âŸ¼ns v  â†’  u = v.
Proof.
  intros H; revert H v.
  induction 1 as [ x E | x o E H1 IH1 ]; inversion 1; auto.
  - rewrite E in H0. discriminate H0.
  - rewrite E in H0. discriminate H0.
Qed.

Fact ð”¾nsa_fun x n u v : x, n âŸ¼nsa u  â†’  x, n âŸ¼nsa v  â†’  u = v.
Proof.
  intros H; revert H v.
  induction 1 as [ x n E | x n o E H1 IH1 ]; inversion 1; auto.
  - rewrite E in H0. discriminate H0.
  - rewrite E in H0. discriminate H0.
Qed.


Let Fixpoint ns_pwc x (D: ð”»ns x) : {o | x âŸ¼ns o}.
Proof. refine(
   match b x as bx return b x = bx â†’ _ with
   | true => Î» E, exist _ 0 _
   | false => Î» E, let (o,Go) := ns_pwc (g x) (prj_ð”»ns E D)
                   in exist _ (S o) _
   end eq_refl).
  - constructor 1; exact E.
  - constructor 2; assumption.
Defined.

Let Fixpoint nsa_pwc x n (D: ð”»ns x) : {o | x, n âŸ¼nsa o}.
Proof. refine(
   match b x as bx return b x = bx â†’ _ with
   | true => Î» E, exist _ n _
   | false => Î» E, let (o,Go) := nsa_pwc (g x) (S n) (prj_ð”»ns E D)
                   in exist _ o _
   end eq_refl).
  - constructor 1; exact E.
  - constructor 2; assumption.
Defined.

Definition ns (x: X) D : nat := proj1_sig (ns_pwc x D).

(* ns is correct wrt its agnostic specification *)
Fact ns_correct {x} D : x âŸ¼ns ns x D.
Proof. apply (proj2_sig _). Qed.

(* ns is complete wrt its agnostic specification *)
Lemma ns_complete {x o} : x âŸ¼ns o  ->  âˆ€D, o = ns x D.
Proof.
  intros G D.
  assert (G': x âŸ¼ns ns x D) by (apply (ns_correct D)).
  apply (ð”¾ns_fun x); assumption.
Qed.

Definition nsa (x: X) (n: nat) D : nat := proj1_sig (nsa_pwc x n D).

(* nsa is correct wrt its agnostic specification *)
Fact nsa_correct {x n} D : x, n âŸ¼nsa nsa x n D.
Proof. apply (proj2_sig _). Qed.

(* nsa is complete wrt its agnostic specification *)
Lemma nsa_complete {x n o} : x,n âŸ¼nsa o  ->  âˆ€D, o = nsa x n D.
Proof.
  intros G D.
  assert (G': x,n âŸ¼nsa nsa x n D) by (apply (nsa_correct D)).
  apply (ð”¾nsa_fun x n); assumption.
Qed.

(* The specification of ns satifies the specification of nsa in some sense *)
Lemma gr_ns_nsa_n : âˆ€{x o}, x âŸ¼ns o  ->  âˆ€n, x, n âŸ¼nsa (o + n).
Proof.
  intros x o G. induction G as [ x E | x o E G IH]; intro n.
  - constructor 1. exact E.
  - constructor 2.
    + exact E.
    + change (S o + n) with (S (o + n)). rewrite plus_n_Sm. apply (IH (S n)).
Qed.

Corollary gr_ns_nsa : âˆ€{x o}, x âŸ¼ns o  ->  x, 0 âŸ¼nsa o.
Proof. intros x o G. rewrite plus_n_O. apply gr_ns_nsa_n, G. Qed.

(* The desired theorem follows *)
Theorem ns_nsa : âˆ€x (D: ð”»ns x), nsa x 0 D = ns x D.
Proof.
  intros x D.
  rewrite <- (nsa_complete (gr_ns_nsa (ns_correct D))).
  reflexivity.
Qed.

End sec_nb_steps.


Extract Inductive bool => "bool" [ "true" "false" ].
Recursive Extraction ns nsa.

(*
let rec ns g b x =
  if b x then O else S (ns g b (g x))

let rec nsa g b x n =
  if b x then n else nsa g b (g x) (S n)
*)

