(* https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/eq_rect_eq.20in.20buchberger.20project *)
From Coq Require Import Arith Relation_Definitions EqdepFacts Eqdep_dec.

Inductive mon : nat -> Set :=
| n_0 : mon 0
| c_n : forall d : nat, nat -> mon d -> mon (S d).


Inductive mdiv : forall d : nat, mon d -> mon d -> Prop :=
| mdiv_nil : mdiv 0 n_0 n_0
| mdiv_cons :
    forall (d : nat) (v v' : mon d) (n n' : nat),
      n <= n' -> mdiv d v v' -> mdiv (S d) (c_n d n v) (c_n d n' v').

Lemma mdiv_inv : forall d x y,
    mdiv d x y <->
    match d return mon d -> mon d -> Prop with
    | 0 => fun x y => n_0 = x /\ n_0 = y
    | S d => fun x y => exists v v' n n', n <= n' /\ mdiv d v v' /\ c_n d n v = x /\ c_n d n' v' = y
    end x y.
Proof.
  intros d x y;split.
  - intros m;destruct m;eauto 8.
  - destruct d;intros m.
    + destruct m as [[] []];constructor.
    + destruct m as [? [? [? [? [? [? [[] []]]]]]]].
      constructor;assumption.
Defined.

Lemma mdiv_trans : forall d : nat, transitive (mon d) (mdiv d).
Proof.
  intros d; elim d; unfold transitive in |- *; auto.
  - intros x y z mxy myz.
    apply mdiv_inv in mxy;apply mdiv_inv in myz.
    apply mdiv_inv.
    intuition.

  - intros n Rec x y z mxy myz.
    apply mdiv_inv in mxy;apply mdiv_inv in myz.
    destruct mxy as [vxy [vxy' [nxy [nxy' [Hnxy [Hdivxy [eq1 eq2]]]]]]].
    destruct myz as [vyz [vyz' [nyz [nyz' [Hnyz [Hdivyz [eq3 eq4]]]]]]].
    destruct eq1,eq2,eq4.
    injection eq3;clear eq3;intros eqv eqn.
    destruct eqn.
    pose proof (eq_sigT_snd eqv) as eqv'.

    rewrite (UIP_refl_nat n _) in eqv'.
    simpl in eqv';destruct eqv';clear eqv.

    apply mdiv_cons.
    * apply le_trans with (m := nyz); assumption.
    * apply Rec with (y := vyz); assumption.
Qed.
