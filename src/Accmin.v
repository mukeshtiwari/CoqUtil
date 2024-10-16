(* Written by Dominique Larchey-Wendling on Zulip *)


Require Import Arith Lia Extraction.

Section minimize.

  Variables (P : nat -> Prop).

  Let R x y := x = S y /\ ~ P y.

  Fact Acc_not n : P n -> Acc R n.
  Proof. constructor; now intros ? []. Qed.

  Hint Resolve Acc_not : core.

  Fact P_Acc_plus n i : P (i+n) -> Acc R n.
  Proof.
    induction i as [ | i IH ] in n |- *; intros Hn; auto.
    constructor; intros ? (-> & ?).
    apply IH.
    now replace (i+S n) with (S i+n) by lia.
  Qed.

  Lemma P_above_Acc n : (exists m, n <= m /\ P m) -> Acc R n.
  Proof.
    intros (m & H1 & H2).
    apply P_Acc_plus with (i := m-n).
    now replace (m-n+n) with m by lia.
  Qed.

  Variables P_dec : forall n, { P n } + { ~ P n }.

  Definition Acc_least : forall n, Acc R n -> { m | n <= m /\ P m /\ forall k, P k -> k < n \/ m <= k }.
  Proof.
    refine (fix loop n hn { struct hn } :=
      match P_dec n with
      | left H  => exist _ n _
      | right H => let (m,hm) := loop (S n) (Acc_inv hn _) in exist _ m _
      end).
    + repeat split; auto; lia.
    + now split.
    + destruct hm as (? & ? & ?).
      repeat split; (lia || auto).
      intros k Hk.
      destruct (H2 _ Hk) as [ ?%le_S_n | ]; auto.
      destruct (eq_nat_dec k n) as [ -> | ]; lia || easy.
  Qed.

  Definition minimize n : (exists m, n <= m /\ P m) -> { m | n <= m /\ P m /\ forall k, P k -> k < n \/ m <= k }.
  Proof. intros H; apply Acc_least, P_above_Acc, H. Defined.

End minimize.

Extraction Inline Acc_least.

Recursive Extraction minimize.
