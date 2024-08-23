From Coq Require Import
  Program.Tactics
  List Psatz.


Program Definition nth_safe {A} (l: list A) (n: nat) (IN: (n < length l)%nat) : A :=
  match (nth_error l n) with
    | Some res => res
    | None => _
  end.
Next Obligation.
  symmetry in Heq_anonymous. apply nth_error_None in Heq_anonymous. lia.
Defined.


Lemma nth_safe_nth: forall
    {A : Type} (l : list A) (n : nat) d
    (Ha : (n < length l)), nth_safe l n Ha = nth n l d.  
Proof.
  intros *.
  unfold nth_safe.
  pose (fn := (fun (la : list A) (na : nat) (Hb : na < length la)
                  (o : option A) (Hc : o = nth_error la na) =>
                match o as o' return o' = nth_error la na -> A with
                | Some res => fun _ : Some res = nth_error la na => res
                | None => fun Heq : None = nth_error la na =>
                            nth_safe_obligation_1 A la na Hb Heq
                end Hc) l n Ha).
  enough (forall (o : option A) (Ht : o = nth_error l n), fn o Ht = nth n l d) as Htt.
  +
    eapply Htt.
  +
    intros *.
    destruct o as [x |]. 
    ++
      simpl.
      eapply eq_sym, nth_error_nth; auto.
    ++
      pose proof (proj1(nth_error_None l n) (eq_sym Ht)).
      nia.
Qed.
