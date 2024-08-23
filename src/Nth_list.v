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

(* using refine *)

(*

  Definition nth_safe {A : Type}
  (l : list A) (n : nat) (Ha : (n < length l)) : A.
Proof.
  refine
    (match (nth_error l n) as nth return (nth_error l n) = nth -> A with
     | Some res => fun Hb => res
     | None => fun Hb => _ 
     end eq_refl).
  eapply  nth_error_None in Hb;
    abstract nia.
Defined.

(*
Next Obligation.
  symmetry in Heq_anonymous. apply nth_error_None in Heq_anonymous. lia.
Defined.
*)

Lemma nth_safe_nth: forall
    {A : Type} (l : list A) (n : nat) d
    (Ha : (n < length l)), nth_safe l n Ha = nth n l d.  
Proof.
  intros *. unfold nth_safe.
  pose (fn := (fun (la : list A) (na : nat) (Hb : na < length la)
                  (o : option A) (Hc : nth_error la na = o) =>
                 match o as nth return nth_error la na = nth -> A with
                 | Some res => fun _ : nth_error la na = Some res => res
                 | None => fun Hbt : nth_error la na = None =>
                             nth_safe_subproof A la na Hb
                               (match nth_error_None la na with
                                | conj H _ => H
                                end Hbt)
                 end Hc) l n Ha).
  enough (forall (o : option A) Ht, fn o Ht = nth n l d) as Htt.
  +
    eapply Htt.
  +
    intros *.
    destruct o as [x |]. 
    ++
      simpl. eapply eq_sym, nth_error_nth.
      exact Ht.
    ++
      pose proof (proj1(nth_error_None l n) Ht).
      nia.
Qed.      

*)
