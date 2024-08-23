Require Import Lia
  Coq.Bool.Bool
  Coq.Init.Byte
  Coq.NArith.NArith
  Coq.Strings.Byte
  Coq.ZArith.ZArith
  Coq.Lists.List.

Open Scope N_scope.

(* a more complicated definition, for no reason, that I wrote before the simple one *)
Definition np_total (np : N):  (np <? 256 = true) ->  byte.
Proof.
  intros H.
  refine(match (np <? 256) as b return forall mp, np = mp ->
      (mp <? 256) = b -> _ with
   | true => fun mp Hmp Hmpt =>
      match of_N mp as npt return _ = npt -> _ with
      | Some x => fun _ => x
      | None => fun Hf => _
      end eq_refl
   | false => fun mp Hmp Hmf => _
  end np eq_refl eq_refl).
  abstract(
  apply of_N_None_iff in Hf;
  apply N.ltb_lt in Hmpt; nia).
  abstract (subst; congruence).
Defined.



(* Now I am trying to prove the same theorem again *)
Lemma np_true : forall np (Ha : np <? 256 = true) x,
  of_N np = Some x -> np_total np Ha = x.
Proof.
  intros * Hb; unfold np_total.
  Fail destruct (np <? 256).
  pose (fn := fun (b : bool) (npw : N) (Hw : (npw <? 256) = b)
              (f : forall mp : N, npw = mp -> (mp <? 256) = false -> byte) =>
          ((if b as b' return (forall mp : N, npw = mp -> (mp <? 256) = b' -> byte)
            then
              (fun
                  (mp : N) (Hmp : npw = mp) (Hmpt : (mp <? 256) = true) =>
                  match of_N mp as npt return (of_N mp = npt -> byte) with
                  | Some x0 => fun _ : of_N mp = Some x0 => x0
                  | None => fun Hf : of_N mp = None =>
                              (fun
                                  (npwf mpf : N) (Hmpf : npwf = mpf)
                                  (Hmptf : (mpf <? 256) = true)
                                  (Hff : of_N mpf = None) =>
                                  np_total_subproof npwf mpf Hmpf Hmptf Hff)
                                npw mp Hmp Hmpt Hf
                  end eq_refl) 
            else
              (fun (mp : N) (Hmp : npw = mp) (Hmf : (mp <? 256) = false) =>
                 f mp Hmp Hmf))
             npw eq_refl Hw)).
  enough (forall b npw H f, b = true -> npw = np -> fn b npw H f = x) as Hc.
  +
    eapply Hc.
    exact Ha. exact eq_refl.
  +
    intros * Hc Hd.
    destruct b; try congruence; subst; simpl.
    (* one more generalization *)
    clear fn f Hc Ha.
    Fail destruct (of_N np).
    Check np_total_subproof.
    set (fn := (fun (npw : N) (Hc : (npw <? 256) = true)
                   (o : option byte) (Ha : of_N npw = o)  =>
                 match o as o' return of_N npw = o' -> byte
                 with
                 | Some x => fun _ : of_N npw = Some x => x
                 | None => fun Hf : of_N npw = None =>
                             np_total_subproof npw npw eq_refl Hc Hf
                 end Ha) np H).
    enough (forall o Hc, o = Some x -> fn o Hc = x) as Hd.
    ++
      eapply Hd.
      exact Hb.
    ++
      intros * Hc.
      destruct o as [y | ].
      +++
        simpl; inversion Hc; auto.
      +++
        congruence.
Qed.
