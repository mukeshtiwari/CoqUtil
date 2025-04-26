
  Definition someListProp (l : list nat) : Prop:=
        match nth_error l 10  with
        | Some _ => True
        | _ => False
        end.
    
    Record DepRec := {
        l : list nat ;
        P : someListProp l
    }.
    
Lemma some_DepRec_lemma (r : DepRec) (f : DepRec -> Prop) : f r.
Proof.
  destruct r as [r ha].
  unfold someListProp in *.
  set (fn := fun (o : option nat) =>
    match o with 
    | Some _ => True
    | None => False
  end).
  generalize (eq_refl (nth_error r 10)).
  generalize (nth_error r 10) at 2.
  intros * hb.
  set(hc := (eq_rect _ fn ha _ hb)).
  replace ha with (eq_rect_r fn hc hb) by apply rew_opp_l.
  clearbody hc.
  rewrite hb in ha.
  destruct o.
