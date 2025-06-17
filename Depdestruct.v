Lemma invert_eq_rect {A} {x y} (P : A -> Type) (hb : x = y) (ha : P x) :
  let hc := eq_rect x P ha y hb in
  ha = eq_rect_r P hc hb.
Proof.
  destruct hb; simpl. 
  unfold eq_rect_r; simpl.
  reflexivity.
Defined.


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


(* another one *)

 Lemma some_DepRec_lemma (r : DepRec) (f : DepRec -> Prop) : f r.
Proof.
  destruct r as [r ha].
  unfold someListProp in *.
  generalize (eq_refl (nth_error r 10)).
  generalize (nth_error r 10) at 2.
  intros * hb.
  set (fn := fun (o : option nat) =>
    match o with 
    | Some _ => True
    | None => False
  end).
  set(hc := (eq_rect _ fn ha _ hb)).
  assert (hd : ha = eq_rect o fn hc (nth_error r 10) (eq_sym hb)).
  subst hc. rewrite rew_compose, eq_trans_sym_inv_r.
  cbn; reflexivity. rewrite hd. clear hd.
  clearbody hc. 
  rewrite hb in ha.
  destruct o.
