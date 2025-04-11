From Coq Require Export RelationClasses Morphisms Setoid.

Class Model :=
  {
    worlds : Type;
    worlds_eq : relation worlds;
    worlds_eq_equiv :: Equivalence worlds_eq;
  }.

Record state `{Model} :=
  {
    state_fun : worlds -> bool;
    state_proper :: Proper (worlds_eq ==> eq) state_fun
  }.

Coercion state_fun : state >-> Funclass. (* Improve readability *)

Context `{Model}.
Context (s : state).

Program Definition restricted_Model `{Model} : Model :=
  {|
    worlds := {w : worlds | s w = true};
    worlds_eq w1 w2 := worlds_eq (proj1_sig w1) (proj1_sig w2)
  |}.

Next Obligation.
  split.
  -
    intros []; easy.
  -
    intros [] []; easy.
  -
    intros [] [] [] H1 H2;
    rewrite H1;
    exact H2.
Defined.

Program Definition restricted_state (t : state) : @state restricted_Model :=
  {|
    state_fun w := t (proj1_sig w)
  |}.

Next Obligation.
  intros [] [] H3.
  rewrite H3.
  reflexivity.
Defined.

(* 
Theorem gen_goal :
  forall (t : state) (w1 w2 : worlds) (sw1 sw2 : bool) (Ha : sw1 = s w1) (Hb : sw2 = s w2),
    (if sw1 as anonymous' return (anonymous' = s w1 -> bool)
     then fun Heq_anonymous : true = s w1 => t (exist (fun w : worlds => s w = true) w1 (eq_sym Heq_anonymous))
     else fun _ : false = s w1 => false) Ha =
      (if sw2 as anonymous' return (anonymous' = s w2 -> bool)
       then fun Heq_anonymous : true = s w2 => t (exist (fun w : worlds => s w = true) w2 (eq_sym Heq_anonymous))
       else fun _ : false = s w2 => false) Hb.

*)
Program Definition unrestricted_state (t : @state restricted_Model) : state :=
  {|
    state_fun w :=
      match s w with
      | true => t (exist _ w _)
      | false => false
      end
  |}.
Next Obligation.
  intros w1 w2 H1.
  unfold unrestricted_state_obligation_1.
  pose proof (state_proper s w1 w2 H1) as Hproper.
  set (f := fun w (x : bool) =>
              (if x as an' return (an' = s w -> bool)
               then (fun Heqa => t (exist _ w (eq_sym Heqa))) else fun x => false)).
  Check f.
  enough (forall sw1 He1 sw2 He2, f w1 sw1 He1 = f w2 sw2 He2) as HH.
  1: eapply HH.
  intros *.
  destruct sw1, sw2; try congruence.
  +
    simpl.
    apply state_proper.
    simpl.
    exact H1.
  +
    simpl. exact eq_refl.
Defined.

(* another proof by generalisation *)
Program Definition unrestricted_state (t : @state restricted_Model) : state :=
  {|
    state_fun w :=
      match s w with
      | true => t (exist _ w _)
      | false => false
      end
  |}.
Next Obligation.
  intros w1 w2 H1.
  unfold unrestricted_state_obligation_1.
  pose proof (state_proper s w1 w2 H1) as Hproper.
  generalize (eq_refl (s w1)) as ha.
  generalize (s w1) at 1 3.
  destruct b; intros; simpl.
  generalize (eq_refl (s w2)) as hb.
  generalize (s w2) at 1 3.
  destruct b; intros.
  eapply state_proper; simpl.
  exact H1.
  congruence.
  generalize (eq_refl (s w2)) as hb.
  generalize (s w2) at 1 3.
  destruct b; intros.
  congruence.
  reflexivity.
Qed.
