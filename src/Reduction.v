
Inductive formula {atom : Type} : Type :=
| f_atom : atom -> formula
| f_not  : formula -> formula
| f_conj  : formula -> formula -> formula
| f_disj  : formula -> formula -> formula
| f_imp  : formula -> formula -> formula
| f_box  : formula -> formula
| f_diamond  : formula -> formula.

(* Kripke model *)
Record Model {atom : Type} :=
{
  worlds : Type;
  accessible : worlds -> worlds -> Prop;
  valuation : worlds -> atom -> Prop;
}.


Inductive atom : Type :=
| P : atom
| Q : atom.

Inductive worlds3 : Type :=
| Γ : worlds3
| Δ : worlds3
| Ω : worlds3.

Definition R3 (w1 w2 : worlds3) : Prop :=
  match w1, w2 with
  | Γ, Δ  => True
  | Γ, Ω => True
  | _, _ => False
  end.

Definition V3 (w : worlds3) (a : atom) : Prop :=
  match w, a with
  | Δ, P => True
  | Ω, Q => True
  | _, _ => False
  end.

Definition M1 : Model :=
  {|
    worlds := worlds3;
    accessible := R3;
    valuation := V3
  |}.

Fixpoint satisfies {atom : Set} (M : @Model atom) (w0 : worlds M) (f : @formula atom) : Prop :=
  match f with
  | f_atom p => valuation M w0 p
  | f_not f' => ~(satisfies M w0 f')
  | f_conj f1 f2 => (satisfies M w0 f1) /\ (satisfies M w0 f2)
  | f_disj f1 f2 => (satisfies M w0 f1) \/ (satisfies M w0 f2)
  | f_imp f1 f2 => (satisfies M w0 f1) -> (satisfies M w0 f2)
  | f_box f' => forall w, (accessible M w0 w) -> (satisfies M w f')
  | f_diamond f' => exists w, (accessible M w0 w) /\ (satisfies M w f')
  end.

Proposition Delta_P_or_Q : satisfies M1 Δ (f_disj (f_atom P) (f_atom Q)).
Proof.
  cbn; left; exact I.
Qed.

Proposition Omega_P_or_Q : satisfies M1 Ω (f_disj (f_atom P) (f_atom Q)).
Proof.
  cbn; right; exact I.
Qed.

Proposition Omega_box_P_or_Q : satisfies M1 Γ (f_box (f_disj (f_atom P) (f_atom Q))).
Proof.
  (* Relevant Reductions: *)
  cbv delta [satisfies].
  cbv fix.
  cbv beta.
  cbv match.
  fold @satisfies.
  (* Goal at this point:
  "forall w : worlds M1, accessible M1 Γ w -> satisfies M1 w (f_disj (f_atom P) (f_atom Q))"
  *)
  (* same as previous proof for rest *)
  intros w H.
  destruct w ; simpl in H.
 - destruct H.
 - apply Delta_P_or_Q.
 - apply Omega_P_or_Q.
Qed.
