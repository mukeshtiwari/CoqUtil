Require Import Init.Specif Logic.PropExtensionality.

Lemma sig_proj1_inverse (A: Type) (P: A -> Prop) (x: A) (proof: P x) :
  proj1_sig (exist P x proof) = x.
Proof.
  reflexivity.
Qed.

Lemma proj1_sig_injective {A: Type} {P: A-> Prop} (x y: @sig A P) :
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x. destruct y.
  repeat rewrite sig_proj1_inverse.
  intro Ha.
  (* we generalise the goal *)
  set (fn := fun (u : A) pa => exist P u pa).
  enough (forall u v pa pb,  u = v -> fn u pa = fn v pb) as Hb.
  eapply Hb; exact Ha.
  intros * Hb.
  Fail eapply f_equal. (* still fails *)
  subst; unfold fn.
  eapply f_equal.
  (* now proof *)
  eapply proof_irrelevance.
Qed.
