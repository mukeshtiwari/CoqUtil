Definition domain {A B} (f: A -> option B) := fun x => exists y, f x = Some y.

Definition apply_function {A B} {f: A -> option B} {x} (H: domain f x): B.
Proof.
  unfold domain in H. destruct (f x).
  + exact b.
  + abstract (exfalso; destruct H; congruence).
Defined.

Theorem T {A B} {f1 f2: A -> option B}
  (H: forall x, domain f1 x -> domain f2 x -> f1 x = f2 x) :
  forall x (H1: domain f1 x) (H2: domain f2 x), apply_function H1 = apply_function H2.
Proof.
  intros. pose proof (H _ H1 H2). unfold apply_function.
  set (fn :=
         fun (o : option B) (f : A -> option B) (y : A)
             (Ha : f y = o) (Hb : exists t : B, o = Some t) =>
           match o as o' return ((exists yt : B, o' = Some yt) -> B) with
           | Some b =>  fun _ : exists yt : B, Some b = Some yt => b
           | None =>  fun H3 : exists yt : B, None = Some yt =>
                        apply_function_subproof B H3
           end Hb).
  change (match f1 x as o return ((exists y : B, o = Some y) -> B) with
  | Some b => fun _ : exists y : B, Some b = Some y => b
  | None => fun H3 : exists y : B, None = Some y => apply_function_subproof B H3
           end H1) with (fn (f1 x) f1 x eq_refl H1).
  change( match f2 x as o return ((exists y : B, o = Some y) -> B) with
  | Some b => fun _ : exists y : B, Some b = Some y => b
  | None => fun H3 : exists y : B, None = Some y => apply_function_subproof B H3
          end H2) with (fn (f2 x) f2 x eq_refl H2).
  enough (forall oa ob fa fb ya yb Ha Hb Hc Hd,
             oa = ob -> ya = yb ->              
             fn oa fa ya Ha Hb = fn ob fb yb Hc Hd).
  +
    eapply H3. assumption.
    exact eq_refl.
  +
    intros *.
    destruct oa, ob;
      intros * He Hf;
      inversion He; try congruence.
    ++
      simpl; auto.
    ++
      simpl.
      destruct Hb;
      congruence.
Qed.

