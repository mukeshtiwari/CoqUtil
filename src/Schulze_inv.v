From Coq Require Import ZArith List Utf8.
Import ListNotations.
Open Scope Z.


Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
    format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.


Section Schulze.

  Variable (cand : Type)
  (marg : cand -> cand -> Z)
  (cand_all : list cand)
  (cand_fin : forall c: cand, In c cand_all)
  (dec_cand : forall n m : cand, {n = m} + {n <> m})
  (cand_not_nil : cand_all <> []).

  (* prop-level path *)
  Inductive Path (k : Z) : cand -> cand -> Prop :=
  | unit c d : marg c d >= k -> Path k c d
  | cons c d e : marg c d >= k -> Path k d e -> Path k c e.

  (* winning condition of Schulze Voting *)
  Definition wins_prop (c: cand) := forall d: cand, exists k: Z,
    Path k c d /\ (forall l, Path l d c -> l <= k).

  (* dually, the notion of not winning: *)
  Definition loses_prop (c : cand) := exists k: Z, exists  d: cand,
    Path k d c /\ (forall l, Path l c d -> l < k).

  (** Section 3: A Scrutiny Sheet for the Schulze Method **)

  (* boolean function that determines whether the margin between a
    pair  of candidates is below a given integer *)
  Definition marg_lt (k : Z) (p : (cand * cand)) :=
    Zlt_bool (marg (fst p) (snd p)) k.

  (* definition of the (monotone) operator W_k that defines coclosed sets *)
  Definition W (k : Z) (p : cand * cand -> bool) (x : cand * cand) :=
    andb (marg_lt k x)
    (forallb (fun m => orb (marg_lt k (fst x, m)) (p (m, snd x))) cand_all).

  (* k-coclosed predicates *)
  Definition coclosed (k : Z) (p : (cand * cand) -> bool) :=
    forall x, p x = true -> W k p x = true.

  (* type-level path to replace prop-level path *)
  Inductive PathT (k: Z) : cand -> cand -> Type :=
  | unitT c d : marg c d >= k -> PathT k c d
  | consT c d e : marg c d >= k -> PathT k d e -> PathT k c e.

  (* type-level winning condition in Schulze counting *)
  Definition wins_type c :=
    forall d : cand, existsT (k : Z),
    ((PathT k c d) * (existsT (f : (cand * cand) -> bool), 
      f (d, c) = true /\ coclosed (k + 1) f))%type.

  (* dually, the type-level condition for non-winners *)
  Definition loses_type (c : cand) :=
    existsT (k : Z) (d : cand), ((PathT k d c) *
      (existsT (f : (cand * cand) -> bool), f (c, d) = true /\ coclosed k f))%type.


  Definition ballot := cand -> nat.

  Inductive State: Type :=
  | partial: (list ballot * list ballot)  -> (cand -> cand -> Z) -> State
  | winners: (cand -> bool) -> State.


  Inductive Count (bs : list ballot) : State -> Type :=
  | ax us (m : cand -> cand -> Z) : us = bs -> (forall c d, m c d = 0%Z) ->
      Count bs (partial (us, []) m)             (* zero margin      *)
  | cvalid u us m nm inbs : Count bs (partial (u :: us, inbs) m) ->
      (forall c, (u c > 0)%nat) ->              (* u is valid       *)
      (forall c d : cand,
        ((u c < u d)%nat -> nm c d = m c d + 1) (* c preferred to d *) /\
        ((u c = u d)%nat -> nm c d = m c d)     (* c, d rank equal  *) /\
        ((u c > u d)%nat -> nm c d = m c d - 1))(* d preferred to c *) ->
      Count bs (partial (us, inbs) nm)
  | cinvalid u us m inbs : Count bs (partial (u :: us, inbs) m) ->
      (exists c, (u c = 0)%nat)                 (* u is invalid     *) ->
      Count bs (partial (us, u :: inbs) m)
  | fin m inbs w 
      (d : (forall c, (wins_type c) + (loses_type c))):
      Count bs (partial ([], inbs) m)           (* no ballots left  *) ->
      (forall c, w c = true  <-> (exists x, d c = inl x)) ->
      (forall c, w c = false <-> (exists x, d c = inr x)) ->
      Count bs (winners w).

  

  Inductive count_shape_partial_0 
    {bs us m} : Count bs (partial (us, []) m)  -> Prop :=
  | ax_S pa pb  : count_shape_partial_0 (ax bs us m pb pa).

  Inductive count_shape_partial_1 
    {bs us inbs nm} : Count bs (partial (us, inbs) nm) -> Prop := 
  | cvalid_S u m (e : Count bs (partial (u :: us, inbs) m))
    (pa : (∀ c : cand, (u c > 0)%nat)) 
    (pb : (∀ c d : cand,
      ((u c < u d)%nat → nm c d = m c d + 1)
    ∧ (u c = u d → nm c d = m c d)
    ∧ ((u c > u d)%nat → nm c d = m c d - 1))) : 
    count_shape_partial_1 (cvalid bs u us m nm inbs e pa pb).

  Inductive count_shape_partial_2 
    {bs us u inbs m} : Count bs (partial (us, u :: inbs) m) -> Prop := 
  | cinvalid_S (e : Count bs (partial (u :: us, inbs) m)) 
    (pa : (∃ c : cand, u c = 0%nat)) : 
    count_shape_partial_2 (cinvalid bs u us m inbs e pa).

  Inductive count_shape_winner 
    {bs w} :  Count bs (winners w) -> Prop :=
  | fin_S m inbs (d : (forall c, (wins_type c) + (loses_type c))) 
    (e : Count bs (partial ([], inbs) m)) 
    (pa : (forall c, w c = true  <-> (exists x, d c = inl x)))
    (pb : (forall c, w c = false <-> (exists x, d c = inr x))) :
    count_shape_winner (fin bs m inbs w d e pa pb).

  Local Open Scope nat_scope.

  Definition forall_exists_fin_dec : forall (A : Type) (l : list A) (f : A -> nat),
    {forall x, In x l -> f x > 0} + {exists x, In x l /\ f x = 0} := 
    fun (A : Type) =>
      fix F l f {struct l} :=
      match l with
      | [] => left (fun (x : A) (H : In x []) => match H with end)
      | h :: t =>
        match Nat.eq_dec (f h) 0 with
        | left e =>
          right (ex_intro _  h (conj (in_eq h t) e))
        | right n =>
          match F t f with
          | left Fl =>
            left (fun x H =>
                    match H with
                    | or_introl H1 =>
                      match zerop (f x) with
                      | left e =>
                        False_ind (f x > 0) ((eq_ind h (fun v : A => f v <> 0) n x H1) e)
                      | right r => r
                      end
                    | or_intror H2 => Fl x H2
                    end)
          | right Fr =>
            right
              match Fr with
              | ex_intro _ x (conj Frl Frr) =>
                ex_intro _ x (conj (in_cons h x t Frl) Frr)
              end
          end
        end
      end.

    Definition ballot_valid_dec : forall b : ballot, 
      {forall c, b c > 0} + {exists c, b c = 0} :=
      fun b => let H := forall_exists_fin_dec cand cand_all in
        match H b with
        | left Lforall =>
          left (fun c : cand => Lforall c (cand_fin c))
        | right Lexists => 
            right
              match Lexists with
              | ex_intro _ x (conj _ L) =>
                ex_intro (fun c : cand => b c = 0) x L
              end
        end.

  Local Open Scope Z_scope.
  Definition update_marg (p : ballot) (m : cand -> cand -> Z) : cand -> cand -> Z :=
    fun c d => 
      if (Nat.ltb (p c) (p d))%nat
      then (m c d + 1)%Z
      else 
        (if (Nat.ltb (p d) (p c))%nat
        then (m c d -1)%Z
        else m c d).

  Definition count_invert {bs : list ballot} {st : State} : Count bs st -> Prop.
  Proof.
    refine 
    match st with 
    | partial (us, inbs) m =>
      match us as ush return us = ush -> _ with 
      | [] => fun ha => 
        match inbs with
        | [] => @count_shape_partial_0 bs us m 
        | _ => fun _ => False
        end  
      | ush :: ust => fun ha => _ 
      end eq_refl
    | winners w => @count_shape_winner bs w
    end.
    +
      rewrite ha.
  Admitted.
