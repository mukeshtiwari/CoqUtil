From Stdlib Require Import ZArith List Utf8.
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

  Inductive state: Type :=
  | partial: (list ballot * list ballot)  -> (cand -> cand -> Z) -> state
  | winners: (cand -> bool) -> state.


  Inductive Count (bs : list ballot) : state -> Type :=
  | ax us (m : cand -> cand -> Z) : us = bs -> (forall c d, m c d = 0%Z) ->
      Count bs (partial (us, []) m)             (* zero margin      *)
  | cvalid u us m nm inbs : Count bs (partial (u :: us, inbs) m) ->
      (forall c, (0 < u c)%nat) ->              (* u is valid       *)
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



  Theorem count_inv_destruct : ∀ (bs : list ballot) (s : state) (e : Count bs s), 
    match s as s' in state return Count _ s' -> Prop
    with 
    | partial (us, inbs) m => 
      match inbs as inbs' return (Count _ (partial (us, inbs') m) -> Prop)
      with 
      | [] => fun (ea : Count bs (partial (us, []) m)) => 
          (∃ (hu : us = bs)  (hv : ∀ c d : cand, m c d = 0),  ea = ax _ us m hu hv) ∨
          (∃ u m' hu hv hw, ea = cvalid _ u us m' m [] hu hv hw)
      | inbsh :: inbst => fun (ea : Count bs (partial (us, inbsh :: inbst) m)) => 
        (∃ u m' ha hb hc, ea = cvalid _ u us m' m (inbsh :: inbst) ha hb hc) ∨ 
        (∃ (ha : Count bs (partial (inbsh :: us, inbst) m)) (hb : exists c, (inbsh c = 0)%nat),
          ea = cinvalid _ inbsh us m inbst ha hb)
      end
    | winners f => fun ea => ∃ m inbs d ha hb hc, ea = fin _ m inbs f d ha hb hc
    end e.
  Proof.
    intros *.
    destruct e as [us m ha hb | u us n nm inbs ha hb hc | u us m inbs ha | m inbs w d ha hb hc].
    +
      left; repeat eexists.
    +
      destruct inbs as [| inbsh inbst].
      ++
        right; repeat eexists.
      ++
        left; repeat eexists.
    +
      right; repeat eexists.
    +
      repeat eexists.
  Defined.

  Theorem count_inv_convoy : ∀ (bs : list ballot) (s : state) (e : Count bs s), 
    match s as s' in state return Count _ s' -> Prop
    with 
    | partial (us, inbs) m => 
      match inbs as inbs' return (Count _ (partial (us, inbs') m) -> Prop)
      with 
      | [] => fun (ea : Count bs (partial (us, []) m)) => 
          ((∃ (hu : us = bs)  (hv : ∀ c d : cand, m c d = 0),  ea = ax _ us m hu hv) ∨
          (∃ u m' hu hv hw, ea = cvalid _ u us m' m [] hu hv hw))%type
      | inbsh :: inbst => fun (ea : Count bs (partial (us, inbsh :: inbst) m)) => 
        ((∃ u m' ha hb hc, ea = cvalid _ u us m' m (inbsh :: inbst) ha hb hc) ∨ 
        (∃ (ha : Count bs (partial (inbsh :: us, inbst) m)) (hb : exists c, (inbsh c = 0)%nat),
          ea = cinvalid _ inbsh us m inbst ha hb))%type 
      end
    | winners f => fun ea => (∃ m inbs d ha hb hc, ea = fin _ m inbs f d ha hb hc)%type
    end e.
  Proof.
    intros *.
    refine
    (match e as e' in Count _ s' return
      (match s' return Count _ s' -> Prop
      with 
      | partial (us, inbs) m => 
        match inbs as inbs' return (Count _ (partial (us, inbs') m) -> Prop)
        with 
        | [] => fun (ea : Count bs (partial (us, []) m)) => 
            ((∃ (hu : us = bs)  (hv : ∀ c d : cand, m c d = 0),  ea = ax _ us m hu hv) ∨
            (∃ u m' hu hv hw, ea = cvalid _ u us m' m [] hu hv hw))%type
        | inbsh :: inbst => fun (ea : Count bs (partial (us, inbsh :: inbst) m)) => 
          ((∃ u m' ha hb hc, ea = cvalid _ u us m' m (inbsh :: inbst) ha hb hc) ∨ 
          (∃ (ha : Count bs (partial (inbsh :: us, inbst) m)) (hb : exists c, (inbsh c = 0)%nat),
            ea = cinvalid _ inbsh us m inbst ha hb))%type
        end
      | winners f => fun ea => ∃ m inbs d ha hb hc, (ea = fin _ m inbs f d ha hb hc)%type
      end e') 
    with 
    | ax _ us m ha hb => or_introl (ex_intro _ ha (ex_intro _ hb eq_refl))
    | cvalid _ u us m nm inbs ha hb hc => _ 
    | cinvalid _ u us m inbs ha hb => _ 
    | fin _ m inbs w d ha hb hc => _ 
    end).
    destruct inbs as [| inbsh inbst].
    +
      right; repeat eexists.
    +
      left; repeat eexists.
    +
      right; repeat eexists.
    +
      repeat eexists.
  Defined.
    

      

  

  Theorem count_inv : ∀ (bs : list ballot) (s : state) (e : Count bs s), 
    match e as e' in Count _ s' return Count _ s' -> Type 
    with 
    | ax _ us m ha hb => fun (b : Count bs (partial (us, []) m)) => 
      b = ax _ us m ha hb 
    | cvalid _ u us m nm inbs ha hb hc => fun (b : Count bs (partial (us, inbs) nm)) => 
      b = cvalid _ u us m nm inbs ha hb hc
    | cinvalid _ u us m inbs ha hb => fun (b : Count bs (partial (us, u :: inbs) m)) => 
      b = cinvalid _ u us m inbs ha hb 
    | fin _ m inbs w d ha hb hc => fun (b : Count bs (winners w)) => 
      b = fin _ m inbs w d ha hb hc
    end e.
  Proof.
    destruct e; exact eq_refl.
  Defined.


  Definition count_inv_ax_ret_type {bs : list ballot} (s : state) : 
    Count bs s -> Prop.
  Proof.
    refine 
      match s as s' return Count _ s' -> Prop 
      with 
      | partial (us, vx) m => 
        match vx as vx' return (Count _ (partial (us, vx') m) -> Prop) with 
        | [] => fun (c : (Count _ (partial (us, []) m))) => 
          (∃ (hu : us = bs)  (hv : ∀ c d : cand, m c d = 0),  
            c = ax _ us m hu hv) ∨
          (∃ u m' hu hv hw, c = cvalid _ u us m' m [] hu hv hw)
        | vxh :: vxt => fun _ => IDProp
        end
      | winners _ => fun c => IDProp 
      end.
  Defined.


  Theorem count_inv_ax : ∀ (bs us : list ballot) (m : cand -> cand -> Z) 
    (e : Count bs (partial (us , []) m)), 
    (∃ (ha : us = bs)  (hb : ∀ c d : cand, m c d = 0),  e = ax _ us m ha hb) ∨
    (∃ u m' ha hb hc, e = cvalid _ u us m' m [] ha hb hc).
  Proof.
    intros *.
    pose proof count_inv_convoy bs _ e as ha.
    cbn in ha. exact ha.
    (* 
    refine 
      match e as e' in Count _ s' return count_inv_ax_ret_type s' e' with
      | ax _ us' m' ha hb => _ 
      | cvalid _ u us' m' nm inbs ha hb hc => _
      | _ => _
      end; cbn; try (exact idProp).
    +
      left; repeat eexists.
    +
      destruct inbs as [| h t].
      right; repeat eexists.
      exact idProp. *)
  Defined.


  Theorem count_inv_fin_ret_type {bs : list ballot} (s : state) :
    Count bs s -> Prop.
  Proof.
    refine 
      match s as s' return Count _ s' -> Prop 
      with 
      | partial (us, vx) m => fun _ =>  IDProp
      | winners f => fun c => 
        ∃ m inbs d ha hb hc, c = fin _ m inbs f d ha hb hc
      end.
  Defined.


  Theorem count_inv_fin : ∀ (bs : list ballot) (f : cand -> bool) 
    (e : Count bs (winners f)), 
    ∃ m inbs d ha hb hc, e = fin _ m inbs f d ha hb hc.
  Proof.
    intros *.
    pose proof count_inv_convoy _ _ e as ha.
    cbn in ha.
    exact ha.
    (* 
    refine 
      match e as e' in Count _ s'  
        return count_inv_fin_ret_type s' e'  
      with 
      | fin _ m' inbs' f' d' ha' hb' hc' => _
      | _ => idProp
      end.
    repeat eexists. *)
  Defined.


End Schulze.  
