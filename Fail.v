(fix fn (n m : nat) (ha : n ≤ m) {struct ha} : ∀ hb : n ≤ m, ha = hb :=
   match
     ha as ha' in (_ ≤ m')
     return
       (∀ pfa : m = m',
          ha = eq_rect m' (λ w : nat, n ≤ w) ha' m (eq_sym pfa)
          → ∀ hb : n ≤ m', ha' = hb)
   with
   | le_n _ =>
       λ (pfa : m = n) (hb : ha =
                             eq_rect n (λ w : nat, n ≤ w) (le_n n) m (eq_sym pfa)) 
         (hc : n ≤ n),
         (λ hc0 : n ≤ n,
            match
              hc0 as hc' in (_ ≤ n')
              return
                (∀ pfb : n = n',
                   le_n n' = eq_rect n (λ w : nat, w ≤ n') hc' n' pfb)
            with
            | le_n _ =>
                λ pfb : n = n,
                  let hd : pfb = eq_refl := uip_nat n pfb in
                  EqdepFacts.internal_eq_rew_r_dep
                    (λ (m0 : nat) (pfa0 : m0 = n),
                       ∀ ha0 : n ≤ m0,
                         ha0 =
                         eq_rect n (λ w : nat, n ≤ w) (le_n n) m0 (eq_sym pfa0)
                         → le_n n = eq_rect n (λ w : nat, w ≤ n) (le_n n) n pfb)
                    (λ (ha0 : n ≤ n) (_ : ha0 =
                                          eq_rect n (λ w : nat, n ≤ w) 
                                            (le_n n) n 
                                            (eq_sym eq_refl)),
                       eq_ind_r
                         (λ pfb0 : n = n,
                            le_n n = eq_rect n (λ w : nat, w ≤ n) (le_n n) n pfb0)
                         (eq_refl
                          :
                          le_n n = eq_rect n (λ w : nat, w ≤ n) (le_n n) n eq_refl)
                         hd)
                    pfa ha hb
            | le_S _ nw pfb =>
                λ pfc : n = S nw,
                  EqdepFacts.internal_eq_rew_r_dep
                    (λ (m0 : nat) (pfa0 : m0 = n),
                       ∀ ha0 : n ≤ m0,
                         ha0 =
                         eq_rect n (λ w : nat, n ≤ w) (le_n n) m0 (eq_sym pfa0)
                         → le_n (S nw) =
                           eq_rect n (λ w : nat, w ≤ S nw) 
                             (le_S n nw pfb) (S nw) pfc)
                    (λ (ha0 : n ≤ n) (_ : ha0 =
                                          eq_rect n (λ w : nat, n ≤ w) 
                                            (le_n n) n 
                                            (eq_sym eq_refl)),
                       EqdepFacts.internal_eq_rew_r_dep
                         (λ (n0 : nat) (pfc0 : n0 = S nw),
                            n0 ≤ n0
                            → ∀ pfb0 : n0 ≤ nw,
                                le_n (S nw) =
                                eq_rect n0 (λ w : nat, w ≤ S nw) 
                                  (le_S n0 nw pfb0) (S nw) pfc0)
                         (λ (hc1 : S nw ≤ S nw) (pfb0 : S nw ≤ nw),
                            le_unique_fail_subproof nw pfb0 hc1)
                         pfc hc0 pfb)
                    pfa ha hb
            end eq_refl)
           hc
   | le_S _ m' pfb =>
       λ (pfa : m = S m') (hb : ha =
                                eq_rect (S m') (λ w : nat, n ≤ w) 
                                  (le_S n m' pfb) m (eq_sym pfa)) 
         (hc : n ≤ S m'),
         (λ hc0 : n ≤ S m',
            match
              hc0 as hc' in (_ ≤ iV)
              return
                (match iV as iV0 return (n ≤ iV0 → Prop) with
                 | 0 => λ _ : n ≤ 0, IDProp
                 | S mp =>
                     λ hc'0 : n ≤ S mp,
                       ∀ (pf : mp = m') (pfa0 : m = S m') (pfb0 : n ≤ m'),
                         ha =
                         eq_rect (S m') (λ w : nat, n ≤ w) 
                           (le_S n m' pfb0) m (eq_sym pfa0)
                         → le_S n mp
                             (eq_rect m' (λ w : nat, n ≤ w) pfb0 mp (eq_sym pf)) =
                           hc'0
                 end hc')
            with
            | le_n _ =>
                match
                  n as n0
                  return
                    (∀ ha0 : n0 ≤ m,
                       n0 ≤ S m'
                       → match n0 as iV return (n0 ≤ iV → Prop) with
                         | 0 => λ _ : n0 ≤ 0, IDProp
                         | S mp =>
                             λ hc' : n0 ≤ S mp,
                               ∀ (pf : mp = m') (pfa0 : m = S m') (pfb0 : n0 ≤ m'),
                                 ha0 =
                                 eq_rect (S m') (λ w : nat, n0 ≤ w)
                                   (le_S n0 m' pfb0) m 
                                   (eq_sym pfa0)
                                 → le_S n0 mp
                                     (eq_rect m' (λ w : nat, n0 ≤ w) pfb0 mp
                                        (eq_sym pf)) =
                                   hc'
                         end (le_n n0))
                with
                | 0 => λ (_ : 0 ≤ m) (_ : 0 ≤ S m'), idProp
                | S n0 =>
                    (λ (n1 : nat) (ha0 : S n1 ≤ m) (hc1 : S n1 ≤ S m') 
                       (pf : n1 = m') (pfa0 : m = S m') 
                       (pfb0 : S n1 ≤ m') (_ : ha0 =
                                               eq_rect 
                                                 (S m') 
                                                 (λ w : nat, S n1 ≤ w)
                                                 (le_S (S n1) m' pfb0) m
                                                 (eq_sym pfa0)),
                       le_unique_fail_subproof0 n1 m ha0 m' hc1 pf pfa0 pfb0)
                      n0
                end ha hc0
            | le_S _ nw pfc =>
                λ (pf : nw = m') (pfa0 : m = S m') (pfb0 : n ≤ m') 
                  (hb0 : ha =
                         eq_rect (S m') (λ w : nat, n ≤ w) 
                           (le_S n m' pfb0) m (eq_sym pfa0)),
                  let H :
                    (λ n0 : nat,
                       n0 = m'
                       → le_S n nw
                           (eq_rect m' (λ w : nat, n ≤ w) pfb0 nw (eq_sym pf)) =
                         le_S n nw pfc)
                      m' :=
                    match
                      pf as _ in (_ = n0)
                      return
                        (n0 = m'
                         → le_S n nw
                             (eq_rect m' (λ w : nat, n ≤ w) pfb0 nw (eq_sym pf)) =
                           le_S n nw pfc)
                    with
                    | eq_refl =>
                        λ H : nw = m',
                          (λ hpf : nw = m',
                             EqdepFacts.internal_eq_rew_r_dep
                               (λ (nw0 : nat) (pf0 : nw0 = m'),
                                  ∀ pfc0 : n ≤ nw0,
                                    nw0 = m'
                                    → le_S n nw0
                                        (eq_rect m' (λ w : nat, n ≤ w) pfb0 nw0
                                           (eq_sym pf0)) =
                                      le_S n nw0 pfc0)
                               (λ (pfc0 : n ≤ m') (hpf0 : m' = m'),
                                  EqdepFacts.internal_eq_rew_r_dep
                                    (λ (m0 : nat) (pfa1 : m0 = S m'),
                                       ∀ ha0 : n ≤ m0,
                                         ha0 =
                                         eq_rect (S m') 
                                           (λ w : nat, n ≤ w) 
                                           (le_S n m' pfb0) m0 
                                           (eq_sym pfa1)
                                         → le_S n m'
                                             (eq_rect m' 
                                                (λ w : nat, n ≤ w) pfb0 m'
                                                (eq_sym eq_refl)) =
                                           le_S n m' pfc0)
                                    (λ (ha0 : n ≤ S m') 
                                       (_ : ha0 =
                                            eq_rect (S m') 
                                              (λ w : nat, n ≤ w) 
                                              (le_S n m' pfb0) 
                                              (S m') (eq_sym eq_refl)),
                                       let hd : hpf0 = eq_refl := 
                                         uip_nat m' hpf0 in
                                       (let H0 : pfb0 = pfc0 := 
                                          fn n m' pfb0 pfc0 in
                                        (let H1 : m' = m' := eq_refl in
                                         (let H2 : n = n := eq_refl in
                                          (λ (_ : n = n) 
                                             (_ : m' = m') 
                                             (H3 : pfb0 = pfc0),
                                             eq_trans
                                               (f_equal 
                                                  (λ f : ..., f pfb0) eq_refl)
                                               (f_equal (le_S n m') H3))
                                            H2)
                                           H1)
                                          H0)
                                       :
                                       le_S n m'
                                         (eq_rect m' (λ w : nat, n ≤ w) pfb0 m'
                                            (eq_sym eq_refl)) =
                                       le_S n m' pfc0)
                                    pfa0 ha hb0)
                               pf pfc hpf)
                            H
                    end in
                  H eq_refl
            end eq_refl)
           hc pfa pfb hb
   end eq_refl eq_refl)
