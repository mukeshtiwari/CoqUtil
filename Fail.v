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
                            le_unique_subproof nw pfb0 hc1)
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
              hc0 as hc' in (_ ≤ mp)
              return
                (∀ (pf : mp = S m') (pfa0 : m = S m') (pfb0 : n ≤ m'),
                   ha =
                   eq_rect (S m') (λ w : nat, n ≤ w) (le_S n m' pfb0) m
                     (eq_sym pfa0)
                   → le_S n m' pfb0 = eq_rect mp (le n) hc' (S m') pf)
            with
            | le_n _ =>
                λ (pf : n = S m') (pfa0 : m = S m') (pfb0 : n ≤ m') 
                  (hb0 : ha =
                         eq_rect (S m') (λ w : nat, n ≤ w) 
                           (le_S n m' pfb0) m (eq_sym pfa0)),
                  EqdepFacts.internal_eq_rew_r_dep
                    (λ (n0 : nat) (pf0 : n0 = S m'),
                       ∀ ha0 : n0 ≤ m,
                         n0 ≤ S m'
                         → ∀ pfb1 : n0 ≤ m',
                             ha0 =
                             eq_rect (S m') (λ w : nat, n0 ≤ w) 
                               (le_S n0 m' pfb1) m (eq_sym pfa0)
                             → le_S n0 m' pfb1 =
                               eq_rect n0 (le n0) (le_n n0) (S m') pf0)
                    (λ (ha0 : S m' ≤ m) (hc1 : S m' ≤ S m') 
                       (pfb1 : S m' ≤ m') (hb1 : ha0 =
                                                 eq_rect 
                                                   (S m') 
                                                   (λ w : nat, S m' ≤ w)
                                                   (le_S (S m') m' pfb1) m
                                                   (eq_sym pfa0)),
                       EqdepFacts.internal_eq_rew_r_dep
                         (λ (m0 : nat) (pfa1 : m0 = S m'),
                            ∀ ha1 : S m' ≤ m0,
                              ha1 =
                              eq_rect (S m') (λ w : nat, S m' ≤ w)
                                (le_S (S m') m' pfb1) m0 
                                (eq_sym pfa1)
                              → le_S (S m') m' pfb1 =
                                eq_rect (S m') (le (S m')) 
                                  (le_n (S m')) (S m') eq_refl)
                         (λ (ha1 : S m' ≤ S m') (_ : ha1 =
                                                     eq_rect 
                                                     (S m') 
                                                     (λ w : nat, S m' ≤ w)
                                                     (le_S (S m') m' pfb1) 
                                                     (S m') 
                                                     (eq_sym eq_refl)),
                            le_unique_subproof0 m' hc1 pfb1)
                         pfa0 ha0 hb1)
                    pf ha hc0 pfb0 hb0
            | le_S _ nw pfc =>
                λ (pf : S nw = S m') (pfa0 : m = S m') 
                  (pfb0 : n ≤ m') (hb0 : ha =
                                         eq_rect (S m') 
                                           (λ w : nat, n ≤ w) 
                                           (le_S n m' pfb0) m 
                                           (eq_sym pfa0)),
                  let H :
                    (λ n0 : nat,
                       n0 = S m'
                       → le_S n m' pfb0 =
                         eq_rect (S nw) (le n) (le_S n nw pfc) (S m') pf)
                      (S m') :=
                    match
                      pf as _ in (_ = n0)
                      return
                        (n0 = S m'
                         → le_S n m' pfb0 =
                           eq_rect (S nw) (le n) (le_S n nw pfc) (S m') pf)
                    with
                    | eq_refl =>
                        λ H : S nw = S m',
                          (λ hpf : S nw = S m',
                             let H0 : nw = m' :=
                               f_equal
                                 (λ e : nat,
                                    match e with
                                    | 0 => nw
                                    | S n0 => n0
                                    end)
                                 hpf
                               in
                             (λ hpf0 : nw = m',
                                EqdepFacts.internal_eq_rew_r_dep
                                  (λ (m0 : nat) (pfa1 : m0 = S m'),
                                     ∀ ha0 : n ≤ m0,
                                       ha0 =
                                       eq_rect (S m') 
                                         (λ w : nat, n ≤ w) 
                                         (le_S n m' pfb0) m0 
                                         (eq_sym pfa1)
                                       → le_S n m' pfb0 =
                                         eq_rect (S nw) 
                                           (le n) (le_S n nw pfc) 
                                           (S m') pf)
                                  (λ (ha0 : n ≤ S m') 
                                     (_ : ha0 =
                                          eq_rect (S m') 
                                            (λ w : nat, n ≤ w) 
                                            (le_S n m' pfb0) 
                                            (S m') (eq_sym eq_refl)),
                                     eq_ind_r
                                       (λ nw0 : nat,
                                          ∀ (pfc0 : n ≤ nw0) (pf0 : S nw0 = S m'),
                                            le_S n m' pfb0 =
                                            eq_rect (S nw0) 
                                              (le n) (le_S n nw0 pfc0) 
                                              (S m') pf0)
                                       (λ (pfc0 : n ≤ m') (pf0 : S m' = S m'),
                                          let hd : pf0 = eq_refl :=
                                            uip_nat (S m') pf0 in
                                          eq_ind_r
                                            (λ pf1 : S m' = S m',
                                               le_S n m' pfb0 =
                                               eq_rect 
                                                 (S m') 
                                                 (le n) 
                                                 (le_S n m' pfc0) 
                                                 (S m') pf1)
                                            ((let H1 : 
                                                pfb0 = pfc0 := 
                                                fn n m' pfb0 pfc0 in
                                              (let H2 : m' = m' := eq_refl in
                                               (let H3 : n = n := eq_refl in
                                                (λ ... ... ..., eq_trans ... ...)
                                                  H3)
                                                 H2)
                                                H1)
                                             :
                                             le_S n m' pfb0 =
                                             eq_rect (S m') 
                                               (le n) 
                                               (le_S n m' pfc0) 
                                               (S m') eq_refl)
                                            hd)
                                       hpf0 pfc pf)
                                  pfa0 ha hb0)
                               H0)
                            H
                    end in
                  H eq_refl
            end eq_refl)
           hc pfa pfb hb
   end eq_refl eq_refl)
