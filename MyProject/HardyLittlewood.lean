import Mathlib

/-!
# Hardy–Littlewood singular series

Construction of the singular series for an admissible tuple of offsets,
proof that the infinite product converges to a positive constant, and
the statement of the Hardy–Littlewood k-tuple conjecture.
-/

/-! ### Step 1 (Part A): Candidates mod 6
Primes greater than 3 lie in the residue classes 1 or 5 mod 6.
`isCandidate` encodes this filter.
-/

def isCandidate (n : Nat) : Bool :=
  (n % 6 == 1) || (n % 6 == 5)

lemma primeGtThreeIsCandidate (p : Nat) (hp : p.Prime) (h_gt : p > 3) :
    isCandidate p = true := by
  have h2 : ¬ (2 ∣ p) := by
    intro hdvd
    rcases hp.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega
  have h3 : ¬ (3 ∣ p) := by
    intro hdvd
    rcases hp.eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega
  unfold isCandidate
  simp only [Bool.or_eq_true, beq_iff_eq]
  omega

/-! ### Step 2 (Part A): Active primes and primorial modulus
`activePrimes limit` is the set of primes less than `limit`;
`primorialModulus limit` is their product.
-/

def activePrimes (limit : Nat) : Finset Nat :=
  (Finset.range limit).filter Nat.Prime

def primorialModulus (limit : Nat) : Nat :=
  (activePrimes limit).prod id

example : activePrimes 4 = {2, 3} := by decide
example : primorialModulus 4 = 6 := by decide

lemma memActivePrimesIsPrime (limit : Nat) (q : Nat)
    (hq : q ∈ activePrimes limit) : q.Prime := by
  unfold activePrimes at hq
  exact (Finset.mem_filter.mp hq).2

lemma primorialModulusPos (limit : Nat) : 0 < primorialModulus limit := by
  unfold primorialModulus
  apply Finset.prod_pos
  intro q hq
  exact (memActivePrimesIsPrime limit q hq).pos

/-! ### Step 3 (Part A): CRT identification
`crtMap` realises the Chinese-Remainder bijection between residues
modulo the primorial and tuples of residues modulo the active primes.
-/

lemma activePrimeDvdPrimorialModulus (limit : Nat) (q : Nat)
    (hq : q ∈ activePrimes limit) : q ∣ primorialModulus limit := by
  unfold primorialModulus
  exact Finset.dvd_prod_of_mem id hq

def crtMap (limit : Nat) (n : ZMod (primorialModulus limit)) :
    ∀ q : activePrimes limit, ZMod (q : Nat) :=
  fun q => ZMod.castHom (activePrimeDvdPrimorialModulus limit q q.2) (ZMod q) n

/-- `crtMap` is a bijection between residues mod the primorial and tuples
    of residues mod each active prime, since the active primes are
    pairwise coprime (CRT). 
-/

theorem crtMapBijective (limit : Nat) :
    Function.Bijective (crtMap limit) := by
  have hcoprime : Pairwise (Function.onFun Nat.Coprime (fun q : activePrimes limit => (q : ℕ))) := by
    intro q q' hne
    have hqp : (q : ℕ).Prime := memActivePrimesIsPrime limit q q.2
    have hqp' : (q' : ℕ).Prime := memActivePrimesIsPrime limit q' q'.2
    have hneq : (q : ℕ) ≠ (q' : ℕ) := fun h => hne (Subtype.ext h)
    exact (Nat.coprime_primes hqp hqp').mpr hneq
  have hprodeq : (∏ q : activePrimes limit, (q : ℕ)) = primorialModulus limit := by
    unfold primorialModulus
    exact Finset.prod_coe_sort (activePrimes limit) id
  have E : ZMod (primorialModulus limit) ≃+* (∀ q : activePrimes limit, ZMod (q : ℕ)) := by
    rw [← hprodeq]
    exact ZMod.prodEquivPi (fun q : activePrimes limit => (q : ℕ)) hcoprime
  have hfun_eq : crtMap limit
      = (E : ZMod (primorialModulus limit) → ∀ q : activePrimes limit, ZMod (q : ℕ)) := by
    funext n
    funext q
    have hring_eq :
        ZMod.castHom (activePrimeDvdPrimorialModulus limit q q.2) (ZMod (q : ℕ))
          = (Pi.evalRingHom (fun q : activePrimes limit => ZMod (q : ℕ)) q).comp E.toRingHom := by
      apply Subsingleton.elim
    show (ZMod.castHom (activePrimeDvdPrimorialModulus limit q q.2) (ZMod (q : ℕ))) n = E n q
    calc (ZMod.castHom (activePrimeDvdPrimorialModulus limit q q.2) (ZMod (q : ℕ))) n
        = ((Pi.evalRingHom (fun q : activePrimes limit => ZMod (q : ℕ)) q).comp E.toRingHom) n := by
          rw [hring_eq]
      _ = E n q := by simp [Pi.evalRingHom_apply]
  rw [hfun_eq]
  exact E.bijective

/-! ### Step 4 (Part A): Survivor cardinality for `{0,2}`
Count the residues modulo the primorial that avoid 0 and -2 at every
active prime.  The CRT reduces the count to a product of local counts.
-/

/-- The local survivors mod a prime `p`: residues `n : ZMod p` where
    neither `n` nor `n + 2` is `≡ 0`, i.e. `n ≠ 0` and `n ≠ -2`. -/
def localSurvivors (p : Nat) (hp : p.Prime) : Finset (ZMod p) :=
  have : NeZero p := ⟨hp.pos.ne'⟩
  Finset.univ.filter (fun n => n ≠ 0 ∧ n ≠ (-2 : ZMod p))

/-- The global survivors mod the primorial: residues `n` whose image under
    `crtMap` (i.e. every per-prime component) is a local survivor. -/
def wheelSurvivors (limit : Nat) : Finset (ZMod (primorialModulus limit)) :=
  have : NeZero (primorialModulus limit) := ⟨(primorialModulusPos limit).ne'⟩
  Finset.univ.filter (fun n => ∀ q : activePrimes limit,
    crtMap limit n q ≠ 0 ∧ crtMap limit n q ≠ (-2 : ZMod (q : ℕ)))

lemma localSurvivorsCardTwo : (localSurvivors 2 (by norm_num)).card = 1 := by
  decide

/-- For a prime `p ≠ 2`, the two forbidden residues `0` and `-2` are
    distinct, so exactly `p - 2` residues survive. -/
lemma localSurvivorsCard (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    (localSurvivors p hp).card = p - 2 := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  have hne : (0 : ZMod p) ≠ (-2 : ZMod p) := by
    intro heq
    have h2 : (2 : ZMod p) = 0 := by
      have := neg_eq_zero.mp heq.symm
      simpa using this
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hp2 (le_antisymm hle hp.two_le)
  have hclogged : Finset.univ.filter (fun n : ZMod p => n = 0 ∨ n = -2) = {0, -2} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
  have hcard2 : ({0, -2} : Finset (ZMod p)).card = 2 := Finset.card_pair hne
  have hcompl : localSurvivors p hp
      = Finset.univ \ Finset.univ.filter (fun n : ZMod p => n = 0 ∨ n = -2) := by
    unfold localSurvivors
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_or]
  rw [hcompl, hclogged, Finset.card_sdiff, Finset.inter_eq_left.mpr
      (by intro n _; exact Finset.mem_univ n), Finset.card_univ, ZMod.card, hcard2]

/-- Helper: `localSurvivorsCardTwo` restated for any proof-term `p = 2`,
    using `subst` so the dependent type `ZMod p` changes correctly. -/
lemma localSurvivorsCardEqTwoOfEq (p : Nat) (hp : p.Prime) (h : p = 2) :
    (localSurvivors p hp).card = 1 := by
  subst h
  exact localSurvivorsCardTwo

/-- Splits the global survivor count into a product of local survivor
    counts, one factor per active prime - the payoff of the Step 3 CRT
    bijection. `wheelSurvivorsCardFormula` below turns this into a
    closed-form arithmetic expression. -/
theorem wheelSurvivorsCardEqProd (limit : Nat) :
    (wheelSurvivors limit).card =
      ∏ q : activePrimes limit, (localSurvivors q.1 (memActivePrimesIsPrime limit q.1 q.2)).card := by
  set e : ZMod (primorialModulus limit) ≃ (∀ q : activePrimes limit, ZMod (q : ℕ)) :=
    Equiv.ofBijective (crtMap limit) (crtMapBijective limit) with he
  have himg : wheelSurvivors limit
      = (Fintype.piFinset (fun q : activePrimes limit =>
          localSurvivors q.1 (memActivePrimesIsPrime limit q.1 q.2))).image e.symm := by
    have hcoe : (e : ZMod (primorialModulus limit) → ∀ q : activePrimes limit, ZMod (q : ℕ))
        = crtMap limit := by
      rw [he]; rfl
    ext n
    unfold wheelSurvivors localSurvivors
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Fintype.mem_piFinset]
    constructor
    · intro hn
      refine ⟨e n, fun q => ?_, e.symm_apply_apply n⟩
      rw [congrFun hcoe n]
      exact hn q
    · rintro ⟨f, hf, rfl⟩
      intro q
      have hcrt : crtMap limit (e.symm f) = f := by
        rw [← hcoe]
        exact e.apply_symm_apply f
      rw [congrFun hcrt q]
      exact hf q
  rw [himg, Finset.card_image_of_injective _ e.symm.injective, Fintype.card_piFinset]

/-- Closed form for the twin-prime wheel survivor count: 1 out of `p = 2`'s
    residues, and `p - 2` out of `p`'s residues for every odd active prime. -/
theorem wheelSurvivorsCardFormula (limit : Nat) :
    (wheelSurvivors limit).card =
      ∏ q ∈ activePrimes limit, (if q = 2 then 1 else q - 2) := by
  rw [wheelSurvivorsCardEqProd, ← Finset.prod_coe_sort (activePrimes limit)
      (fun q => if q = 2 then 1 else q - 2)]
  apply Finset.prod_congr rfl
  intro q _
  by_cases hq2 : (q.1 : ℕ) = 2
  · simp only [hq2]
    exact localSurvivorsCardEqTwoOfEq q.1 (memActivePrimesIsPrime limit q.1 q.2) hq2
  · simp only [hq2]
    exact localSurvivorsCard q.1 (memActivePrimesIsPrime limit q.1 q.2) hq2

/-! ### Step 5 (Part A): Square-root shield
A natural number `x ≤ X` is prime if and only if it has no proper prime
factor ≤ √X.
-/

private def shieldRadius (X : Nat) : Nat :=
  Nat.sqrt X

private def hasSmallProperPrimeFactor (X x : Nat) : Prop :=
  ∃ p, p.Prime ∧ p ∣ x ∧ p < x ∧ p ≤ shieldRadius X

lemma primeHasNoSmallProperFactor (x : Nat) (hx : x.Prime) :
    ¬ ∃ p, p.Prime ∧ p ∣ x ∧ p < x := by
  rintro ⟨p, hp, hpd, hplt⟩
  rcases hx.eq_one_or_self_of_dvd p hpd with h1 | h2
  · exact absurd h1 hp.one_lt.ne'
  · exact absurd h2 hplt.ne

/-- For `x` in range `[2, X]`, `x` is prime iff it has no proper prime
    factor at or below `√X` (the standard trial-division bound). -/
theorem squareRootShield (X x : Nat) (hx2 : 2 ≤ x) (hxX : x ≤ X) :
    x.Prime ↔ ¬ hasSmallProperPrimeFactor X x := by
  constructor
  · intro hx hcontra
    obtain ⟨p, hp, hpd, hplt, _⟩ := hcontra
    exact primeHasNoSmallProperFactor x hx ⟨p, hp, hpd, hplt⟩
  · intro hnot
    by_contra hxp
    have hiff := Nat.prime_def_le_sqrt (p := x)
    have hstep : ¬ ∀ m, 2 ≤ m → m ≤ x.sqrt → ¬ m ∣ x := by
      intro hall
      exact hxp (hiff.mpr ⟨hx2, hall⟩)
    push Not at hstep
    obtain ⟨m, hm2, hmle, hmdvd⟩ := hstep
    set p := m.minFac with hp_def
    have hm1 : m ≠ 1 := by omega
    have hp_prime : p.Prime := Nat.minFac_prime hm1
    have hp_dvd_m : p ∣ m := Nat.minFac_dvd m
    have hp_dvd_x : p ∣ x := hp_dvd_m.trans hmdvd
    have hp_le_m : p ≤ m := Nat.minFac_le (by omega)
    have hp_le_sqrtx : p ≤ Nat.sqrt x := hp_le_m.trans hmle
    have hsqrtx_le_sqrtX : Nat.sqrt x ≤ Nat.sqrt X := Nat.sqrt_le_sqrt hxX
    have hp_le_shield : p ≤ shieldRadius X := by
      unfold shieldRadius
      exact hp_le_sqrtx.trans hsqrtx_le_sqrtX
    have hsqrtx_lt_x : Nat.sqrt x < x := Nat.sqrt_lt_self (by omega)
    have hp_lt_x : p < x := lt_of_le_of_lt hp_le_sqrtx hsqrtx_lt_x
    exact hnot ⟨p, hp_prime, hp_dvd_x, hp_lt_x, hp_le_shield⟩

/-! ### Step 1 (Part B): Admissible tuples
`w T p` is the number of distinct residues occupied by the offsets `T`
modulo `p`.  `T` is admissible if `w T p < p` for every prime `p`.
-/

def w (T : Finset Nat) (p : Nat) : Nat :=
  (T.image (fun t => t % p)).card