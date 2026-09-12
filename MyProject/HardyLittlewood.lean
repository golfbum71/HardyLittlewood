/-
Copyright (c) 2026 Geo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geo
-/
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
    pairwise coprime (CRT). -/
theorem crtMapBijective (limit : Nat) :
    Function.Bijective (crtMap limit) := by
  have hcoprime :
      Pairwise (Function.onFun Nat.Coprime (fun q : activePrimes limit => (q : ℕ))) := by
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
    change (ZMod.castHom (activePrimeDvdPrimorialModulus limit q q.2) (ZMod (q : ℕ))) n = E n q
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
      ∏ q : activePrimes limit,
        (localSurvivors q.1 (memActivePrimesIsPrime limit q.1 q.2)).card := by
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
/-! ### Step 2 (Part B): Admissibility predicate
`T` is admissible if, for every prime `p`, the offsets in `T` do not
occupy all residues mod `p` (equivalently `w T p < p`).
-/

def is_admissible (T : Finset Nat) : Prop :=
  ∀ p : Nat, p.Prime → w T p < p

/-- For any prime `p` strictly greater than `T.card`, admissibility is
automatic: `w T p ≤ T.card < p`. This reduces checking `is_admissible T`
to a finite computation over primes `p ≤ T.card`. -/
lemma admissible_of_large_prime (T : Finset Nat) (p : Nat) (_hp : p.Prime)
    (h : T.card < p) : w T p < p := by
  unfold w
  exact lt_of_le_of_lt Finset.card_image_le h

/-! ### Step 3 (Part B): Singular series convergence
Defines the per-prime correction factor `singularSeriesFactor T p` and
proves the infinite product of these factors over all primes converges
to a strictly positive constant.
-/

/-- If every offset in `T` is `< p`, then `t % p = t` for all `t ∈ T`, so
`w T p = T.card` exactly (not just `≤`). -/
lemma wEqCardOfLt (T : Finset Nat) (p : Nat) (hT : ∀ t ∈ T, t < p) :
    w T p = T.card := by
  unfold w
  have himg : T.image (fun t => t % p) = T := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨t, htT, rfl⟩
      rwa [Nat.mod_eq_of_lt (hT t htT)]
    · intro hx
      exact ⟨x, hx, Nat.mod_eq_of_lt (hT x hx)⟩
  rw [himg]

noncomputable def singularSeriesFactor (T : Finset Nat) (p : Nat) : Real :=
  (p : Real) ^ (T.card - 1) * ((p : Real) - w T p) / ((p : Real) - 1) ^ T.card

lemma singularSeriesFactorPos (T : Finset Nat) (hT : is_admissible T)
    (p : Nat) (hp : p.Prime) : 0 < singularSeriesFactor T p := by
  unfold singularSeriesFactor
  have hw : w T p < p := hT p hp
  have hwR : (w T p : Real) < (p : Real) := by exact_mod_cast hw
  have hp2 : (2 : Real) ≤ (p : Real) := by exact_mod_cast hp.two_le
  have hnum_pos : 0 < (p : Real) - w T p := by linarith
  have hpow_pos : 0 < (p : Real) ^ (T.card - 1) := by
    have : (0 : Real) < (p : Real) := by linarith
    positivity
  have hden_pos : 0 < ((p : Real) - 1) ^ T.card := by
    have : (0 : Real) < (p : Real) - 1 := by linarith
    positivity
  exact div_pos (mul_pos hpow_pos hnum_pos) hden_pos

noncomputable def singularSeriesDelta (T : Finset Nat) (p : Nat) : Real :=
  singularSeriesFactor T p - 1

lemma singularSeriesFactorEqOneAdd (T : Finset Nat) (p : Nat) :
    singularSeriesFactor T p = 1 + singularSeriesDelta T p := by
  unfold singularSeriesDelta
  ring

/-- Core real-analysis lemma. Uses only `abs_le` + `mul_le_mul_of_nonneg_left`
to avoid any risk of a renamed `abs_add`/`abs_mul` in this snapshot. -/
private lemma polyGapBound (p : ℝ) (hp1 : 1 ≤ p) :
    ∀ m : ℕ,
      |(p - 1) ^ (m + 2) - p ^ (m + 1) * (p - ((m : ℝ) + 2))|
        ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) / 2 * p ^ m := by
  intro m
  induction m with
  | zero =>
    push_cast
    have heq : (p - 1) ^ (0 + 2) - p ^ (0 + 1) * (p - (0 + 2)) = 1 := by ring
    rw [heq]
    norm_num
  | succ n ih =>
    push_cast
    have hrec :
        (p - 1) ^ (n + 1 + 2) - p ^ (n + 1 + 1) * (p - ((n : ℝ) + 1 + 2))
          = ((n : ℝ) + 2) * p ^ (n + 1)
            + (p - 1) * ((p - 1) ^ (n + 2) - p ^ (n + 1) * (p - ((n : ℝ) + 2))) := by
      ring
    rw [hrec]
    have hpm1 : (0 : ℝ) ≤ p - 1 := by linarith
    obtain ⟨hipbL, hipbR⟩ := abs_le.mp ih
    have hmulR := mul_le_mul_of_nonneg_left hipbR hpm1
    have hmulL := mul_le_mul_of_nonneg_left hipbL hpm1
    have hp1p : p - 1 ≤ p := by linarith
    have hbound_nonneg : (0:ℝ) ≤ ((n:ℝ)+1)*((n:ℝ)+2)/2 * p^n := by positivity
    have hAnonneg : (0:ℝ) ≤ ((n:ℝ)+2) * p^(n+1) := by positivity
    have htarget_eq : ((n:ℝ)+1+1)*((n:ℝ)+1+2)/2 * p^(n+1)
        = ((n:ℝ)+2)*p^(n+1) + p * (((n:ℝ)+1)*((n:ℝ)+2)/2*p^n) := by ring
    rw [abs_le]
    constructor <;> nlinarith [hmulR, hmulL, hp1p, hbound_nonneg, hAnonneg, htarget_eq]

/-- **Key convergence estimate.** Once `p` exceeds every offset in `T`
(so `w T p = T.card` exactly, by `wEqCardOfLt`), the correction factor's
deviation from 1 shrinks like `O(1/p^2)` — fast enough for the sum over
all primes to converge. -/
theorem deltaBoundOfLargePrime (T : Finset Nat) (hk : 1 ≤ T.card) :
    ∃ C : Real, 0 ≤ C ∧ ∀ p : Nat, p.Prime → (∀ t ∈ T, t < p) →
      |singularSeriesDelta T p| ≤ C / (p : Real) ^ 2 := by
  set k := T.card with hkdef
  have hkR1 : (1 : Real) ≤ (k : Real) := by exact_mod_cast hk
  have hC_nonneg : 0 ≤ (k:Real) * ((k:Real) - 1) * 2 ^ (k - 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  refine ⟨(k : Real) * ((k : Real) - 1) * 2 ^ (k - 1), hC_nonneg, ?_⟩
  intro p hp hp_gt
  have hpR2 : (2 : Real) ≤ (p : Real) := by exact_mod_cast hp.two_le
  have hpR1 : (1 : Real) ≤ (p : Real) := by linarith
  have hp2pos : (0 : Real) < (p : Real) ^ 2 := pow_pos (by linarith) 2
  have hpm1 : (p : Real) - 1 ≠ 0 := by linarith
  have hw : w T p = k := wEqCardOfLt T p hp_gt
  have hδ_eq : singularSeriesDelta T p
      = -(((p:Real) - 1) ^ k - (p:Real) ^ (k - 1) * ((p:Real) - k)) / ((p:Real) - 1) ^ k := by
    unfold singularSeriesDelta singularSeriesFactor
    rw [← hkdef, hw]
    field_simp
    ring
  by_cases hk1 : k = 1
  · have hδ0 : singularSeriesDelta T p = 0 := by
      rw [hδ_eq, hk1]
      norm_num
    rw [hδ0]
    simp only [abs_zero, ge_iff_le]
    positivity
  · have hk2 : 2 ≤ k := by omega
    have hden_pos : (0:Real) < ((p:Real) - 1) ^ k := by positivity
    obtain ⟨m, hm⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have h1 : k - 1 = m + 1 := by omega
    have h2 : k - 2 = m := by omega
    have hbound_k : |((p:Real) - 1) ^ k - (p:Real) ^ (k - 1) * ((p:Real) - k)|
        ≤ ((k:Real) - 1) * (k:Real) / 2 * (p:Real) ^ (k - 2) := by
      have hb := polyGapBound (p:Real) hpR1 m
      have hLHS_eq : ((p:Real) - 1) ^ k - (p:Real) ^ (k - 1) * ((p:Real) - k)
          = (p - 1) ^ (m + 2) - p ^ (m + 1) * (p - ((m:Real) + 2)) := by
        rw [h1, hm]; push_cast; ring
      have hRHS_eq : ((k:Real) - 1) * (k:Real) / 2 * (p:Real) ^ (k - 2)
          = ((m:Real) + 1) * ((m:Real) + 2) / 2 * p ^ m := by
        rw [h2, hm]; push_cast; ring
      rw [hLHS_eq, hRHS_eq]
      exact hb
    have hpk_le : (p:Real)^k ≤ 2^k * ((p:Real)-1)^k := by
      have hstep : (p:Real) ≤ 2 * ((p:Real) - 1) := by linarith
      have hmono := pow_le_pow_left₀ (by positivity : (0:Real) ≤ (p:Real)) hstep k
      rwa [mul_pow] at hmono
    have hXp2 : |((p:Real)-1)^k - (p:Real)^(k-1)*((p:Real)-k)| * (p:Real)^2
        ≤ ((k:Real)*((k:Real)-1)/2) * (p:Real)^k := by
      have h0 := mul_le_mul_of_nonneg_right hbound_k (le_of_lt hp2pos)
      have hexp2 : (k-2)+2 = k := by omega
      calc |((p:Real)-1)^k - (p:Real)^(k-1)*((p:Real)-k)| * (p:Real)^2
          ≤ (((k:Real)-1)*(k:Real)/2 * (p:Real)^(k-2)) * (p:Real)^2 := h0
        _ = ((k:Real)*((k:Real)-1)/2) * (p:Real)^k := by
            rw [mul_assoc, ← pow_add, hexp2]; ring
    have hCD : ((k:Real)*((k:Real)-1)/2) * (p:Real)^k
        ≤ ((k:Real)*((k:Real)-1)*2^(k-1)) * ((p:Real)-1)^k := by
      have hksucc : k = (k - 1) + 1 := by omega
      have h2k : (2:Real)^k = 2 * 2^(k-1) := by
        conv_lhs => rw [hksucc]
        rw [pow_succ]
        ring
      have hcoef_nonneg : (0:Real) ≤ (k:Real)*((k:Real)-1)/2 := by nlinarith
      calc ((k:Real)*((k:Real)-1)/2) * (p:Real)^k
          ≤ ((k:Real)*((k:Real)-1)/2) * (2^k * ((p:Real)-1)^k) :=
            mul_le_mul_of_nonneg_left hpk_le hcoef_nonneg
        _ = ((k:Real)*((k:Real)-1)*2^(k-1)) * ((p:Real)-1)^k := by rw [h2k]; ring
    have hnum_nonneg : ((k:Real)*((k:Real)-1)*2^(k-1)) * ((p:Real)-1)^k
        - |((p:Real)-1)^k - (p:Real)^(k-1)*((p:Real)-k)| * (p:Real)^2 ≥ 0 := by
      linarith [hXp2, hCD]
    rw [hδ_eq, abs_div, abs_neg, abs_of_pos hden_pos]
    have expand : (k:Real)*((k:Real)-1)*2^(k-1) / (p:Real)^2
        - |((p:Real)-1)^k - (p:Real)^(k-1)*((p:Real)-k)| / ((p:Real)-1)^k
        = (((k:Real)*((k:Real)-1)*2^(k-1)) * ((p:Real)-1)^k
            - |((p:Real)-1)^k - (p:Real)^(k-1)*((p:Real)-k)| * (p:Real)^2)
          / ((p:Real)^2 * ((p:Real)-1)^k) := by
      field_simp
    have hge : (k:Real)*((k:Real)-1)*2^(k-1) / (p:Real)^2
        - |((p:Real)-1)^k - (p:Real)^(k-1)*((p:Real)-k)| / ((p:Real)-1)^k ≥ 0 := by
      rw [expand]
      exact div_nonneg hnum_nonneg (by positivity)
    linarith [hge]

/-- `∑ ‖δ(p)‖` over all primes converges. Requires `T` nonempty (`hk`),
matching `deltaBoundOfLargePrime`'s hypothesis. -/
lemma singularSeriesDeltaSummable (T : Finset Nat) (hk : 1 ≤ T.card) :
    Summable (fun p : Nat.Primes => ‖singularSeriesDelta T p‖) := by
  obtain ⟨C, hC_nonneg, hC⟩ := deltaBoundOfLargePrime T hk
  have hrpow : Summable (fun p : Nat.Primes => (p:ℝ) ^ (-2:ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have hconv : ∀ p : Nat.Primes, (p:ℝ) ^ (-2:ℝ) = 1 / (p:ℝ) ^ 2 := by
    intro p
    have hp_pos : (0:ℝ) < (p:ℝ) := by exact_mod_cast p.2.pos
    have step1 : (p:ℝ) ^ (-2:ℝ) = ((p:ℝ) ^ (2:ℝ))⁻¹ := by
      rw [show (-2:ℝ) = -(2:ℝ) by ring, Real.rpow_neg hp_pos.le]
    have step2 : (p:ℝ) ^ (2:ℝ) = (p:ℝ) ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [step1, step2, inv_eq_one_div]
  have hg : Summable (fun p : Nat.Primes => C / (p:ℝ) ^ 2) := by
    have hmul : Summable (fun p : Nat.Primes => C * (p:ℝ) ^ (-2:ℝ)) := hrpow.mul_left C
    have heq : (fun p : Nat.Primes => C * (p:ℝ) ^ (-2:ℝ))
        = (fun p : Nat.Primes => C / (p:ℝ) ^ 2) := by
      funext p
      rw [hconv p, mul_one_div]
    rwa [heq] at hmul
  have hfin : {p : Nat.Primes | ¬ ∀ t ∈ T, t < (p:ℕ)}.Finite := by
    have hinj : Function.Injective (fun p : Nat.Primes => (p:ℕ)) := by
      intro p q h
      exact Subtype.ext h
    have hpre : ((fun p : Nat.Primes => (p:ℕ)) ⁻¹' (Set.Iic (T.sup id))).Finite :=
      (Set.finite_Iic (T.sup id)).preimage hinj.injOn
    refine hpre.subset ?_
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    have hp' := hp
    push Not at hp'
    obtain ⟨t, htT, hnlt⟩ := hp'
    have ht_le : t ≤ T.sup id := by simpa using Finset.le_sup (f := id) htT
    simp only [Set.mem_preimage, Set.mem_Iic]
    omega
  apply Summable.of_norm_bounded_eventually hg
  rw [Filter.eventually_cofinite]
  apply hfin.subset
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  intro hp_gt
  apply hp
  rw [norm_norm]
  exact hC (p:ℕ) p.2 hp_gt

/-- The infinite product defining the singular series actually converges
(to a nonzero limit) — not just its `1 + δ(p)` summands being small, but
the product itself being well-defined. -/
theorem singularSeriesMultipliable (T : Finset Nat) (hk : 1 ≤ T.card) :
    Multipliable (fun p : Nat.Primes => singularSeriesFactor T p) := by
  have hM : Multipliable (fun p : Nat.Primes => 1 + singularSeriesDelta T p) :=
    multipliable_one_add_of_summable (singularSeriesDeltaSummable T hk)
  have heq : (fun p : Nat.Primes => singularSeriesFactor T p)
      = (fun p : Nat.Primes => 1 + singularSeriesDelta T p) := by
    funext p
    exact singularSeriesFactorEqOneAdd T p
  rw [heq]
  exact hM

noncomputable def hardyLittlewoodConstant (T : Finset Nat) : Real :=
  ∏' p : Nat.Primes, singularSeriesFactor T p

/-- Self-contained Weierstrass-type product bound: if every finite subset of `s`
keeps `∑ |δ(p)|` under control, the product `∏ (1 + δ(p))` over `s` is bounded
below by `1 - ∑ |δ(p)|`. Proved by induction. -/
private lemma prodOneAddGeSub (δ : Nat.Primes → ℝ) (hpos : ∀ p, 0 < 1 + δ p)
    (s : Finset Nat.Primes) (hbound : ∑ p ∈ s, |δ p| ≤ 1) :
    1 - ∑ p ∈ s, |δ p| ≤ ∏ p ∈ s, (1 + δ p) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.sum_insert hp] at hbound ⊢
    rw [Finset.prod_insert hp]
    have hab : (0:ℝ) ≤ |δ p| := abs_nonneg _
    have hs_le : ∑ q ∈ s, |δ q| ≤ 1 := by linarith
    have hsum_nonneg : (0:ℝ) ≤ ∑ q ∈ s, |δ q| :=
      Finset.sum_nonneg (fun q _ => abs_nonneg (δ q))
    have ihP := ih hs_le
    have h1 : (0:ℝ) ≤ 1 + δ p := le_of_lt (hpos p)
    have hfac_nonneg : (0:ℝ) ≤ 1 - ∑ q ∈ s, |δ q| := by linarith
    have hle : -|δ p| ≤ δ p := neg_abs_le (δ p)
    have hmul1 : -|δ p| * (1 - ∑ q ∈ s, |δ q|) ≤ δ p * (1 - ∑ q ∈ s, |δ q|) :=
      mul_le_mul_of_nonneg_right hle hfac_nonneg
    have hmul2 : (1 + δ p) * (1 - ∑ q ∈ s, |δ q|) ≤ (1 + δ p) * ∏ q ∈ s, (1 + δ q) :=
      mul_le_mul_of_nonneg_left ihP h1
    nlinarith [hmul1, hmul2, mul_nonneg hab hsum_nonneg]

/-- `hardyLittlewoodConstant T` is strictly positive for admissible `T`. -/
theorem hardyLittlewoodConstantPos (T : Finset Nat) (hT : is_admissible T)
    (hk : 1 ≤ T.card) : 0 < hardyLittlewoodConstant T := by
  set δ : Nat.Primes → ℝ := fun p => singularSeriesDelta T p with hδdef
  have hpos : ∀ p : Nat.Primes, 0 < 1 + δ p := by
    intro p
    have := singularSeriesFactorPos T hT (p:ℕ) p.2
    rwa [singularSeriesFactorEqOneAdd T (p:ℕ)] at this
  have hsummable : Summable (fun p : Nat.Primes => ‖δ p‖) := singularSeriesDeltaSummable T hk
  obtain ⟨S₀, hS₀⟩ := summable_iff_vanishing_norm.mp hsummable (1/2 : ℝ) (by norm_num)
  have hS₀tail : ∀ t : Finset Nat.Primes, Disjoint t S₀ → ∑ p ∈ t, |δ p| < 1/2 := by
    intro t htdisj
    have h := hS₀ t htdisj
    have heq : ∑ p ∈ t, ‖δ p‖ = ∑ p ∈ t, |δ p| := by simp [Real.norm_eq_abs]
    rw [heq] at h
    rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun p _ => abs_nonneg (δ p)))] at h
  set B := ∏ p ∈ S₀, (1 + δ p) with hBdef
  have hB_pos : 0 < B := Finset.prod_pos (fun p _ => hpos p)
  set m : ℝ := B / 2 with hmdef
  have hm_pos : 0 < m := by positivity
  have hHP : HasProd (fun p : Nat.Primes => singularSeriesFactor T p) (hardyLittlewoodConstant T) :=
    (singularSeriesMultipliable T hk).hasProd
  have hHPδ : HasProd (fun p : Nat.Primes => 1 + δ p) (hardyLittlewoodConstant T) := by
    have heqf : (fun p : Nat.Primes => singularSeriesFactor T p)
        = (fun p : Nat.Primes => 1 + δ p) := by
      funext p; exact singularSeriesFactorEqOneAdd T p
    rwa [heqf] at hHP
  have hTendsto : Filter.Tendsto (fun s : Finset Nat.Primes => ∏ p ∈ s, (1 + δ p))
      Filter.atTop (nhds (hardyLittlewoodConstant T)) := by
    unfold HasProd SummationFilter.unconditional at hHPδ
    exact hHPδ
  have hev : ∀ᶠ s : Finset Nat.Primes in Filter.atTop, m ≤ ∏ p ∈ s, (1 + δ p) := by
    rw [Filter.eventually_atTop]
    refine ⟨S₀, fun s hs => ?_⟩
    have hsplit : s = S₀ ∪ (s \ S₀) := (Finset.union_sdiff_of_subset hs).symm
    have hdisjoint : Disjoint S₀ (s \ S₀) := Finset.disjoint_sdiff
    rw [hsplit, Finset.prod_union hdisjoint]
    have htail_disj : Disjoint (s \ S₀) S₀ := hdisjoint.symm
    have htail_lt := hS₀tail (s \ S₀) htail_disj
    have htail_le : ∑ p ∈ s \ S₀, |δ p| ≤ 1 := by linarith
    have htail_bound := prodOneAddGeSub δ hpos (s \ S₀) htail_le
    have htail_pos : 0 < ∏ p ∈ s \ S₀, (1 + δ p) := Finset.prod_pos (fun p _ => hpos p)
    have hhalf : (1:ℝ)/2 ≤ ∏ p ∈ s \ S₀, (1 + δ p) := by linarith
    calc B / 2 = B * (1/2) := by ring
      _ ≤ B * (∏ p ∈ s \ S₀, (1 + δ p)) := by
          apply mul_le_mul_of_nonneg_left hhalf (le_of_lt hB_pos)
      _ = (∏ p ∈ S₀, (1 + δ p)) * ∏ p ∈ s \ S₀, (1 + δ p) := by rw [hBdef]
  have hge : m ≤ hardyLittlewoodConstant T := ge_of_tendsto hTendsto hev
  linarith [hm_pos, hge]

/-! ### Step 3 (Part B, continued): Finite-check wrapper and `{0,2}` admissibility
Admissibility only needs checking at primes up to `T.card`; beyond that,
`admissible_of_large_prime` handles it automatically.
-/

theorem admissible_of_finite_check (T : Finset Nat) :
    (∀ p, p.Prime → p ≤ T.card → w T p < p) → is_admissible T := by
  intro h p hp
  by_cases hle : p ≤ T.card
  · exact h p hp hle
  · push Not at hle
    exact admissible_of_large_prime T p hp hle

lemma is_admissible_zero_two : is_admissible ({0, 2} : Finset Nat) := by
  apply admissible_of_finite_check
  intro p hp hle
  have hcard : ({0, 2} : Finset Nat).card = 2 := by decide
  rw [hcard] at hle
  have hp2 : p = 2 := by
    have := hp.two_le
    omega
  subst hp2
  decide

/-! ### Step 4 (Part B): Hardy–Littlewood conjecture (formalized statement, not proved)
Everything above is finite and fully proved. This section states — as a
precise `Prop`, deliberately left unproved — the genuinely open conjecture
that the exact count of prime k-tuples up to `N` is asymptotically
`C_k · N / (log N)^k`, where `C_k` is `hardyLittlewoodConstant`.
-/

/-- The actual count of `n < N` such that `n + t` is prime for every `t ∈ T`. -/
private noncomputable def actualTupleCount (T : Finset Nat) (N : Nat) : Nat :=
  ((Finset.range N).filter (fun n => ∀ t ∈ T, (n + t).Prime)).card

/-- The conjectured main term: `C_k · N / (log N)^k`. -/
private noncomputable def hardyLittlewoodMainTerm (T : Finset Nat) (N : Nat) : Real :=
  hardyLittlewoodConstant T * (N : Real) / (Real.log N) ^ T.card

/-- **The Hardy–Littlewood conjecture**, stated precisely as a `Prop` and
deliberately *not proved* — the genuinely open mathematical content. -/
def hardyLittlewoodConjecture (T : Finset Nat) (_hT : is_admissible T) : Prop :=
  Asymptotics.IsEquivalent Filter.atTop
    (fun N => (actualTupleCount T N : Real))
    (fun N => hardyLittlewoodMainTerm T N)

/-- **The twin prime conjecture**, formalized as the `T = {0,2}` instance of
`hardyLittlewoodConjecture`. -/
def twinPrimeConjecture : Prop :=
  hardyLittlewoodConjecture ({0, 2} : Finset Nat) is_admissible_zero_two

/-! ### Step 5 (Part B): The conjecture implies infinitely many twin primes
Closes the loop: the open conjecture, if merely *assumed*, already implies
infinitely many twin primes — not just morally, but by an actual proof.
-/

/-- Real-analysis helper: `N / (log N)^2 → ∞` as `N → ∞`. -/
private lemma tendstoNatCastDivLogSqAtTop :
    Filter.Tendsto (fun N : ℕ => (N : ℝ) / (Real.log N) ^ 2) Filter.atTop Filter.atTop := by
  have hreal : Filter.Tendsto (fun x : ℝ => x / (Real.log x) ^ 2) Filter.atTop Filter.atTop := by
    have hz : Filter.Tendsto (fun x : ℝ => Real.log x ^ 2 / x) Filter.atTop (nhds 0) := by
      have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
      simpa using h
    have hpos : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ 2 / x ∈ Set.Ioi (0 : ℝ) := by
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
      have hlog : 0 < Real.log x := Real.log_pos hx
      have hxpos : 0 < x := lt_trans one_pos hx
      exact Set.mem_Ioi.mpr (by positivity)
    have hnW : Filter.Tendsto (fun x : ℝ => Real.log x ^ 2 / x) Filter.atTop
        (nhdsWithin 0 (Set.Ioi 0)) := tendsto_nhdsWithin_iff.mpr ⟨hz, hpos⟩
    have hinv := tendsto_inv_nhdsGT_zero.comp hnW
    have heq : ((fun y : ℝ => y⁻¹) ∘ fun x : ℝ => Real.log x ^ 2 / x)
        = fun x : ℝ => x / Real.log x ^ 2 := by
      funext x
      rw [Function.comp_apply, inv_div]
    rwa [heq] at hinv
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- The conjectured main term genuinely tends to infinity, for any admissible
`T` with `T.card = 2` (in particular, the twin-prime pattern). -/
private lemma hardyLittlewoodMainTermTendstoAtTop (T : Finset Nat)
    (hT : is_admissible T) (hk2 : T.card = 2) :
    Filter.Tendsto (fun N : ℕ => hardyLittlewoodMainTerm T N) Filter.atTop Filter.atTop := by
  have hconst := hardyLittlewoodConstantPos T hT (by omega)
  unfold hardyLittlewoodMainTerm
  rw [hk2]
  have hmain := tendstoNatCastDivLogSqAtTop.const_mul_atTop hconst
  simp only [← mul_div_assoc] at hmain
  exact hmain

/-- If the Hardy–Littlewood conjecture holds at `k = 2` (i.e.
`twinPrimeConjecture`), then there are infinitely many twin primes. -/
theorem twinPrimeConjectureImpliesInfiniteTwinPrimes
    (h : twinPrimeConjecture) :
    {n : ℕ | n.Prime ∧ (n + 2).Prime}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  unfold twinPrimeConjecture hardyLittlewoodConjecture at h
  have hk2 : ({0, 2} : Finset Nat).card = 2 := by decide
  have hmain_atTop :=
    hardyLittlewoodMainTermTendstoAtTop ({0, 2} : Finset Nat) is_admissible_zero_two hk2
  have hcount_atTop : Filter.Tendsto
      (fun N : ℕ => (actualTupleCount ({0, 2} : Finset Nat) N : ℝ))
      Filter.atTop Filter.atTop := h.tendsto_atTop_iff.mpr hmain_atTop
  have hev := Filter.tendsto_atTop.mp hcount_atTop ((hfin.toFinset.card : ℝ) + 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨B, hB⟩ := hev
  have hBcount : (hfin.toFinset.card : ℝ) + 1 ≤
      (actualTupleCount ({0, 2} : Finset Nat) B : ℝ) := hB B le_rfl
  have hbound : actualTupleCount ({0, 2} : Finset Nat) B ≤ hfin.toFinset.card := by
    unfold actualTupleCount
    apply Finset.card_le_card
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨_, hn2⟩ := hn
    have h0 : (n + 0).Prime := hn2 0 (by decide)
    have h2 : (n + 2).Prime := hn2 2 (by decide)
    rw [Nat.add_zero] at h0
    exact hfin.mem_toFinset.mpr ⟨h0, h2⟩
  have hfinal : (hfin.toFinset.card : ℝ) + 1 ≤ (hfin.toFinset.card : ℝ) := by
    calc (hfin.toFinset.card : ℝ) + 1
        ≤ (actualTupleCount ({0, 2} : Finset Nat) B : ℝ) := hBcount
      _ ≤ (hfin.toFinset.card : ℝ) := by exact_mod_cast hbound
  linarith
