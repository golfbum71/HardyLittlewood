import Mathlib

/-!
# Quantitative Challenge: The Hardy–Littlewood Prime k-Tuple Conjecture

States the quantitative Hardy–Littlewood conjecture as a `Prop` (deliberately
unproved — this is the genuinely open mathematical content) and proves, as an
actual theorem, that the conjecture implies infinitely many prime k-tuples for
any admissible constellation with a positive singular series.
-/

open Finset Filter
open scoped Topology

/-- A constellation is a finite set of integer offsets. -/
abbrev Constellation : Type := Finset ℤ

/-- The number of distinct residue classes occupied by `H` modulo a prime `p`. -/
def omega (H : Constellation) (p : ℕ) : ℕ :=
  (H.image (fun (h : ℤ) => (h : ZMod p))).card

def IsAdmissible (H : Constellation) : Prop :=
  ∀ p : ℕ, p.Prime → omega H p < p

/-- `n + H` is a prime tuple: `n + h` is prime for every offset `h ∈ H`. -/
def IsPrimeTuple (n : ℤ) (H : Constellation) : Prop :=
  ∀ h ∈ H, ∃ p : ℕ, n + h = p ∧ p.Prime

open Classical in
/-- The counting function `π_H(x)`: how many `n ≤ x` yield a prime tuple. -/
noncomputable def piTuple (H : Constellation) (x : ℝ) : ℕ :=
  (Finset.filter (fun n : ℕ => IsPrimeTuple (n : ℤ) H) (Finset.range (Nat.ceil x))).card

/-- The per-prime singular series term. -/
noncomputable def singularSeriesTerm (H : Constellation) (k : ℕ) (p : ℕ) : ℝ :=
  (1 - (omega H p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ k

/-- The Hardy–Littlewood constant `𝔖(H)`, as an infinite product over primes. -/
noncomputable def hardyLittlewoodConstant (H : Constellation) : ℝ :=
  ∏' p : Nat.Primes, singularSeriesTerm H H.card p

noncomputable def asymptoticBound (k : ℕ) (x : ℝ) : ℝ :=
  x / (Real.log x) ^ k

/-- **The quantitative Hardy–Littlewood conjecture**, stated precisely as a
`Prop` and deliberately *not proved* — this is the genuinely open content. -/
def QuantitativeHardyLittlewood (H : Constellation) : Prop :=
  Tendsto (fun x : ℝ => (piTuple H x : ℝ) / (hardyLittlewoodConstant H * asymptoticBound H.card x))
    atTop (nhds 1)

/-- `x / (log x)^k → ∞` as `x → ∞`, for any `k`. -/
private lemma tendsto_div_log_pow_atTop (k : ℕ) :
    Tendsto (fun x : ℝ => x / (Real.log x) ^ k) atTop atTop := by
  have hz : Tendsto (fun x : ℝ => Real.log x ^ k / x) atTop (nhds 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero
    simpa using h
  have hpos : ∀ᶠ x : ℝ in atTop, Real.log x ^ k / x ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hxpos : 0 < x := lt_trans one_pos hx
    exact Set.mem_Ioi.mpr (by positivity)
  have hnW : Tendsto (fun x : ℝ => Real.log x ^ k / x) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, hpos⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hnW
  have heq : ((fun y : ℝ => y⁻¹) ∘ fun x : ℝ => Real.log x ^ k / x)
      = fun x : ℝ => x / Real.log x ^ k := by
    funext x; rw [Function.comp_apply, inv_div]
  rwa [heq] at hinv

/-- **If** the quantitative Hardy–Littlewood conjecture holds for an admissible
constellation `H` with a positive singular series constant, **then** there are
infinitely many prime `H`-tuples. This is the genuinely provable content of
this file — the conjecture itself remains open. -/
theorem quantitativeHardyLittlewood_implies_infinite
    (H : Constellation) (_hA : IsAdmissible H)
    (hconst : 0 < hardyLittlewoodConstant H)
    (h : QuantitativeHardyLittlewood H) :
    {n : ℤ | IsPrimeTuple n H}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  unfold QuantitativeHardyLittlewood at h
  have hmain_atTop : Tendsto (fun x : ℝ => hardyLittlewoodConstant H * asymptoticBound H.card x)
      atTop atTop := (tendsto_div_log_pow_atTop H.card).const_mul_atTop hconst
  have hprod_atTop : Tendsto (fun x : ℝ =>
      ((piTuple H x : ℝ) / (hardyLittlewoodConstant H * asymptoticBound H.card x))
        * (hardyLittlewoodConstant H * asymptoticBound H.card x)) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro M
    have h1 : ∀ᶠ x : ℝ in atTop,
        (1:ℝ)/2 < (piTuple H x : ℝ) / (hardyLittlewoodConstant H * asymptoticBound H.card x) :=
      (tendsto_order.mp h).1 (1/2) (by norm_num)
    have h2 : ∀ᶠ x : ℝ in atTop,
        (2 * (|M| + 1) : ℝ) ≤ hardyLittlewoodConstant H * asymptoticBound H.card x :=
      Filter.tendsto_atTop.mp hmain_atTop (2 * (|M| + 1))
    filter_upwards [h1, h2] with x hx1 hx2
    nlinarith [hx1, hx2, abs_nonneg M, le_abs_self M]
  have heq : (fun x : ℝ =>
      ((piTuple H x : ℝ) / (hardyLittlewoodConstant H * asymptoticBound H.card x))
        * (hardyLittlewoodConstant H * asymptoticBound H.card x))
      =ᶠ[atTop] (fun x : ℝ => (piTuple H x : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    have hasymp_ne : asymptoticBound H.card x ≠ 0 := by
      unfold asymptoticBound; positivity
    have hne : hardyLittlewoodConstant H * asymptoticBound H.card x ≠ 0 :=
      mul_ne_zero hconst.ne' hasymp_ne
    field_simp
  have hcount_atTop : Tendsto (fun x : ℝ => (piTuple H x : ℝ)) atTop atTop :=
    Tendsto.congr' heq hprod_atTop
  have hbound : ∀ x : ℝ, piTuple H x ≤ hfin.toFinset.card := by
    intro x
    unfold piTuple
    refine Finset.card_le_card_of_injOn (fun n : ℕ => (n : ℤ)) ?_ (Nat.cast_injective.injOn)
    intro n hn
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hn
    obtain ⟨_, hnprime⟩ := hn
    simp only [Finset.mem_coe]
    exact hfin.mem_toFinset.mpr hnprime
  have hev := Filter.tendsto_atTop.mp hcount_atTop ((hfin.toFinset.card : ℝ) + 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨B, hB⟩ := hev
  have hBcount : (hfin.toFinset.card : ℝ) + 1 ≤ (piTuple H B : ℝ) := hB B le_rfl
  have hfinal : (hfin.toFinset.card : ℝ) + 1 ≤ (hfin.toFinset.card : ℝ) := by
    calc (hfin.toFinset.card : ℝ) + 1 ≤ (piTuple H B : ℝ) := hBcount
      _ ≤ (hfin.toFinset.card : ℝ) := by exact_mod_cast hbound B
  linarith
