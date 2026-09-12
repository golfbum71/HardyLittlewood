# Hardy–Littlewood Singular Series

This repository formalizes, in Lean 4 / Mathlib, the wheel-sieve infrastructure
behind the Hardy–Littlewood prime k-tuple conjecture: admissibility, the
singular series and its convergence, and the precise statement of the
conjecture itself — worked through concretely for the twin-prime tuple `{0,2}`.

The project imports `Mathlib` exclusively, with no external dependencies
beyond it.

## Contents

### Part A — CRT & Wheel-Sieve Setup

* **Step 1: `isCandidate` & `primeGtThreeIsCandidate`**
  Filters residues to 1, 5 mod 6 and shows every prime `p > 3` passes this filter.

* **Step 2: `activePrimes` & `primorialModulus`**
  The set of primes below a bound, and their product (the primorial modulus).

* **Step 3: `crtMap` & `crtMapBijective`**
  The CRT bijection between residues mod the primorial and tuples of residues
  mod each active prime.

* **Step 4: `localSurvivors` & `wheelSurvivors`**
  Residues avoiding 0 and -2 mod every active prime — the local conditions
  surviving for the `{0,2}` tuple. `wheelSurvivorsCardEqProd` uses the CRT
  bijection to express the survivor count as a product of local counts;
  `wheelSurvivorsCardFormula` gives the closed form (1 at `p = 2`, `p - 2`
  for odd primes).

* **Step 5: `squareRootShield`**
  Trial-division criterion: for `x ≤ X`, primality is equivalent to having
  no proper prime factor `≤ √X`.

### Part B — Admissible Tuples

* **`w T p`**: the number of distinct residue classes an offset set `T`
  occupies mod `p`.
* **`is_admissible`**: `∀ p prime, w T p < p`, with `admissible_of_large_prime`
  reducing the check to finitely many primes (`p ≤ T.card`), and
  `admissible_of_finite_check` as the corresponding finite-check wrapper.
* `is_admissible_zero_two` establishes admissibility of the twin-prime tuple.

### Part C — Singular Series Construction

* `singularSeriesFactor`, `singularSeriesDelta`: the per-prime correction
  factor and its deviation from 1.
* `deltaBoundOfLargePrime`, `singularSeriesDeltaSummable`: the key
  `O(1/p²)` convergence estimate and the resulting summability over all primes.
* `singularSeriesMultipliable`, `hardyLittlewoodConstant`,
  `hardyLittlewoodConstantPos`: the infinite product converges and is
  strictly positive on any admissible tuple, via a self-contained
  Weierstrass-style product bound.

### Part D — The Conjecture

* `hardyLittlewoodConjecture`: the quantitative Hardy–Littlewood k-tuple
  conjecture, stated precisely as an `IsEquivalent atTop` asymptotic and
  deliberately left unproved — the genuinely open mathematical content.
* `twinPrimeConjecture`: the `T = {0,2}` specialization.
* `twinPrimeConjectureImpliesInfiniteTwinPrimes`: a fully proved theorem —
  *if* the twin-prime instance of the conjecture holds, infinitely many
  twin primes follow.

All of `MyProject/HardyLittlewood.lean`'s content is namespaced under `RNS`.

## Repository Structure
my_project/
├── lakefile.toml
├── config.json
├── MyProject.lean # imports MyProject.Basic, MyProject.HardyLittlewood
├── MyProject/
│ ├── Basic.lean
│ └── HardyLittlewood.lean # Parts A–D, namespaced under RNS
├── Challenge.lean # independently-verifiable challenge statement
└── Bridge.lean # fills Challenge's gaps from RNS's proven results


Four separate Lake library targets build from this layout:

* **`MyProject`** — the source of record; imports and checks everything above.
* **`Solution`** — mirrors `MyProject` via `globs = ["MyProject.+"]`, for
  external verification.
* **`Challenge`** — an independently-stated version of the Hardy–Littlewood
  constant and its positivity, in `Finset ℤ`/`ZMod`-cast vocabulary rather
  than this project's own `Finset ℕ`/`%`-arithmetic encoding. Everything in
  it is proved except two genuine gaps:
  - `hardyLittlewoodConstant` (a definition hole)
  - `hardyLittlewoodConstant_pos` (a theorem hole)
* **`Bridge`** — fills both gaps by transporting the `RNS`-namespaced results
  from `MyProject/HardyLittlewood.lean` across a shift-invariance argument
  (translating a constellation by a constant doesn't change which residues
  it occupies mod any prime) and a `ℕ ↔ ℤ` correspondence for the
  nonnegative representative of each constellation.

This structure is designed for use with the [`leanprover/comparator`](https://github.com/leanprover/comparator)
tool: `Challenge.lean` and `Bridge.lean` can be checked against each other
in a sandboxed, independent-kernel verification, so that a reviewer never
needs to trust this repository's own definitions or build scripts —
only their own `Challenge.lean` and the config's exact declaration names.

## Building

```powershell
lake exe cache get
lake build MyProject
lake build Solution
lake build Challenge
lake build Bridge
```

## Project Status

All proofs in `MyProject/HardyLittlewood.lean`, `Challenge.lean`, and
`Bridge.lean` are complete with **no `sorry` placeholders**, except the two
statements in `Challenge.lean` that `Bridge.lean` exists to fill (by design —
that's the Challenge/Solution split, not an incompleteness in the underlying
mathematics).

Not yet done: running the actual sandboxed `landrun`/`lean4export` Comparator
check (requires a Linux environment — Windows/WSL2 setup pending).

A closed-form check that `hardyLittlewoodConstant {0, -2}` matches the
classical constant `2·∏(1 − 1/(p−1)²)` was intentionally left out of this
build to keep scope focused on the conjecture statement itself.
