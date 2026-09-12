# Hardy–Littlewood Singular Series (Scaffolding)

This repository contains Lean 4 scaffolding designed to formalize the Hardy–Littlewood prime k-tuple singular series. It establishes the Chinese Remainder Theorem (CRT) and wheel-sieve machinery needed to analyze admissible tuples, working through the twin-prime case `{0,2}` as a concrete implementation. 

The file imports `Mathlib` exclusively, with no external dependencies.

## Contents

### Part A — CRT & Wheel-Sieve Setup

* **Step 1: `isCandidate` & `primeGtThreeIsCandidate`**  
  Filters residues to 1, 5 mod 6 and shows that every prime $p > 3$ passes this filter.

* **Step 2: `activePrimes` & `primorialModulus`**  
  Defines the set of primes below a given bound and computes their product (the primorial modulus).

* **Step 3: `crtMap` & `crtMapBijective`**  
  Constructs the CRT bijection mapping residues modulo the primorial to tuples of residues modulo each active prime.

* **Step 4: `localSurvivors` & `wheelSurvivors`**  
  Isolates the residues that avoid 0 and -2 modulo every active prime (the surviving local conditions for the `{0,2}` tuple). 
  
  `wheelSurvivorsCardEqProd` uses the CRT bijection to express the total survivor count as a product of local counts. `wheelSurvivorsCardFormula` computes the closed-form count (1 when $p = 2$, and $p - 2$ for odd primes).

* **Step 5: `squareRootShield`**  
  Proves the trial-division criterion: for $x \le X$, primality is equivalent to having no proper prime factors $\le \sqrt{X}$. This bound is used to ensure later finiteness checks remain strictly decidable.

### Part B — Admissible Tuples (Work in Progress)

* **`w T p`**  
  Counts the number of distinct residue classes occupied by an offset set $T$ mod $p$. This provides the exact prerequisite needed for the general admissibility predicate ($\omega(T, p) < p$ for all $p$), which is the next planned definition.

## Project Status

All proofs in this repository are fully broken down and contain **no `sorry` placeholders**. 

This code represents the foundational infrastructure. The construction of the infinite singular series product, its convergence/positivity proofs, and the formal statement of the Hardy–Littlewood conjecture itself will be integrated in subsequent updates.
