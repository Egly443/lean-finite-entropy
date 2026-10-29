/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import FiniteEntropy.Entropy
public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# The finite KL sum and Mathlib's `klFun`

`Finset.klDivergence s p q = ∑ i ∈ s, p i * log (p i / q i)` is the Kullback–Leibler divergence of
probability vectors with `q i = 0 → p i = 0`. For general nonnegative weights, Mathlib's
measure-theoretic divergence `InformationTheory.klDiv` is the *generalised* divergence
`∫ klFun (dμ/dν) dν`, with `klFun x = x log x + 1 - x`, which adds the mass difference
`∑ q - ∑ p`. This file proves the finite form of that identity, so the two notions are related
explicitly rather than by name.

Without support inclusion the raw sum is not a divergence: for point masses on two different
points it is `0`, while `klDiv` is `∞`. Every inequality in this library about
`Finset.klDivergence` carries the support hypothesis.

## Main statements

* `Finset.klDivergence_add_sum_sub_sum`: under support inclusion,
  `KL(p ‖ q) + ∑ q - ∑ p = ∑ i ∈ s, q i * klFun (p i / q i)`.
* `Finset.klDivergence_eq_sum_mul_klFun`: for weights of equal total mass (for example
  probability vectors) the raw sum is the generalised divergence.
-/

public section

open Real InformationTheory

namespace Finset

variable {ι : Type*} {s : Finset ι} {p q : ι → ℝ}

/-- Under support inclusion, the finite KL sum plus the mass difference is the `klFun` form of the
generalised divergence (the integrand of `InformationTheory.toReal_klDiv_eq_integral_klFun`). -/
theorem klDivergence_add_sum_sub_sum (hpq : ∀ i ∈ s, q i = 0 → p i = 0) :
    s.klDivergence p q + ∑ i ∈ s, q i - ∑ i ∈ s, p i = ∑ i ∈ s, q i * klFun (p i / q i) := by
  rw [klDivergence, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i hi => ?_
  by_cases h : q i = 0
  · simp [h, hpq i hi h]
  have hx : q i * (p i / q i) = p i := by field_simp
  rw [klFun_apply]
  linear_combination (1 - log (p i / q i)) * hx

/-- For weights of equal total mass (for example two probability vectors), under support inclusion
the finite KL sum is the generalised divergence `∑ i ∈ s, q i * klFun (p i / q i)`. -/
theorem klDivergence_eq_sum_mul_klFun (hpq : ∀ i ∈ s, q i = 0 → p i = 0)
    (hmass : ∑ i ∈ s, p i = ∑ i ∈ s, q i) :
    s.klDivergence p q = ∑ i ∈ s, q i * klFun (p i / q i) := by
  rw [← klDivergence_add_sum_sub_sum hpq, hmass, add_sub_cancel_right]

end Finset
