/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Sum

/-!
# Binomial coefficients and binary entropy

With `H = Real.binEntropy` (natural logarithm), for natural numbers `k ≤ n` the binomial
coefficient `C(n, k)` is `exp (n H(k / n))` up to a polynomial factor:

`exp (n H(k / n)) / (n + 1) ≤ C(n, k) ≤ exp (n H(k / n))`.

Both bounds come from the binomial expansion of `(p + (1 - p)) ^ n` with `p = k / n`: every term
is at most the total `1`, and the term with index `k` is the largest of the `n + 1` terms. The same
expansion bounds the volume of a Hamming ball: for `2k ≤ n`, `∑ j ≤ k, C(n, j) ≤ exp (n H(k / n))`.

## Main statements

* `Real.log_choose_le_mul_binEntropy`: `log C(n, k) ≤ n H(k / n)`.
* `Real.choose_le_exp_mul_binEntropy`: `C(n, k) ≤ exp (n H(k / n))`.
* `Real.exp_mul_binEntropy_le_choose`: `exp (n H(k / n)) ≤ (n + 1) C(n, k)`.
* `Real.sum_choose_le_exp_mul_binEntropy`: the Hamming-ball bound.

## References

* [T. M. Cover, J. A. Thomas, *Elements of information theory*][CoverThomas2006]
-/

@[expose] public section

open Finset

namespace Real

/-- The binomial term `C(n, j) p ^ j (1 - p) ^ (n - j)`. -/
private noncomputable def term (n j : ℕ) (p : ℝ) : ℝ := n.choose j * p ^ j * (1 - p) ^ (n - j)

private theorem term_nonneg (n j : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ term n j p := by
  unfold term
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- The binomial terms sum to `1`. -/
private theorem sum_term (n : ℕ) (p : ℝ) : ∑ j ∈ range (n + 1), term n j p = 1 := by
  have := (add_pow p (1 - p) n).symm
  rw [add_sub_cancel, one_pow] at this
  rw [← this]
  exact sum_congr rfl fun j _ => by unfold term; ring

/-- For `0 < k < n` and `p = k / n`, `p ^ k (1 - p) ^ (n - k) = exp (-n H(p))`. -/
private theorem pow_mul_pow_eq_exp {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) = exp (-(n * binEntropy ((k : ℝ) / n))) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hp : 0 < (k : ℝ) / n := by positivity
  have hq : 0 < 1 - (k : ℝ) / n := by
    rw [sub_pos, div_lt_one hn]; exact_mod_cast hkn
  have key : -(n * binEntropy ((k : ℝ) / n)) =
      log (((k : ℝ) / n) ^ k) + log ((1 - (k : ℝ) / n) ^ (n - k)) := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog, log_pow, log_pow,
      Nat.cast_sub hkn.le]
    field_simp
    ring
  rw [key, exp_add, exp_log (pow_pos hp k), exp_log (pow_pos hq _)]

/-- For `0 < k < n` and `p = k / n`, the `k`-th binomial term is `C(n, k) / exp (n H(p))`. -/
private theorem term_eq {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    term n k ((k : ℝ) / n) = n.choose k / exp (n * binEntropy ((k : ℝ) / n)) := by
  rw [term, mul_assoc, pow_mul_pow_eq_exp hk hkn, exp_neg]
  exact (div_eq_mul_inv _ _).symm

/-- **The binomial coefficient is at most `exp (n H(k / n))`.** -/
theorem choose_le_exp_mul_binEntropy {n k : ℕ} (hkn : k ≤ n) :
    (n.choose k : ℝ) ≤ exp (n * binEntropy ((k : ℝ) / n)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases hkn.eq_or_lt with rfl | hkn
  · have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp [div_self this]
  have hn : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hp1 : (k : ℝ) / n ≤ 1 := by rw [div_le_one hn]; exact_mod_cast hkn.le
  have hle : term n k ((k : ℝ) / n) ≤ 1 := by
    rw [← sum_term n ((k : ℝ) / n)]
    exact single_le_sum (fun j _ => term_nonneg n j (by positivity) hp1)
      (mem_range.mpr (by omega))
  rwa [term_eq hk hkn, div_le_one (exp_pos _)] at hle

/-- **`log C(n, k) ≤ n H(k / n)`.** -/
theorem log_choose_le_mul_binEntropy {n k : ℕ} (hkn : k ≤ n) :
    log (n.choose k) ≤ n * binEntropy ((k : ℝ) / n) := by
  rw [← log_exp (n * binEntropy _)]
  exact log_le_log (by exact_mod_cast Nat.choose_pos hkn) (choose_le_exp_mul_binEntropy hkn)

/-- The ratio of consecutive binomial terms: `T (j + 1) (j + 1) (1 - p) = T j (n - j) p`. -/
private theorem term_succ (n j : ℕ) (p : ℝ) (hj : j < n) :
    term n (j + 1) p * ((j + 1) * (1 - p)) = term n j p * ((n - j : ℕ) * p) := by
  have hc : ((n.choose (j + 1) : ℕ) : ℝ) * (j + 1) = n.choose j * (n - j : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq n j
  have hpow : (1 - p) ^ (n - j) = (1 - p) ^ (n - (j + 1)) * (1 - p) := by
    rw [← pow_succ, show n - (j + 1) + 1 = n - j by omega]
  unfold term
  rw [hpow, pow_succ]
  linear_combination (p ^ j * p * (1 - p) ^ (n - (j + 1)) * (1 - p)) * hc

/-- For `p = k / n`, the binomial term with index `k` is the largest. -/
private theorem term_le_term {n k : ℕ} (hk : 0 < k) (hkn : k < n) (j : ℕ) (hj : j ≤ n) :
    term n j ((k : ℝ) / n) ≤ term n k ((k : ℝ) / n) := by
  set p := (k : ℝ) / n
  have hn : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn
  have hp : 0 < p := by positivity
  have hp1 : p < 1 := by rw [div_lt_one hn]; exact_mod_cast hkn
  have hnp : (n : ℝ) * p = k := by simp only [p]; field_simp
  have hT : ∀ i, 0 ≤ term n i p := fun i => term_nonneg n i hp.le hp1.le
  -- increasing below `k`
  have up : ∀ i, i < k → term n i p ≤ term n (i + 1) p := by
    intro i hi
    have h := term_succ n i p (by omega)
    have hik : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
    have hcmp : ((i : ℝ) + 1) * (1 - p) ≤ ((n - i : ℕ) : ℝ) * p := by
      rw [Nat.cast_sub (by omega : i ≤ n)]
      nlinarith
    have hpos : 0 < ((i : ℝ) + 1) * (1 - p) := mul_pos (by positivity) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hcmp (hT i), hT (i + 1)]
  -- decreasing from `k` on
  have down : ∀ i, k ≤ i → i < n → term n (i + 1) p ≤ term n i p := by
    intro i hi hin
    have h := term_succ n i p hin
    have hik : (k : ℝ) ≤ i := by exact_mod_cast hi
    have hcmp : ((n - i : ℕ) : ℝ) * p ≤ ((i : ℝ) + 1) * (1 - p) := by
      rw [Nat.cast_sub hin.le]
      nlinarith
    have hpos : 0 < ((i : ℝ) + 1) * (1 - p) := mul_pos (by positivity) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hcmp (hT i), hT (i + 1)]
  have climb : ∀ d i, i + d = k → term n i p ≤ term n k p := by
    intro d
    induction d with
    | zero => intro i h; rw [show i = k by omega]
    | succ d ih => intro i h; exact (up i (by omega)).trans (ih (i + 1) (by omega))
  have descend : ∀ d, k + d ≤ n → term n (k + d) p ≤ term n k p := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro h
      exact (down (k + d) (by omega) (by omega)).trans (ih (by omega))
  rcases le_or_gt j k with hjk | hjk
  · exact climb (k - j) j (by omega)
  · simpa [show k + (j - k) = j by omega] using descend (j - k) (by omega)

/-- **`exp (n H(k / n)) ≤ (n + 1) C(n, k)`**: the binomial coefficient is within a factor `n + 1`
of `exp (n H(k / n))`. -/
theorem exp_mul_binEntropy_le_choose {n k : ℕ} (hkn : k ≤ n) :
    exp (n * binEntropy ((k : ℝ) / n)) ≤ (n + 1) * n.choose k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [CharP.cast_eq_zero, zero_div, binEntropy_zero, mul_zero, exp_zero,
      Nat.choose_zero_right, Nat.cast_one, mul_one]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  rcases hkn.eq_or_lt with rfl | hkn
  · have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [div_self this, binEntropy_one, mul_zero, exp_zero, Nat.choose_self, Nat.cast_one,
      mul_one]
    linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hsum : 1 ≤ (n + 1) * term n k ((k : ℝ) / n) := by
    have h1 := sum_term n ((k : ℝ) / n)
    have h2 : ∑ j ∈ range (n + 1), term n j ((k : ℝ) / n) ≤ (n + 1) * term n k ((k : ℝ) / n) :=
      calc ∑ j ∈ range (n + 1), term n j ((k : ℝ) / n)
          ≤ ∑ _j ∈ range (n + 1), term n k ((k : ℝ) / n) :=
            sum_le_sum fun j hj => term_le_term hk hkn j (Nat.lt_succ_iff.mp (mem_range.mp hj))
        _ = (n + 1) * term n k ((k : ℝ) / n) := by
            rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    linarith
  rwa [term_eq hk hkn, mul_div_assoc', one_le_div (exp_pos _)] at hsum

/-- **The Hamming-ball bound.** If `2k ≤ n`, then `∑ j ≤ k, C(n, j) ≤ exp (n H(k / n))`. -/
theorem sum_choose_le_exp_mul_binEntropy {n k : ℕ} (hkn : 2 * k ≤ n) :
    ∑ j ∈ range (k + 1), (n.choose j : ℝ) ≤ exp (n * binEntropy ((k : ℝ) / n)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hkn' : k < n := by omega
  set p := (k : ℝ) / n
  have hn : (0 : ℝ) < n := by exact_mod_cast hk.trans hkn'
  have hp : 0 < p := by positivity
  have hnp : (n : ℝ) * p = k := by simp only [p]; field_simp
  have hp2 : p ≤ 1 - p := by
    have : (2 * k : ℝ) ≤ n := by exact_mod_cast hkn
    nlinarith
  have hq : 0 < 1 - p := hp.trans_le hp2
  -- each term with `j ≤ k` dominates `C(n, j)` times the `k`-th power product
  have hmono : ∀ j ∈ range (k + 1),
      (n.choose j : ℝ) * (p ^ k * (1 - p) ^ (n - k)) ≤ term n j p := by
    intro j hj
    have hj := Nat.lt_succ_iff.mp (mem_range.mp hj)
    unfold term
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [show n - j = n - (j + d) + d by omega, pow_add, pow_add]
    have := pow_le_pow_left₀ hp.le hp2 d
    have h1 := pow_pos hp j
    have h2 := pow_pos hq (n - (j + d))
    have h12 := mul_pos h1 h2
    calc p ^ j * p ^ d * (1 - p) ^ (n - (j + d)) = p ^ j * (1 - p) ^ (n - (j + d)) * p ^ d := by
          ring
      _ ≤ p ^ j * (1 - p) ^ (n - (j + d)) * (1 - p) ^ d := mul_le_mul_of_nonneg_left this h12.le
      _ = _ := by ring
  have hle : (∑ j ∈ range (k + 1), (n.choose j : ℝ)) * (p ^ k * (1 - p) ^ (n - k)) ≤ 1 := by
    have h1 := sum_term n p
    rw [sum_mul]
    refine ((sum_le_sum hmono).trans (sum_le_sum_of_subset_of_nonneg
      (fun x hx => by simp only [mem_range] at hx ⊢; omega)
      fun j _ _ => term_nonneg n j hp.le (by linarith))).trans h1.le
  rw [pow_mul_pow_eq_exp hk hkn', exp_neg, ← div_eq_mul_inv, div_le_one (exp_pos _)] at hle
  exact hle

end Real
