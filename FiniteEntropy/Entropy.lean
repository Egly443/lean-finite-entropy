/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Shannon entropy and Kullback–Leibler divergence of finite weights

For weights `p : ι → ℝ` on a finite set `s`, the (natural-log) Shannon entropy is
`∑ i ∈ s, negMulLog (p i)`, and the Kullback–Leibler divergence from `q` is
`∑ i ∈ s, p i * log (p i / q i)`. Mathlib has the measure-theoretic divergence
`InformationTheory.klDiv` and the real functions `Real.negMulLog`, `Real.binEntropy` and
`InformationTheory.klFun`; this file supplies the finite, counting-friendly layer that
combinatorial entropy arguments use.

## Main definitions

* `Finset.entropy s p`: the Shannon entropy `∑ i ∈ s, negMulLog (p i)`.
* `Finset.klDivergence s p q`: the Kullback–Leibler sum `∑ i ∈ s, p i * log (p i / q i)`, the
  KL divergence for probability vectors with support inclusion.

## Main statements

* `Finset.sum_sub_sum_le_klDivergence`: `∑ p - ∑ q ≤ KL(p ‖ q)` whenever `q` vanishes only where
  `p` does; hence **Gibbs' inequality** `Finset.klDivergence_nonneg`. Equivalently the generalised
  divergence `∑ (p log (p / q) - p + q)` of unnormalised weights (the finite form of Mathlib's
  `InformationTheory.klFun`) is nonnegative; the normalised form alone can be negative when the
  total masses differ.
* `Finset.eq_of_klDivergence_eq`: equality in Gibbs' inequality forces `p = q`.
* `Finset.klDivergence_uniform`: `KL(p ‖ uniform) = log |s| - H(p)` for a probability vector.
* `Finset.entropy_le_log_card`: a probability vector on `s` has entropy at most `log |s|`, with
  equality exactly for the uniform vector (`Finset.entropy_eq_log_card_iff`,
  `Finset.entropy_uniform`).
* `Finset.entropy_eq_entropy_add_sum`: the **chain rule** (grouping rule) for a map `f`.
* `Finset.entropy_le_entropy_add_log`: grouping loses at most `log B` when fibres have at most `B`
  points.
* `Finset.entropy_product_le`: **subadditivity**, the entropy of a joint distribution is at most
  the sum of the entropies of its marginals.
* `Finset.log_sum_eq_entropy_add_sum`, `Finset.entropy_add_sum_le_log_sum`: the Gibbs
  variational principle `log ∑ M = max_q (H(q) + ∑ q log M)`, attained at `q ∝ M`.
* `Finset.neg_log_sum_sq_le_entropy`: collision entropy is at most Shannon entropy.

## Implementation notes

Entropy uses natural logarithms, as `Real.binEntropy` does. Lean's conventions `log 0 = 0` and
`x / 0 = 0` make `negMulLog 0 = 0` and `0 * log (0 / q) = 0`, so no support restrictions are
needed in the definitions; the hypotheses of the theorems say where weights may vanish.

## References

* [C. E. Shannon, *A mathematical theory of communication*][Shannon1948]
* [S. Kullback, R. A. Leibler, *On information and sufficiency*][KullbackLeibler1951]
* [T. M. Cover, J. A. Thomas, *Elements of information theory*][CoverThomas2006]
-/

@[expose] public section

open Real

namespace Real

/-- The pointwise inequality behind Gibbs' inequality: `a - b ≤ a log (a / b)`. -/
theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) :
    a - b ≤ a * log (a / b) := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using hb
  have hb : 0 < b := hb.lt_of_ne fun h => ha.ne' (hab h.symm)
  have h := log_le_sub_one_of_pos (div_pos hb ha)
  rw [show a / b = (b / a)⁻¹ by rw [inv_div], log_inv]
  have : a * (b / a - 1) = b - a := by field_simp
  nlinarith

/-- Equality in the pointwise Gibbs inequality forces `a = b`. -/
theorem eq_of_mul_log_div_eq_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0)
    (h : a * log (a / b) = a - b) : a = b := by
  rcases ha.eq_or_lt with rfl | ha
  · rw [zero_mul] at h
    linarith
  have hb : 0 < b := hb.lt_of_ne fun h => ha.ne' (hab h.symm)
  by_contra hne
  have hlt := log_lt_sub_one_of_pos (div_pos hb ha) (by
    rw [Ne, div_eq_one_iff_eq ha.ne']; exact fun e => hne e.symm)
  rw [show a / b = (b / a)⁻¹ by rw [inv_div], log_inv] at h
  have : a * (b / a - 1) = b - a := by field_simp
  nlinarith

end Real

namespace Finset

variable {ι κ : Type*}

/-- The Shannon entropy (natural logarithm) of the weights `p` on `s`. -/
noncomputable def entropy (s : Finset ι) (p : ι → ℝ) : ℝ := ∑ i ∈ s, negMulLog (p i)

/-- The Kullback–Leibler sum `∑ i ∈ s, p i * log (p i / q i)` of the weights `p` against `q`.
For probability vectors with `q i = 0 → p i = 0` this is the Kullback–Leibler divergence; in
general it is a totalised real sum, not the extended divergence (see
`FiniteEntropy.KLFun` for its relation to Mathlib's `klFun`). -/
noncomputable def klDivergence (s : Finset ι) (p q : ι → ℝ) : ℝ := ∑ i ∈ s, p i * log (p i / q i)

variable {s : Finset ι} {p q : ι → ℝ}

/-- Entropy of weights in `[0, 1]` is nonnegative. -/
theorem entropy_nonneg (h0 : ∀ i ∈ s, 0 ≤ p i) (h1 : ∀ i ∈ s, p i ≤ 1) : 0 ≤ s.entropy p :=
  sum_nonneg fun i hi => negMulLog_nonneg (h0 i hi) (h1 i hi)

/-- The entropy over the empty set is `0`. -/
@[simp] theorem entropy_empty (p : ι → ℝ) : (∅ : Finset ι).entropy p = 0 := by simp [entropy]

/-- The entropy over a single point. -/
@[simp] theorem entropy_singleton (i : ι) (p : ι → ℝ) :
    ({i} : Finset ι).entropy p = negMulLog (p i) := by
  simp [entropy]

/-- Entropy only depends on the weights on `s`. -/
theorem entropy_congr (h : ∀ i ∈ s, p i = q i) : s.entropy p = s.entropy q :=
  sum_congr rfl fun i hi => by rw [h i hi]

/-- The KL sum only depends on the weights on `s`. -/
theorem klDivergence_congr {p' q' : ι → ℝ} (hp : ∀ i ∈ s, p i = p' i) (hq : ∀ i ∈ s, q i = q' i) :
    s.klDivergence p q = s.klDivergence p' q' :=
  sum_congr rfl fun i hi => by rw [hp i hi, hq i hi]

/-- Points of zero mass do not change the entropy: it can be computed on any `s ⊆ t` outside
which `p` vanishes. -/
theorem entropy_eq_of_subset {t : Finset ι} (hst : s ⊆ t) (h : ∀ i ∈ t, i ∉ s → p i = 0) :
    t.entropy p = s.entropy p :=
  (sum_subset hst fun i hi his => by rw [h i hi his, negMulLog_zero]).symm

/-- Points where `p` vanishes do not change the KL sum. -/
theorem klDivergence_eq_of_subset {t : Finset ι} (hst : s ⊆ t) (h : ∀ i ∈ t, i ∉ s → p i = 0) :
    t.klDivergence p q = s.klDivergence p q :=
  (sum_subset hst fun i hi his => by rw [h i hi his, zero_mul]).symm

/-! ### Gibbs' inequality -/

/-- `∑ p - ∑ q ≤ KL(p ‖ q)`, provided `q ≥ 0` vanishes only where `p ≥ 0` does. -/
theorem sum_sub_sum_le_klDivergence (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hpq : ∀ i ∈ s, q i = 0 → p i = 0) : ∑ i ∈ s, p i - ∑ i ∈ s, q i ≤ s.klDivergence p q := by
  rw [← sum_sub_distrib]
  exact sum_le_sum fun i hi => sub_le_mul_log_div (hp i hi) (hq i hi) (hpq i hi)

/-- **Gibbs' inequality.** If `∑ q ≤ ∑ p` (for instance both are probability vectors), then
`KL(p ‖ q) ≥ 0`. -/
theorem klDivergence_nonneg (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hpq : ∀ i ∈ s, q i = 0 → p i = 0) (hsum : ∑ i ∈ s, q i ≤ ∑ i ∈ s, p i) :
    0 ≤ s.klDivergence p q := by
  have := sum_sub_sum_le_klDivergence hp hq hpq
  linarith

/-- **Equality in Gibbs' inequality.** If `KL(p ‖ q) = ∑ p - ∑ q`, then `p = q` on `s`. -/
theorem eq_of_klDivergence_eq (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hpq : ∀ i ∈ s, q i = 0 → p i = 0)
    (h : s.klDivergence p q = ∑ i ∈ s, p i - ∑ i ∈ s, q i) : ∀ i ∈ s, p i = q i := by
  rw [klDivergence, ← sum_sub_distrib] at h
  have hle : ∀ i ∈ s, p i - q i ≤ p i * log (p i / q i) := fun i hi =>
    sub_le_mul_log_div (hp i hi) (hq i hi) (hpq i hi)
  have hzero := (sum_eq_zero_iff_of_nonneg fun i hi => sub_nonneg.mpr (hle i hi)).mp
    (by rw [sum_sub_distrib, h, sub_self])
  exact fun i hi => eq_of_mul_log_div_eq_sub (hp i hi) (hq i hi) (hpq i hi)
    (by linarith [hzero i hi])

/-! ### Entropy of probability vectors -/

/-- **Entropy as a divergence from uniform.** For a probability vector `p` on `s`,
`H(p) = log |s| - KL(p ‖ uniform)`. -/
theorem klDivergence_uniform (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1) :
    s.klDivergence p (fun _ => 1 / (#s : ℝ)) = log #s - s.entropy p := by
  have hs : s.Nonempty := nonempty_of_sum_ne_zero (by rw [hp1]; exact one_ne_zero)
  have hn : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  have hlog : log (#s : ℝ) = ∑ i ∈ s, p i * log #s := by rw [← sum_mul, hp1, one_mul]
  rw [hlog, klDivergence, entropy, ← sum_sub_distrib]
  refine sum_congr rfl fun i hi => ?_
  rcases (hp i hi).eq_or_lt with h | h
  · rw [← h]; simp
  rw [div_div_eq_mul_div, div_one, log_mul h.ne' hn.ne', negMulLog]
  ring

/-- A probability vector on `s` has entropy at most `log |s|`. -/
theorem entropy_le_log_card (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1) :
    s.entropy p ≤ log #s := by
  have hs : s.Nonempty := nonempty_of_sum_ne_zero (by rw [hp1]; exact one_ne_zero)
  have hkl := klDivergence_nonneg (q := fun _ => 1 / (#s : ℝ)) hp (fun _ _ => by positivity)
    (fun _ _ h => absurd h (by positivity)) (by
      rw [sum_const, nsmul_eq_mul, hp1]; field_simp; exact le_rfl)
  linarith [klDivergence_uniform hp hp1]

/-- The uniform vector `1 / |s|` on `s` has entropy `log |s|`. For empty `s` this is the formal
identity `0 = log 0`, not the entropy of a probability law. -/
theorem entropy_uniform (s : Finset ι) : s.entropy (fun _ => 1 / (#s : ℝ)) = log #s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hn : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  rw [entropy, sum_const, nsmul_eq_mul, negMulLog, one_div, log_inv]
  field_simp

/-- **The maximum of entropy.** A probability vector on `s` has entropy `log |s|` if and only if
it is uniform. -/
theorem entropy_eq_log_card_iff (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1) :
    s.entropy p = log #s ↔ ∀ i ∈ s, p i = 1 / #s := by
  have hs : s.Nonempty := nonempty_of_sum_ne_zero (by rw [hp1]; exact one_ne_zero)
  have hn : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  constructor
  · intro h
    refine eq_of_klDivergence_eq (q := fun _ => 1 / (#s : ℝ)) hp (fun _ _ => by positivity)
      (fun _ _ h => absurd h (by positivity)) ?_
    rw [klDivergence_uniform hp hp1, h, sub_self, hp1, sum_const, nsmul_eq_mul,
      mul_one_div_cancel hn.ne', sub_self]
  · intro h
    rw [entropy, sum_congr rfl fun i hi => by rw [h i hi]]
    exact entropy_uniform s

/-! ### The chain rule -/

/-- Rescaling: `∑ negMulLog p = negMulLog (∑ p) + (∑ p) · ∑ negMulLog (p / ∑ p)`. -/
theorem entropy_eq_negMulLog_sum_add (hp : ∀ i ∈ s, 0 ≤ p i) :
    s.entropy p = negMulLog (∑ i ∈ s, p i) +
      (∑ i ∈ s, p i) * s.entropy (fun i => p i / ∑ j ∈ s, p j) := by
  set P := ∑ i ∈ s, p i
  rcases (sum_nonneg hp).eq_or_lt with hP | hP
  · have h0 : ∀ i ∈ s, p i = 0 := (sum_eq_zero_iff_of_nonneg hp).mp hP.symm
    rw [show P = 0 from hP.symm, negMulLog_zero, zero_mul, add_zero, entropy]
    exact sum_eq_zero fun i hi => by rw [h0 i hi, negMulLog_zero]
  have key : ∀ i ∈ s, negMulLog (p i) = p i / P * negMulLog P + P * negMulLog (p i / P) := by
    intro i _
    rw [← negMulLog_mul, mul_div_cancel₀ _ hP.ne']
  rw [entropy, sum_congr rfl key, sum_add_distrib, ← sum_mul, ← sum_div, div_self hP.ne', one_mul,
    entropy, mul_sum]

/-- **The chain rule.** For a map `f`, the entropy of `p` is the entropy of the pushforward
weights plus the average entropy of the normalised fibres. -/
theorem entropy_eq_entropy_add_sum [DecidableEq κ] (f : ι → κ) (hp : ∀ i ∈ s, 0 ≤ p i) :
    s.entropy p = (s.image f).entropy (fun k => ∑ i ∈ s with f i = k, p i) +
      ∑ k ∈ s.image f, (∑ i ∈ s with f i = k, p i) *
        (s.filter (f · = k)).entropy (fun i => p i / ∑ j ∈ s with f j = k, p j) := by
  rw [entropy, ← sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem f hi), entropy,
    ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  exact entropy_eq_negMulLog_sum_add fun i hi => hp i (mem_filter.mp hi).1

/-- **Grouping costs at most `log B`.** If every fibre of `f` on `s` has at most `B` points, the
entropy of a probability vector exceeds the entropy of its pushforward by at most `log B`. -/
theorem entropy_le_entropy_add_log [DecidableEq κ] (f : ι → κ) {B : ℕ}
    (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1) (hB : ∀ k, #(s.filter (f · = k)) ≤ B) :
    s.entropy p ≤ (s.image f).entropy (fun k => ∑ i ∈ s with f i = k, p i) + log B := by
  rw [entropy_eq_entropy_add_sum f hp]
  gcongr
  have hmass : ∑ k ∈ s.image f, ∑ i ∈ s with f i = k, p i = 1 := by
    rw [sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem f hi), hp1]
  calc ∑ k ∈ s.image f, (∑ i ∈ s with f i = k, p i) *
        (s.filter (f · = k)).entropy (fun i => p i / ∑ j ∈ s with f j = k, p j)
      ≤ ∑ k ∈ s.image f, (∑ i ∈ s with f i = k, p i) * log B := by
        refine sum_le_sum fun k hk => ?_
        have hP0 : 0 ≤ ∑ i ∈ s with f i = k, p i := sum_nonneg fun i hi => hp i (mem_filter.mp hi).1
        rcases hP0.eq_or_lt with hP | hP
        · rw [← hP, zero_mul, zero_mul]
        refine mul_le_mul_of_nonneg_left ?_ hP0
        have hfib : (s.filter (f · = k)).Nonempty := by
          obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
          exact ⟨i, mem_filter.mpr ⟨hi, rfl⟩⟩
        calc _ ≤ log #(s.filter (f · = k)) := entropy_le_log_card
              (fun i hi => div_nonneg (hp i (mem_filter.mp hi).1) hP0)
              (by rw [← sum_div]; exact div_self hP.ne')
          _ ≤ log B := log_le_log (by exact_mod_cast hfib.card_pos) (by exact_mod_cast hB k)
    _ = log B := by rw [← sum_mul, hmass, one_mul]

/-! ### Subadditivity -/

/-- **Subadditivity.** The entropy of a probability vector on `s ×ˢ t` is at most the sum of the
entropies of its two marginals. -/
theorem entropy_product_le {t : Finset κ} {p : ι × κ → ℝ} (hp : ∀ x ∈ s ×ˢ t, 0 ≤ p x)
    (hp1 : ∑ x ∈ s ×ˢ t, p x = 1) :
    (s ×ˢ t).entropy p ≤
      s.entropy (fun i => ∑ j ∈ t, p (i, j)) + t.entropy (fun j => ∑ i ∈ s, p (i, j)) := by
  set m : ι → ℝ := fun i => ∑ j ∈ t, p (i, j)
  have hm0 : ∀ i ∈ s, 0 ≤ m i := fun i hi =>
    sum_nonneg fun j hj => hp (i, j) (mem_product.mpr ⟨hi, hj⟩)
  have hm1 : ∑ i ∈ s, m i = 1 := by rw [← hp1, sum_product]
  -- the chain rule along the first coordinate
  have hchain : (s ×ˢ t).entropy p =
      s.entropy m + ∑ i ∈ s, m i * t.entropy (fun j => p (i, j) / m i) := by
    rw [entropy, sum_product, entropy, ← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    exact entropy_eq_negMulLog_sum_add fun j hj => hp (i, j) (mem_product.mpr ⟨hi, hj⟩)
  rw [hchain, add_le_add_iff_left]
  -- conditioning reduces entropy: Jensen for the concave `negMulLog` in each column
  calc ∑ i ∈ s, m i * t.entropy (fun j => p (i, j) / m i)
      = ∑ j ∈ t, ∑ i ∈ s, m i • negMulLog (p (i, j) / m i) := by
        simp only [entropy, mul_sum, smul_eq_mul]
        exact sum_comm
    _ ≤ ∑ j ∈ t, negMulLog (∑ i ∈ s, m i • (p (i, j) / m i)) := by
        refine sum_le_sum fun j hj => concaveOn_negMulLog.le_map_sum hm0 hm1 fun i hi => ?_
        exact div_nonneg (hp (i, j) (mem_product.mpr ⟨hi, hj⟩)) (hm0 i hi)
    _ = t.entropy (fun j => ∑ i ∈ s, p (i, j)) := by
        refine sum_congr rfl fun j hj => congrArg negMulLog (sum_congr rfl fun i hi => ?_)
        rw [smul_eq_mul]
        rcases (hm0 i hi).eq_or_lt with h | h
        · have : p (i, j) = 0 := by
            have := (sum_eq_zero_iff_of_nonneg fun j' hj' =>
              hp (i, j') (mem_product.mpr ⟨hi, hj'⟩)).mp h.symm j hj
            exact this
          rw [← h, this]; simp
        · exact mul_div_cancel₀ _ h.ne'

/-! ### The Gibbs variational principle -/

/-- For positive weights `M` with total `W`, `log W = H(M / W) + ∑ (M / W) log M`. -/
theorem log_sum_eq_entropy_add_sum {M : ι → ℝ} (hM : ∀ i ∈ s, 0 < M i) (hs : s.Nonempty) :
    log (∑ i ∈ s, M i) = s.entropy (fun i => M i / ∑ j ∈ s, M j) +
      ∑ i ∈ s, M i / (∑ j ∈ s, M j) * log (M i) := by
  set W := ∑ j ∈ s, M j
  have hW : 0 < W := sum_pos hM hs
  rw [entropy, ← sum_add_distrib]
  have : ∀ i ∈ s, negMulLog (M i / W) + M i / W * log (M i) = M i / W * log W := by
    intro i hi
    rw [negMulLog, log_div (hM i hi).ne' hW.ne']
    ring
  rw [sum_congr rfl this, ← sum_mul, ← sum_div, div_self hW.ne', one_mul]

/-- **The Gibbs variational principle.** For a probability vector `q` and positive weights `M`,
`H(q) + ∑ q log M ≤ log ∑ M`. -/
theorem entropy_add_sum_le_log_sum {M : ι → ℝ} (hM : ∀ i ∈ s, 0 < M i)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hq1 : ∑ i ∈ s, q i = 1) :
    s.entropy q + ∑ i ∈ s, q i * log (M i) ≤ log (∑ i ∈ s, M i) := by
  have hs : s.Nonempty := nonempty_of_sum_ne_zero (by rw [hq1]; exact one_ne_zero)
  set W := ∑ j ∈ s, M j
  have hW : 0 < W := sum_pos hM hs
  have hkl := klDivergence_nonneg (q := fun i => M i / W) hq (fun i hi => (div_pos (hM i hi) hW).le)
    (fun i hi h => absurd h (div_pos (hM i hi) hW).ne') (by rw [← sum_div, div_self hW.ne', hq1])
  have : s.klDivergence q (fun i => M i / W) =
      log W - (s.entropy q + ∑ i ∈ s, q i * log (M i)) := by
    have hlog : log W = ∑ i ∈ s, q i * log W := by rw [← sum_mul, hq1, one_mul]
    rw [hlog, klDivergence, entropy, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i hi => ?_
    rcases (hq i hi).eq_or_lt with h | h
    · rw [← h]; simp
    rw [div_div_eq_mul_div, log_div (mul_pos h hW).ne' (hM i hi).ne', log_mul h.ne' hW.ne',
      negMulLog]
    ring
  linarith

/-! ### Collision entropy -/

/-- **Collision entropy is at most Shannon entropy**: `-log ∑ p² ≤ H(p)` for a probability
vector `p`. -/
theorem neg_log_sum_sq_le_entropy (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1) :
    -log (∑ i ∈ s, p i ^ 2) ≤ s.entropy p := by
  classical
  set t := s.filter fun i => 0 < p i
  have hzero : ∀ i ∈ s, i ∉ t → p i = 0 := fun i hi hit =>
    le_antisymm (not_lt.mp fun h => hit (mem_filter.mpr ⟨hi, h⟩)) (hp i hi)
  have ht1 : ∑ i ∈ t, p i = 1 := by
    rw [← hp1]; exact sum_filter_of_ne fun i hi h => lt_of_le_of_ne (hp i hi) (Ne.symm h)
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := t) (w := p) (p := p)
    (fun i hi => (mem_filter.mp hi).2.le) ht1 fun i hi => (mem_filter.mp hi).2
  simp only [smul_eq_mul] at hjensen
  have hsq : ∑ i ∈ t, p i * p i = ∑ i ∈ s, p i ^ 2 := by
    rw [sum_filter_of_ne fun i hi h => ?_]
    · exact sum_congr rfl fun i _ => (sq _).symm
    · rcases (hp i hi).eq_or_lt with h' | h'
      · rw [← h'] at h; simp at h
      · exact h'
  have hent : s.entropy p = -∑ i ∈ t, p i * log (p i) := by
    rw [entropy, ← sum_neg_distrib]
    simp only [negMulLog, neg_mul]
    exact (sum_subset (filter_subset _ s) fun i hi hit => by rw [hzero i hi hit]; simp).symm
  rw [hent, ← hsq]
  linarith

end Finset
