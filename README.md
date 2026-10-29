# Entropy and KL divergence on finite types

[![CI](https://github.com/Egly443/lean-finite-entropy/actions/workflows/ci.yml/badge.svg)](https://github.com/Egly443/lean-finite-entropy/actions/workflows/ci.yml)

A Lean 4 library of finite information theory for counting proofs: Shannon entropy and
Kullback–Leibler divergence of finitely supported weights, Gibbs' inequality with its equality
case, maximum entropy, the chain rule and fibre bound, subadditivity, the Gibbs variational
principle, collision entropy, and the entropy estimates for binomial coefficients and Hamming
balls.

It is a **Mathlib-ready strawman**, written to Mathlib's conventions and offered for reuse as is,
by people and by AI systems. Anyone in the Mathlib community may upstream it, in whole or in part,
if and when they choose. The author does not plan to drive it through Mathlib review.

**Provenance:** AI-generated with human guidance. Every file:

* builds with no `sorry` and no warnings;
* uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`);
* passes Mathlib's `#lint`, `runLinter` and `lint-style`, and the `linter.mathlibStandardSet`
  linters;
* depends only on Mathlib;
* meets [LeanPool](https://github.com/LeanPool/lean-pool)'s content rules (file headers, no
  waivers or `set_option`).

Licensed under Apache 2.0.

Entropy uses natural logarithms, as `Real.binEntropy` does. Weights are functions `p : ι → ℝ` on a
`Finset ι`; the hypotheses of each theorem say when they must be nonnegative or sum to `1`.

## Using it

The library is pinned to Lean and Mathlib `v4.35.0-rc3` (see `lean-toolchain` and
`lakefile.toml`). To depend on it, add to your `lakefile.toml`:

```toml
[[require]]
name = "finite_entropy"
git = "https://github.com/Egly443/lean-finite-entropy"
rev = "main"
```

and `import FiniteEntropy`, or import individual modules. To build it, run `lake exe cache get`
and then `lake build`.

Releases are tagged `vX.Y.Z` from `main` by the manually triggered `Release` workflow
(`.github/workflows/release.yml`).

## Contents

| File | Main results |
|---|---|
| `FiniteEntropy/Entropy.lean` | `Finset.entropy s p = ∑ i ∈ s, negMulLog (p i)` and `Finset.klDivergence s p q = ∑ i ∈ s, p i * log (p i / q i)`. **Gibbs' inequality** in unnormalised form, `∑ p - ∑ q ≤ KL(p ‖ q)` (`sum_sub_sum_le_klDivergence`, pointwise `Real.sub_le_mul_log_div`), hence `klDivergence_nonneg`, with the equality case `eq_of_klDivergence_eq` (pointwise `Real.eq_of_mul_log_div_eq_sub`). **Entropy as divergence from uniform** `klDivergence_uniform`: `KL(p ‖ uniform) = log |s| - H(p)`. **Maximum entropy**: `entropy_le_log_card`, `entropy_uniform`, `entropy_eq_log_card_iff` (equality only for the uniform vector). The **chain rule** `entropy_eq_entropy_add_sum` for a map `f` (pushforward entropy plus average fibre entropy), its rescaling form `entropy_eq_negMulLog_sum_add`, and the **fibre bound** `entropy_le_entropy_add_log` (fibres of size at most `B` cost at most `log B`). **Subadditivity** `entropy_product_le`: `H(X, Y) ≤ H(X) + H(Y)`. **Gibbs variational principle** `log_sum_eq_entropy_add_sum`, `entropy_add_sum_le_log_sum`: `log ∑ M = max_q (H(q) + ∑ q log M)`. **Collision entropy** `neg_log_sum_sq_le_entropy`: `-log ∑ p² ≤ H(p)`. Also `entropy_nonneg`, `entropy_empty`. |
| `FiniteEntropy/Binomial.lean` | For natural numbers `k ≤ n`: `Real.log_choose_le_mul_binEntropy` (`log C(n, k) ≤ n H(k / n)`), `Real.choose_le_exp_mul_binEntropy` (`C(n, k) ≤ exp (n H(k / n))`), the matching lower bound `Real.exp_mul_binEntropy_le_choose` (`exp (n H(k / n)) ≤ (n + 1) C(n, k)`), and the **Hamming-ball bound** `Real.sum_choose_le_exp_mul_binEntropy` (`∑ j ≤ k, C(n, j) ≤ exp (n H(k / n))` for `2k ≤ n`). |
| `FiniteEntropy/KLFun.lean` | **Relation to Mathlib's generalised divergence.** `Finset.klDivergence_add_sum_sub_sum`: under support inclusion, `KL(p ‖ q) + ∑ q - ∑ p = ∑ q klFun (p / q)` with Mathlib's `InformationTheory.klFun x = x log x + 1 - x` (the finite form of `toReal_klDiv_eq_integral_klFun`); `Finset.klDivergence_eq_sum_mul_klFun` for equal masses. Separate from `Entropy.lean` because `klFun` imports measure theory. |

Everything in `Entropy.lean` rests on one pointwise fact, `a - b ≤ a log (a / b)` (from
`log x ≤ x - 1`), and on the rescaling identity `negMulLog (P x) = x negMulLog P + P negMulLog x`
(Mathlib's `negMulLog_mul`). Subadditivity uses Jensen's inequality for the concave `negMulLog`
column by column. The binomial bounds come from the binomial expansion of `(p + (1 - p)) ^ n` with
`p = k / n`: every term is at most `1`, the `k`-th term is the largest (a ratio argument), and for
`p ≤ 1/2` the terms with `j ≤ k` dominate `C(n, j) p^k (1 - p)^(n - k)`.

## Notes for anyone upstreaming to Mathlib

* **Placement.** `Entropy.lean` would go to `Mathlib/InformationTheory/Entropy/Finite.lean` (or
  next to `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`), and `Binomial.lean` next to
  `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean`.
* **Lemmas that belong elsewhere.** `Real.sub_le_mul_log_div` and `Real.eq_of_mul_log_div_eq_sub`
  belong in `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`, next to
  `self_sub_one_le_mul_log`.
* **Names.** `Finset.klDivergence` rather than `klDiv`, which Mathlib uses for measures in the
  `InformationTheory` namespace.
* **Overlap with Mathlib.** No finite entropy. `InformationTheory.klFun x = x log x + 1 - x` is
  the integrand of the generalised divergence; `sum_sub_sum_le_klDivergence` is its finite sum
  form. Mathlib's `InformationTheory.klDiv` for measures has the chain rule
  (`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean`) and, from `v4.35`, the
  data-processing inequality (`.../DataProcessing.lean`). `Finset.klDivergence` is **not** the
  value of `klDiv` on finitely supported weights: `klDiv` is the generalised divergence, which
  adds `∑ q - ∑ p` and is `∞` without absolute continuity, while the raw real sum here is, for
  example, `0` for point masses on two different points and `-log 2` for `p = 1, q = 2` on one
  point. Under nonnegativity and support inclusion, `klDivergence_add_sum_sub_sum` (in
  `KLFun.lean`) proves `KL(p ‖ q) + ∑ q - ∑ p = ∑ q klFun (p / q)`, the finite form of
  `toReal_klDiv_eq_integral_klFun`, and for equal masses (probability vectors) the correction
  vanishes (`klDivergence_eq_sum_mul_klFun`). The measure statement itself, `klDiv` of the atomic
  measures, is not proved here. Every Gibbs-type theorem in this package carries the support
  hypothesis.
* **Pending Mathlib work.** mathlib4 PR #34773 ("Adds generic Shannon Entropy definition over
  PMF") defines Shannon entropy of a `PMF`; it was open in February 2026 and is not in this
  package's Mathlib. If it lands, `Finset.entropy s p` is its value
  on a `PMF` supported on `s`, and the results here would be restated for it. On the Lean Zulip
  (*new members*, "generic shannon entropy formalization mathlib4", February 2026) Rémy Degenne
  suggested deriving finite entropy from `klDiv` through `H(P) = log N - KL(P ‖ uniform)`; that
  identity is `klDivergence_uniform` here.
* **Design questions.** Weights on a `Finset` rather than `PMF` or `Measure`: counting proofs
  manipulate partial sums and fibres, and a `Finset` index keeps the vertex type fixed. A `PMF`
  layer would be a thin wrapper. Mathlib reviewers have preferred defining probabilistic notions
  for measures and deriving the discrete case (Zulip thread above; Degenne's "mathlib-only approach
  to entropy" in the PFR stream, 2023, defines `measureEntropy` and conditional entropy that way),
  so a reviewer may ask for this package as the finite-sum layer under such a definition.
* **Older Mathlib.** None.

## Relation to other libraries

TauCeti has relative entropy for transport plans (`TauCeti.relEntropy...` in optimal transport)
and inequalities for `x log x`, but no finite Shannon entropy API. [LeanPool](https://github.com/LeanPool/lean-pool)'s `channel-capacity`
project works with Markov kernels and measure-theoretic divergence, and `runs-of-multiples` has a
project-specific entropy of a map on a finite set of naturals. Neither has the chain rule,
subadditivity or the binomial bounds as reusable statements.

The Polynomial Freiman–Ruzsa project (`teorth/pfr`, `PFR/ForMathlib/Entropy`) has a full
measure-theoretic entropy library for random variables on finite types (chain rule, conditional
entropy, submodularity), written for that proof and not upstreamed as of May 2025 (Zulip,
*Polynomial Freiman-Ruzsa conjecture*, "Has Entropy been upstreamed to Mathlib"). LeanPool already
carries a copy of it inside its `zhang-yeung-inequality` project
(`LeanPool/ZhangYeungInequality/PFR/ForMathlib/Entropy/`, LeanPool at `edbe5bd`), including
`ProbabilityTheory.entropy_eq_sum_finset` (the entropy of a finite-range random variable as a
finite `negMulLog` sum of its law), `ProbabilityTheory.chain_rule` (`H[X, Y] = H[Y] + H[X | Y]`)
and `ProbabilityTheory.entropy_pair_le_add` (subadditivity). Those are statements about random
variables on a probability space and normalised laws; this package states the same facts for
unnormalised finite weight vectors (the grouping identity `entropy_eq_entropy_add_sum` allows any
total mass), adds the Gibbs, maximum-entropy, variational and collision results in that form, and
the binomial bounds, which neither has. No bridge between the two is proved; a user with random
variables should use the PFR API. This package is not derived from it.

## Not included

* Shearer's lemma and Han's inequality: they need entropy of sub-vectors indexed by subsets, a
  larger API.
* Entropy of random variables (as in the PFR project) and a bridge to Mathlib's measure-theoretic
  `InformationTheory.klDiv` through `PMF.toMeasure`: the measure-theoretic identification is a
  separate task; this package stays finite.
* Entropy telescoping over trees and Rényi entropies beyond order 2: they iterate the chain rule
  here and are not standard named results.

## Citation

The mathematics is standard; the works below are its sources. BibTeX entries for Mathlib's
`docs/references.bib` are in `references.bib`, each checked against zbMATH and normalised with the
`bibtool` command from Mathlib's `scripts/lint-bib.sh`.

* C. E. Shannon, *A mathematical theory of communication*, Bell Syst. Tech. J. 27 (1948),
  379–423 and 623–656, doi:10.1002/j.1538-7305.1948.tb01338.x.
* S. Kullback, R. A. Leibler, *On information and sufficiency*, Ann. Math. Statist. 22 (1951),
  79–86, doi:10.1214/aoms/1177729694.
* T. M. Cover, J. A. Thomas, *Elements of information theory*, 2nd ed., Wiley-Interscience, 2006,
  doi:10.1002/047174882X.
