/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import FiniteEntropy.Binomial
public import FiniteEntropy.Entropy
public import FiniteEntropy.KLFun

/-!
# Entropy and KL divergence on finite types

Imports every module of the library: Shannon entropy and the Kullback–Leibler sum of finite weights
with Gibbs' inequality, the chain rule, subadditivity and the Gibbs variational principle
(`Entropy`), the relation of the KL sum to Mathlib's `klFun` (`KLFun`), and the binomial–entropy
bounds (`Binomial`).
-/
