/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.FlatMixture.Internal

/-!
# Decomposing a capped finite source into flat sources

A nonnegative probability vector with every point mass at most `1 / K` is
exactly a normalized nonnegative mixture of uniform `K`-element supports.
The weights are indexed by those supports, so repeated components have
already been combined. The hypotheses imply that the finite ambient type
has at least `K` elements; no separate cardinality assumption is needed.

The proof completes the probability vector to a doubly stochastic matrix
and applies the Birkhoff--von Neumann theorem from Mathlib, formalized by
Bhavik Mehta in `Mathlib.Analysis.Convex.Birkhoff`. This is a finite existence
theorem, without a computational claim for the mixture weights.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open scoped Classical in
/-- A normalized source capped at `1 / K` is an exact convex mixture of
uniform supports of cardinality `K`. The positive threshold excludes division
by zero; empty ambient types cannot satisfy normalization. -/
theorem exists_flat_mixture_of_capped_weights {α : Type*} [Fintype α]
    (p : α → ℝ) {K : Nat} (positive : 0 < K) (nonnegative : ∀ x, 0 ≤ p x)
    (mass : ∑ x, p x = 1) (cap : ∀ x, (K : ℝ) * p x ≤ 1) :
    ∃ w : {S : Finset α // S.card = K} → ℝ,
      (∀ S, 0 ≤ w S) ∧ (∑ S, w S) = 1 ∧
      ∀ x, p x = ∑ S, w S * (if x ∈ S.val then (K : ℝ)⁻¹ else 0) :=
  Internal.exists_flat_mixture_of_capped_weights p positive nonnegative mass cap

end Algebraic.Cutwidth.Extractor
