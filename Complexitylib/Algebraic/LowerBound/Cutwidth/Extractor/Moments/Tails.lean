/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Defs
public import Mathlib.Analysis.Real.Sqrt
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Tails.Internal

/-!
# Both sign-sum tails from low-order parity bias

The budget `100 * m² * δ ≤ 1` lets the first four parity-bias moment bounds
satisfy the quartic certificate in `FourthMoment`. Each tail beyond one eighth
of the square root of `m` has weighted mass at least `1/36`.

This normalization is a direct deduction from the checked moment bounds and
quartic estimate. Deriving parity bias from the source reduction of
Chattopadhyay and Liao, *Extractors for Sum of Two Sources* (2021), Lemma 5.4,
equation (5), remains a separate theorem.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Sufficiently small parity bias forces a positive sign-sum tail of mass
at least `1/36`, beyond one eighth of `sqrt m`. -/
theorem signSum_positive_tail_of_parityBias {α : Type*} {m : Nat} {s : Finset α}
    {w : α → ℝ} {σ : α → Fin m → ℝ} {δ : ℝ}
    (hw : ∀ a ∈ s, 0 ≤ w a) (hmass : ∑ a ∈ s, w a = 1) (hm : 0 < m)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (hδ : 0 ≤ δ) (hbudget : 100 * (m : ℝ) ^ 2 * δ ≤ 1)
    (h : ParityBiasBound s w σ δ) :
    (1 / 36 : ℝ) ≤ ∑ a ∈ s,
      if Real.sqrt (m : ℝ) / 8 < signSum σ a then w a else 0 :=
  (Internal.signSum_tails_of_parityBias hw hmass hm hσ hδ hbudget h).1

/-- The same parity-bias budget forces the corresponding negative sign-sum
tail, with the same mass and threshold. -/
theorem signSum_negative_tail_of_parityBias {α : Type*} {m : Nat} {s : Finset α}
    {w : α → ℝ} {σ : α → Fin m → ℝ} {δ : ℝ}
    (hw : ∀ a ∈ s, 0 ≤ w a) (hmass : ∑ a ∈ s, w a = 1) (hm : 0 < m)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (hδ : 0 ≤ δ) (hbudget : 100 * (m : ℝ) ^ 2 * δ ≤ 1)
    (h : ParityBiasBound s w σ δ) :
    (1 / 36 : ℝ) ≤ ∑ a ∈ s,
      if signSum σ a < -(Real.sqrt (m : ℝ) / 8) then w a else 0 :=
  (Internal.signSum_tails_of_parityBias hw hmass hm hσ hδ hbudget h).2

end Algebraic.Cutwidth.Extractor
