/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Envelope

/-!
# Original-source envelopes throughout actual affine iteration

The named envelopes follow the exact observation kernels. Their caps
remain bounds on the original source coordinates, and their sums grow by
the second and fourth powers of the short-message alphabet per round.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

variable {n d h t L : Nat} {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]

theorem affineIterationState_leftEnvelope_cap
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (μ : Z → ℝ)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z))
    (cap : ∀ z x₀, s.weight z * mapWeight (s.source z) (s.left z) x₀ ≤ μ z)
    (z : AffineIterationTranscript Z t L i) (x₀ : Fin n → Bool) :
    (s.iterate e i).weight z *
        mapWeight ((s.iterate e i).source z) ((s.iterate e i).left z) x₀ ≤
      s.leftEnvelope e μ i z := by
  induction i generalizing x₀ with
  | zero => exact cap z x₀
  | succ i ih =>
      have probability := affineIterationState_iterate_probability s e i hw hl hr
      exact affineRoundTranscript_left_envelope d h t L e
        (s.iterate e i).weight (s.iterate e i).left (s.iterate e i).right
        (s.iterate e i).leftRows (s.iterate e i).rightRows (s.iterate e i).rightWords
        (s.iterate e i).source (s.leftEnvelope e μ i)
        probability.1 probability.2.1 probability.2.2 ih z x₀

theorem affineIterationState_rightEnvelope_cap
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (ν : Z → ℝ)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z))
    (cap : ∀ z y₀, s.weight z *
      mapWeight (fun b => s.rightWords z b none) (s.right z) y₀ ≤ ν z)
    (z : AffineIterationTranscript Z t L i) (y₀ : Fin d → Bool) :
    (s.iterate e i).weight z *
        mapWeight (fun b => (s.iterate e i).rightWords z b none)
          ((s.iterate e i).right z) y₀ ≤
      s.rightEnvelope e ν i z := by
  induction i generalizing y₀ with
  | zero => exact cap z y₀
  | succ i ih =>
      have probability := affineIterationState_iterate_probability s e i hw hl hr
      exact affineRoundTranscript_right_envelope d h t L e
        (s.iterate e i).weight (s.iterate e i).left (s.iterate e i).right
        (s.iterate e i).leftRows (s.iterate e i).rightRows (s.iterate e i).rightWords
        (fun z b => (s.iterate e i).rightWords z b none) (s.rightEnvelope e ν i)
        probability.1 probability.2.1 probability.2.2 ih z y₀

theorem affineIterationState_leftEnvelope_nonnegative
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (μ : Z → ℝ)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (z : AffineIterationTranscript Z t L i) : 0 ≤ s.leftEnvelope e μ i z := by
  induction i with
  | zero => exact nonnegative z
  | succ i ih =>
      have probability := affineIterationState_iterate_probability s e i hw hl hr
      exact affineRoundTranscriptLeftEnvelope_nonnegative d h t L e
        (s.leftEnvelope e μ i) (s.iterate e i).right
        (s.iterate e i).rightRows (s.iterate e i).rightWords ih probability.2.2 z

theorem affineIterationState_rightEnvelope_nonnegative
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (ν : Z → ℝ)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) (nonnegative : ∀ z, 0 ≤ ν z)
    (z : AffineIterationTranscript Z t L i) : 0 ≤ s.rightEnvelope e ν i z := by
  induction i with
  | zero => exact nonnegative z
  | succ i ih =>
      have probability := affineIterationState_iterate_probability s e i hw hl hr
      exact affineRoundTranscriptRightEnvelope_nonnegative h t L e
        (s.rightEnvelope e ν i) (s.iterate e i).left (s.iterate e i).leftRows
        ih probability.2.1 z

theorem affineIterationState_leftEnvelope_sum
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (μ : Z → ℝ)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    (∑ z, s.leftEnvelope e μ i z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ (2 * i) * ∑ z, μ z := by
  induction i with
  | zero =>
      change (∑ z : Z, μ z) = _
      simp only [Nat.mul_zero, pow_zero, one_mul]
  | succ i ih =>
      have probability := affineIterationState_iterate_probability s e i hw hl hr
      change (∑ z, affineRoundTranscriptLeftEnvelope d h t L e (s.leftEnvelope e μ i)
        (s.iterate e i).right (s.iterate e i).rightRows (s.iterate e i).rightWords z) = _
      rw [affineRoundTranscriptLeftEnvelope_sum _ _ _ _ _ _ _ _ _ probability.2.2, ih]
      rw [show 2 * (i + 1) = 2 + 2 * i by lia, pow_add, mul_assoc]

theorem affineIterationState_rightEnvelope_sum
    (s : AffineIterationState n d h t L Z A B) (e i : Nat) (ν : Z → ℝ)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z)) :
    (∑ z, s.rightEnvelope e ν i z) =
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ (4 * i) * ∑ z, ν z := by
  induction i with
  | zero =>
      change (∑ z : Z, ν z) = _
      simp only [Nat.mul_zero, pow_zero, one_mul]
  | succ i ih =>
      have probability := affineIterationState_iterate_probability s e i hw hl hr
      change (∑ z, affineRoundTranscriptRightEnvelope h t L e (s.rightEnvelope e ν i)
        (s.iterate e i).left (s.iterate e i).leftRows z) = _
      rw [affineRoundTranscriptRightEnvelope_sum _ _ _ _ _ _ _ probability.2.1, ih]
      rw [show 4 * (i + 1) = 4 + 4 * i by lia, pow_add, mul_assoc]

end Algebraic.Cutwidth.Extractor.Internal
