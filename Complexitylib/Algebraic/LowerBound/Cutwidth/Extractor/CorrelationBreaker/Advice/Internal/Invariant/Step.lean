/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Step.Build
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Step.Comparison
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Bounds.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Weak
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Step
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.UniformState
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# One actual advice-bit transition

The exact transcript certificate advances through the executed flip-flop
maps. Before separation it uses the weak estimate, the first unequal bits
use opposite-advice extraction, and later bits use preservation with the
tampered state fixed by the transcript. Each successor retains normalized
factors of the original law and the original X/Y source envelopes.

This implements the one-bit transition underlying Chattopadhyay--Goyal--Li
Algorithm 2 and Lemma 6.9, Section 6.3: <https://arxiv.org/pdf/1505.00107>.
The scalar recurrence is the conservative checked estimate of this library.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

/-- Advance the exact original-law invariant through both actual advice-bit executions. -/
theorem AdviceInvariant.step
    {n m L : Nat} {Z A B : Type u} [Fintype Z] [Fintype A] [Fintype B]
    {p : (Z × B) × A → ℝ}
    {x : Z → A → Fin n → Bool} {y : Z → B → Fin m → Bool}
    {honest tampered : (Z × B) × A → Fin (matchedBlockOutputBits 64 L) → Bool}
    {separated : Prop} {ρ α β : ℝ}
    (I : AdviceInvariant n m L p x y honest tampered separated ρ α β)
    (e : Nat) (guard : FlipFlopSizeGuard n m L e)
    (x' : Z → A → Fin n → Bool) (y' : Z → B → Fin m → Bool) (b b' : Bool) :
    Nonempty (AdviceInvariant n m L p x y
      (fun a => flipFlopStep n m L e (x a.1.1 a.2) (y a.1.1 a.1.2) (honest a) b)
      (fun a => flipFlopStep n m L e (x' a.1.1 a.2) (y' a.1.1 a.1.2) (tampered a) b')
      (separated ∨ b ≠ b') (adviceStepError L e ρ α β)
      ((Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ 8 * α)
      ((Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) ^ 5 * β)) := by
  classical
  let xl := fun t => x (I.origin t)
  let xt := fun t => x' (I.origin t)
  let yr := fun t => y (I.origin t)
  let yt := fun t => y' (I.origin t)
  have hμ : 0 ≤ ∑ t, I.μ t := Finset.sum_nonneg (fun t _ => I.left_nonnegative t)
  have hξ : 0 ≤ ∑ t, I.ξ t := Finset.sum_nonneg (fun t _ => I.right_nonnegative t)
  have budget := adviceStepError_mono L e (le_refl ρ) I.left_sum I.right_sum
  by_cases hs : separated
  · have near := flipFlopStep_preservation_dist_le n m L e guard I.w I.l I.r
      xl xt yr yt I.q I.fixedTampered b b' I.μ I.ξ
      I.probability I.left_probability I.right_probability I.left_nonnegative
      I.right_nonnegative I.left_cap I.right_cap I.state
    have fixed : (fun t _ => I.fixedTampered t) = I.q' := by
      funext t a
      exact (I.fixed hs t a).symm
    rw [fixed] at near
    simp only [Nat.cast_pow, Nat.cast_ofNat] at near
    exact I.advance_observed e x' y' b b' (separated ∨ b ≠ b')
      ((near.trans (advicePostStep_le L e ρ _ _ hξ)).trans budget)
  · by_cases different : b ≠ b'
    · have opposite : b' = !b := by
        cases b <;> cases b' <;> simp_all
      subst b'
      have near := flipFlopOpposite_uniformState_dist_le n m L e guard I.w I.l I.r
        xl xt yr yt I.q I.q' b I.μ I.ξ
        I.probability I.left_probability I.right_probability I.left_nonnegative
        I.right_nonnegative I.left_cap I.right_cap I.state
      rw [← flipFlopObservedOutputWeight_opposite] at near
      simp only [Nat.cast_pow, Nat.cast_ofNat] at near
      have hρ : 0 ≤ ρ := (weightDist_nonneg _ _).trans I.state
      exact I.advance_observed e x' y' b (!b) (separated ∨ b ≠ !b)
        ((near.trans (adviceOppositeStep_le L e ρ _ _ hρ hμ)).trans budget)
    · have near := flipFlopOutput_weak_dist_le n m L e guard I.w I.l I.r
        xl xt yr yt I.q I.q' b b' I.μ I.ξ
        I.probability I.left_probability I.right_probability I.left_nonnegative
        I.right_nonnegative I.left_cap I.right_cap I.state
      simp only [Nat.cast_pow, Nat.cast_ofNat] at near
      exact I.advance_weak e x' y' b b' (separated ∨ b ≠ b')
        (fun h => h.elim hs different)
        ((near.trans (adviceWeakStep_le L e ρ _ _ hμ)).trans budget)

end Algebraic.Cutwidth.Extractor.Internal
