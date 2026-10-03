/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.True
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.UniformState
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Repairing the initial state for the true-versus-false execution

A correlated repair makes the original honest right state uniform while
preserving the weighted original right-source marginal and the entire left
kernel. Its exact uniform cap discharges the middle-source hypothesis of
the true branch. The actual full opposite transcript may change, so returning
to its own retained marginal costs twice the original state discrepancy.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem flipFlopOpposite_true_uniformState_dist_le (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (μ ξ : Z → ℝ) {ρ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    let K : Nat := 2 ^ (2 ^ 62 * L)
    let J : Nat := 2 ^ (2 ^ 142 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    let ε := ((2 : ℝ) ^ e)⁻¹
    weightDist (flipFlopOppositeWeight n m L e w l r x x' y y' q q' true)
      (uniformSecondWeight (flipFlopOppositeWeight n m L e w l r x x' y y' q q' true)) ≤
        2 * ρ + 10 * ε + (K : ℝ) * (2 * (1 + D ^ 2) + D ^ 5) * (∑ z, μ z) +
          2 * (K : ℝ) * D ^ 2 / C + (J : ℝ) * (2 * C ^ 3 + C ^ 5) * ∑ z, ξ z := by
  let Q := Fin (matchedBlockOutputBits 64 L) → Bool
  obtain ⟨r', hr', same, uniform, repair⟩ :=
    exists_factored_uniform_right_repair w l r q hw hl hr
  let ν : Z → ℝ := fun z => w z * (Fintype.card Q : ℝ)⁻¹
  have sumν : ∑ z, ν z = (Fintype.card Q : ℝ)⁻¹ := by
    simp only [ν, ← Finset.sum_mul, hw.2, one_mul]
  have state_cap : ∀ z u, w z * mapWeight Prod.snd (r' z) u ≤ ν z :=
    fun z u => (uniform z u).le
  have preserved : ∀ z y₀, w z * mapWeight (fun cq => y z cq.1) (r' z) y₀ ≤ ξ z := by
    intro z y₀
    rw [rightCoordinateRepair_source_eq w r r' same y]
    exact right_cap z y₀
  have seed := retainedSeedWeight_uniform_image_dist w r' (fun _ => Prod.snd)
    (flipFlopSeedPrefix L) (flipFlopSeedPrefix_uniform L) uniform
  have extracted := flipFlopOpposite_true_dist_le n m L e guard w l r' x x'
    (fun z cq => y z cq.1) (fun z cq => y' z cq.1)
    (fun _ => Prod.snd) (fun z cq => q' z cq.1) μ ν ξ hw hl hr'
    left_nonnegative (fun z => mul_nonneg (hw.1 z) (by positivity)) right_nonnegative
    left_cap state_cap preserved seed.le
  let evaluate : ((Z × (B × Q)) × A) → (FlipFlopOppositeTranscript Z L × A) × Q :=
    fun p =>
      ((flipFlopOppositeTranscript n m L e x x'
        (fun z cq => y z cq.1) (fun z cq => y' z cq.1)
        (fun _ => Prod.snd) (fun z cq => q' z cq.1) true p, p.2),
        flipFlopStep n m L e (x p.1.1 p.2) (y p.1.1 p.1.2.1) p.1.2.2 true)
  have original : mapWeight evaluate (factoredWeight w l (rightCoordinateLift r q)) =
      flipFlopOppositeWeight n m L e w l r x x' y y' q q' true := by
    rw [factoredWeight_rightCoordinateLift, mapWeight_comp]
    rfl
  have near := (weightDist_map_le (factoredWeight w l (rightCoordinateLift r q))
    (factoredWeight w l r') evaluate).trans (repair.le.trans state)
  rw [original] at near
  have result := weightDist_uniformSecond_le_of_dist near extracted
  dsimp only at result ⊢
  rw [sumν] at result
  convert result using 1
  rw [div_eq_mul_inv]
  ring

end Algebraic.Cutwidth.Extractor.Internal
