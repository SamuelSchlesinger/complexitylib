/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Half.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Half.Internal.Capped
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.UniformState
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A selected half-step after whole-state repair

Repair the honest right look-ahead input while retaining its correlated
original right state. Its exact uniform marginal supplies the middle-source
cap, while all original source envelopes remain unchanged. The complete
actual retained transcript requires the usual two repair costs.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem flipFlopHalfWeight_probability (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (q' : Z → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopHalfWeight n m L e w l r x x' y y' q q' b b') :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem flipFlopHalf_dist_le (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (q' : Z → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
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
    weightDist (flipFlopHalfWeight n m L e w l r x x' y y' q q' b b')
      (uniformSecondWeight (flipFlopHalfWeight n m L e w l r x x' y y' q q' b b')) ≤
        4 * ε + 2 * ρ + (K : ℝ) * D * (1 + D ^ 2) * (∑ z, μ z) +
          (K : ℝ) * D ^ 2 / C + (J : ℝ) * C ^ 2 * ∑ z, ξ z := by
  let Q := Fin (matchedBlockOutputBits 64 L) → Bool
  let Mid := Fin (matchedBlockSeedBits L) → Bool
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
  have extracted := flipFlopHalf_dist_le_of_caps n m L e guard w l r' x x'
    (fun z cq => y z cq.1) (fun z cq => y' z cq.1) (fun _ => Prod.snd) q' b b'
    μ ν ξ hw hl hr' left_nonnegative (fun z => mul_nonneg (hw.1 z) (by positivity))
    right_nonnegative left_cap state_cap preserved seed.le
  let evaluate : ((Z × (B × Q)) × A) →
      ((LookAheadBaseTranscript Z Q Mid × Q) × A) × Q := fun p =>
    let honest := flipFlopLookAhead n L e (x p.1.1 p.2) p.1.2.2
    let tampered := flipFlopLookAhead n L e (x' p.1.1 p.2) (q' p.1.1)
    let transcript := ((p.1.1, (p.1.2.2, q' p.1.1)), (honest, tampered))
    (((transcript, matchedBlockExtractor m 64 L e (y' p.1.1 p.1.2.1)
      (if b' then tampered.2 else tampered.1)), p.2),
      matchedBlockExtractor m 64 L e (y p.1.1 p.1.2.1)
        (if b then honest.2 else honest.1))
  have original : mapWeight evaluate (factoredWeight w l (rightCoordinateLift r q)) =
      flipFlopHalfWeight n m L e w l r x x' y y' q q' b b' := by
    rw [factoredWeight_rightCoordinateLift, mapWeight_comp]
    rfl
  have near := (weightDist_map_le (factoredWeight w l (rightCoordinateLift r q))
    (factoredWeight w l r') evaluate).trans (repair.le.trans state)
  rw [original] at near
  have result := weightDist_uniformSecond_le_of_dist near extracted
  rw [sumν] at result
  dsimp only
  convert result using 1
  rw [div_eq_mul_inv]
  ring

end Algebraic.Cutwidth.Extractor.Internal
