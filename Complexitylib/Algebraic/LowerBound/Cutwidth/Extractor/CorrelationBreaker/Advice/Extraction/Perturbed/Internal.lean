/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# The actual advice breaker on an approximately uniform right input

Repair only the honest right-input coordinate, preserving both original
source factors and the tampered program. The exact-uniform theorem applies
on this enlarged state. Forgetting the repaired coordinate recovers the
original retained marginal, so transfer costs the original discrepancy once.
This is the input-repair step needed for Chattopadhyay--Liao Theorem 6.1.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

private theorem perturbed_of_uniform (n m L e : Nat) {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) {ρ ε : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ ρ)
    (uniform_case : ∀ r' : Z → B × (Fin m → Bool) → ℝ,
      (∀ z, IsProbabilityWeight (r' z)) →
      (∀ z, mapWeight Prod.snd (r' z) = uniformWeight (Fin m → Bool)) →
      let actual := adviceCorrelationBreakerWeight n m L e w l r' x x'
        (fun _ => Prod.snd) (fun z bq => y' z bq.1) advice advice'
      weightDist actual (uniformSecondWeight actual) ≤ ε) :
    let actual := adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice'
    weightDist actual (uniformSecondWeight actual) ≤ ρ + ε := by
  obtain ⟨r', hr', first, uniform, repair⟩ :=
    exists_factored_uniform_right_repair_rows w l r y hw hl hr
  let Q := Fin m → Bool
  let Out := Fin (matchedBlockSeedBits L) → Bool
  let evaluate : ((Z × (B × Q)) × A) → ((Z × B) × Out) × Out := fun p =>
    (((p.1.1, p.1.2.1),
      adviceCorrelationBreaker n m L e (x' p.1.1 p.2) (y' p.1.1 p.1.2.1) advice'),
      adviceCorrelationBreaker n m L e (x p.1.1 p.2) p.1.2.2 advice)
  let retain : (Z × B) × A → (Z × B) × Out := fun p =>
    (p.1, adviceCorrelationBreaker n m L e (x' p.1.1 p.2) (y' p.1.1 p.1.2) advice')
  have original : mapWeight evaluate (factoredWeight w l (rightCoordinateLift r y)) =
      adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice' := by
    rw [factoredWeight_rightCoordinateLift, mapWeight_comp]
    rfl
  have near := (weightDist_map_le (factoredWeight w l (rightCoordinateLift r y))
    (factoredWeight w l r') evaluate).trans (repair.le.trans seed)
  rw [original] at near
  have projected := weightDist_uniformSecond_map_first_le
    (adviceCorrelationBreakerWeight n m L e w l r' x x'
      (fun _ => Prod.snd) (fun z bq => y' z bq.1) advice advice')
    (fun t : (Z × (B × Q)) × Out => ((t.1.1, t.1.2.1), t.2))
  simp only [adviceCorrelationBreakerWeight, mapWeight_comp] at projected
  have bounded : weightDist (mapWeight evaluate (factoredWeight w l r'))
      (uniformSecondWeight (mapWeight evaluate (factoredWeight w l r'))) ≤ ε :=
    projected.trans (uniform_case r' hr' uniform)
  have same : firstWeight
      (adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice') =
      firstWeight (mapWeight evaluate (factoredWeight w l r')) := by
    calc
      _ = mapWeight retain (factoredWeight w l r) := by
        rw [adviceCorrelationBreakerWeight, ← mapWeight_fst, mapWeight_comp]
      _ = mapWeight retain
          (mapWeight (fun p : (Z × (B × Q)) × A => ((p.1.1, p.1.2.1), p.2))
            (factoredWeight w l r')) := by
        rw [factoredWeight_forget_right_eq w l r r' (fun z b => by rw [first])]
      _ = _ := by
        rw [← mapWeight_fst, mapWeight_comp, mapWeight_comp]
  exact weightDist_uniformSecond_le_of_dist_of_same_first near bounded same

theorem adviceCorrelationBreaker_perturbed_dist_le (n m L e : Nat) {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e) (size : matchedBlockOutputBits 64 L ≤ m)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (μ : Z → ℝ) {ρ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ ρ)
    (length : advice.length = advice'.length) (different : advice ≠ advice') :
    let actual := adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice'
    weightDist actual (uniformSecondWeight actual) ≤
      ρ + adviceCorrelationBreakerError m L e advice.length (∑ z, μ z) := by
  apply perturbed_of_uniform n m L e w l r x x' y y' advice advice' hw hl hr seed
  intro r' hr' uniform
  exact adviceCorrelationBreaker_dist_le n m L e guard size w l r' x x'
    (fun _ => Prod.snd) (fun z bq => y' z bq.1) advice advice' μ
    hw hl hr' nonnegative cap uniform length different

theorem adviceCorrelationBreaker_perturbed_dyadic_dist_le (n m L target : Nat) {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (μ : Z → ℝ) {ρ : ℝ}
    (guard : FlipFlopSizeGuard n m L (adviceErrorExponent advice.length target))
    (size : matchedBlockOutputBits 64 L ≤ m)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ ρ)
    (length : advice.length = advice'.length) (different : advice ≠ advice')
    (left : (∑ z, μ z) ≤ ((2 : ℝ) ^ (2 ^ 150 * (advice.length + 1) * L))⁻¹)
    (right : 2 ^ 150 * (advice.length + 1) * L ≤ m) :
    let e := adviceErrorExponent advice.length target
    let actual := adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice'
    weightDist actual (uniformSecondWeight actual) ≤ ρ + ((2 : ℝ) ^ target)⁻¹ := by
  apply perturbed_of_uniform n m L (adviceErrorExponent advice.length target)
    w l r x x' y y' advice advice' hw hl hr seed
  intro r' hr' uniform
  exact adviceCorrelationBreaker_dyadic_dist_le n m L target w l r' x x'
    (fun _ => Prod.snd) (fun z bq => y' z bq.1) advice advice' μ guard size
    hw hl hr' nonnegative cap uniform length different left right

end Algebraic.Cutwidth.Extractor.Internal
