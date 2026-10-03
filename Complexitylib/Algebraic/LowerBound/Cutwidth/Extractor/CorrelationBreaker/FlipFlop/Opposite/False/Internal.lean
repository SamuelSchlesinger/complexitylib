/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.UniformState
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The honest-false, tampered-true flip-flop proof

Repair only the first honest refresh coordinate inside the factored right
kernel. This keeps both original source envelopes intact. The next actual
two-round look-ahead and final refresh retain their complete transcript;
transport to the original law therefore charges the repair distance twice.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem flipFlopOppositeWeight_probability (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopOppositeWeight n m L e w l r x x' y y' q q' b) :=
  (factoredWeight_probability w l r hw hl hr).map _

private theorem tamperedRefresh_after_repair
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype Seed] [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {W : X → Seed → Mid} {QExt : Q → Mid → Seed} {R : Y → Mid → Out}
    {K L J : Nat} {ε η θ ρ : ℝ}
    (first : WeightedStrongSeededExtractor W K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor QExt L η) (second_error : 0 ≤ η)
    (refresh : WeightedStrongSeededExtractor R J θ) (refresh_error : 0 ≤ θ)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → X) (q q' : Z → B → Q) (initialSeed : Q → Seed)
    (y y' : Z → B → Y) (μ ξ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (refresh_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (refresh_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (balanced : mapWeight initialSeed (uniformWeight Q) = uniformWeight Seed)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    weightDist (lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y' R)
      (uniformSecondWeight
        (lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y' R)) ≤
      2 * ρ + θ + 2 * ε + η +
        (K : ℝ) * (1 + Fintype.card (Mid × Mid)) * (∑ z, μ z) +
        (L : ℝ) * Fintype.card (Seed × Seed) / Fintype.card Q +
        (J : ℝ) * Fintype.card (Q × Q) * Fintype.card Out * ∑ z, ξ z := by
  obtain ⟨r', hr', same, uniform, repair⟩ :=
    exists_factored_uniform_right_repair w l r q hw hl hr
  let ν : Z → ℝ := fun z => w z * (Fintype.card Q : ℝ)⁻¹
  have sumν : ∑ z, ν z = (Fintype.card Q : ℝ)⁻¹ := by
    simp only [ν, ← Finset.sum_mul, hw.2, one_mul]
  have right_cap : ∀ z u, w z * mapWeight Prod.snd (r' z) u ≤ ν z :=
    fun z u => (uniform z u).le
  have preserved : ∀ z y₀, w z * mapWeight (fun bq => y z bq.1) (r' z) y₀ ≤ ξ z := by
    intro z y₀
    rw [rightCoordinateRepair_source_eq w r r' same y]
    exact refresh_cap z y₀
  have seed := retainedSeedWeight_uniform_image_dist w r' (fun _ => Prod.snd)
    initialSeed balanced uniform
  have extracted := first.lookAhead_tampered_refresh_dist_le
    first_error second second_error refresh refresh_error w l r'
    x x' (fun _ => Prod.snd) (fun z bq => q' z bq.1) initialSeed
    (fun z bq => y z bq.1) (fun z bq => y' z bq.1) μ ν ξ hw hl hr'
    left_nonnegative (fun z => mul_nonneg (hw.1 z) (by positivity)) refresh_nonnegative
    left_cap right_cap preserved seed.le
  let evaluate : ((Z × (B × Q)) × A) →
      ((LookAheadBaseTranscript Z Q Mid × Out) × A) × Out := fun p =>
    let zq := (p.1.1, (p.1.2.2, q' p.1.1 p.1.2.1))
    let messages := lookAheadBaseMessage x x' initialSeed W QExt zq p.2
    ((((zq, messages), R (y' p.1.1 p.1.2.1) messages.2.1), p.2),
      R (y p.1.1 p.1.2.1) messages.1.2)
  have original : mapWeight evaluate (factoredWeight w l (rightCoordinateLift r q)) =
      lookAheadTamperedRefreshWeight w l r x x' q q' initialSeed W QExt y y' R := by
    rw [factoredWeight_rightCoordinateLift, mapWeight_comp]
    rfl
  have near := (weightDist_map_le (factoredWeight w l (rightCoordinateLift r q))
    (factoredWeight w l r') evaluate).trans (repair.le.trans state)
  rw [original] at near
  have result := weightDist_uniformSecond_le_of_dist near extracted
  rw [sumν] at result
  convert result using 1
  rw [div_eq_mul_inv]
  ring

theorem flipFlopOpposite_false_dist_le (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (μ ν : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => flipFlopSeedPrefix L (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r
        (fun z b => flipFlopSeedPrefix L (q z b)))) ≤ δ) :
    let K : Nat := 2 ^ (2 ^ 62 * L)
    let J : Nat := 2 ^ (2 ^ 142 * L)
    let M : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let N : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    let ε := ((2 : ℝ) ^ e)⁻¹
    let ρ := 2 * ε + δ + (K : ℝ) * (∑ z, μ z) + (J : ℝ) * N ^ 2 * ∑ z, ν z
    weightDist (flipFlopOppositeWeight n m L e w l r x x' y y' q q' false)
      (uniformSecondWeight (flipFlopOppositeWeight n m L e w l r x x' y y' q q' false)) ≤
        2 * ρ + 4 * ε + (K : ℝ) * (1 + M ^ 2) * M ^ 4 * (∑ z, μ z) +
          (K : ℝ) * M ^ 2 / N + (J : ℝ) * N ^ 5 * ∑ z, ν z := by
  let Q := Fin (matchedBlockOutputBits 64 L) → Bool
  let Mid := Fin (matchedBlockSeedBits L) → Bool
  let T := LookAheadBaseTranscript Z Q Mid
  let W : (Fin n → Bool) → Mid → Mid := matchedBlockExtractor n 24 L e
  let QExt : Q → Mid → Mid := matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e
  let R : (Fin m → Bool) → Mid → Q := matchedBlockExtractor m 64 L e
  let w₁ := lookAheadBaseWeight w l r x x' q q' (flipFlopSeedPrefix L) W QExt
  let l₁ := lookAheadBaseLeft l x x' (flipFlopSeedPrefix L) W QExt
  let r₁ : T → B → ℝ := lookAheadBaseRight r q q'
  let qbar : T → B → Q := fun t b => R (y t.1.1 b) t.2.1.1
  let qbar' : T → B → Q := fun t b => R (y' t.1.1 b) t.2.2.2
  let μ₁ : T → ℝ := lookAheadBaseLeftEnvelope μ r q q'
  let ν₁ : T → ℝ := lookAheadBaseRightEnvelope ν l x x' (flipFlopSeedPrefix L) W QExt
  have room : 64 ≤ L := by have := guard.1; lia
  have error : e + 24 + 2 ≤ L := by have := guard.1; lia
  have first : WeightedStrongSeededExtractor W (2 ^ (2 ^ 62 * L)) (((2 : ℝ) ^ e)⁻¹) :=
    matchedBlockExtractor_depth24 n L e guard.2.1 room error
  have second : WeightedStrongSeededExtractor QExt (2 ^ (2 ^ 62 * L)) (((2 : ℝ) ^ e)⁻¹) :=
    matchedBlockExtractor_depth24 _ L e guard.2.2.2 room error
  have refresh : WeightedStrongSeededExtractor R (2 ^ (2 ^ 142 * L)) (((2 : ℝ) ^ e)⁻¹) :=
    matchedBlockExtractor_depth64 m L e guard.2.2.1 room (by have := guard.1; lia)
  obtain ⟨hw₁, hl₁, hr₁⟩ := lookAheadBase_probability
    w l r x x' q q' (flipFlopSeedPrefix L) W QExt hw hl hr
  have first_bound := first.lookAhead_first_refresh_dist_le (by positivity)
    refresh (by positivity) w l r x x' q q' (flipFlopSeedPrefix L) QExt y μ ν
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed
  have projected := weightDist_uniformSecond_map_first_le
    (lookAheadFirstRefreshWeight w l r x x' q q' (flipFlopSeedPrefix L) W QExt y R)
    Prod.fst
  rw [lookAheadFirstRefreshWeight_retainedSeed
    w l r x x' q q' (flipFlopSeedPrefix L) W QExt y R hl (fun z => (hr z).1)] at projected
  have refreshed := projected.trans first_bound
  have bound := tamperedRefresh_after_repair first (by positivity) second (by positivity)
    refresh (by positivity) w₁ l₁ r₁ (fun t => x t.1.1) (fun t => x' t.1.1)
    qbar qbar' (flipFlopSeedPrefix L) (fun t => y t.1.1) (fun t => y' t.1.1)
    μ₁ ν₁ hw₁ hl₁ hr₁
    (lookAheadBaseLeftEnvelope_nonnegative μ r q q' left_nonnegative (fun z => (hr z).1))
    (lookAheadBaseRightEnvelope_nonnegative ν l x x' (flipFlopSeedPrefix L) W QExt
      right_nonnegative (fun z => (hl z).1))
    (lookAheadBase_left_envelope w l r x x' q q' (flipFlopSeedPrefix L) W QExt μ
      hw.1 (fun z => (hl z).1) (fun z => (hr z).1) left_cap)
    (lookAheadBase_right_envelope w l r x x' q q' (flipFlopSeedPrefix L) W QExt y ν
      hw.1 (fun z => (hl z).1) (fun z => (hr z).1) right_cap)
    (flipFlopSeedPrefix_uniform L) refreshed
  have factor := lookAheadBase_factored w l r x x' q q' (flipFlopSeedPrefix L) W QExt
    (fun z => (hl z).1) (fun z => (hr z).1)
  have actual : lookAheadTamperedRefreshWeight w₁ l₁ r₁ (fun t => x t.1.1)
      (fun t => x' t.1.1) qbar qbar' (flipFlopSeedPrefix L) W QExt
      (fun t => y t.1.1) (fun t => y' t.1.1) R =
      flipFlopOppositeWeight n m L e w l r x x' y y' q q' false := by
    unfold lookAheadTamperedRefreshWeight
    change mapWeight _ (factoredWeight
      (lookAheadBaseWeight w l r x x' q q' (flipFlopSeedPrefix L) W QExt)
      (lookAheadBaseLeft l x x' (flipFlopSeedPrefix L) W QExt)
      (lookAheadBaseRight r q q')) = _
    rw [← factor, mapWeight_comp]
    unfold flipFlopOppositeWeight
    apply congrArg (fun f : (Z × B) × A → (FlipFlopOppositeTranscript Z L × A) × Q =>
      mapWeight f (factoredWeight w l r))
    funext p
    simp only [flipFlopOppositeTranscript, flipFlopStep, flipFlopLookAhead,
      lookAheadBaseMessage, qbar, qbar', W, QExt, R, Bool.false_eq_true, Bool.not_false]
    dsimp only [matchedBlockOutputBits, matchedBlockSeedBits]
    rfl
  rw [actual] at bound
  have sumμ := lookAheadBaseLeftEnvelope_sum (Mid := Mid) μ r q q' (fun z => (hr z).2)
  have sumν := lookAheadBaseRightEnvelope_sum ν l x x' (flipFlopSeedPrefix L) W QExt
    (fun z => (hl z).2)
  change (∑ t, μ₁ t) = _ at sumμ
  change (∑ t, ν₁ t) = _ at sumν
  rw [sumμ, sumν] at bound
  dsimp only
  convert bound using 1
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

end Algebraic.Cutwidth.Extractor.Internal
