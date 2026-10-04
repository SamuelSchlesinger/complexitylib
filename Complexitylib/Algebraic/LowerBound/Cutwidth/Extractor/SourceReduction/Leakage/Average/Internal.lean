/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Average.Internal.Conditioning
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Actual affine extraction averaged over leaky seeds

Conditioning on the complete source-dependent leakage gives an exact factored
law with a constant joint source envelope. Its total pays exactly the number
of leaked bits. Applying the checked actual affine construction, then forgetting
only the leakage transcript, gives the honest-base-seed average used by
Chattopadhyay--Liao, Lemma 5.3, printed pp.19--20:
<https://arxiv.org/abs/2110.12652>. The tampered seed is `f y i` XOR its leakage;
it is never replaced by the honest seed `y`.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem affineLeakageOutputWeight_average_dist_le (n t a target : Nat)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) →
      Fin (affinePhaseOneRightBits n t a (affineIterationTarget t target)) → Bool)
    (advice : Option (Fin t) → List Bool)
    (g : (Fin (affinePhaseOneRightBits n t a (affineIterationTarget t target)) → Bool) →
      Fin n → Bool)
    (f : (Fin (affinePhaseOneRightBits n t a (affineIterationTarget t target)) → Bool) →
      Fin t → Fin (affinePhaseOneRightBits n t a (affineIterationTarget t target)) → Bool)
    (positive : 0 < t) (probability : IsProbabilityWeight p)
    (cap : ∀ x, p x ≤ ((2 : ℝ) ^ (affineIterationSourceEntropy n t a target +
      (t + 1) * affinePhaseOneRightBits n t a (affineIterationTarget t target)))⁻¹)
    (honest_length : (advice none).length = a)
    (tampered_length : ∀ i, (advice (some i)).length = a)
    (different : ∀ i, advice none ≠ advice (some i)) :
    let σ := affineIterationTarget t target
    let d := affinePhaseOneRightBits n t a σ
    let h := growingMatchedBlockDepth t
    let L₀ := affinePhaseOneInitialScale n t a σ
    let L := affinePhaseOneScale n t a σ
    let e := affinePhaseOneLocalError σ
    let cb := affineCorrelationBreaker n d h L₀ e L (adviceErrorExponent a e) e
      (affineIterationRounds t)
    ∑ y, uniformWeight (Fin d → Bool) y *
      weightDist (affineLeakageOutputWeight cb p leak advice (g y) y (f y))
        (uniformSecondWeight (affineLeakageOutputWeight cb p leak advice (g y) y (f y))) ≤
      ((2 : ℝ) ^ target)⁻¹ := by
  let σ := affineIterationTarget t target
  let d := affinePhaseOneRightBits n t a σ
  let h := growingMatchedBlockDepth t
  let L₀ := affinePhaseOneInitialScale n t a σ
  let L := affinePhaseOneScale n t a σ
  let e := affinePhaseOneLocalError σ
  let X := Fin n → Bool
  let Y := Fin d → Bool
  let Z := Option (Fin t) → Y
  let Out := Fin (matchedBlockOutputBits h L) → Bool
  let cb := affineCorrelationBreaker n d h L₀ e L (adviceErrorExponent a e) e
    (affineIterationRounds t)
  let w : Z → ℝ := mapWeight leak p
  let l : Z → X → ℝ := conditionalWeight (mapWeight (fun x => (leak x, x)) p)
  let r : Z → Y → ℝ := fun _ => uniformWeight Y
  let μ : Z → ℝ := fun _ =>
    ((2 : ℝ) ^ (affineIterationSourceEntropy n t a target + (t + 1) * d))⁻¹
  let seeds : Z → Y → AffinePhaseOneCopies t d := fun z y i =>
    match i with
    | none => xorInput y (z none)
    | some j => xorInput (f y j) (z (some j))
  have hw : IsProbabilityWeight w := probability.map leak
  have hl : ∀ z, IsProbabilityWeight (l z) :=
    fun z => (probability.map (fun x => (leak x, x))).conditionalWeight z
  have hr : ∀ z, IsProbabilityWeight (r z) := fun _ => isProbabilityWeight_uniform Y
  have source_cap : ∀ z x, w z * mapWeight (fun x : X => x) (l z) x ≤ μ z := by
    intro z x
    change w z * mapWeight id (l z) x ≤ μ z
    rw [mapWeight_id]
    change mapWeight leak p z *
      conditionalWeight (mapWeight (fun x => (leak x, x)) p) z x ≤ μ z
    rw [leakageConditioning_factor p leak probability.1]
    split_ifs
    · exact cap x
    · exact inv_nonneg.mpr (pow_nonneg (by norm_num) _)
  have uniform : ∀ z, mapWeight (fun y => seeds z y none) (r z) = uniformWeight Y :=
    fun z => leakage_xor_uniform (z none)
  have mass : (∑ z, μ z) ≤ ((2 : ℝ) ^ affineIterationSourceEntropy n t a target)⁻¹ :=
    (leakage_envelope_sum t d (affineIterationSourceEntropy n t a target)).le
  let actual := affineCorrelationBreakerWeight n d t h L₀ e L (adviceErrorExponent a e) e
    (affineIterationRounds t) w l r (fun _ x => x) (fun _ y => g y) seeds advice Finset.univ
  have security : weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ :=
    affineCorrelationBreaker_parameters_dist_le n t a target w l r
      (fun _ x => x) (fun _ y => g y) seeds advice Finset.univ μ positive hw hl hr
      (fun _ => inv_nonneg.mpr (pow_nonneg (by norm_num) _)) source_cap uniform
      honest_length tampered_length different mass
  let project : (Z × Y) × (↥(Finset.univ : Finset (Fin t)) → Out) →
      Y × (Fin t → Out) := fun zys => (zys.1.2, fun i => zys.2 ⟨i, Finset.mem_univ i⟩)
  let tagged : (Y × (Fin t → Out)) × Out → ℝ := fun youtputs =>
    uniformWeight Y youtputs.1.1 *
      affineLeakageOutputWeight cb p leak advice (g youtputs.1.1) youtputs.1.1
        (f youtputs.1.1) (youtputs.1.2, youtputs.2)
  have actual_eq : mapWeight (fun zo => (project zo.1, zo.2)) actual = tagged := by
    change mapWeight _ (mapWeight _ (factoredWeight w l r)) = tagged
    rw [mapWeight_comp]
    rw [show factoredWeight w l r =
      mapWeight (fun yx : Y × X => ((leak yx.2, yx.1), yx.2))
        (fun yx => uniformWeight Y yx.1 * p yx.2) from
      (leakageConditioning_factored p leak (uniformWeight Y) probability.1).symm]
    rw [mapWeight_comp]
    exact leakage_map_tagged (uniformWeight Y) p (fun y x =>
      ((fun i => cb (xorInput x (g y)) (xorInput (f y i) (leak x (some i)))
        (advice (some i))), cb (xorInput x (g y)) (xorInput y (leak x none)) (advice none)))
  have projected := weightDist_uniformSecond_map_first_le actual project
  rw [actual_eq] at projected
  have average := weightDist_uniformSecond_tagged (uniformWeight Y)
    (fun y => affineLeakageOutputWeight cb p leak advice (g y) y (f y))
    (isProbabilityWeight_uniform Y).1
  exact (le_of_eq average.symm).trans (projected.trans security)

end Algebraic.Cutwidth.Extractor.Internal
