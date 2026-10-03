/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.UniformState
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState
import Mathlib.Tactic.Positivity

/-!
# Final extraction from a separated advice-chain witness

Once the tampered current state is fixed by the transcript, the tampered
final extraction is a left-only finite leak. Two-sided leakage therefore
extracts from the original left source while retaining the entire original
right state and that tampered output. The witness's exact deterministic
factorization transfers the estimate to the original executed law.

This is the final strong-extraction upgrade following the advice-chain
argument of Chattopadhyay--Goyal--Li, Section 6.3, and the finite two-sided
merging argument of Chattopadhyay--Liao, Lemma 3.26. The advice induction
must construct the separated witness; this internal theorem does not
assert that such a witness exists.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u v

/-- A separated actual-state witness permits strong extraction retaining the original right state. -/
theorem AdviceInvariant.final_dist_le {n m L : Nat} {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    {p : (Z × B) × A → ℝ}
    {x : Z → A → Fin n → Bool} {y : Z → B → Fin m → Bool}
    {honest tampered : (Z × B) × A → Fin (matchedBlockOutputBits 64 L) → Bool}
    {separated : Prop} {ρ α β : ℝ}
    (invariant : AdviceInvariant n m L p x y honest tampered separated ρ α β)
    (different : separated) {Out : Type v} [Fintype Out] [Nonempty Out]
    {E : (Fin n → Bool) → (Fin (matchedBlockSeedBits L) → Bool) → Out}
    {K : Nat} {ε : ℝ} (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (x' : Z → A → Fin n → Bool) :
    let actual := mapWeight (fun a : (Z × B) × A =>
      ((a.1, E (x' a.1.1 a.2) (flipFlopSeedPrefix L (tampered a))),
        E (x a.1.1 a.2) (flipFlopSeedPrefix L (honest a)))) p
    weightDist actual (uniformSecondWeight actual) ≤
      ε + ρ + (K : ℝ) * Fintype.card Out * α := by
  classical
  let := invariant.tagFinite
  let source := fun t a => x (invariant.origin t) a
  let seed := fun t b => flipFlopSeedPrefix L (invariant.q t b)
  let leak := fun t (_ : Unit) a =>
    E (x' (invariant.origin t) a) (flipFlopSeedPrefix L (invariant.fixedTampered t))
  have prefixBound := (retainedSeedWeight_image_dist_le invariant.w invariant.r invariant.q
    (flipFlopSeedPrefix L) (flipFlopSeedPrefix_uniform L)).trans invariant.state
  have observed : observedSeedWeight invariant.w invariant.r (fun _ _ => ()) seed =
      mapWeight (fun ts => ((ts.1, ()), ts.2))
        (retainedSeedWeight invariant.w invariant.r seed) := by
    unfold observedSeedWeight retainedSeedWeight
    rw [mapWeight_comp]
  have projected := weightDist_uniformSecond_map_first_le
    (retainedSeedWeight invariant.w invariant.r seed) (fun t => (t, ()))
  rw [← observed] at projected
  have cap (t : invariant.Tag) (u₀ : Unit) (x₀ : Fin n → Bool) :
      invariant.w t * mapWeight (fun a => ((), source t a)) (invariant.l t) (u₀, x₀) ≤
        invariant.μ t := by
    cases u₀
    have tagged : mapWeight (fun a => ((), source t a)) (invariant.l t) ((), x₀) =
        mapWeight (source t) (invariant.l t) x₀ := by
      unfold mapWeight
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : source t a = x₀ <;> simp only [Prod.mk.injEq, true_and, h, ↓reduceIte]
    rw [tagged]
    exact invariant.left_cap t x₀
  have bound := extract.two_sided_leakage_dist_le error
    invariant.w invariant.l invariant.r source seed
    (fun _ _ => ()) (fun _ _ => ()) leak (fun tu => invariant.μ tu.1)
    invariant.probability invariant.left_probability invariant.right_probability
    (fun tu => invariant.left_nonnegative tu.1) cap (projected.trans prefixBound)
  have result := weightDist_uniformSecond_map_first_le
    (twoSidedExtractionWeight invariant.w invariant.l invariant.r source seed
      (fun _ _ => ()) (fun _ _ => ()) leak E)
    (fun t : (invariant.Tag × B) × (Unit × Out) =>
      ((invariant.origin t.1.1, t.1.2), t.2.2))
  have actual : mapWeight
      (fun t : ((invariant.Tag × B) × (Unit × Out)) × Out =>
        (((invariant.origin t.1.1.1, t.1.1.2), t.1.2.2), t.2))
      (twoSidedExtractionWeight invariant.w invariant.l invariant.r source seed
        (fun _ _ => ()) (fun _ _ => ()) leak E) =
      mapWeight (fun a : (Z × B) × A =>
        ((a.1, E (x' a.1.1 a.2) (flipFlopSeedPrefix L (tampered a))),
          E (x a.1.1 a.2) (flipFlopSeedPrefix L (honest a)))) p := by
    rw [twoSidedExtractionWeight_eq_map, ← invariant.factored, mapWeight_comp,
      mapWeight_comp]
    congr 1
    funext a
    dsimp only [Function.comp_apply, source, seed, leak]
    rw [invariant.origin_observe a, invariant.honest_eq a]
    have fixed : invariant.fixedTampered (invariant.observe a) = tampered a :=
      (invariant.fixed different (invariant.observe a) a.1.2).symm.trans
        (invariant.tampered_eq a)
    rw [fixed]
  rw [actual] at result
  apply result.trans
  have averaged : weightDist
      (twoSidedExtractionWeight invariant.w invariant.l invariant.r source seed
        (fun _ _ => ()) (fun _ _ => ()) leak E)
      (uniformSecondWeight
        (twoSidedExtractionWeight invariant.w invariant.l invariant.r source seed
          (fun _ _ => ()) (fun _ _ => ()) leak E)) ≤
        ε + ρ + (K : ℝ) * Fintype.card Out * ∑ t, invariant.μ t := by
    simpa only [Fintype.sum_prod_type, Fintype.sum_unique] using bound
  exact averaged.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left invariant.left_sum
      (show 0 ≤ (K : ℝ) * Fintype.card Out by positivity)))

end Algebraic.Cutwidth.Extractor.Internal
