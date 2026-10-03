/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Internal.Lifting

/-!
# Projecting the lifted coupling to a repaired joint law

The old and new pairs share the second coordinate. Their probability of
disagreement bounds the distance of their joint laws. Conversely,
marginalization cannot increase distance, so the joint repair costs exactly
the distance of the prescribed first marginal.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem exists_joint_marginal_replacement {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} {q : α → ℝ} (hp : IsProbabilityWeight p)
    (hq : IsProbabilityWeight q) :
    ∃ p' : α × β → ℝ, IsProbabilityWeight p' ∧ firstWeight p' = q ∧
      (∀ b, ∑ a, p' (a, b) = ∑ a, p (a, b)) ∧
        weightDist p p' = weightDist (firstWeight p) q := by
  obtain ⟨ρ, hρ, preserve, replace, disagreement⟩ :=
    exists_marginal_replacement_coupling hp hq
  let f (z : (α × β) × α) := z.1
  let g (z : (α × β) × α) := (z.2, z.1.2)
  let p' := mapWeight g ρ
  have old : mapWeight f ρ = p := by
    funext z
    rw [show f = Prod.fst from rfl, mapWeight_fst]
    exact preserve z
  have new : mapWeight Prod.snd ρ = q := by
    funext a'
    rw [mapWeight_snd_apply]
    exact replace a'
  have first : firstWeight p' = q := by
    rw [← mapWeight_fst, mapWeight_comp]
    exact new
  have second : mapWeight Prod.snd p' = mapWeight Prod.snd p := by
    change mapWeight Prod.snd (mapWeight g ρ) = _
    rw [mapWeight_comp, ← old, mapWeight_comp]
  have upper : weightDist p p' ≤ weightDist (firstWeight p) q := by
    have bound := weightDist_map_map_le hρ f g
    rw [old] at bound
    have mismatch : (∑ z with f z ≠ g z, ρ z) =
        ∑ z with z.1.1 ≠ z.2, ρ z := by
      congr 1
      ext ⟨⟨a, b⟩, a'⟩
      simp [f, g]
    calc
      weightDist p p' ≤ ∑ z with f z ≠ g z, ρ z := by
        convert bound using 1
        congr 1
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      _ = _ := mismatch.trans disagreement
  have lower : weightDist (firstWeight p) q ≤ weightDist p p' := by
    have bound := weightDist_map_le p p' Prod.fst
    simpa only [mapWeight_fst, first] using bound
  refine ⟨p', hρ.map g, first, ?_, le_antisymm upper lower⟩
  intro b
  simpa only [mapWeight_snd_apply] using congrFun second b

end Algebraic.Cutwidth.Extractor.Internal
