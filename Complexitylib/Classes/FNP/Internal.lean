/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.FNP.Defs
public import Complexitylib.Classes.P

/-!
# FNP and TFNP — Internal proofs

Helper lemmas for `OrRelation` used by the surface-layer theorem
`orRelation_mem_TFNP_of_NP_coNP_witnesses`.
-/


public section

namespace Complexity

open Complexity Asymptotics Filter

/-- The combined relation is polynomially balanced when both components are. -/
theorem polyBalanced_orRelation {R₁ R₂ : List Bool → List Bool → Prop}
    (h₁ : PolyBalanced R₁) (h₂ : PolyBalanced R₂) :
    PolyBalanced (OrRelation R₁ R₂) := by
  obtain ⟨p₁, hb₁⟩ := h₁
  obtain ⟨p₂, hb₂⟩ := h₂
  refine ⟨p₁ + p₂, ?_⟩
  intro x y hR
  simp only [OrRelation] at hR
  cases hR with
  | inl h => have := hb₁ x y h; simp [Polynomial.eval_add]; omega
  | inr h => have := hb₂ x y h; simp [Polynomial.eval_add]; omega

/-- If both pair languages are in P, so is the pair language of the combined
    relation. Since `OrRelation R₁ R₂ = R₁ ∨ R₂`, the pair language is
    `pairLang R₁ ∪ pairLang R₂`, and P is closed under union. -/
theorem pairLang_orRelation_mem_P {R₁ R₂ : List Bool → List Bool → Prop}
    (h₁ : pairLang R₁ ∈ P) (h₂ : pairLang R₂ ∈ P) :
    pairLang (OrRelation R₁ R₂) ∈ P := by
  -- pairLang (OrRelation R₁ R₂) = pairLang R₁ ∪ pairLang R₂
  have heq : pairLang (OrRelation R₁ R₂) = pairLang R₁ ∪ pairLang R₂ := by
    ext z; simp only [pairLang, OrRelation, Set.mem_ofPred_eq, Set.mem_union]; aesop
  rw [heq]
  -- Extract polynomial degrees from P = ⋃ k, DTIME(· ^ k)
  obtain ⟨d₁, hd₁⟩ := Set.mem_iUnion.mp h₁
  obtain ⟨d₂, hd₂⟩ := Set.mem_iUnion.mp h₂
  -- Apply DTIME_union and embed into P
  apply Set.mem_iUnion.mpr
  obtain ⟨k, tm, f, hdf, hfo⟩ := DTIME_union hd₁ hd₂
  refine ⟨max d₁ d₂, k, tm, f, hdf, hfo.trans ?_⟩
  -- (n^d₁ + n^d₂) =O n^(max d₁ d₂)
  show (fun n => ((n ^ d₁ + n ^ d₂ : ℕ) : ℝ)) =O[atTop]
       (fun n => ((n ^ max d₁ d₂ : ℕ) : ℝ))
  apply IsBigO.of_bound 2
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simp only [Real.norm_natCast]
  have h1 : n ^ d₁ ≤ n ^ max d₁ d₂ := Nat.pow_le_pow_right hn (le_max_left d₁ d₂)
  have h2 : n ^ d₂ ≤ n ^ max d₁ d₂ := Nat.pow_le_pow_right hn (le_max_right d₁ d₂)
  have : n ^ d₁ + n ^ d₂ ≤ 2 * n ^ max d₁ d₂ := by omega
  exact_mod_cast this

/-- The disjunctive relation is in FNP when both components are. -/
theorem orRelation_mem_FNP {R₁ R₂ : List Bool → List Bool → Prop}
    (hR₁ : R₁ ∈ FNP) (hR₂ : R₂ ∈ FNP) :
    OrRelation R₁ R₂ ∈ FNP :=
  ⟨polyBalanced_orRelation hR₁.1 hR₂.1, pairLang_orRelation_mem_P hR₁.2 hR₂.2⟩

end Complexity
