/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DepthThree.Internal.Basic
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform
import Complexitylib.Circuits.Frontier.Explicit
import Mathlib.Tactic

/-!
# Depth-three lower bounds for the explicit hard family -- proofs

Internal proofs for `Complexitylib.Circuits.DepthThree.Explicit`.

The explicit family `Algebraic.Cutwidth.Extractor.sourceReductionHardFamily` satisfies the
frontier method's hypotheses: its accepted sets are eventually `K`-rectangle-free with
`log K = o(n)` and accept half of the cube. A `K`-rectangle-free set contains no subcube of
dimension `2 ⌈log₂ K⌉ = o(n)`. On inputs of positive length the family is balanced padding,
`f(x) = g(x_1, …, x_{n-1}) ⊕ x_0`, so flipping the first input bit exchanges accepted and rejected
inputs: the rejected sets have the same size and contain no larger subcubes.
-/

@[expose] public section

namespace Complexity

open Filter Asymptotics Algebraic.Cutwidth.Extractor

namespace DepthThree

/-- Flipping the first input bit negates the padded family. -/
theorem sourceReductionHardFamily_flipOn_zero (m : ℕ) (x : BitString (m + 1)) :
    sourceReductionHardFamily (m + 1) (x.flipOn {0}) = !sourceReductionHardFamily (m + 1) x := by
  rw [sourceReductionHardFamily_succ]
  unfold Algebraic.Cutwidth.balancePad
  have htail : Fin.tail (x.flipOn {0}) = Fin.tail x := by
    funext i
    simp only [Fin.tail, BitString.flipOn_apply, Finset.mem_singleton]
    rw [ite_eq_right (Fin.succ_ne_zero i)]
  rw [htail, BitString.flipOn_apply_of_mem (Finset.mem_singleton_self 0)]
  cases sourceReductionFamily m (Fin.tail x) <;> cases x 0 <;> rfl

theorem setOf_false_eq_image (m : ℕ) :
    {x : BitString (m + 1) | sourceReductionHardFamily (m + 1) x = false} =
      (fun x : BitString (m + 1) => x.flipOn {0}) ''
        {x | sourceReductionHardFamily (m + 1) x = true} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hx
    refine ⟨x.flipOn {0}, ?_, ?_⟩
    · rw [sourceReductionHardFamily_flipOn_zero, hx]; rfl
    · funext i; by_cases hi : i ∈ ({0} : Finset (Fin (m + 1))) <;> simp [hi]
  · rintro ⟨y, hy, rfl⟩
    rw [sourceReductionHardFamily_flipOn_zero, hy]; rfl

/-- The rejected inputs are as many as the accepted ones. -/
theorem ncard_false_eq_ncard_true (m : ℕ) :
    {x : BitString (m + 1) | sourceReductionHardFamily (m + 1) x = false}.ncard =
      {x : BitString (m + 1) | sourceReductionHardFamily (m + 1) x = true}.ncard := by
  rw [setOf_false_eq_image]
  refine Set.ncard_image_of_injective _ fun x y h => ?_
  have := congrArg (fun z : BitString (m + 1) => z.flipOn {0}) h
  simpa using this

/-- A subcube of rejected inputs flips to a subcube of accepted inputs. -/
theorem containsSubcube_true_of_false {m D : ℕ}
    (h : ContainsSubcube {x : BitString (m + 1) | sourceReductionHardFamily (m + 1) x = false} D) :
    ContainsSubcube {x : BitString (m + 1) | sourceReductionHardFamily (m + 1) x = true} D := by
  obtain ⟨a, J, hJ, hsub⟩ := h
  refine ⟨a.flipOn {0}, J, hJ, fun T hT => ?_⟩
  have hx := hsub T hT
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [BitString.flipOn_comm, sourceReductionHardFamily_flipOn_zero, hx]
  rfl

/-- The explicit family's subcube-dimension bound and density, from the frontier hypotheses. -/
theorem sourceReductionHardFamily_hypotheses :
    ∃ D : ℕ → ℕ, (fun n => (D n : ℝ)) =o[atTop] (fun n => (n : ℝ)) ∧
      (∀ᶠ n in atTop, ¬ ContainsSubcube {x | sourceReductionHardFamily n x = true} (D n)) ∧
      (fun n : ℕ => (n : ℝ) * Real.log 2 -
        Real.log {x | sourceReductionHardFamily n x = true}.ncard) =o[atTop]
        (fun n => (n : ℝ)) := by
  obtain ⟨K, hrect, hlogK, hdense⟩ := Frontier.sourceReductionHardFamily_frontierHypotheses
  refine ⟨fun n => 2 * Nat.clog 2 (K n), isLittleO_two_mul_clog hlogK, ?_, ?_⟩
  · filter_upwards [hrect] with n hn
    exact not_containsSubcube_of_rectangleFree hn (Nat.le_pow_clog one_lt_two _)
  · refine hdense.congr_left fun n => ?_
    simp [Nat.card_eq_fintype_card, Fintype.card_bool]

/-- **`Σ₃^k` for the explicit family.** -/
theorem sourceReductionHardFamily_sigmaThree {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((1 / (k : ℝ) - ε) * n) ≤
      sigmaThreeSize k (sourceReductionHardFamily n) := by
  obtain ⟨D, hD, hfree, hdense⟩ := sourceReductionHardFamily_hypotheses
  exact eventually_le_sigmaThreeSize hD hfree hdense hk hε

/-- **`Π₃^k` for the explicit family.** -/
theorem sourceReductionHardFamily_piThree {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((1 / (k : ℝ) - ε) * n) ≤
      piThreeSize k (sourceReductionHardFamily n) := by
  obtain ⟨D, hD, hfree, hdense⟩ := sourceReductionHardFamily_hypotheses
  have hfree' : ∀ᶠ n in atTop,
      ¬ ContainsSubcube {x | (!sourceReductionHardFamily n x) = true} (D n) := by
    filter_upwards [hfree, eventually_ge_atTop 1] with n hn hn1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    intro h
    refine hn (containsSubcube_true_of_false (h.mono fun x hx => ?_))
    simpa using hx
  have hdense' : (fun n : ℕ => (n : ℝ) * Real.log 2 -
      Real.log {x | (!sourceReductionHardFamily n x) = true}.ncard) =o[atTop]
      (fun n => (n : ℝ)) := by
    refine hdense.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 1] with n hn1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Bool.not_eq_true']
    rw [ncard_false_eq_ncard_true]
  filter_upwards [eventually_le_sigmaThreeSize hD hfree' hdense' hk hε] with n hn
  rw [piThreeSize_eq_sigmaThreeSize_not]
  exact hn

end DepthThree

end Complexity
