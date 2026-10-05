/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Compressed.Hardness
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Compressed.Modular

/-!
# The explicit lower bound from modular contribution rank

The fixed hard family retains its Gaussian coefficient when the modular
contribution matrix has sublinear information content. The modulus may vary
with the input length and the circuit. The factorization is constructed from
the matrix itself, so no separate compression certificate is assumed.
-/

public section

namespace Algebraic.Cutwidth.Aggregate.Compressed

open Filter MultiOutput SingleCut
open Algebraic.Aggregate.Compressed.Modular

private theorem eventually_lt_size_modular_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C)
    (D : ℕ → ℕ)
    (hD : (fun n => (D n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (p : ℕ) [Fact p.Prime],
      ∀ c : Circuit (Algebraic.Aggregate.signature (State p)) n 1,
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      2 * Nat.clog 2 (p ^ contributionRank c.program) ≤ D n →
        (1 + 1 / A - ε) * n < c.size := by
  let Good (n g : ℕ) := ∃ (p : ℕ), p.Prime ∧
    ∃ c : Program (Algebraic.Aggregate.signature (State p)) n g,
      ∃ out : Wire n g,
        (∀ x, c.trace Algebraic.Aggregate.interpretation x out =
          Extractor.sourceReductionHardFamily n x) ∧
        2 * Nat.clog 2 (p ^ contributionRank c) ≤ D n
  have hard := family_eventually_hard
  have hKtwo : ∀ᶠ n in atTop, 1 < familyThreshold n := by
    filter_upwards [hard] with n hn
    have hpos := (Nat.two_pow_pos (n - 2)).trans_le hn.2
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    exact hn.1.one_lt (x := x) (by simpa [accepting] using hx)
  have slices : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ g, Good n g → SliceBound A η C n g (D n) (familyThreshold n) := by
    intro η hη
    obtain ⟨C, hC⟩ := order η hη
    refine ⟨C, orderingBound_nonneg hC, ?_⟩
    filter_upwards [hard, hKtwo, eventually_component_guard D familyThreshold hD
      familyThreshold_log_isLittleO hKtwo] with n hn hKpos hguard g hg
    obtain ⟨p, hp, c, out, agrees, budget⟩ := hg
    let : Fact p.Prime := ⟨hp⟩
    have equality : (fun x => c.trace Algebraic.Aggregate.interpretation x out) =
        Extractor.sourceReductionHardFamily n := funext agrees
    apply sliceBound_of_circuit c (factorization c) out
      (by simpa only [budget_compressedState] using budget)
      (equality ▸ hn.1) (equality ▸ hn.2) hKpos hguard
      (by positivity) (orderingBound_nonneg hC) hC
  have result := eventually_lt_size_of_sliceBound hA Good D familyThreshold hD
    familyThreshold_log_isLittleO hKtwo slices hε
  filter_upwards [result] with n hn p inst c computes budget
  apply hn c.size
  refine ⟨p, inst.out, c.program, c.outputs 0, ?_, budget⟩
  intro x
  exact congrFun (computes x) 0

/-- The full Gaussian coefficient follows from the exact modular state budget, uniformly
over prime moduli and circuits, with no additional factorization hypothesis. -/
theorem sourceReductionHardFamily_eventually_lt_size_modular_stateBudget
    (D : ℕ → ℕ)
    (hD : (fun n => (D n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (p : ℕ) [Fact p.Prime],
      ∀ c : Circuit (Algebraic.Aggregate.signature (State p)) n 1,
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      2 * Nat.clog 2 (p ^ contributionRank c.program) ≤ D n →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
          c.size := by
  have bound := eventually_lt_size_modular_of_orderingBound
    (mul_pos two_pos Gaussian.frontierCoefficient_pos)
    Multigraph.exists_orderingBound_frontier D hD hε
  rwa [Gaussian.one_add_inv_two_mul_frontierCoefficient] at bound

/-- A sublinear rank-times-residue budget preserves the coefficient for varying prime moduli. -/
theorem sourceReductionHardFamily_eventually_lt_size_modular_rankBudget
    (D : ℕ → ℕ)
    (hD : (fun n => (D n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (p : ℕ) [Fact p.Prime],
      ∀ c : Circuit (Algebraic.Aggregate.signature (State p)) n 1,
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      2 * contributionRank c.program * Nat.clog 2 p ≤ D n →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
          c.size := by
  filter_upwards [sourceReductionHardFamily_eventually_lt_size_modular_stateBudget D hD hε]
    with n bound p inst c computes budget
  apply bound p c computes
  have compressed := budget_compressedState_le c.program
  rw [budget_compressedState] at compressed
  exact compressed.trans budget

/-- At any fixed prime modulus, a sublinear rank bound alone suffices. -/
theorem sourceReductionHardFamily_eventually_lt_size_modular_fixedPrime
    (p : ℕ) [Fact p.Prime] (R : ℕ → ℕ)
    (hR : (fun n => (R n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ c : Circuit (Algebraic.Aggregate.signature (State p)) n 1,
      c.Computes Algebraic.Aggregate.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
      contributionRank c.program ≤ R n →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
          c.size := by
  let D (n : ℕ) := 2 * R n * Nat.clog 2 p
  have hD : (fun n => (D n : ℝ)) =o[atTop] (fun n => (n : ℝ)) := by
    simpa only [D, Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm] using
      hR.const_mul_left (2 * (Nat.clog 2 p : ℝ))
  filter_upwards [sourceReductionHardFamily_eventually_lt_size_modular_rankBudget D hD hε]
    with n bound c computes rank
  exact bound p c computes (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 rank))

end Algebraic.Cutwidth.Aggregate.Compressed
