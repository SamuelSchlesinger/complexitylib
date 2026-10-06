/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Gold.Parameters
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Gold.Properties
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.ConjunctionEntropy

/-!
# Gate lower bounds for the Gold map

Let `K` be a binary field of odd dimension `n ≥ 3` with any linear coordinate basis.
Every signed unbounded AND/OR/XOR circuit computing all `n` output bits of
`x ↦ x³` has at least `(3n - 3)/2` conjunction gates, and its total gate count `g`
satisfies `(4 + 2c)g ≥ (7 + 4c)n - (3 + 4c)` with `c = 1 - H₂(1/4)`, so
`g ≥ 1.771556n - 0.857781`. Fan-in, fanout, depth, literal repetitions, and nonlinear
reuse are unrestricted; the permutation, nonliteral, affine-restriction, and
component properties are proved for the Gold map itself.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry.Gold

open Cutwidth.Aggregate.Geometry

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] {n : ℕ}

/-- In odd dimension `n ≥ 3`, computing the Gold map requires at least `(3n - 3)/2`
conjunction gates, for every supplied linear coordinate basis. -/
theorem three_mul_input_le_two_mul_conjunctionCount_add_three
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) (odd : Odd n) (dimension : 3 ≤ n)
    (c : Circuit signature n n) (computes : c.Computes interpretation (goldFunction e)) :
    3 * n ≤ 2 * conjunctionCount c.program + 3 := by
  have same : c.eval interpretation = goldFunction e := funext computes
  have rigid : NonaffineOnFlats (c.eval interpretation) ((n + 3) / 2) := by
    rw [same]
    exact goldFunction_nonaffineOnFlats e odd
  have bound := rigid.output_add_input_le_conjunctionCount_add (by omega) (by omega)
  obtain ⟨k, rfl⟩ := odd
  omega

/-- The restriction–rank and entropy inequalities for the Gold map in odd dimension. -/
theorem entropy_mul_size_lower_bound (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) (odd : Odd n)
    (dimension : 3 ≤ n) (c : Circuit signature n n)
    (computes : c.Computes interpretation (goldFunction e)) :
    (7 + 4 * Entropy.bitSaving) * n - (3 + 4 * Entropy.bitSaving) ≤
      (4 + 2 * Entropy.bitSaving) * c.size := by
  have out (i : Fin n) : c.outputFunction interpretation i = fun x => goldFunction e x i := by
    funext x
    exact congrFun (computes x) i
  have same : c.eval interpretation = goldFunction e := funext computes
  have bijective : Function.Bijective (c.eval interpretation) := by
    rw [same]
    exact goldFunction_bijective e odd
  have bound := conjunctionCount_entropy_mul_size_lower_bound (r := 1) c bijective
    (by intro i j b; rw [out]; exact goldFunction_nonliteral e odd dimension i j b)
    (by
      intro S affine
      exact card_flat_le_two e S (fun i => by simpa only [out i] using affine i))
  have conjunctions := three_mul_input_le_two_mul_conjunctionCount_add_three
    e odd dimension c computes
  have counts : 3 * (n : ℝ) ≤ 2 * conjunctionCount c.program + 3 := by
    exact_mod_cast conjunctions
  push_cast at bound
  linarith

/-- The Gold-map gate bound in normalized form: `g ≥ C n - P` with `C ≈ 1.771556` and
`P ≈ 0.857781`. -/
theorem gateCoefficient_mul_sub_constantPenalty_le_size
    (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] K) (odd : Odd n) (dimension : 3 ≤ n)
    (c : Circuit signature n n) (computes : c.Computes interpretation (goldFunction e)) :
    gateCoefficient * n - constantPenalty ≤ c.size := by
  have bound := entropy_mul_size_lower_bound e odd dimension c computes
  have positive : 0 < 4 + 2 * Entropy.bitSaving := by
    linarith [Entropy.bitSaving_pos]
  unfold gateCoefficient constantPenalty
  rw [div_mul_eq_mul_div, ← sub_div]
  exact (div_le_iff₀ positive).mpr (by simpa only [mul_comm] using bound)

/-- For every `ε > 0`, all sufficiently large odd dimensions require more than
`(C - ε)n` gates for the Gold map, uniformly over binary fields and coordinate bases. -/
theorem exists_gateCoefficient_sub_mul_lt_size {ε : ℝ} (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {L : Type*} [Field L] [Fintype L] [Algebra (ZMod 2) L] {n : ℕ}
      (e : (Fin n → ZMod 2) ≃ₗ[ZMod 2] L), N ≤ n → Odd n →
      ∀ c : Circuit signature n n, c.Computes interpretation (goldFunction e) →
        (gateCoefficient - ε) * n < c.size := by
  refine ⟨⌈constantPenalty / ε⌉₊ + 3, ?_⟩
  intro L _ _ _ n e large odd c computes
  have bound := gateCoefficient_mul_sub_constantPenalty_le_size e odd (by omega) c computes
  have ceiling : constantPenalty / ε < n := by
    have := Nat.le_ceil (constantPenalty / ε)
    have cast : ((⌈constantPenalty / ε⌉₊ + 3 : ℕ) : ℝ) ≤ n := by exact_mod_cast large
    push_cast at cast
    linarith
  have penalty : constantPenalty < ε * n := by
    rwa [div_lt_iff₀ positive, mul_comm] at ceiling
  nlinarith

end Algebraic.Aggregate.Geometry.Gold
