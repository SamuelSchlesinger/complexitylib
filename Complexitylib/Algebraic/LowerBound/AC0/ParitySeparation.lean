/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.AC0.Normalization
public import Complexitylib.Algebraic.CircuitFamily.Growth
public import Complexitylib.Algebraic.LowerBound.AC0.ParityScale

/-!
# Parity is not in AC0

This module passes from the finite switching-lemma tradeoff to the qualitative
complexity-class separation. Given fixed polynomial cost and fixed logical
depth bounds, choose the diagonal input width

`n = (20 * (t + 1))^(d - 1)`.

The finite theorem forces `2^(t+1) <= 20 * t * S(n)`, while substituting this
input width into the polynomial upper bound leaves a fixed polynomial in `t`.
The latter is eventually at most `2^t`, giving a contradiction.

The reusable family theorem works directly for arbitrary internal NOT gates:
the switching argument follows free NOT chains semantically and charges only
AND/OR gates. The checked `AC0.Computable` endpoint is retained as a
specialization, while `AC0.RawComputable` now follows without dual-rail
normalization or its factor-two cost expansion.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace ParityParameters

/-- The input width used to diagonalize against fixed size and depth bounds. -/
def diagonalInput (depth scale : Nat) : Nat :=
  (20 * (scale + 1)) ^ (depth - 1)

/-- Substituting the diagonal input width into a fixed polynomial gives a
fixed polynomial in the scale parameter. The constants are deliberately
coarse; only their independence from `scale` matters. -/
theorem scaledPolynomial_le
    (coefficient degree depth scale : Nat)
    (scalePositive : 0 < scale) :
    20 * scale * (coefficient *
        (diagonalInput depth scale + 1) ^ degree) <=
      (20 * coefficient * (2 * 40 ^ (depth - 1)) ^ degree) *
        scale ^ ((depth - 1) * degree + 1) := by
  have baseLe : 20 * (scale + 1) <= 40 * scale := by omega
  have inputLe :
      (20 * (scale + 1)) ^ (depth - 1) <=
        (40 * scale) ^ (depth - 1) :=
    Nat.pow_le_pow_left baseLe (depth - 1)
  have inputPositive :
      0 < (20 * (scale + 1)) ^ (depth - 1) := by
    positivity
  have successorLe :
      (20 * (scale + 1)) ^ (depth - 1) + 1 <=
        2 * (40 * scale) ^ (depth - 1) := by
    calc
      (20 * (scale + 1)) ^ (depth - 1) + 1 <=
          2 * (20 * (scale + 1)) ^ (depth - 1) := by omega
      _ <= 2 * (40 * scale) ^ (depth - 1) :=
        Nat.mul_le_mul_left 2 inputLe
  calc
    20 * scale * (coefficient *
        (diagonalInput depth scale + 1) ^ degree) =
        20 * scale * coefficient *
          ((20 * (scale + 1)) ^ (depth - 1) + 1) ^ degree := by
      simp [diagonalInput]
      ring
    _ <= 20 * scale * coefficient *
          (2 * (40 * scale) ^ (depth - 1)) ^ degree := by
      gcongr
    _ = (20 * coefficient * (2 * 40 ^ (depth - 1)) ^ degree) *
          scale ^ ((depth - 1) * degree + 1) := by
      simp only [mul_pow, pow_mul, pow_succ]
      ring

end ParityParameters

namespace Family

/-- No family with polynomial AND/OR cost and constant logical depth computes
parity at every input width, even when NOT gates occur at arbitrary internal
wires. -/
theorem not_computes_parity_raw
    (family : Algebraic.Circuit.Family signature 1)
    (polynomialCost : family.HasPolynomialCost andOrCost)
    (constantDepth : HasConstantLogicalDepth family) :
    Not (family.Computes interpretation Parity.targetFamily) := by
  intro computes
  obtain ⟨coefficient, degree, costBound⟩ := polynomialCost
  obtain ⟨depthBound, depthBounded⟩ := constantDepth
  let depth := max 2 depthBound
  let growthCoefficient :=
    20 * coefficient * (2 * 40 ^ (depth - 1)) ^ degree
  let growthDegree := (depth - 1) * degree + 1
  obtain ⟨cutoff, growthFrom⟩ := Filter.eventually_atTop.1
    (Circuit.Resource.eventually_const_mul_pow_le_two_pow
      growthCoefficient growthDegree)
  let scale := max cutoff 1
  let n := ParityParameters.diagonalInput depth scale
  have twoLeDepth : 2 <= depth := le_max_left 2 depthBound
  have scalePositive : 0 < scale := by
    dsimp [scale]
    omega
  have circuitDepth :
      Circuit.logicalDepth (family.circuit n) <= depth :=
    (depthBounded n).trans (le_max_right 2 depthBound)
  have lower :
      2 ^ (scale + 1) <=
        20 * scale * (family.circuit n).program.cost andOrCost :=
    Circuit.parity_size_tradeoff_at_scale_raw
      (family.circuit n) (computes n)
      depth scale twoLeDepth circuitDepth (by omega) (by
        simp [n, ParityParameters.diagonalInput])
  have upper :
      20 * scale * (family.circuit n).program.cost andOrCost <=
        2 ^ scale := by
    calc
      20 * scale * (family.circuit n).program.cost andOrCost <=
          20 * scale * (coefficient * (n + 1) ^ degree) := by
        gcongr
        simpa [Circuit.Family.cost, Circuit.cost] using costBound n
      _ <= growthCoefficient * scale ^ growthDegree := by
        simpa [n, growthCoefficient, growthDegree] using
          ParityParameters.scaledPolynomial_le
            coefficient degree depth scale scalePositive
      _ <= 2 ^ scale := growthFrom scale (le_max_left cutoff 1)
  have impossible : 2 ^ (scale + 1) <= 2 ^ scale := lower.trans upper
  have strict : 2 ^ scale < 2 ^ (scale + 1) :=
    Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self scale)
  exact (Nat.not_lt_of_ge impossible) strict

/-- Compatibility specialization to families with checked input-level
negations. -/
theorem not_computes_parity
    (family : Algebraic.Circuit.Family signature 1)
    (polynomialCost : family.HasPolynomialCost andOrCost)
    (constantDepth : HasConstantLogicalDepth family)
    (_negationsAtInputs : forall n,
      Program.NegationsAtInputs (family.circuit n).program) :
    Not (family.Computes interpretation Parity.targetFamily) :=
  not_computes_parity_raw family polynomialCost constantDepth

end Family

/-- The parity target family is not computable by nonuniform AC0 as defined
by the library's checked source model. -/
theorem parity_not_computable :
    Not (Computable Parity.targetFamily) := by
  rintro ⟨family, computes, polynomialCost, constantDepth,
    negationsAtInputs⟩
  exact Family.not_computes_parity family polynomialCost constantDepth
    negationsAtInputs computes

/-- Parity is not computable even in the raw presentation that allows NOT
gates at arbitrary internal wires. This conclusion is now direct and does not
pass through dual-rail normalization. -/
theorem parity_not_raw_computable :
    Not (RawComputable Parity.targetFamily) := by
  rintro ⟨family, computes, polynomialCost, constantDepth⟩
  exact Family.not_computes_parity_raw family polynomialCost constantDepth
    computes

end AC0
end Algebraic
