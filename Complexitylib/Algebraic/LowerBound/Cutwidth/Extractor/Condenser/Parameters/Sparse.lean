/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Sparse.Defs
public import Mathlib.Basic.Real.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Sparse.Internal

/-!
# Sparse field sizes preserving the condenser output rate

For a target rate `1 + 1/u`, round `(u+1)*T` up to a field bit length
`b = 2 * 3^s`, and then choose the powering bit length `r = b-T`.
The rate inequality `u*b ≤ (u+1)*r` survives this sparse rounding.
For `m = ceil(k/r)`, the coordinate count is at most `k`, and the output
length satisfies `u*(m*b) ≤ (u+1)*k + u*b`.

These finite inequalities are a parameter choice for the binomial modulus
family. They adapt the field-size and powering tradeoff in Cheraghchi's
2010 thesis, Corollary 2.23, to a sparse grid; this grid choice is our
deduction, not a statement attributed to that source:
https://arxiv.org/pdf/1107.4709.
The normalized degree loss is at most `error` whenever
`D*k ≤ error*2^T`. No asymptotic bound, field construction, or runtime
certificate is claimed here.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The selected field bit length covers the entire rate and error budget. -/
theorem sparseFieldBits_lower (u T : Nat) :
    (u + 1) * T ≤ sparseFieldBits u T :=
  Internal.sparseFieldBits_lower u T

/-- Sparse rounding costs at most a fixed factor in field bit length. -/
theorem sparseFieldBits_upper {u T : Nat} (positive : 0 < T) :
    sparseFieldBits u T ≤ 6 * ((u + 1) * T) :=
  Internal.sparseFieldBits_upper positive

/-- The powering and slack bit lengths add up to the field bit length. -/
theorem sparsePowerBits_add {u T : Nat} :
    sparsePowerBits u T + T = sparseFieldBits u T :=
  Internal.sparsePowerBits_add

/-- Positive rate and slack parameters leave a positive powering bit length. -/
theorem sparsePowerBits_pos {u T : Nat} (rate : 0 < u) (positive : 0 < T) :
    0 < sparsePowerBits u T :=
  Internal.sparsePowerBits_pos rate positive

/-- The exact integer inequality expressing the target output rate `1+1/u`. -/
theorem sparsePowerBits_rate (u T : Nat) :
    u * sparseFieldBits u T ≤ (u + 1) * sparsePowerBits u T :=
  Internal.sparsePowerBits_rate u T

/-- Ceiling division supplies enough coordinates to carry all `k` bits. -/
theorem condenserCoordinates_capacity {k r : Nat} (positive : 0 < r) :
    k ≤ r * condenserCoordinates k r :=
  Internal.condenserCoordinates_capacity positive

/-- A positive bit capacity per coordinate requires at most `k` coordinates. -/
theorem condenserCoordinates_le {k r : Nat} (positive : 0 < r) :
    condenserCoordinates k r ≤ k :=
  Internal.condenserCoordinates_le positive

/-- Ceiling division costs at most one additional field element in output length. -/
theorem condenserCoordinates_output {u k r b : Nat}
    (rate : u * b ≤ (u + 1) * r) :
    u * (condenserCoordinates k r * b) ≤ (u + 1) * k + u * b :=
  Internal.condenserCoordinates_output rate

/-- The elementary degree-loss budget after choosing a power-of-two field size. -/
theorem condenserCoordinates_loss {D k r T : Nat} {error : ℝ}
    (positive : 0 < r) (budget : (D * k : ℝ) ≤ error * 2 ^ T) :
    (((D - 1) * (2 ^ r - 1) * condenserCoordinates k r : Nat) : ℝ) /
      2 ^ (r + T) ≤ error :=
  Internal.condenserCoordinates_loss positive budget

/-- The output-rate bound specialized to the sparse field bit length. -/
theorem sparseCondenser_output {u T k : Nat} :
    u * (condenserCoordinates k (sparsePowerBits u T) * sparseFieldBits u T) ≤
      (u + 1) * k + u * sparseFieldBits u T :=
  Internal.sparseCondenser_output

/-- The exact normalized loss bound specialized to the sparse field bit length. -/
theorem sparseCondenser_loss {u T D k : Nat} {error : ℝ}
    (rate : 0 < u) (positive : 0 < T) (budget : (D * k : ℝ) ≤ error * 2 ^ T) :
    (((D - 1) * (2 ^ sparsePowerBits u T - 1) *
      condenserCoordinates k (sparsePowerBits u T) : Nat) : ℝ) /
        2 ^ sparseFieldBits u T ≤ error :=
  Internal.sparseCondenser_loss rate positive budget

end Algebraic.Cutwidth.Extractor
