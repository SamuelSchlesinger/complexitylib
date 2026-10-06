/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.MatMul.Tripartite.Defs
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Arithmetic matrix multiplication: definitions

* `matMulPolynomial K n`: the outputs `C i k = ∑ j, A i j B j k` of `n × n` matrix
  multiplication as polynomials in the `2 n²` inputs, with coefficients in `K`; it is `matMul n`
  evaluated at the variables.

The Jacobian of matrix multiplication at a point `(A₀, B₀)` sends a change `(δA, δB)` to
`δA B₀ + A₀ δB`: the entry of the output `C i k` at the input `A i' j` is `[i = i'] B₀ j k`, and
at the input `B j k'` it is `[k = k'] A₀ i j`. Its blocks between a set `Y` of outputs and a set
`X` of inputs have rank bounded below by the following sums, in the notation of
`MatMul.Tripartite.Defs`. Here `cY` holds the pairs `(i, k)` with `C i k ∈ Y`, and `aX` and `bX`
the pairs `(i, j)` and `(j, k)` with `A i j ∈ X` and `B j k ∈ X`; `H` is a set of row (or column)
vertices.

* `Tripartite.jacobianRows cY aX bX H`: the sum over the rows `i ∈ H` of
  `min (#{k : C i k ∈ Y}, #{j : A i j ∈ X})`, plus the sum over the columns `k` of
  `min (#{i ∉ H : C i k ∈ Y}, #{j : B j k ∈ X})`.
* `Tripartite.jacobianCols cY aX bX H`: the mirror image, with rows and columns and the two
  factors exchanged.

For a split `S` with placed terminals `a`, `b`, `c` (`Tripartite.place`):

* `Tripartite.jacobianChargeI a b c` charges the forward block (outputs outside `S`, inputs in
  `S`) with `H` the heavy rows, and the backward block (outputs in `S`, inputs outside `S`) with
  `H` the light rows;
* `Tripartite.jacobianChargeK a b c` does the same with the columns.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

/-- **Matrix multiplication as polynomials.** The output `C i k` is the polynomial
`∑ j, X (A i j) X (B j k)` in the `2 n²` inputs: `matMul n` at the variables. -/
noncomputable def matMulPolynomial (K : Type*) [CommSemiring K] (n : Nat) :
    Fin (n * n) → MvPolynomial (Fin (n * n + n * n)) K :=
  matMul n MvPolynomial.X

namespace Tripartite

variable {n : Nat}

/-- The Jacobian charge of a block of rows: blocks of rows `i ∈ H` against the inputs `A i j`,
then blocks of columns `k` against the inputs `B j k`, with the rows `i ∉ H` only. -/
def jacobianRows (cY aX bX : Finset (Fin n × Fin n)) (H : Finset (Fin n)) : Nat :=
  (∑ i, if i ∈ H then min (rowSet cY i).card (rowSet aX i).card else 0) +
    ∑ k, min (colSet cY k \ H).card (colSet bX k).card

/-- The Jacobian charge of a block of columns: blocks of columns `k ∈ H` against the inputs
`B j k`, then blocks of rows `i` against the inputs `A i j`, with the columns `k ∉ H` only. -/
def jacobianCols (cY aX bX : Finset (Fin n × Fin n)) (H : Finset (Fin n)) : Nat :=
  (∑ k, if k ∈ H then min (colSet cY k).card (colSet bX k).card else 0) +
    ∑ i, min (rowSet cY i \ H).card (rowSet aX i).card

/-- **The row Jacobian charge** of a split placing `a`, `b`, `c`: the forward block with the
heavy rows and the backward block with the light rows. -/
def jacobianChargeI (a b c : Finset (Fin n × Fin n)) : Nat :=
  jacobianRows cᶜ a b (heavyI a c) + jacobianRows c aᶜ bᶜ (heavyI a c)ᶜ

/-- **The column Jacobian charge** of a split placing `a`, `b`, `c`: the forward block with the
heavy columns and the backward block with the light columns. -/
def jacobianChargeK (a b c : Finset (Fin n × Fin n)) : Nat :=
  jacobianCols cᶜ a b (heavyK b c) + jacobianCols c aᶜ bᶜ (heavyK b c)ᶜ

end Tripartite

end Algebraic.Cutwidth.MultiOutput
