/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Diagonal.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Log

/-!
# One computable family of periodic dissociated-cluster tensors

The paired-cluster construction uses a size-dependent order chosen by bounded search.
Admissibility simultaneously bounds coefficient bit length and the finite rank error.
The definition is independent of any requested approximation to the leading coefficient.
This is a computable formula, not a machine-level polynomial-time certificate.
-/

@[expose] public section

namespace Algebraic.Tensor3.Dissociated

/-- Enough indices for a dissociated cluster of size `2p+1`. -/
def selectionSize (p : ℕ) : ℕ := 3 ^ (2 * p) + 1

/-- The block length makes the relative survivor loss exactly `1/(p+1)`. -/
def blockLength (p : ℕ) : ℕ := (p + 1) * selectionSize p

/-- Slice-label period. -/
def rowPeriod (p : ℕ) : ℕ := blockLength p + 1

/-- Column-label period. -/
def columnPeriod (p : ℕ) : ℕ := p * blockLength p + 1

/-- The finite checks needed for the rank estimate and linear coefficient bit bound. -/
def Admissible (k p : ℕ) : Prop :=
  1 ≤ p ∧ p ≤ Nat.log 2 (2 * k + 1) ∧ blockLength p ≤ k ∧
    rowPeriod p * columnPeriod p ≤ Nat.log 2 (2 * k + 1) ∧
    (p + 1) * (16 * (p + 1) * blockLength p + 2) ≤ 2 * k + 1

instance (k p : ℕ) : Decidable (Admissible k p) := by
  unfold Admissible
  infer_instance

/-- The finite search considers at most logarithmically many orders. -/
def candidates (k : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 (2 * k + 1) + 1)).filter (Admissible k)

/-- The largest admissible order, or zero before the first admissible order appears. -/
def order (k : ℕ) : ℕ := (candidates k).sup id

/-- Integer coordinates of the odd-dimensional tensor, with zero below the onset. -/
def oddEntry (k a j l : ℕ) : ℕ :=
  if Admissible k (order k) then
    if (l : ℤ) = j + ((a : ℤ) - k) then
      2 ^ 2 ^ (a % rowPeriod (order k) * columnPeriod (order k) +
        j % columnPeriod (order k))
    else 0
  else 0

/-- The odd-dimensional complex tensor has the specified integer coordinates. -/
def oddTensor (k : ℕ) : Tensor3 (Fin (2 * k + 1)) (Fin (2 * k + 1)) (Fin (2 * k + 1)) :=
  fun a j l => (oddEntry k a j l : ℂ)

/-- The odd-dimensional core used at an arbitrary ambient dimension. -/
def coreIndex (m : ℕ) : ℕ := (m - 1) / 2

/-- Integer entries in every dimension, padding the odd core by zeros. -/
def entry (m a j l : ℕ) : ℕ :=
  if a < 2 * coreIndex m + 1 ∧ j < 2 * coreIndex m + 1 ∧ l < 2 * coreIndex m + 1 then
    oddEntry (coreIndex m) a j l
  else 0

/-- A single tensor family indexed by its full ambient dimension. -/
def tensor (m : ℕ) : Tensor3 (Fin m) (Fin m) (Fin m) :=
  fun a j l => (entry m a j l : ℂ)

end Algebraic.Tensor3.Dissociated
