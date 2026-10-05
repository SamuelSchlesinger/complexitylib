/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.Dissociated.Defs
public import Complexitylib.Algebraic.LinearAlgebra.Tensor.BorderRank
public import Mathlib.Data.Nat.Size
import Complexitylib.Algebraic.LinearAlgebra.Tensor.Dissociated.Internal

/-!
# A single integer-entry tensor family of border rank `(7/3-o(1)) m`

The computable family `Dissociated.tensor m` is independent of epsilon, is defined
at every dimension by zero padding an odd core, and has coefficient binary length
at most `m+1`. Its complex border rank is eventually at least `(7/3-ε)m` for every
positive epsilon. In particular it eventually has border rank at least `17m/8`.

This uniformizes the checked periodic paired-cluster construction. The motivating
research note, *Distinct subset sums and explicit tensor border rank*, Revision 2,
uses the same dissociated-cluster and periodic coefficient ideas to approach `17/8`.
Here the existing stronger paired-cluster proof replaces its five-far-diagonal
branch. All tensor-theoretic inputs are proved in the library: substitution,
Koszul flattenings, block nonsingularity, and the deletion game.

The entry formula and bounded parameter search are computable, and their binary
output size is polynomial. A polynomial-time machine implementation is not proved
by these declarations; output-size bounds alone do not certify running time.
-/

public section

namespace Algebraic.Tensor3.Dissociated

open Filter

/-- The order search never exceeds the binary logarithm of the odd core dimension. -/
theorem order_le_log (k : ℕ) : order k ≤ Nat.log 2 (2 * k + 1) :=
  Internal.order_le_log k

/-- The admissible candidate set has at most logarithmically many elements. -/
theorem card_candidates_le (k : ℕ) : (candidates k).card ≤ Nat.log 2 (2 * k + 1) + 1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- Every fixed positive order eventually becomes admissible in the uniform search. -/
theorem eventually_admissible {p : ℕ} (hp : 1 ≤ p) : ∀ᶠ k in atTop, Admissible k p :=
  Internal.eventually_admissible hp

/-- The selected cluster order tends to infinity. -/
theorem order_tendsto : Tendsto order atTop atTop :=
  tendsto_atTop.2 Internal.eventually_le_order

/-- The finite rank guarantee once the selected order passes the construction's checks. -/
theorem odd_lowerBound_of_admissible {k : ℕ} (hk : Admissible k (order k)) :
    (7 / 3 - 8 / (3 * ((order k : ℝ) + 1))) * (2 * k + 1) ≤ (oddTensor k).borderRank :=
  Internal.lowerBound_of_admissible hk

/-- Every valid tensor coefficient has at most `m+1` binary digits. -/
theorem entry_size_le (m : ℕ) (a j l : Fin m) : (entry m a j l).size ≤ m + 1 :=
  Internal.entry_size_le a.isLt j l

/-- Every coordinate is a nonnegative integer with the stated binary-size bound. -/
theorem tensor_entry (m : ℕ) (a j l : Fin m) :
    ∃ v : ℕ, v.size ≤ m + 1 ∧ tensor m a j l = (v : ℂ) :=
  ⟨entry m a j l, entry_size_le m a j l, rfl⟩

/-- The dense coordinate array has polynomial total binary output size. -/
theorem sum_entry_size_le (m : ℕ) :
    (∑ a : Fin m, ∑ j : Fin m, ∑ l : Fin m, (entry m a j l).size) ≤ m ^ 3 * (m + 1) := by
  calc
    _ ≤ ∑ _a : Fin m, ∑ _j : Fin m, ∑ _l : Fin m, (m + 1) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum fun l _ => entry_size_le m a j l
    _ = _ := by simp [pow_succ]; ring

/-- The same computable family has border rank `(7/3-o(1))m` at all dimensions. -/
theorem eventually_sub_mul_le_borderRank {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, (7 / 3 - ε) * (m : ℝ) ≤ (tensor m).borderRank :=
  Internal.eventually_lowerBound hε

/-- In particular the single integer-entry family eventually exceeds the note's `17/8` target. -/
theorem eventually_seventeen_div_eight_mul_le_borderRank :
    ∀ᶠ m : ℕ in atTop, (17 / 8 : ℝ) * m ≤ (tensor m).borderRank := by
  convert eventually_sub_mul_le_borderRank (ε := 5 / 24) (by norm_num) using 1
  norm_num

end Algebraic.Tensor3.Dissociated
