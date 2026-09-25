/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SortingSemantics.Defs
public import Mathlib.Data.Fintype.Pi

/-!
# Finite Boolean core of bitonic cleaning

The eight-value closure lemma is proved by kernel reduction.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Sorting
namespace Semantics
namespace Internal

private instance instDecidableSequenceBitonic {n : ℕ} [LinearOrder α]
    (sequence : Fin n → α) : Decidable (SequenceBitonic sequence) := by
  -- Test each index inequality before enumerating the remaining indices.
  exact decidable_of_iff
    (∀ i j, i < j → ∀ k, j < k → ∀ l, k < l →
      min (sequence i) (sequence k) ≤ max (sequence j) (sequence l) ∧
        min (sequence j) (sequence l) ≤ max (sequence i) (sequence k))
    ⟨fun h i j k l hij hjk hkl => h i j hij k hjk l hkl,
      fun h i j hij k hjk l hkl => h i j k l hij hjk hkl⟩

/-- Pairwise minima of the two Boolean halves used by the finite cleaning
check. -/
def boolHalfMin (sequence : Fin 8 → Bool) : Fin 4 → Bool :=
  fun i => min (sequence (Fin.castAdd 4 i)) (sequence (Fin.natAdd 4 i))

/-- Pairwise maxima of the two Boolean halves used by the finite cleaning
check. -/
def boolHalfMax (sequence : Fin 8 → Bool) : Fin 4 → Bool :=
  fun i => max (sequence (Fin.castAdd 4 i)) (sequence (Fin.natAdd 4 i))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem boolBitonicHalves
    (sequence : Fin 8 → Bool) (hsequence : SequenceBitonic sequence) :
    SequenceBitonic (boolHalfMin sequence) ∧
      SequenceBitonic (boolHalfMax sequence) := by
  decide +revert +kernel

end Internal
end Semantics
end Sorting
end MassProduction
end Algebraic
